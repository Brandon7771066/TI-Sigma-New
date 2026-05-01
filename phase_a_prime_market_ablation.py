"""
Phase A-prime-Market Ablation: Strict-Ternary I-Ching SPY Prediction
=====================================================================
Runs the I-Ching market predictor on a locked 60-trading-day historical
window with TWO bug fixes per `URB_825_CROSS_DOMAIN_DIVINATION_AUDIT.md`:

  Fix #1: Strict ternary equality (no credit-for-near-miss)
          correct iff pred_direction == actual_direction
  Fix #2: Hard-fail if yfinance returns no data (no synthetic fallback)

Pre-registered prediction (AGENT_LOCKED_PREDICTIONS_2026-04-30.md §2, MEDIUM):
  hit_rate = 33.2%, band [29%, 38%], horizon 5 trading days, N≈60 windows.
  Falsification: hit rate ≥ 38% with binomial p < 0.05.

Note: NEUTRAL band is ±1% return; horizon is 5 calendar days fwd-looking
(matched to existing IChingPredictor logic, not changed).

Date: 2026-04-30 (DPES session, locked seed)
Cost: $0
"""

import os
import sys
import random
from datetime import date, timedelta
from math import sqrt

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import yfinance as yf
from divination_empirical_testing import IChingPredictor, CombinedPSIPredictor


PRED = {
    'point': 0.332,
    'band_lo': 0.29,
    'band_hi': 0.38,
    'falsify_thr': 0.38,
    'lock_date': '2026-04-30',
    'source': 'AGENT_LOCKED_PREDICTIONS_2026-04-30.md §2',
}

LOCK_DATE = date(2026, 4, 30)
LOCK_SEED_MARKET = 20573  # same seed-base as Phase 4-bis
HORIZON_DAYS = 5
NEUTRAL_BAND = 0.01  # ±1% return = NEUTRAL (matches existing logic)
SYMBOL = 'SPY'
WINDOW_TRADING_DAYS = 60


def fetch_prices(symbol: str, start: date, end: date) -> dict:
    """Hard-fail on empty / missing data. No synthetic fallback."""
    ticker = yf.Ticker(symbol)
    hist = ticker.history(start=start, end=end + timedelta(days=1))
    if hist.empty:
        raise RuntimeError(f"yfinance returned empty data for {symbol} {start}..{end}")
    return {d.date(): float(row['Close']) for d, row in hist.iterrows()}


def label_direction(ret: float) -> str:
    if ret > NEUTRAL_BAND:
        return "BULLISH"
    if ret < -NEUTRAL_BAND:
        return "BEARISH"
    return "NEUTRAL"


def main():
    print("=" * 72)
    print("PHASE A-PRIME-MARKET ABLATION (strict ternary, hard-fail data)")
    print("=" * 72)
    print(f"Pre-registered prediction (locked {PRED['lock_date']}):")
    print(f"  hit_rate = {PRED['point']*100:.1f}%  band [{PRED['band_lo']*100:.0f}%, {PRED['band_hi']*100:.0f}%]")
    print(f"  Falsification: hit rate ≥ {PRED['falsify_thr']*100:.0f}% with binomial p < 0.05")
    print(f"  Source: {PRED['source']}")
    print()

    end = LOCK_DATE
    start = end - timedelta(days=int(WINDOW_TRADING_DAYS * 1.5) + 30)
    print(f"Fetching {SYMBOL} prices {start} .. {end + timedelta(days=HORIZON_DAYS+10)}")
    prices = fetch_prices(SYMBOL, start - timedelta(days=10),
                          end + timedelta(days=HORIZON_DAYS + 10))
    trading_days = sorted(prices.keys())
    eligible_starts = [d for d in trading_days if d <= end - timedelta(days=HORIZON_DAYS+5)]
    eligible_starts = eligible_starts[-WINDOW_TRADING_DAYS:]
    print(f"  Got {len(prices)} trading days; {len(eligible_starts)} eligible prediction windows")
    print()

    # Reproducibility: seed the IChingPredictor's RNG via random module
    # (the IChing predictor uses random.randint internally for line casts)
    predictor = IChingPredictor()

    rows = []
    correct = 0
    direction_counts = {"BULLISH": 0, "BEARISH": 0, "NEUTRAL": 0}
    for i, d_start in enumerate(eligible_starts):
        # Per-window deterministic seed = LOCK_SEED + i so the same window
        # always casts the same hexagram across reruns
        random.seed(LOCK_SEED_MARKET + i)

        # Find the 5-trading-day-forward target
        future_days = [d for d in trading_days if d > d_start]
        if len(future_days) < HORIZON_DAYS:
            continue
        d_target = future_days[HORIZON_DAYS - 1]

        pred = predictor.predict_market(d_target, SYMBOL)
        ret = (prices[d_target] - prices[d_start]) / prices[d_start]
        actual_dir = label_direction(ret)
        # IChingPredictor returns UP/DOWN/FLAT — map to BULLISH/BEARISH/NEUTRAL
        ichingmap = {"UP": "BULLISH", "DOWN": "BEARISH", "FLAT": "NEUTRAL"}
        pred_dir = ichingmap.get(pred.predicted_value, pred.predicted_value)
        # Strict ternary equality — no credit-for-near-miss
        is_correct = (pred_dir == actual_dir)
        if is_correct:
            correct += 1
        direction_counts[pred_dir] = direction_counts.get(pred_dir, 0) + 1
        rows.append({
            'start': d_start, 'target': d_target,
            'pred': pred_dir, 'actual': actual_dir,
            'ret_pct': ret * 100, 'correct': is_correct,
        })

    n = len(rows)
    hit_rate = correct / n if n else 0.0
    # Binomial p-value vs base rate of 1/3 (random ternary), one-sided
    # Normal approx for speed
    p0 = 1.0 / 3.0
    if n >= 10:
        z = (hit_rate - p0) / sqrt(p0 * (1 - p0) / n)
        # one-sided p-value (right tail)
        from math import erf
        p_one_sided = 0.5 * (1 - erf(z / sqrt(2)))
    else:
        z, p_one_sided = float('nan'), float('nan')

    print(f"  N predictions: {n}")
    print(f"  Hits (strict ternary): {correct}/{n}")
    print(f"  Hit rate: {hit_rate*100:.2f}%")
    print(f"  Direction distribution: BULL={direction_counts['BULLISH']}  "
          f"BEAR={direction_counts['BEARISH']}  NEUT={direction_counts['NEUTRAL']}")
    print(f"  z vs 1/3: {z:+.3f}  one-sided p (right tail): {p_one_sided:.4f}")

    print()
    print("=" * 72)
    print("PHASE A-PRIME-MARKET PRE-REGISTRATION VERDICT")
    print("=" * 72)
    print(f"  Pre-registered: hit_rate = {PRED['point']*100:.1f}%  "
          f"band [{PRED['band_lo']*100:.0f}%, {PRED['band_hi']*100:.0f}%]")
    print(f"  Actual:         hit_rate = {hit_rate*100:.2f}%")
    if PRED['band_lo'] <= hit_rate <= PRED['band_hi']:
        verdict = "✅ WITHIN BAND — agent prediction confirmed"
    elif hit_rate >= PRED['falsify_thr'] and p_one_sided < 0.05:
        verdict = (f"❌ OUTSIDE BAND (HIGH) AND p<0.05 — divination market signal SURVIVES: "
                   f"hit rate {hit_rate*100:.1f}% > {PRED['falsify_thr']*100:.0f}% with p={p_one_sided:.4f}")
    elif hit_rate >= PRED['falsify_thr']:
        verdict = (f"⚠️  ABOVE FALSIFY-THR but p≥0.05 — hit rate {hit_rate*100:.1f}% suggestive "
                   f"but not significant (p={p_one_sided:.4f})")
    else:
        verdict = (f"❌ OUTSIDE BAND (LOW) — hit rate {hit_rate*100:.1f}% < {PRED['band_lo']*100:.0f}% — "
                   f"divination market signal absent or worse than predicted")
    print(f"  {verdict}")

    return rows, hit_rate, p_one_sided


if __name__ == '__main__':
    main()

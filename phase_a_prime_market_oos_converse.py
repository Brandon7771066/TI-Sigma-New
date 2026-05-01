"""
OOS Replication of §8.2 Anti-Correlation + Test of Brandon's Converse-Divination Claim
========================================================================================
Pre-registered at AGENT_LOCKED_PREDICTIONS_2026-04-30.md §10.2 (LOCKED 2026-04-30
AFTER §8.2 result was known — honest post-result pre-registration).

Tests Brandon's claim: "strong 'anti-divination' signals are ACTUALLY HIGH PRO-CONVERSE
DIVINATION SIGNALS!!! TI saves the day!!!"

Method: Same `phase_a_prime_market_ablation.py` script logic on a DIFFERENT historical
window (SPY 2024-06-01 .. 2024-12-31, no overlap with Feb-Apr 2026). Reports BOTH:
  - Original I-Ching hit rate (replication of §8.2 anti-correlation?)
  - Converse I-Ching hit rate (BULL↔BEAR inverted, NEUT→NEUT)

Pre-registered (§10.2):
  Original OOS hit rate: 33%, band [27%, 39%], LOW conviction
  Converse OOS hit rate: 33%, band [27%, 39%], LOW conviction
  Falsification of "noise" hypothesis: either tail with binomial p<0.05.
  Confirmation of Brandon's converse claim: converse > 39% with p < 0.05
                                            AND original < 27% with p < 0.05.

Date: 2026-04-30 (DPES session, locked seed)
Cost: $0
"""

import os
import sys
import random
from datetime import date, timedelta
from math import sqrt, erf

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import yfinance as yf
from divination_empirical_testing import IChingPredictor


PRED = {
    'point': 0.33,
    'band_lo': 0.27,
    'band_hi': 0.39,
    'lock_date': '2026-04-30',
    'source': 'AGENT_LOCKED_PREDICTIONS_2026-04-30.md §10.2',
}

LOCK_SEED_MARKET = 20573  # same seed-base as Phase 4-bis
HORIZON_DAYS = 5
NEUTRAL_BAND = 0.01
SYMBOL = 'SPY'

# OOS window — DIFFERENT from §8.2's Feb-Apr 2026 window
OOS_START = date(2024, 6, 1)
OOS_END = date(2024, 12, 31)


def fetch_prices(symbol, start, end):
    ticker = yf.Ticker(symbol)
    hist = ticker.history(start=start, end=end + timedelta(days=1))
    if hist.empty:
        raise RuntimeError(f"yfinance returned empty data for {symbol} {start}..{end}")
    return {d.date(): float(row['Close']) for d, row in hist.iterrows()}


def label_direction(ret):
    if ret > NEUTRAL_BAND:
        return "BULLISH"
    if ret < -NEUTRAL_BAND:
        return "BEARISH"
    return "NEUTRAL"


def converse_dir(d):
    if d == "BULLISH":
        return "BEARISH"
    if d == "BEARISH":
        return "BULLISH"
    return "NEUTRAL"  # NEUT stays per §10.2 spec


def two_sided_p(z):
    return 2 * (1 - 0.5 * (1 + erf(abs(z) / sqrt(2))))


def main():
    print("=" * 76)
    print("OOS REPLICATION + CONVERSE-DIVINATION TEST (§10.2)")
    print("=" * 76)
    print(f"Pre-registered (locked {PRED['lock_date']}, post-§8.2):")
    print(f"  Original OOS hit rate band: [{PRED['band_lo']*100:.0f}%, {PRED['band_hi']*100:.0f}%]")
    print(f"  Converse OOS hit rate band: [{PRED['band_lo']*100:.0f}%, {PRED['band_hi']*100:.0f}%]")
    print(f"  Source: {PRED['source']}")
    print(f"  OOS window: SPY {OOS_START} .. {OOS_END}")
    print()

    print(f"Fetching SPY prices...")
    prices = fetch_prices(SYMBOL, OOS_START - timedelta(days=10),
                          OOS_END + timedelta(days=HORIZON_DAYS + 10))
    trading_days = sorted(prices.keys())
    eligible = [d for d in trading_days
                if OOS_START <= d <= OOS_END - timedelta(days=HORIZON_DAYS + 5)]
    print(f"  Got {len(prices)} trading days; {len(eligible)} eligible windows")
    print()

    predictor = IChingPredictor()
    rows = []
    orig_correct = 0
    conv_correct = 0
    direction_counts = {"BULLISH": 0, "BEARISH": 0, "NEUTRAL": 0}
    actual_counts = {"BULLISH": 0, "BEARISH": 0, "NEUTRAL": 0}

    for i, d_start in enumerate(eligible):
        random.seed(LOCK_SEED_MARKET + i)
        future = [d for d in trading_days if d > d_start]
        if len(future) < HORIZON_DAYS:
            continue
        d_target = future[HORIZON_DAYS - 1]

        pred = predictor.predict_market(d_target, SYMBOL)
        ret = (prices[d_target] - prices[d_start]) / prices[d_start]
        actual = label_direction(ret)
        ichingmap = {"UP": "BULLISH", "DOWN": "BEARISH", "FLAT": "NEUTRAL"}
        pred_dir = ichingmap.get(pred.predicted_value, pred.predicted_value)
        conv_pred = converse_dir(pred_dir)

        is_orig_correct = (pred_dir == actual)
        is_conv_correct = (conv_pred == actual)
        if is_orig_correct:
            orig_correct += 1
        if is_conv_correct:
            conv_correct += 1
        direction_counts[pred_dir] += 1
        actual_counts[actual] += 1
        rows.append({
            'start': d_start, 'target': d_target,
            'pred': pred_dir, 'conv_pred': conv_pred, 'actual': actual,
            'ret_pct': ret * 100,
            'orig_correct': is_orig_correct, 'conv_correct': is_conv_correct,
        })

    n = len(rows)
    orig_hr = orig_correct / n
    conv_hr = conv_correct / n
    p0 = 1.0 / 3.0
    z_orig = (orig_hr - p0) / sqrt(p0 * (1 - p0) / n)
    z_conv = (conv_hr - p0) / sqrt(p0 * (1 - p0) / n)
    p_orig_two = two_sided_p(z_orig)
    p_conv_two = two_sided_p(z_conv)

    print(f"  N predictions: {n}")
    print(f"  Predicted direction distribution: BULL={direction_counts['BULLISH']}  "
          f"BEAR={direction_counts['BEARISH']}  NEUT={direction_counts['NEUTRAL']}")
    print(f"  Actual direction distribution:    BULL={actual_counts['BULLISH']}  "
          f"BEAR={actual_counts['BEARISH']}  NEUT={actual_counts['NEUTRAL']}")
    print()
    print(f"  ORIGINAL I-Ching hit rate:  {orig_correct}/{n} = {orig_hr*100:.2f}%  "
          f"(z={z_orig:+.3f}, two-sided p={p_orig_two:.4f})")
    print(f"  CONVERSE I-Ching hit rate:  {conv_correct}/{n} = {conv_hr*100:.2f}%  "
          f"(z={z_conv:+.3f}, two-sided p={p_conv_two:.4f})")
    print()

    # ────────────────────────────────────────────────────────────────────
    # Verdict per §10.2 decision matrix
    # ────────────────────────────────────────────────────────────────────
    print("=" * 76)
    print("§10.2 VERDICT")
    print("=" * 76)

    orig_in_band = PRED['band_lo'] <= orig_hr <= PRED['band_hi']
    conv_in_band = PRED['band_lo'] <= conv_hr <= PRED['band_hi']
    orig_anticorr_sig = (orig_hr < PRED['band_lo']) and (p_orig_two < 0.05)
    conv_signal_sig = (conv_hr > PRED['band_hi']) and (p_conv_two < 0.05)

    print(f"  Original in band [27%, 39%]:    {'YES' if orig_in_band else 'NO'}")
    print(f"  Converse in band [27%, 39%]:    {'YES' if conv_in_band else 'NO'}")
    print(f"  Anti-correlation REPLICATES?    "
          f"{'YES' if orig_anticorr_sig else 'NO'}  "
          f"(orig < 27% AND p < 0.05)")
    print(f"  Converse signal SURVIVES OOS?   "
          f"{'YES' if conv_signal_sig else 'NO'}  "
          f"(converse > 39% AND p < 0.05)")
    print()

    if conv_signal_sig and orig_anticorr_sig:
        verdict = ("✅✅ BRANDON'S CONVERSE-DIVINATION CLAIM CONFIRMED OUT-OF-SAMPLE — "
                   "TI Sigma 5-valued logic interpretation earned. Lock as URB #827.")
    elif orig_in_band and conv_in_band:
        verdict = ("❌ BOTH HIT RATES IN ~CHANCE BAND — Feb-Apr 2026 §8.2 result "
                   "regressed to chance OOS. Anti-correlation was likely noise. "
                   "Brandon's converse claim NOT supported on this OOS window.")
    elif orig_anticorr_sig and not conv_signal_sig:
        verdict = ("⚠️  Anti-correlation REPLICATED but converse hit rate is not "
                   "significantly above chance — confusing pattern, likely involves "
                   "high NEUT prediction count without clean inversion. Re-design needed.")
    elif conv_signal_sig and not orig_anticorr_sig:
        verdict = ("⚠️  Converse hit rate beat chance significantly but original NOT "
                   "significantly anti-correlated — inconsistent with Brandon's framing. "
                   "Possible converse-via-prediction-distribution-bias artifact.")
    else:
        verdict = ("❌ MIXED / NOISY — neither claim survives clean OOS test. "
                   "Need much larger N (~300+) across multiple regimes.")
    print(f"  {verdict}")

    # Cross-window comparison
    print()
    print("=" * 76)
    print("CROSS-WINDOW SUMMARY")
    print("=" * 76)
    print(f"  Feb-Apr 2026 (§8.2):   original = 21.67% (13/60),  z=-1.917, p_one=0.028 LOW")
    print(f"  2024-06 .. 2024-12:    original = {orig_hr*100:.2f}% ({orig_correct}/{n}), "
          f"z={z_orig:+.3f}, p_two={p_orig_two:.4f}")
    print(f"  2024-06 .. 2024-12:    converse = {conv_hr*100:.2f}% ({conv_correct}/{n}), "
          f"z={z_conv:+.3f}, p_two={p_conv_two:.4f}")

    return rows, orig_hr, conv_hr, p_orig_two, p_conv_two


if __name__ == '__main__':
    main()

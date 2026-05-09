"""
LCC Program A — Bidirectional LCC in Stock Markets (Pass 16 first-cut runner).

Pre-registration: papers/LCC_BIDIRECTIONAL_VALIDATION_AND_BOK_VIRUS_EXPERIMENTS.md
Brandon's directive (Pass 16): "Try applying all of the above to LCC
Program A stock-market runner."

Method:
  1. Fetch 1y daily closes for N curated equity pairs via yfinance.
  2. Compute Gaussian-weighted lagged cross-correlation R(A, B) per the
     pre-reg formula (sigma = 5 lag-units, lag-window +/- 20 days).
  3. Compare R against C_EMERICK = 1/(phi*sqrt(2)) ≈ 0.4370.
  4. For each pair, additionally compute simple lag-1 forward + reverse
     Pearson correlations as a bidirectional-asymmetry sanity check.
  5. Report Fisher-z 95% CIs.

#69 caveats:
  - statsmodels not installed in this env; cannot run formal Granger
    causality. We report only correlation-based results this Pass.
  - N pairs is small (8); look-elsewhere correction = pairs * lag-window.
  - Network fetches via yfinance can fail; failures are reported, not
    silenced.

Seed: 20260509.
"""
import math
import sys
import warnings
from pathlib import Path

import numpy as np
import pandas as pd

warnings.filterwarnings("ignore")

PHI = (1 + math.sqrt(5)) / 2
C_EMERICK = 1 / (PHI * math.sqrt(2))   # ~0.43701602
SIGMA_LAG = 5.0
LAG_WINDOW = 20
SEED = 20260509
np.random.seed(SEED)

PAIRS = [
    # Within-sector (expected coupling)
    ("AAPL", "MSFT"),
    ("JPM", "GS"),
    ("XOM", "CVX"),
    ("KO", "PEP"),
    # Cross-sector (expected weak coupling)
    ("AAPL", "JPM"),
    ("XOM", "AAPL"),
    # Energy ETF vs commodity proxy
    ("XLE", "USO"),
    # Index vs leader
    ("SPY", "AAPL"),
]


def fetch_pair(a, b, period="1y"):
    """Fetch daily closes for two tickers, aligned on common dates."""
    import yfinance as yf
    df = yf.download([a, b], period=period, progress=False,
                     auto_adjust=True, threads=False)["Close"]
    if df is None or df.empty:
        return None
    df = df.dropna()
    if len(df) < 60:
        return None
    return df


def gaussian_weighted_lagged_xcorr(x, y, sigma=SIGMA_LAG, max_lag=LAG_WINDOW):
    """LCC R(A,B) per pre-reg formula (sec 1.1).
    R = sum_tau corr(A_t, B_{t+tau}) * W(tau), W Gaussian, sigma=sigma.
    """
    x = np.asarray(x, dtype=float); y = np.asarray(y, dtype=float)
    x = (x - x.mean()) / (x.std() if x.std() > 0 else 1.0)
    y = (y - y.mean()) / (y.std() if y.std() > 0 else 1.0)
    lags = np.arange(-max_lag, max_lag + 1)
    weights = np.exp(-0.5 * (lags / sigma) ** 2)
    weights = weights / weights.sum()
    rs = []
    for tau in lags:
        if tau >= 0:
            xt = x[: len(x) - tau]; yt = y[tau:]
        else:
            xt = x[-tau:]; yt = y[: len(y) + tau]
        if len(xt) < 5: rs.append(0.0); continue
        c = np.corrcoef(xt, yt)[0, 1]
        rs.append(c if not math.isnan(c) else 0.0)
    R = float(np.dot(weights, rs))
    return R, lags, np.asarray(rs)


def fisher_z_ci(r, n, alpha=0.05):
    if abs(r) >= 0.999 or n <= 4:
        return (None, None)
    z = 0.5 * math.log((1 + r) / (1 - r))
    se = 1 / math.sqrt(n - 3)
    crit = 1.96 if alpha == 0.05 else 2.576
    lo = math.tanh(z - crit * se); hi = math.tanh(z + crit * se)
    return lo, hi


def asymmetric_lag1(x, y):
    """Forward: corr(x_t, y_{t+1}) ; reverse: corr(y_t, x_{t+1}).
    Bidirectional coupling => both nonzero; one-way => one dominates.
    """
    fwd = np.corrcoef(x[:-1], y[1:])[0, 1]
    rev = np.corrcoef(y[:-1], x[1:])[0, 1]
    return float(fwd), float(rev)


def main():
    print("=" * 70)
    print("LCC Program A — Bidirectional LCC stock-market runner (Pass 16)")
    print("=" * 70)
    print(f"C_EMERICK = 1/(phi*sqrt(2)) = {C_EMERICK:.5f}")
    print(f"Pairs: {len(PAIRS)}; sigma_lag = {SIGMA_LAG}; lag-window = +/- {LAG_WINDOW}")
    print()
    rows = []
    for a, b in PAIRS:
        try:
            df = fetch_pair(a, b)
        except Exception as e:
            print(f"  {a}/{b}: fetch FAILED -> {e}"); continue
        if df is None:
            print(f"  {a}/{b}: insufficient data"); continue
        # Use log-returns to avoid trend dominance
        ret = np.log(df).diff().dropna()
        x = ret[a].values; y = ret[b].values
        n = len(x)
        R, lags, rs = gaussian_weighted_lagged_xcorr(x, y)
        lo, hi = fisher_z_ci(R, n)
        fwd, rev = asymmetric_lag1(x, y)
        above = "ABOVE" if R >= C_EMERICK else "below"
        rows.append({
            "pair": f"{a}/{b}", "n_days": n, "R_lcc": R,
            "ci_lo": lo, "ci_hi": hi, "fwd_lag1": fwd, "rev_lag1": rev,
            "above_C": R >= C_EMERICK,
            "asym": abs(fwd - rev),
        })
        ci_str = f"[{lo:+.3f},{hi:+.3f}]" if lo is not None else "[CI N/A]"
        print(f"  {a:>5}/{b:<5}  N={n:4d}  R_lcc={R:+.4f} {ci_str:20s} "
              f"{above} C  fwd={fwd:+.3f} rev={rev:+.3f}  |asym|={abs(fwd-rev):.3f}")

    if not rows:
        print("\nNo pairs returned data; aborting summary.")
        return 1

    print()
    print("## Summary")
    above = [r for r in rows if r["above_C"]]
    below = [r for r in rows if not r["above_C"]]
    print(f"  Pairs at or above C_EMERICK = {C_EMERICK:.4f}: {len(above)} / {len(rows)}")
    if above:
        for r in above:
            print(f"    {r['pair']}  R={r['R_lcc']:+.4f}  fwd-rev asym={r['asym']:.3f}")
    print()
    print("  Pre-reg falsification anchor: pairs above C should show LARGER")
    print("  bidirectional-asymmetry magnitude than pairs below C, IF the")
    print("  C_EMERICK-gated bidirectionality conjecture holds.")
    if above and below:
        a_asym = np.mean([r["asym"] for r in above])
        b_asym = np.mean([r["asym"] for r in below])
        print(f"  mean |fwd-rev| above C: {a_asym:.4f}")
        print(f"  mean |fwd-rev| below C: {b_asym:.4f}")
        print(f"  delta: {a_asym - b_asym:+.4f} ({'supports' if a_asym > b_asym else 'CONTRA'} pre-reg)")
    print()
    print("## #69 caveats")
    print("  - statsmodels not installed; no formal Granger causality this run.")
    print("  - N pairs = 8 (curated); look-elsewhere correction not applied.")
    print("  - Lag-1 asymmetry is a coarse proxy for bidirectional causality.")
    print("  - Sector-pair selection is non-blind; future runs should sample randomly.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

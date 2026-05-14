"""Pass-49 L-1 — Program A: Bidirectional LCC in Markets, FIRST WINDOW.

Pre-registered per `papers/LCC_BIDIRECTIONAL_VALIDATION_AND_BOK_VIRUS_EXPERIMENTS.md`
§2 with one DEVIATION (honestly logged):

DEVIATION: The pre-registered PRIMARY dyad is #6 UMCSENT (FRED, monthly)
× SPY (yfinance, monthly). FRED access requires `pandas_datareader` which
is NOT installed in this environment. Pass-49 L-1 substitutes daily dyad
#1 SPY × ^VIX (both yfinance, available) as the FIRST-WINDOW result.

The dyad-#6 PRIMARY result is DEFERRED to Pass-50 (after pandas_datareader
install or direct FRED CSV fetch). Per Program A §2.5 stop-rule, this
deviation is logged and does NOT permit re-running on dyad #6 once
pandas_datareader is available — that is a SEPARATE pre-registered window.

PRE-FROZEN PARAMETERS (from §2.5):
  C_EMERICK = 1/(phi*sqrt(2)) ≈ 0.43701602
  Window = 60 trading days, step = 5 days
  σ (Gaussian lag kernel) = 5 days
  Max lag ±10 days
  Granger lags {1,2,3,4,5}; Bonferroni-correct across 5 lags per direction
  α = 0.01

#69 caveat: per the Pass-48 architect-review CRITICAL finding (and the
2026-05-13 update to PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN), the
algebraic form 1/(phi*sqrt(2)) for the C_EMERICK threshold is a
CONJECTURAL FIT pending Track-C M5 first-principles derivation. We
faithfully use the empirical value 0.4370 as pre-registered, and report
the closed-form alongside as the conjectural fit.
"""
from __future__ import annotations
import json, math, hashlib
from pathlib import Path
from datetime import date

import numpy as np
import pandas as pd
import yfinance as yf
from scipy.stats import f as f_dist, fisher_exact
import warnings
warnings.filterwarnings("ignore")


def _ols_ssr(X: np.ndarray, y: np.ndarray) -> tuple[float, int]:
    """Return (sum-of-squared-residuals, n_params) for OLS y ~ X."""
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    resid = y - X @ coef
    return float(resid @ resid), X.shape[1]


def granger_causality_min_p(y: np.ndarray, x: np.ndarray, lags=(1, 2, 3, 4, 5)) -> float:
    """Hand-rolled Granger causality test: H0 = x does NOT Granger-cause y.
    Returns the minimum p-value across the lag set (caller does Bonferroni).
    Replaces statsmodels.tsa.stattools.grangercausalitytests since
    statsmodels could not be installed (broken `github` build dependency).
    Uses the standard SSR-F-test formulation:
      restricted: y_t ~ const + sum lag_i y_{t-i}
      full:       y_t ~ const + sum lag_i y_{t-i} + sum lag_i x_{t-i}
      F = ((SSR_r - SSR_f)/L) / (SSR_f/(n - 2L - 1))
      p = 1 - F.cdf(F; L, n - 2L - 1)
    """
    pmin = 1.0
    for L in lags:
        if len(y) < 3 * L + 5:
            continue
        n = len(y) - L
        Y = y[L:]
        # Build lag matrices
        ny, nx = len(y), len(x)
        ylag = np.column_stack([y[L - i - 1: ny - i - 1] for i in range(L)])
        xlag = np.column_stack([x[L - i - 1: nx - i - 1] for i in range(L)])
        const = np.ones((n, 1))
        Xr = np.column_stack([const, ylag])
        Xf = np.column_stack([const, ylag, xlag])
        ssr_r, _ = _ols_ssr(Xr, Y)
        ssr_f, _ = _ols_ssr(Xf, Y)
        df1, df2 = L, n - 2 * L - 1
        if df2 <= 0 or ssr_f <= 0:
            continue
        F = ((ssr_r - ssr_f) / df1) / (ssr_f / df2)
        if F < 0 or not np.isfinite(F):
            continue
        p = 1.0 - f_dist.cdf(F, df1, df2)
        if p < pmin:
            pmin = float(p)
    return pmin

PHI = (1 + 5**0.5) / 2
C_EMERICK = 1 / (PHI * (2**0.5))  # 0.43701602...
WINDOW = 60
STEP = 5
SIGMA = 5
MAX_LAG = 10
GRANGER_LAGS = [1, 2, 3, 4, 5]
ALPHA = 0.01
N_LAGS_FOR_BONFERRONI = len(GRANGER_LAGS)


def gaussian_weighted_lagged_xcorr(x: np.ndarray, y: np.ndarray, sigma: int = SIGMA, max_lag: int = MAX_LAG) -> float:
    """R(A,B) = sum over τ in [-max_lag, +max_lag] of corr(x_t, y_{t+τ}) * W(τ)
    where W(τ) is unit-area Gaussian with given σ, restricted to integer τ.
    Implements the Resonance Equation from §1.1 of bidirectional paper."""
    xs = (x - x.mean()) / (x.std() + 1e-12)
    ys = (y - y.mean()) / (y.std() + 1e-12)
    n = len(xs)
    weights = np.array([math.exp(-0.5 * (tau / sigma) ** 2) for tau in range(-max_lag, max_lag + 1)])
    weights /= weights.sum()
    R = 0.0
    for i, tau in enumerate(range(-max_lag, max_lag + 1)):
        if tau >= 0:
            a, b = xs[: n - tau], ys[tau:]
        else:
            a, b = xs[-tau:], ys[: n + tau]
        if len(a) < 10:
            continue
        c = float(np.corrcoef(a, b)[0, 1])
        if math.isnan(c):
            continue
        R += weights[i] * c
    return R


def granger_min_p(y_target: np.ndarray, x_pred: np.ndarray, lags=GRANGER_LAGS) -> float:
    """Min p across lags for H0 'x_pred does NOT Granger-cause y_target'."""
    return granger_causality_min_p(y_target, x_pred, lags=tuple(lags))


def main():
    out_dir = Path(__file__).parent
    sym_x, sym_y = "SPY", "^VIX"
    start, end = "2014-01-01", "2024-12-31"

    # Freeze pre-reg sha
    pre_reg = {
        "C_EMERICK_empirical": C_EMERICK,
        "C_EMERICK_conjectural_form": "1/(phi*sqrt(2))",
        "WINDOW": WINDOW, "STEP": STEP, "SIGMA": SIGMA, "MAX_LAG": MAX_LAG,
        "GRANGER_LAGS": GRANGER_LAGS, "ALPHA": ALPHA,
        "DYAD": [sym_x, sym_y], "DATE_RANGE": [start, end],
        "DEVIATION_FROM_PROGRAM_A": "primary dyad #6 (UMCSENT x SPY) deferred; using dyad #1 SPY x ^VIX",
        "PROGRAM_A_DOC_SHA_PREFIX": hashlib.sha256(
            Path("papers/LCC_BIDIRECTIONAL_VALIDATION_AND_BOK_VIRUS_EXPERIMENTS.md").read_bytes()
        ).hexdigest()[:16],
    }
    pre_reg_sha = hashlib.sha256(json.dumps(pre_reg, sort_keys=True).encode()).hexdigest()
    print(f"PRE-REG SHA-256: {pre_reg_sha}")

    print(f"Fetching {sym_x} & {sym_y} {start} -> {end} ...")
    df = yf.download([sym_x, sym_y], start=start, end=end, progress=False, auto_adjust=True)["Close"]
    df = df.dropna()
    print(f"  obs: {len(df)} trading days")
    if len(df) < WINDOW + STEP:
        raise SystemExit("not enough data")

    rx = np.log(df[sym_x]).diff().dropna().values
    ry = np.log(df[sym_y]).diff().dropna().values
    n = min(len(rx), len(ry))
    rx, ry = rx[:n], ry[:n]

    # 60/40 chronological split: first 60% = TUNE/VAL (in-window), last 40% = HOLDOUT.
    cut = int(n * 0.6)
    rx_tune, ry_tune = rx[:cut], ry[:cut]
    rx_hold, ry_hold = rx[cut:], ry[cut:]

    def windowed_analysis(rx_seg, ry_seg, label):
        records = []
        bonf_alpha = ALPHA / N_LAGS_FOR_BONFERRONI
        for start_i in range(0, len(rx_seg) - WINDOW + 1, STEP):
            wx = rx_seg[start_i:start_i + WINDOW]
            wy = ry_seg[start_i:start_i + WINDOW]
            R = gaussian_weighted_lagged_xcorr(wx, wy)
            p_xy = granger_min_p(wy, wx)  # x -> y
            p_yx = granger_min_p(wx, ry_seg[start_i:start_i + WINDOW])  # y -> x
            bidirectional = (p_xy < bonf_alpha) and (p_yx < bonf_alpha)
            regime = "above" if abs(R) >= C_EMERICK else "below"
            records.append({
                "window_start_in_segment": int(start_i),
                "R": float(R), "abs_R": float(abs(R)),
                "p_x_to_y": float(p_xy), "p_y_to_x": float(p_yx),
                "bidirectional": bool(bidirectional),
                "regime": regime,
            })
        # 2x2 contingency
        a = sum(1 for r in records if r["regime"] == "above" and r["bidirectional"])
        b = sum(1 for r in records if r["regime"] == "above" and not r["bidirectional"])
        c = sum(1 for r in records if r["regime"] == "below" and r["bidirectional"])
        d = sum(1 for r in records if r["regime"] == "below" and not r["bidirectional"])
        try:
            odds_ratio, p_fisher = fisher_exact([[a, b], [c, d]], alternative="two-sided")
        except Exception:
            odds_ratio, p_fisher = float("nan"), float("nan")
        return {
            "label": label, "n_windows": len(records),
            "contingency": {"above_bid": a, "above_not": b, "below_bid": c, "below_not": d},
            "odds_ratio_above_vs_below_bidirectional": odds_ratio,
            "fisher_p": p_fisher,
            "frac_above_bidirectional": (a / (a + b)) if (a + b) > 0 else float("nan"),
            "frac_below_bidirectional": (c / (c + d)) if (c + d) > 0 else float("nan"),
            "windows": records,
        }

    tune = windowed_analysis(rx_tune, ry_tune, "TUNE_VAL")
    hold = windowed_analysis(rx_hold, ry_hold, "HOLDOUT")

    # Verdict per §2.6 + §2.7 (adapted for non-primary dyad — note the
    # "primary outcome" of Program A is dyad #6; this is a SECONDARY
    # outcome only).
    p_h = hold["fisher_p"]; or_h = hold["odds_ratio_above_vs_below_bidirectional"]
    if math.isnan(p_h):
        verdict = "INDETERMINATE_INSUFFICIENT_DATA"
    elif p_h < 0.05 and or_h is not None and not math.isnan(or_h) and or_h > 1.0:
        verdict = "SECONDARY_CONFIRM_DYAD1_HOLDOUT"
    elif p_h < 0.05 and or_h < 1.0:
        verdict = "SECONDARY_REVERSE_DIRECTION"
    else:
        verdict = "NULL_NOISE_HOLDOUT"

    # Filter A: TUNE -> HOLDOUT direction consistency
    filter_a_pass = (
        not math.isnan(tune["odds_ratio_above_vs_below_bidirectional"]) and
        not math.isnan(or_h) and
        ((tune["odds_ratio_above_vs_below_bidirectional"] - 1) *
         (or_h - 1)) > 0
    )

    out = {
        "test_id": "L-1_program_a_bidirectional_lcc_first_window",
        "pre_reg_sha256": pre_reg_sha,
        "pre_reg_parameters": pre_reg,
        "deviation_logged": pre_reg["DEVIATION_FROM_PROGRAM_A"],
        "data_source": "yfinance free public market data",
        "n_total_obs": int(n),
        "tune_results": tune,
        "holdout_results": hold,
        "filter_A_drift_consistent_TUNE_HOLDOUT": filter_a_pass,
        "verdict": verdict,
    }
    out_dir.joinpath("results.json").write_text(json.dumps(out, indent=2, default=str))
    print(f"\n=== L-1 Program A first-window result ===")
    print(f"VERDICT: {verdict}")
    print(f"HOLDOUT contingency: {hold['contingency']}")
    print(f"  frac bidirectional above C*: {hold['frac_above_bidirectional']:.3f}")
    print(f"  frac bidirectional below C*: {hold['frac_below_bidirectional']:.3f}")
    print(f"  odds ratio (above/below): {or_h:.3f}; Fisher p: {p_h:.4f}")
    print(f"  Filter A (TUNE↔HOLDOUT direction consistent): {filter_a_pass}")


if __name__ == "__main__":
    main()

"""Pass-49 L-1 PRIMARY — Program A primary dyad #6 UMCSENT × SPY (monthly).

Brandon authorized 2026-05-13: execute the PRIMARY dyad now that
`lcc_virus.data_adapters.fred_csv_adapter` is available (no
pandas_datareader dependency required).

This is the PRIMARY outcome of Program A per the bidirectional paper
§2.6: "Primary outcome (dyad #6 UMCSENT × SPY): Fisher's exact p < 0.01
with OR ≥ 2.5 and the direction of the effect being more bidirectional
Granger above C_EMERICK."

ALL parameters frozen pre-data-fetch from §2.5; identical to L-1
SECONDARY runner with three deviations:
  - DYAD = (UMCSENT, SPY); resolution = MONTHLY
  - WINDOW = 60 monthly periods, STEP = 5
  - SIGMA = 5 (months), MAX_LAG = ±10 (months)
  - GRANGER_LAGS, ALPHA, C_EMERICK unchanged
"""
from __future__ import annotations
import json, hashlib, math
from pathlib import Path

import numpy as np
import pandas as pd
import yfinance as yf
from scipy.stats import fisher_exact

# Reuse hand-rolled Granger + resonance from the secondary runner
import sys
_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(_ROOT))
sys.path.insert(0, str(_ROOT / "analyses" / "pass49_program_a_bidirectional_lcc"))
from runner import (  # type: ignore
    granger_causality_min_p,
    gaussian_weighted_lagged_xcorr,
    PHI, C_EMERICK,
)
from lcc_virus.data_adapters.fred_csv_adapter import fetch_series

WINDOW = 60       # 60 monthly periods (~5 years)
STEP = 5
SIGMA = 5         # months
MAX_LAG = 10
GRANGER_LAGS = (1, 2, 3, 4, 5)
ALPHA = 0.01
N_LAGS_BONF = len(GRANGER_LAGS)


def main():
    out_dir = Path(__file__).parent
    sym_x = "UMCSENT"   # Michigan consumer sentiment, FRED, monthly
    sym_y = "SPY"        # yfinance, daily -> resampled monthly
    start, end = "1985-01-01", "2024-12-31"

    pre_reg = {
        "ROLE": "PRIMARY (dyad #6, Program A §2.6)",
        "C_EMERICK_empirical": 0.4370,
        "C_EMERICK_conjectural_form": "1/(phi*sqrt(2))",
        "WINDOW_months": WINDOW, "STEP": STEP, "SIGMA_months": SIGMA,
        "MAX_LAG_months": MAX_LAG, "GRANGER_LAGS": list(GRANGER_LAGS),
        "ALPHA": ALPHA, "DYAD": [sym_x, sym_y],
        "DATE_RANGE": [start, end], "RESOLUTION": "monthly",
        "PRIMARY_SUCCESS_CRITERIA": "Fisher p<0.01 AND OR>=2.5 AND above-more-bidirectional",
        "DEVIATION_FROM_PROGRAM_A": "none — this IS the pre-registered primary",
        "PROGRAM_A_DOC_SHA_PREFIX": hashlib.sha256(
            Path("papers/LCC_BIDIRECTIONAL_VALIDATION_AND_BOK_VIRUS_EXPERIMENTS.md").read_bytes()
        ).hexdigest()[:16],
    }
    pre_reg_sha = hashlib.sha256(json.dumps(pre_reg, sort_keys=True).encode()).hexdigest()
    print(f"PRE-REG SHA-256: {pre_reg_sha}")

    print(f"Fetching FRED UMCSENT {start}..{end} ...")
    umcsent = fetch_series("UMCSENT", start=start, end=end)
    print(f"  UMCSENT obs: {len(umcsent)} months ({umcsent.index.min().date()}..{umcsent.index.max().date()})")

    print(f"Fetching SPY {start}..{end} (resampling daily->monthly) ...")
    spy_daily = yf.download("SPY", start=start, end=end, progress=False, auto_adjust=True)["Close"]
    if hasattr(spy_daily, "columns"):
        spy_daily = spy_daily.iloc[:, 0]
    spy_monthly = spy_daily.resample("MS").last().dropna()
    print(f"  SPY monthly obs: {len(spy_monthly)} ({spy_monthly.index.min().date()}..{spy_monthly.index.max().date()})")

    # Align on the intersection of months
    df = pd.concat([umcsent.rename("UMCSENT"), spy_monthly.rename("SPY")], axis=1).dropna()
    print(f"Aligned monthly obs: {len(df)}")
    if len(df) < WINDOW + STEP * 2:
        raise SystemExit(f"only {len(df)} aligned months; need at least {WINDOW + STEP*2}")

    # Stationarize: % change of UMCSENT, log-return of SPY
    rx = df["UMCSENT"].pct_change().dropna().values.astype(float)
    ry = np.log(df["SPY"]).diff().dropna().values.astype(float)
    n = min(len(rx), len(ry))
    rx, ry = rx[:n], ry[:n]
    print(f"Stationarized obs: {n}")

    # 60/40 chronological split
    cut = int(n * 0.6)
    rx_tune, ry_tune = rx[:cut], ry[:cut]
    rx_hold, ry_hold = rx[cut:], ry[cut:]
    print(f"TUNE: {len(rx_tune)} months; HOLDOUT: {len(rx_hold)} months")

    def windowed_analysis(rx_seg, ry_seg, label):
        bonf = ALPHA / N_LAGS_BONF
        recs = []
        for s in range(0, len(rx_seg) - WINDOW + 1, STEP):
            wx = rx_seg[s:s + WINDOW]; wy = ry_seg[s:s + WINDOW]
            R = gaussian_weighted_lagged_xcorr(wx, wy, sigma=SIGMA, max_lag=MAX_LAG)
            p_xy = granger_causality_min_p(wy, wx, lags=GRANGER_LAGS)
            p_yx = granger_causality_min_p(wx, wy, lags=GRANGER_LAGS)
            bid = (p_xy < bonf) and (p_yx < bonf)
            regime = "above" if abs(R) >= 0.4370 else "below"
            recs.append({"window_start": int(s), "R": float(R), "abs_R": float(abs(R)),
                         "p_x_to_y": float(p_xy), "p_y_to_x": float(p_yx),
                         "bidirectional": bool(bid), "regime": regime})
        a = sum(1 for r in recs if r["regime"] == "above" and r["bidirectional"])
        b = sum(1 for r in recs if r["regime"] == "above" and not r["bidirectional"])
        c = sum(1 for r in recs if r["regime"] == "below" and r["bidirectional"])
        d = sum(1 for r in recs if r["regime"] == "below" and not r["bidirectional"])
        try:
            odr, pf = fisher_exact([[a, b], [c, d]], alternative="two-sided")
        except Exception:
            odr, pf = float("nan"), float("nan")
        return {"label": label, "n_windows": len(recs),
                "contingency": {"above_bid": a, "above_not": b, "below_bid": c, "below_not": d},
                "odds_ratio": odr, "fisher_p": pf,
                "frac_above_bid": (a / (a + b)) if (a + b) > 0 else float("nan"),
                "frac_below_bid": (c / (c + d)) if (c + d) > 0 else float("nan"),
                "max_abs_R": max((r["abs_R"] for r in recs), default=float("nan")),
                "windows": recs}

    tune = windowed_analysis(rx_tune, ry_tune, "TUNE")
    hold = windowed_analysis(rx_hold, ry_hold, "HOLDOUT")

    p = hold["fisher_p"]; orh = hold["odds_ratio"]
    if math.isnan(p) or hold["contingency"]["above_bid"] + hold["contingency"]["above_not"] == 0:
        verdict = "PRIMARY_NULL_NOISE_NO_ABOVE_C_WINDOWS"
    elif p < 0.01 and orh >= 2.5 and hold["frac_above_bid"] > hold["frac_below_bid"]:
        verdict = "PRIMARY_CONFIRM"
    elif p < 0.05 and orh > 1.0 and hold["frac_above_bid"] > hold["frac_below_bid"]:
        verdict = "PRIMARY_WEAK_CONFIRM_BELOW_PRIMARY_BAR"
    elif p < 0.05 and orh < 1.0:
        verdict = "PRIMARY_REVERSE_DIRECTION"
    else:
        verdict = "PRIMARY_NULL_NOISE_HOLDOUT"

    filter_a = (
        not math.isnan(tune["odds_ratio"]) and not math.isnan(orh) and
        ((tune["odds_ratio"] - 1) * (orh - 1)) > 0
    )

    out = {
        "test_id": "L-1_PRIMARY_program_a_dyad6_UMCSENT_x_SPY",
        "pre_reg_sha256": pre_reg_sha,
        "pre_reg_parameters": pre_reg,
        "n_aligned_months": int(len(df)),
        "n_stationarized": int(n),
        "tune_results": tune,
        "holdout_results": hold,
        "filter_A_pass": filter_a,
        "verdict": verdict,
    }
    out_dir.joinpath("results.json").write_text(json.dumps(out, indent=2, default=str))

    print(f"\n=== L-1 PRIMARY (dyad #6 UMCSENT x SPY monthly) ===")
    print(f"VERDICT: {verdict}")
    print(f"HOLDOUT contingency: {hold['contingency']}")
    print(f"  max |R|: {hold['max_abs_R']:.4f} (vs C* = 0.4370)")
    print(f"  frac bidirectional above C*: {hold['frac_above_bid']}")
    print(f"  frac bidirectional below C*: {hold['frac_below_bid']}")
    print(f"  odds ratio: {orh}; Fisher p: {p}")
    print(f"  Filter A (TUNE↔HOLDOUT direction): {filter_a}")


if __name__ == "__main__":
    main()

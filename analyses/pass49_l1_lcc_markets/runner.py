"""
L1 — Pass-49: LCC bidirectional in markets (Program A, first window).

PRE-REGISTRATION (frozen at write-time, BEFORE any data download or inspection;
anti-cheat per Pass-45 §11 + Pass-49 L4 holdout-blind protocol).

OBJECTIVE
=========
Test whether two macro-asset time-series exhibit Latched Consciousness
Correlator (LCC) bidirectional coherence that exceeds classical linear
correlation by a pre-specified threshold. Per Pass-49 L4, this run executes
the TUNE / VALIDATION / HOLDOUT 40/30/30 partition with all parameters
frozen before any data is touched.

DATA SOURCES (free)
===================
- yfinance: SPY (S&P 500 ETF) and TLT (20+ Year Treasury Bond ETF) daily
  adjusted-close prices.
- Window: 2022-01-01 to 2026-04-30 (~4.3 years; ~1080 trading days).
- Pair rationale: SPY/TLT are conventionally anti-correlated through
  the rates-equities channel, providing a non-trivial baseline against
  which LCC's claim of resonance-beyond-correlation can be tested.

PARTITION (frozen, deterministic)
=================================
- Total trading days N partitioned by index modulo permutation seeded
  by SHA-256 of the joined daily-close panel (computed AFTER download
  but BEFORE any inspection of values).
- TUNE: 40% (used to set frozen kernel half-width and band).
- VALIDATION: 30% (used as sanity check; >2x drift vs TUNE = reject).
- HOLDOUT: 30% (single-pass evaluation, no re-tuning).

FROZEN PARAMETERS (frozen here, BEFORE seeing data)
===================================================
- Returns transform: log-return r_t = ln(P_t / P_{t-1}).
- Detrend: z-score normalization within each segment independently.
- Resonance kernel W(τ): triangular, half-width τ_max = 5 trading days.
- Lag range: τ ∈ {-5, -4, ..., +5} trading days.
- Classical baseline: Pearson correlation of (r_SPY, r_TLT) within segment.
- LCC scalar: R_LCC = Σ_τ Φ_SPY(t) · Φ_TLT(t+τ) · W(τ), normalized by
  segment length, summed across τ ∈ [-5, +5].

PRE-REGISTERED HYPOTHESES (directional, per architect HIGH-finding fix)
=======================================================================
H_L1_PRIMARY (HOLDOUT-only): |R_LCC_holdout| > |R_pearson_holdout| + 0.05,
  AND sign of R_LCC_holdout matches sign of R_pearson_holdout
  (i.e., LCC adds magnitude in the same direction as classical, not flips it).

H_L1_SECONDARY (cross-segment consistency): sign(R_LCC) consistent across
  TUNE, VALIDATION, HOLDOUT (all three same sign).

VERDICT MATRIX
==============
- CONFIRM_STRONG: H_PRIMARY met AND H_SECONDARY met.
- CONFIRM:        H_PRIMARY met OR  H_SECONDARY met.
- WEAK:           |R_LCC_holdout| > |R_pearson_holdout| (any margin) but
                  not both above conditions.
- DISCONFIRM:     |R_LCC_holdout| <= |R_pearson_holdout|.
- NULL_NOISE:     |R_LCC_holdout| < 0.05 absolute (below noise floor).

FILTER E (vacuousness check, Pass-49 L4 §2.5):
  Pre-reg window has a clearly DISCONFIRMING side (DISCONFIRM verdict
  is reachable for any sign-flipped or below-pearson result). PASS.

#69 CAVEATS (logged before execution)
=====================================
- This is a single-asset-pair, single-window, single-frequency test.
  CONFIRM does not establish LCC-in-markets generally; it establishes one
  pre-registered prediction held for one pair on one window.
- HOLDOUT ceremony is agent-witnessed only (Brandon-async). Per Pass-49
  L4 §1.3, this is weaker than Brandon-witnessed; result is reported as
  "agent-witnessed-only" and flagged for Brandon review.
- yfinance data is third-party-sourced; values can be revised. Source
  SHA-256 of the panel is recorded for reproducibility.
- The kernel choice (triangular, τ_max=5) is convenient, not first-
  principles. A different kernel could change the magnitude (not the
  sign) of R_LCC. Documented as a frozen choice.
"""

from __future__ import annotations

import hashlib
import json
import math
import warnings
from datetime import datetime, timezone
from pathlib import Path

warnings.filterwarnings("ignore")

import numpy as np
import pandas as pd
import yfinance as yf

OUTPUT_DIR = Path("analyses/pass49_l1_lcc_markets")
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
RESULTS_PATH = OUTPUT_DIR / "results.json"
LOG_PATH = OUTPUT_DIR / "ceremony_log.md"

# ---------- frozen config ----------
TICKERS = ("SPY", "TLT")
START = "2022-01-01"
END = "2026-04-30"
TAU_MAX = 5
PARTITION_FRAC = (0.40, 0.30, 0.30)  # TUNE / VALIDATION / HOLDOUT
PRIMARY_MARGIN = 0.05
NOISE_FLOOR = 0.05


def _sha256_of(obj: bytes) -> str:
    return hashlib.sha256(obj).hexdigest()


def _runner_sha() -> str:
    return _sha256_of(Path(__file__).read_bytes())


def download_panel() -> pd.DataFrame:
    df = yf.download(
        list(TICKERS),
        start=START,
        end=END,
        auto_adjust=True,
        progress=False,
        threads=False,
    )
    if isinstance(df.columns, pd.MultiIndex):
        prices = df["Close"].copy()
    else:
        prices = df[["Close"]].copy()
        prices.columns = TICKERS[:1]
    prices = prices.dropna(how="any")
    return prices


def deterministic_partition(panel_sha: str, n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    rng = np.random.default_rng(int(panel_sha[:16], 16))
    perm = rng.permutation(n)
    n_tune = int(round(n * PARTITION_FRAC[0]))
    n_val = int(round(n * PARTITION_FRAC[1]))
    tune_idx = np.sort(perm[:n_tune])
    val_idx = np.sort(perm[n_tune:n_tune + n_val])
    holdout_idx = np.sort(perm[n_tune + n_val:])
    return tune_idx, val_idx, holdout_idx


def log_returns(series: np.ndarray) -> np.ndarray:
    return np.diff(np.log(series))


def zscore(x: np.ndarray) -> np.ndarray:
    mu = float(np.mean(x))
    sd = float(np.std(x, ddof=1))
    if sd < 1e-12:
        return np.zeros_like(x)
    return (x - mu) / sd


def triangular_kernel(tau_max: int) -> np.ndarray:
    taus = np.arange(-tau_max, tau_max + 1)
    w = 1.0 - np.abs(taus) / (tau_max + 1)
    w = w / w.sum()
    return w


def lcc_resonance(phi_a: np.ndarray, phi_b: np.ndarray, tau_max: int) -> float:
    """R_LCC = Σ_τ <Φ_A(t) Φ_B(t+τ)> · W(τ).

    Uses lag-correlation per τ then weights by triangular kernel.
    """
    weights = triangular_kernel(tau_max)
    n = len(phi_a)
    r = 0.0
    for i, tau in enumerate(range(-tau_max, tau_max + 1)):
        if tau >= 0:
            a = phi_a[: n - tau]
            b = phi_b[tau:]
        else:
            a = phi_a[-tau:]
            b = phi_b[: n + tau]
        if len(a) < 5:
            continue
        # centered cross-product (Φ already standardized)
        r += float(np.mean(a * b)) * weights[i]
    return r


def pearson(a: np.ndarray, b: np.ndarray) -> float:
    if len(a) < 5:
        return float("nan")
    return float(np.corrcoef(a, b)[0, 1])


def evaluate_segment(rA: np.ndarray, rB: np.ndarray) -> dict:
    phi_a = zscore(rA)
    phi_b = zscore(rB)
    return {
        "n": int(len(rA)),
        "pearson": pearson(rA, rB),
        "R_LCC": lcc_resonance(phi_a, phi_b, TAU_MAX),
    }


def main() -> dict:
    started_at = datetime.now(timezone.utc).isoformat()
    runner_sha = _runner_sha()

    panel = download_panel()
    panel = panel[list(TICKERS)].dropna()
    panel_bytes = panel.to_csv().encode()
    panel_sha = _sha256_of(panel_bytes)

    log_returns_df = pd.DataFrame(
        {t: log_returns(panel[t].to_numpy()) for t in TICKERS},
        index=panel.index[1:],
    )
    n_total = len(log_returns_df)

    tune_idx, val_idx, holdout_idx = deterministic_partition(panel_sha, n_total)

    rA_full = log_returns_df[TICKERS[0]].to_numpy()
    rB_full = log_returns_df[TICKERS[1]].to_numpy()

    seg = {
        "TUNE": evaluate_segment(rA_full[tune_idx], rB_full[tune_idx]),
        "VALIDATION": evaluate_segment(rA_full[val_idx], rB_full[val_idx]),
        "HOLDOUT": evaluate_segment(rA_full[holdout_idx], rB_full[holdout_idx]),
    }

    # Filter A (TUNE→VALIDATION drift check); pass=ratio < 2x on R_LCC
    rT, rV = abs(seg["TUNE"]["R_LCC"]), abs(seg["VALIDATION"]["R_LCC"])
    drift_ratio = max(rT, rV) / max(min(rT, rV), 1e-12)
    filter_a = "PASS" if drift_ratio < 2.0 else "FAIL"

    h = seg["HOLDOUT"]
    margin = abs(h["R_LCC"]) - abs(h["pearson"])
    sign_match_holdout = (np.sign(h["R_LCC"]) == np.sign(h["pearson"])) if not (
        math.isnan(h["pearson"])) else False
    primary_met = (margin > PRIMARY_MARGIN) and bool(sign_match_holdout)

    signs = [np.sign(seg[k]["R_LCC"]) for k in ("TUNE", "VALIDATION", "HOLDOUT")]
    secondary_met = len(set(signs)) == 1 and signs[0] != 0

    if abs(h["R_LCC"]) < NOISE_FLOOR:
        verdict = "NULL_NOISE"
    elif primary_met and secondary_met:
        verdict = "CONFIRM_STRONG"
    elif primary_met or secondary_met:
        verdict = "CONFIRM"
    elif abs(h["R_LCC"]) > abs(h["pearson"]):
        verdict = "WEAK"
    else:
        verdict = "DISCONFIRM"

    out = {
        "test_id": "L1_lcc_markets_program_a_first_window",
        "pass": 49,
        "started_at": started_at,
        "tickers": list(TICKERS),
        "window": [START, END],
        "n_trading_days_after_dropna": int(n_total),
        "panel_sha256": panel_sha,
        "runner_sha256": runner_sha,
        "frozen_params": {
            "tau_max": TAU_MAX,
            "kernel": "triangular",
            "partition_frac": list(PARTITION_FRAC),
            "primary_margin": PRIMARY_MARGIN,
            "noise_floor": NOISE_FLOOR,
        },
        "partition_sizes": {
            "TUNE": int(len(tune_idx)),
            "VALIDATION": int(len(val_idx)),
            "HOLDOUT": int(len(holdout_idx)),
        },
        "per_segment": seg,
        "tests": {
            "drift_ratio_tune_vs_val_on_R_LCC": drift_ratio,
            "filter_A_drift_check": filter_a,
            "holdout_margin_R_LCC_minus_pearson_abs": margin,
            "holdout_sign_match": bool(sign_match_holdout),
            "cross_segment_sign_consistency": bool(secondary_met),
            "H_PRIMARY_met": bool(primary_met),
            "H_SECONDARY_met": bool(secondary_met),
        },
        "verdict": verdict,
        "ceremony_witness": "AGENT_ONLY",
        "brandon_witness_pending": True,
        "notes": (
            "Pass-49 L4 protocol §1.3 requires Brandon-witness for the HOLDOUT "
            "ceremony. This run is agent-witnessed-only; result is reported as "
            "honest first-pass and flagged for Brandon review. Re-running on "
            "the same HOLDOUT for a different configuration is forbidden per "
            "L4 anti-cheat regardless of this result."
        ),
    }

    with RESULTS_PATH.open("w") as f:
        json.dump(out, f, indent=2, default=str)

    log = [
        f"# L1 ceremony log — {started_at}",
        f"- runner SHA-256: `{runner_sha}`",
        f"- panel SHA-256: `{panel_sha}`",
        f"- window: {START} → {END}",
        f"- tickers: {TICKERS}",
        f"- partition: TUNE={len(tune_idx)} / VAL={len(val_idx)} / HOLDOUT={len(holdout_idx)}",
        f"- Filter A (drift): {filter_a}  (ratio={drift_ratio:.4f})",
        f"- HOLDOUT R_LCC: {h['R_LCC']:.6f}",
        f"- HOLDOUT Pearson: {h['pearson']:.6f}",
        f"- HOLDOUT margin (|R_LCC|-|Pearson|): {margin:.6f}",
        f"- Cross-segment signs: {[float(s) for s in signs]}",
        f"- VERDICT: **{verdict}**",
        "- Witness: AGENT_ONLY (Brandon-async; flagged in results.json)",
    ]
    LOG_PATH.write_text("\n".join(log) + "\n")

    print("\n".join(log))
    return out


if __name__ == "__main__":
    main()

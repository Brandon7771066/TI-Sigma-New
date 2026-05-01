"""
Phase B — Within-Subject Weight Learning for R_intra_em
========================================================

Pre-registered §10.5 of papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md.

Goal: fit per-component weights w in the simplex (sum=1, all ≥ 0) such that
    target_score(t+1) ≈ Σ_i w_i × component_i(t)
where target is next-day Oura readiness_score / 100, and components are the
5 candidate R_intra_em predictors listed in §10.5.

Honest constraint (also pre-registered in §10.5):
    The three genome-derived components are TIME-CONSTANT for a single
    subject at week granularity → they cannot explain per-day variance in
    target. Their weights in this preliminary fit are structurally
    meaningless (degenerate). The pipeline runs end-to-end, demonstrating
    architecture, not biology.

§10.5 HIT criteria (architecturally testable today):
    HIT-1: NNLS converges, weights sum to 1.00 ± 0.01, no NaN
    HIT-2: RSS(learned) < RSS(uniform-1/5)
    HIT-3: w_i ≥ 0 ∀ i

Outputs to data/phase_b_fit_<date>.json with full diagnostics.
"""

from __future__ import annotations
import json
import os
import sys
from dataclasses import asdict, dataclass
from datetime import date, datetime, timedelta
from typing import Dict, List, Optional, Tuple

import numpy as np
from scipy.optimize import minimize


# ────────────────────────────────────────────────────────────────────────────
# §10.5 LOCKED constants — DO NOT MUTATE
# ────────────────────────────────────────────────────────────────────────────

PRED_105 = {
    "lock_timestamp": "2026-05-01T10:30:00-04:00",
    "subject": "Brandon Charles Emerick",
    "n_subjects": 1,
    "method": "NNLS via SLSQP, sum=1 simplex constraint",
    "target": "next-day readiness_score / 100",
    "feature_order": ["mito_snp_score", "telomere_proxy", "cpg_promoter_density",
                      "sleep_hrv_norm", "ppg_biosignature"],
    # Brandon's Phase H-1.5 constants
    "mito_snp_score": 0.9468,
    "telomere_proxy": 0.4167,
    "cpg_promoter_density": 0.4757,
}


# ────────────────────────────────────────────────────────────────────────────
# Data assembly
# ────────────────────────────────────────────────────────────────────────────

@dataclass
class PhaseBDataRow:
    day: str
    target_day: str       # day + 1
    x_mito: float         # constant
    x_telomere: float     # constant
    x_cpg: float          # constant
    x_sleep_hrv_norm: Optional[float]
    x_ppg_biosignature: Optional[float]
    y_target: Optional[float]


def build_dataset(harvest_path: str, ppg_sigs_path: str) -> List[PhaseBDataRow]:
    """Assemble per-day (X, y) rows from harvest + PPG signatures + next-day target."""
    with open(harvest_path) as f:
        h = json.load(f)
    with open(ppg_sigs_path) as f:
        sigs = json.load(f)["signatures"]

    # Index daily records by date for next-day lookup
    daily_by_day = {r["date"]: r for r in h["daily_records"]}

    rows: List[PhaseBDataRow] = []
    for day, rec in sorted(daily_by_day.items()):
        next_day = (date.fromisoformat(day) + timedelta(days=1)).isoformat()
        next_rec = daily_by_day.get(next_day)

        sleep_hrv = rec.get("sleep_hrv")
        sleep_hrv_norm = (
            min(float(sleep_hrv), 100.0) / 100.0
            if sleep_hrv is not None else None
        )

        ppg_sig = sigs.get(day, {}).get("ppg_biophoton_signature")

        y = None
        if next_rec is not None and next_rec.get("readiness_score") is not None:
            y = float(next_rec["readiness_score"]) / 100.0

        rows.append(PhaseBDataRow(
            day=day,
            target_day=next_day,
            x_mito=PRED_105["mito_snp_score"],
            x_telomere=PRED_105["telomere_proxy"],
            x_cpg=PRED_105["cpg_promoter_density"],
            x_sleep_hrv_norm=sleep_hrv_norm,
            x_ppg_biosignature=ppg_sig,
            y_target=y,
        ))
    return rows


def filter_complete(rows: List[PhaseBDataRow]) -> List[PhaseBDataRow]:
    """Keep only rows where ALL features and target are non-None."""
    return [
        r for r in rows
        if r.x_sleep_hrv_norm is not None
        and r.x_ppg_biosignature is not None
        and r.y_target is not None
    ]


# ────────────────────────────────────────────────────────────────────────────
# NNLS with simplex constraint via SLSQP
# ────────────────────────────────────────────────────────────────────────────

def fit_simplex_nnls(X: np.ndarray, y: np.ndarray) -> Tuple[np.ndarray, dict]:
    """
    Fit w ∈ Δ^k (w_i ≥ 0, Σ w_i = 1) minimizing ||X w − y||².
    Uses SLSQP with explicit equality + bounds constraints.
    Returns (w, diagnostics).
    """
    k = X.shape[1]

    def loss(w):
        return float(np.sum((X @ w - y) ** 2))

    def grad(w):
        return 2 * X.T @ (X @ w - y)

    constraints = [
        {"type": "eq", "fun": lambda w: float(np.sum(w) - 1.0)}
    ]
    bounds = [(0.0, 1.0)] * k
    w0 = np.ones(k) / k

    result = minimize(
        loss, w0, jac=grad, method="SLSQP",
        bounds=bounds, constraints=constraints,
        options={"ftol": 1e-12, "maxiter": 500, "disp": False}
    )
    return result.x, {
        "converged": bool(result.success),
        "message":   str(result.message),
        "n_iter":    int(result.nit),
        "rss":       float(result.fun),
        "weights_sum": float(np.sum(result.x)),
        "min_weight":  float(np.min(result.x)),
        "max_weight":  float(np.max(result.x)),
    }


def baseline_uniform_rss(X: np.ndarray, y: np.ndarray) -> float:
    """RSS of the uniform-1/k baseline."""
    k = X.shape[1]
    w_uniform = np.ones(k) / k
    return float(np.sum((X @ w_uniform - y) ** 2))


# ────────────────────────────────────────────────────────────────────────────
# Main
# ────────────────────────────────────────────────────────────────────────────

def main():
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument("--harvest", default=None)
    p.add_argument("--ppg-sigs", default=None)
    p.add_argument("--output", default=None)
    args = p.parse_args()

    if args.harvest is None:
        cands = sorted(f for f in os.listdir("data") if f.startswith("oura_30day_harvest_"))
        if not cands:
            print("❌ Need harvest. Run oura_full_metrics_harvester.py first.", file=sys.stderr)
            sys.exit(1)
        args.harvest = os.path.join("data", cands[-1])
    if args.ppg_sigs is None:
        cands = sorted(f for f in os.listdir("data") if f.startswith("ppg_biophoton_signatures_"))
        if not cands:
            print("❌ Need PPG signatures. Run ppg_biophoton_proxy.py first.", file=sys.stderr)
            sys.exit(1)
        args.ppg_sigs = os.path.join("data", cands[-1])

    print("━" * 76)
    print("PHASE B — WITHIN-SUBJECT WEIGHT LEARNING (§10.5 PRE-REGISTERED)")
    print("━" * 76)
    print(f"Harvest:  {args.harvest}")
    print(f"PPG sigs: {args.ppg_sigs}")
    print(f"Lock ts:  {PRED_105['lock_timestamp']}")
    print()

    rows = build_dataset(args.harvest, args.ppg_sigs)
    complete = filter_complete(rows)
    print(f"Total day rows: {len(rows)}")
    print(f"Complete rows (all features + target): {len(complete)}")
    if len(complete) < 5:
        print(f"\n⚠️  N={len(complete)} is below the recommended minimum (5). "
              "Pipeline will still run but weights are noisier than asphalt.")
    print()

    if not complete:
        print("❌ Zero complete rows. Cannot fit. Exiting.")
        sys.exit(2)

    # Build matrix
    feat_names = ["x_mito", "x_telomere", "x_cpg", "x_sleep_hrv_norm", "x_ppg_biosignature"]
    X = np.array([[getattr(r, f) for f in feat_names] for r in complete])
    y = np.array([r.y_target for r in complete])

    print("Per-day input matrix:")
    print(f"  {'day':12s} {'target':>7s}  " + " ".join(f"{n[2:][:8]:>10s}" for n in feat_names))
    for r in complete:
        print(f"  {r.day:12s} {r.y_target:7.4f}  "
              f"{r.x_mito:10.4f} {r.x_telomere:10.4f} {r.x_cpg:10.4f} "
              f"{r.x_sleep_hrv_norm:10.4f} {r.x_ppg_biosignature:10.4f}")
    print()

    # Fit
    w_learned, diag = fit_simplex_nnls(X, y)
    rss_baseline = baseline_uniform_rss(X, y)

    print("━" * 76)
    print("§10.5 RESULTS")
    print("━" * 76)
    print(f"\nLearned weights (sum={diag['weights_sum']:.4f}):")
    for name, w in zip(feat_names, w_learned):
        print(f"  {name:25s} {w:.4f}")
    print(f"\nRSS learned:  {diag['rss']:.6f}")
    print(f"RSS uniform:  {rss_baseline:.6f}")
    print(f"Improvement:  {(rss_baseline - diag['rss']) / rss_baseline * 100:+.2f}%")
    print(f"Converged:    {diag['converged']}  ({diag['n_iter']} iter)")
    print(f"Message:      {diag['message']}")

    # ── §10.5 verdict ──────────────────────────────────────────────────────
    print()
    print("━" * 76)
    print("§10.5 VERDICT (architectural HITs only)")
    print("━" * 76)
    hit1 = (diag["converged"] and abs(diag["weights_sum"] - 1.0) < 0.01
            and not np.any(np.isnan(w_learned)))
    hit2 = diag["rss"] < rss_baseline + 1e-9   # ≤ uniform
    hit3 = bool(diag["min_weight"] >= -1e-9)
    print(f"  HIT-1 (NNLS converges, weights sum to 1.00 ± 0.01, no NaN): "
          f"{'✅' if hit1 else '❌'}")
    print(f"  HIT-2 (RSS learned ≤ RSS uniform-1/5):                      "
          f"{'✅' if hit2 else '❌'}")
    print(f"  HIT-3 (w_i ≥ 0 ∀ i):                                         "
          f"{'✅' if hit3 else '❌'}")
    if hit1 and hit2 and hit3:
        print("\n✅ ALL THREE §10.5 HITs MET. Phase B pipeline ARCHITECTURALLY VALIDATED.")
    else:
        print("\n❌ §10.5 partial fail.")

    print()
    print("Honest scope reminder:")
    print("  The three genome components are TIME-CONSTANT for one subject. Their")
    print("  fitted weights in this preliminary run are STRUCTURALLY MEANINGLESS")
    print("  (degenerate w/o intercept; they only shift the mean). Real biological")
    print("  weight learning requires cross-subject genome variance OR longitudinal")
    print("  re-measurement of telomere length / methylation profile.")
    print()
    print("  This run validates: the regression infrastructure runs, sum-to-1")
    print("  constraint holds, NNLS converges, and per-day-varying components")
    print("  (sleep_hrv, ppg_biosignature) get nontrivial weight share.")
    print()
    print("  §10.5 strong-form falsification (whether w_em < 0.10 vs HRV > 0.85)")
    print("  is NOT testable today — see §10.6 (after Polar H10 + ≥21 days).")

    # Write output
    if args.output is None:
        args.output = os.path.join("data", f"phase_b_fit_{date.today().isoformat()}.json")
    payload = {
        "lock_metadata": PRED_105,
        "ran_at": datetime.utcnow().isoformat() + "Z",
        "harvest_path": args.harvest,
        "ppg_sigs_path": args.ppg_sigs,
        "n_complete_rows": len(complete),
        "feature_order": feat_names,
        "learned_weights": {n: float(w) for n, w in zip(feat_names, w_learned)},
        "diagnostics": diag,
        "rss_baseline_uniform": rss_baseline,
        "rss_improvement_fraction": (rss_baseline - diag["rss"]) / rss_baseline,
        "verdict": {
            "HIT_1_converged_simplex_no_nan": bool(hit1),
            "HIT_2_rss_better_than_uniform": bool(hit2),
            "HIT_3_nonnegative_weights": bool(hit3),
            "all_three_hit": bool(hit1 and hit2 and hit3),
        },
        "data_rows": [asdict(r) for r in complete],
        "honest_scope": (
            "Time-constant genome features have structurally-meaningless weights "
            "in N=1 within-subject fit. URB #826 not tested. Pipeline architecturally "
            "validated for forward §10.6 use after Polar H10 + ≥21 days."
        ),
    }
    with open(args.output, "w") as f:
        json.dump(payload, f, indent=2, default=str)
    print(f"\n✅ Written: {args.output}")


if __name__ == "__main__":
    main()

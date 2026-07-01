"""
Bengston JSE Retrospective Meta-Analysis (TSS-EMP-9)
=====================================================

Pass 60 batch-1 — 2026-05-22

Pre-registered random-effects meta-analysis across the published Bengston
corpus. Applies Pass-58 TSIS four-gate stack + Pass-60 PD/TIL/HEM-GILE
mapping layer + Tralse-Joules accounting.

USAGE:
  1. Brandon verifies trial numbers against JSE originals (free archive at
     scientificexploration.org/journal).
  2. Populate the TRIALS list below with verified numbers.
  3. Run: python3 simulations/bengston_jse_meta_analysis_2026-05-22.py
  4. Script writes JSON results + prints summary.

PRE-REGISTERED FALSIFIERS (do NOT modify after execution):
  F-BENGSTON-META-1: pooled Delta_p < 0.20 ⇒ Pass-59 Bengston TSIS reading
                     REFUTED; reclassify as INDETERMINATE pending TSS-EMP-8.
  F-BENGSTON-META-2: pooled Delta_p < 0.046 ⇒ reclassify as FALSE-weak;
                     publicly retract Pass-59 §3 under R11.
  F-TJ-BENGSTON-1:   Pearson r(TJ_integral, Delta_p_per_trial) < 0.40
                     across verified corpus ⇒ TJ-axis does NOT predict
                     Bengston effect strength quantitatively; urb_650
                     requires re-calibration.
"""

import json
import math
from datetime import datetime
from pathlib import Path


# ----- Pass-58 / Pass-60 canonical constants ----------------------------------
T_RAND = 0.0660
T_BORDER = 0.13534
C_LCC = 0.4370
MARGINAL_EPSILON = 0.020      # Pass-60 §2 INDETERMINATE-band width
INDET_BAND_LO = T_RAND - MARGINAL_EPSILON
INDET_BAND_HI = T_RAND + MARGINAL_EPSILON


# ----- TRIALS: Brandon populates from JSE-verified data -----------------------
# Format per trial:
#   "label"     : str
#   "year"      : int
#   "n_treat"   : int    # number of treated animals/subjects
#   "n_ctrl"    : int    # number of controls
#   "p_treat"   : float  # observed remission rate in treated arm
#   "p_ctrl"    : float  # observed remission rate in control arm
#   "healer_hr" : float  # total healer-hours invested in the trial
#   "n_healers" : int
#   "control_type": "no-attention" | "sham-attention"  # weighting factor
#   "verified"  : bool   # True only when Brandon has confirmed against original
TRIALS = [
    {
        "label": "Bengston & Krinsley",
        "year": 2000,
        "n_treat": 33,
        "n_ctrl": 30,        # PLACEHOLDER — verify
        "p_treat": 17 / 33,
        "p_ctrl": 0.001,     # PLACEHOLDER — verify
        "healer_hr": 140,
        "n_healers": 5,
        "control_type": "no-attention",
        "verified": False,
    },
    # ----- Brandon: add verified trials 2..N below per Section 2 of -----
    # ----- papers/PASS_60_BENGSTON_JSE_RETROSPECTIVE_META_ANALYSIS_2026-05-22.md
    # {
    #     "label": "Bengston 2007 St Joseph's",
    #     "year": 2007,
    #     "n_treat": ...,
    #     ...
    # },
]


# ----- Effect-size + meta-analysis helpers -----------------------------------
def cohens_h(p1, p2):
    p1 = max(1e-9, min(1.0 - 1e-9, p1))
    p2 = max(1e-9, min(1.0 - 1e-9, p2))
    return 2.0 * math.asin(math.sqrt(p1)) - 2.0 * math.asin(math.sqrt(p2))


def trial_variance(trial):
    """Approximate variance of Delta_p using p(1-p)/n per arm."""
    p1, n1 = trial["p_treat"], trial["n_treat"]
    p2, n2 = trial["p_ctrl"], trial["n_ctrl"]
    var = (p1 * (1 - p1) / max(1, n1)) + (p2 * (1 - p2) / max(1, n2))
    return max(var, 1e-9)


def derSimonian_Laird_pooled(deltas, variances, weights_design):
    """Random-effects pooled estimate with DerSimonian-Laird tau^2."""
    # Fixed-effect pooled
    w_fe = [1.0 / v for v in variances]
    # Apply design weights (sham=1.0; no-attention=0.7 per pre-registration)
    w_fe = [w * d for w, d in zip(w_fe, weights_design)]
    pooled_fe = sum(w * d for w, d in zip(w_fe, deltas)) / sum(w_fe)

    # Q statistic + tau^2
    Q = sum(w * (d - pooled_fe) ** 2 for w, d in zip(w_fe, deltas))
    df = max(1, len(deltas) - 1)
    c = sum(w_fe) - (sum(w ** 2 for w in w_fe) / sum(w_fe))
    tau2 = max(0.0, (Q - df) / max(c, 1e-9))

    # Random-effects weights
    w_re = [1.0 / (v + tau2) for v in variances]
    w_re = [w * d for w, d in zip(w_re, weights_design)]
    pooled_re = sum(w * d for w, d in zip(w_re, deltas)) / sum(w_re)

    # I^2 heterogeneity
    I2 = max(0.0, (Q - df) / max(Q, 1e-9)) if Q > 0 else 0.0
    return pooled_re, tau2, I2, Q


def classify_pd_til(pooled_delta, gate_count, I2):
    """Pass-60 §3.3 pre-registered band classification."""
    in_marginal_band = INDET_BAND_LO <= pooled_delta <= INDET_BAND_HI
    if in_marginal_band:
        return ("INDETERMINATE-band", 0.0, "pooled effect inside [%.3f, %.3f]" %
                (INDET_BAND_LO, INDET_BAND_HI))
    if pooled_delta >= 0.30 and I2 < 0.50 and gate_count >= 3:
        return ("TRUE-provisional", +1.6, "high effect + low heterogeneity + 3+ gates")
    if pooled_delta >= 0.30 and I2 >= 0.75:
        return ("INDETERMINATE (heterogeneity dominates)", +0.3,
                "effect high but I^2 >= 75%")
    if pooled_delta >= T_BORDER and gate_count >= 3:
        return ("INDETERMINATE-leaning-TRUE", +1.0, "effect >= T_BORDER + 3 gates")
    if pooled_delta < INDET_BAND_LO and gate_count <= 2:
        return ("FALSE-weak", -0.5, "effect < marginal band, gates fail")
    return ("INDETERMINATE", 0.0, "default band")


def tj_estimate(trial):
    """urb_650 TJ accounting: tau(s) x delta(MR)."""
    tau_integral = trial["healer_hr"]            # ~1 TJ-hr per saturated hr
    delta_MR = 2.0 if trial["p_treat"] > 0.30 else 0.5  # remission = +2.0 PD
    return tau_integral * delta_MR * 0.1         # scaling constant from urb_650


def main():
    print("=" * 78)
    print("Bengston JSE Retrospective Meta-Analysis (TSS-EMP-9) — Pass 60")
    print("=" * 78)

    if not TRIALS:
        print("\nNo trials populated. Edit TRIALS[] above per Section 2 of the")
        print("Pass-60 Bengston meta-analysis paper, then re-run.")
        return

    verified_count = sum(1 for t in TRIALS if t.get("verified"))
    print(f"\nTrials loaded: {len(TRIALS)} (verified: {verified_count})")
    if verified_count < len(TRIALS):
        print(f"WARNING: {len(TRIALS) - verified_count} unverified trial(s) — "
              f"this run is a TEMPLATE / DRY-RUN.\n")

    deltas, variances, weights_design, tjs = [], [], [], []
    print(f"{'Trial':30s} {'Year':6s} {'N_t':6s} {'N_c':6s} {'Δp':8s} "
          f"{'Cohen h':8s} {'TJ':6s}")
    print("-" * 78)
    for t in TRIALS:
        delta = t["p_treat"] - t["p_ctrl"]
        h = cohens_h(t["p_treat"], t["p_ctrl"])
        var = trial_variance(t)
        wd = 1.0 if t["control_type"] == "sham-attention" else 0.7
        tj = tj_estimate(t)
        deltas.append(delta)
        variances.append(var)
        weights_design.append(wd)
        tjs.append(tj)
        print(f"{t['label']:30s} {t['year']:6d} {t['n_treat']:6d} "
              f"{t['n_ctrl']:6d} {delta:8.4f} {h:8.4f} {tj:6.1f}")
    print("-" * 78)

    pooled, tau2, I2, Q = derSimonian_Laird_pooled(deltas, variances,
                                                   weights_design)
    print(f"\nPooled Δp (random-effects, DL): {pooled:.4f}")
    print(f"Heterogeneity: τ²={tau2:.4f}  I²={I2:.3f}  Q={Q:.3f}")
    print(f"Marginal INDETERMINATE band: [{INDET_BAND_LO:.3f}, "
          f"{INDET_BAND_HI:.3f}]")

    # TSIS gate count (corpus-level)
    gate_count = 0
    if pooled >= T_RAND:
        gate_count += 1
    if pooled >= T_BORDER:
        gate_count += 1
    gate_count += 1   # APP-1 ≥ 2/3 (intentional engagement + skill-asymmetry)
    # LCC gate unmeasured at corpus level
    print(f"TSIS gates passed (corpus level): {gate_count}/4 "
          f"(LCC unmeasured = open)")

    label, pd, reason = classify_pd_til(pooled, gate_count, I2)
    print(f"\nPass-60 MR Truth Label: {label}")
    print(f"Pass-60 PD coordinate: {pd:+.2f}")
    print(f"Classification reason: {reason}")

    # TJ-axis correlation
    if len(TRIALS) >= 3:
        mean_tj = sum(tjs) / len(tjs)
        mean_d = sum(deltas) / len(deltas)
        num = sum((tj - mean_tj) * (d - mean_d) for tj, d in zip(tjs, deltas))
        den_tj = math.sqrt(sum((tj - mean_tj) ** 2 for tj in tjs))
        den_d = math.sqrt(sum((d - mean_d) ** 2 for d in deltas))
        r = num / max(den_tj * den_d, 1e-9)
        print(f"\nTJ-axis prediction test (F-TJ-BENGSTON-1):")
        print(f"  Pearson r(TJ_integral, Δp) = {r:+.3f}")
        print(f"  Threshold for confirm: r ≥ 0.40")
        print(f"  Verdict: {'CONFIRMED' if r >= 0.40 else 'NOT confirmed at this corpus size'}")
    else:
        print("\nTJ-axis correlation requires ≥3 trials; skipped.")

    # Falsifier check
    print("\nPre-registered falsifier check:")
    if pooled < 0.046:
        print("  F-BENGSTON-META-2 TRIPPED: pooled Δp < 0.046 (FALSE-weak band)")
        print("  → Pass-59 Bengston TSIS reading REQUIRES public retraction (R11)")
    elif pooled < 0.20:
        print("  F-BENGSTON-META-1 TRIPPED: pooled Δp < 0.20")
        print("  → Reclassify Bengston as INDETERMINATE pending TSS-EMP-8")
    else:
        print(f"  Both falsifiers NOT REFUTED at pooled Δp = {pooled:.4f}")

    # Write JSON
    out = {
        "pass": "Pass 60 batch-1",
        "date": datetime.utcnow().isoformat() + "Z",
        "constants": {
            "T_RAND": T_RAND, "T_BORDER": T_BORDER, "C_LCC": C_LCC,
            "MARGINAL_EPSILON": MARGINAL_EPSILON,
            "INDET_BAND": [INDET_BAND_LO, INDET_BAND_HI],
        },
        "trials": TRIALS,
        "trials_verified_count": verified_count,
        "pooled_delta_p": pooled,
        "heterogeneity": {"tau2": tau2, "I2": I2, "Q": Q},
        "tsis_gates_passed": gate_count,
        "pass60_label": label,
        "pass60_pd": pd,
        "pass60_reason": reason,
        "honesty_note": (
            "Numerical conclusions valid only after Brandon completes JSE-paper "
            "verification of all trial cells. This run executes the pre-registered "
            "protocol on the supplied numbers."
        ),
    }
    out_path = Path(__file__).parent / "bengston_jse_meta_analysis_2026-05-22_results.json"
    with open(out_path, "w") as f:
        json.dump(out, f, indent=2, default=str)
    print(f"\nResults written: {out_path}")


if __name__ == "__main__":
    main()

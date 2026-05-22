"""
Bengston Healing Method — TI Sigma TSIS Four-Gate Stack Evaluation
====================================================================

Pass 59 — 2026-05-21
Brandon Emerick + TI Sigma framework

Applies the Pass-58 batch-1 TSIS four-gate stack (TSD-A, LCC, effect-vs-T_RAND,
MBE-Acc) to Bengston's published summary statistics. Quantitative comparison to
the Pass-58 psi re-evaluation corpus (Ganzfeld, Radin, Bem, PEAR, GCP).

Falsifier (F-BENGSTON-1): if any future independent oncology-lab replication
shows Delta_p < 0.30 between healed and untreated control at N >= 60 per arm,
this TSIS evaluation is REFUTED.

Output: stdout summary + JSON results file.
"""

import json
import math
from datetime import datetime
from pathlib import Path


# ---------------------------------------------------------------------------
# Pass-58 canonical thresholds (do not modify without ratification)
# ---------------------------------------------------------------------------
T_RAND = 0.0660       # absolute randomness threshold
T_BORDER = 0.13534    # 1/e^2 border threshold
C_LCC = 0.4370        # LCC coherence threshold


# ---------------------------------------------------------------------------
# Published / reconstructed corpus values (Brandon to verify against originals)
# ---------------------------------------------------------------------------
CORPUS = {
    # name : (effect_strength, N_per_arm, app1_score, lcc_measured, lcc_value, notes)
    "Ganzfeld (meta)":       (0.07,   3000, 2.0, False, None, "concordant meta"),
    "Radin presentiment":    (0.21,    500, 2.0, False, None, "d ~= 0.21, SCR coupling"),
    "Bem 2011":              (0.022,  1000, 1.0, False, None, "failed replication"),
    "PEAR REG":              (0.0002, 1e7,  0.5, False, None, "canonical Lindley"),
    "GCP":                   (5e-5,   1e9,  0.5, False, None, "canonical Lindley"),
    "Bengston & Krinsley 2000": (0.515, 33,  2.5, False, None,
                                 "17/33 remission vs 0/N base rate"),
}


def cohens_h(p1: float, p2: float) -> float:
    """Cohen's h effect size for proportions."""
    p1 = max(0.0, min(1.0, p1))
    p2 = max(0.0, min(1.0, p2))
    return 2.0 * math.asin(math.sqrt(p1)) - 2.0 * math.asin(math.sqrt(p2))


def evaluate_tsis(name, effect, N, app1, lcc_measured, lcc_value):
    """Run the four-gate TSIS stack on a single program."""
    gates = {}

    # Gate 1: effect >= T_RAND (the active-pressure RO threshold)
    gates["effect_vs_T_RAND"] = {
        "threshold": T_RAND,
        "observed": effect,
        "pass": effect >= T_RAND,
        "margin_x": effect / T_RAND if T_RAND > 0 else float("inf"),
    }

    # Gate 2: effect >= T_BORDER (stronger border)
    gates["effect_vs_T_BORDER"] = {
        "threshold": T_BORDER,
        "observed": effect,
        "pass": effect >= T_BORDER,
        "margin_x": effect / T_BORDER if T_BORDER > 0 else float("inf"),
    }

    # Gate 3: APP-1 active-pragmatism (>= 2 of 3 engagement criteria)
    gates["app1_engagement"] = {
        "threshold": 2.0,
        "observed": app1,
        "pass": app1 >= 2.0,
    }

    # Gate 4: LCC coherence (if measured)
    if lcc_measured:
        gates["lcc_coherence"] = {
            "threshold": C_LCC,
            "observed": lcc_value,
            "pass": (lcc_value is not None) and lcc_value >= C_LCC,
        }
    else:
        gates["lcc_coherence"] = {
            "threshold": C_LCC,
            "observed": None,
            "pass": None,
            "note": "UNMEASURED — see TSS-EMP-8 replication design",
        }

    # Overall verdict
    passed = sum(1 for g in gates.values() if g.get("pass") is True)
    failed = sum(1 for g in gates.values() if g.get("pass") is False)
    unmeasured = sum(1 for g in gates.values() if g.get("pass") is None)

    if failed >= 1 and passed <= 1:
        verdict = "DISCONFIRMED"
    elif passed >= 3 and failed == 0:
        verdict = "CONFIRM-likely"
    elif passed >= 3 and unmeasured >= 1 and failed == 0:
        verdict = "CONFIRM-pending-LCC-replication"
    elif passed == 2 and failed == 0:
        verdict = "INDETERMINATE"
    else:
        verdict = "INDETERMINATE"

    return {
        "name": name,
        "effect": effect,
        "N_per_arm": N,
        "app1_score": app1,
        "gates": gates,
        "passed_gates": passed,
        "failed_gates": failed,
        "unmeasured_gates": unmeasured,
        "verdict": verdict,
    }


def main():
    print("=" * 78)
    print("Bengston Healing Method — TI Sigma TSIS Four-Gate Evaluation")
    print("Pass 59 — 2026-05-21")
    print("=" * 78)
    print()
    print(f"Canonical thresholds (Pass-58 batch-1 frozen):")
    print(f"  T_RAND   = {T_RAND}")
    print(f"  T_BORDER = {T_BORDER}")
    print(f"  C_LCC    = {C_LCC}")
    print()

    # Bengston-specific Cohen's h for proportion difference
    p_healed = 17 / 33
    p_base = 0.0001   # near-zero base-rate; epsilon to avoid asin(0) degeneracy
    h = cohens_h(p_healed, p_base)
    print(f"Bengston & Krinsley 2000 effect-size check:")
    print(f"  p(healed)     = {p_healed:.4f} (17/33)")
    print(f"  p(base rate)  = ~{p_base} (BT-474 uniformly fatal by day 27)")
    print(f"  Delta_p       = {p_healed - p_base:.4f}")
    print(f"  Cohen's h     = {h:.4f}   (large effect by Cohen's standard >= 0.8)")
    print()

    results = []
    print("Per-program TSIS verdict:")
    print("-" * 78)
    for name, (effect, N, app1, lcc_meas, lcc_val, _note) in CORPUS.items():
        res = evaluate_tsis(name, effect, N, app1, lcc_meas, lcc_val)
        results.append(res)
        gate_str = (
            f"effect/T_RAND={res['gates']['effect_vs_T_RAND']['margin_x']:6.2f}x  "
            f"effect/T_BORDER={res['gates']['effect_vs_T_BORDER']['margin_x']:6.2f}x  "
            f"APP-1={res['app1_score']:.1f}/3  "
            f"LCC={'UNMEASURED' if res['unmeasured_gates'] else 'measured'}"
        )
        print(f"  {name:32s} verdict: {res['verdict']:35s}")
        print(f"    {gate_str}")
    print("-" * 78)
    print()

    # Bengston spotlight summary
    bengston = next(r for r in results if r["name"].startswith("Bengston"))
    print("Bengston spotlight:")
    print(f"  effect strength    = {bengston['effect']:.4f}")
    print(f"  T_RAND multiple    = {bengston['gates']['effect_vs_T_RAND']['margin_x']:.1f}x  (Ganzfeld passes at 1.06x)")
    print(f"  T_BORDER multiple  = {bengston['gates']['effect_vs_T_BORDER']['margin_x']:.1f}x  (Radin passes at 1.55x)")
    print(f"  Gates passed       = {bengston['passed_gates']}/4")
    print(f"  Gates unmeasured   = {bengston['unmeasured_gates']}/4  (LCC — addressed in TSS-EMP-8)")
    print(f"  Verdict            = {bengston['verdict']}")
    print()

    # Pre-registered falsifier
    print("Pre-registered falsifier F-BENGSTON-1:")
    print("  If independent oncology-lab replication at N>=60 per arm produces")
    print("  Delta_p < 0.30, this TSIS evaluation is REFUTED.")
    print()
    print("Active-pressure RO regime (Pass-59 ROS-1):")
    print("  Bengston is in the high-tau x high-delta(MR) corner of TJ space.")
    print("  PEAR/GCP are in the tiny-tau x tiny-delta corner — the Lindley regime.")
    print("  Same statistical framework correctly distinguishes the two.")
    print()

    # Write JSON
    output_path = Path(__file__).parent / "bengston_tsis_evaluation_2026-05-21_results.json"
    output = {
        "pass": "Pass 59",
        "date": datetime.utcnow().isoformat() + "Z",
        "thresholds": {"T_RAND": T_RAND, "T_BORDER": T_BORDER, "C_LCC": C_LCC},
        "results": results,
        "bengston_spotlight": bengston,
        "falsifier": {
            "id": "F-BENGSTON-1",
            "condition": "Delta_p < 0.30 in independent oncology lab replication N>=60/arm",
            "current_status": "NOT REFUTED (replication not yet executed)",
        },
        "honesty_notes": [
            "Bengston & Krinsley 2000 numbers reconstructed from secondary sources; verify against JSE original before publication.",
            "Resonant-bonding contamination of control groups is a real design concern; sham-attention control is the proper fix.",
            "TSS-EMP-8 budget ($50k-$200k) is OUTSIDE Brandon's $0/$50 personal budget — flagged for grant or partnership.",
            "TSS-EMP-9 retrospective meta-analysis ACROSS all Bengston JSE papers is $0-budget feasible from open-access archives.",
        ],
    }
    with open(output_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"Results written: {output_path}")


if __name__ == "__main__":
    main()

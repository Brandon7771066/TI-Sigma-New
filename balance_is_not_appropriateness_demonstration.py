"""
balance_is_not_appropriateness_demonstration.py
================================================

Controlled toy demonstration for URB #814 (NOT empirical evidence; not a
model of any specific human decision).

What this script is: a sanity check that "balanced" (equal weight on each
side, encoded here as 0.5 on a [0,1] axis) is the wrong prescription for
most real situations, because most real situations are asymmetric and
require a response weighted to one side. It scores three response
strategies — Balanced (always 0.5), Appropriate (matches the situation's
optimal weight), and Compromise (averages 0.5 and the optimal) — on a
hand-curated list of 10 scenarios with explicitly-stated asymmetry.

What this script is NOT: a measurement of how often the fallacy occurs in
practice, a clinical or policy recommendation, or a claim that any
specific scenario's "optimal weight" reflects universal moral truth. The
specific weights are illustrative figures chosen to make the structural
point; they are not normative prescriptions about the listed scenarios.

Pure NumPy. Deterministic seed. Wall time < 1 s.
"""
from __future__ import annotations
import json
import numpy as np

RNG_SEED = 20260430

# 15 scenarios. For each, "optimal_weight" is the appropriate weight on
# "side A" (whatever side A means in the scenario) on a [0, 1] axis. 0.5
# means symmetric (balanced is appropriate); >0.5 means asymmetric toward
# side A; <0.5 means asymmetric toward side B (i.e., the appropriate
# response is to weight AWAY from side A, toward minimal/disengaging).
# Including BOTH directions of asymmetry — not just one — makes the
# demonstration honest: it shows that balance-at-0.5 fails for
# asymmetries running EITHER way, not only when the asymmetric pull is
# "do more." The labels are illustrative; the structural point does not
# depend on the exact figures, and reasonable readers may disagree on
# specific cases.
SCENARIOS = [
    # Asymmetric, optimum > 0.5 (more engagement/assertion/focus).
    ("child_running_into_traffic",        "side A = full intervention",          0.97),
    ("friend_describes_serious_loss",     "side A = listening (vs speaking)",    0.88),
    ("apology_for_serious_harm",          "side A = full ownership",             0.95),
    ("romantic_declaration_of_love",      "side A = undiluted statement",        0.92),
    ("emergency_surgery",                 "side A = total focus on the cut",     0.97),
    ("defensive_coding_hostile_input",    "side A = reject-by-default",          0.95),
    ("vaccine_policy_briefing",           "side A = evidence-supported view",    0.95),
    ("climate_policy_briefing",           "side A = evidence-supported view",    0.95),
    ("witnessing_a_serious_crime",        "side A = truthful testimony",         0.95),
    # Symmetric (balanced IS appropriate).
    ("casual_chat_about_a_movie",         "side A = your speaking turn",         0.50),
    ("commodity_price_negotiation",       "side A = your share of surplus",      0.50),
    # Asymmetric, optimum < 0.5 (less engagement / minimal / disengaging).
    ("boastful_colleague_seeks_praise",   "side A = effusive praise",            0.15),
    ("persistent_salesperson_pressure",   "side A = elaborate justification",    0.10),
    ("stranger_intrusive_question",       "side A = full personal disclosure",   0.15),
    ("drunk_picks_political_argument",    "side A = engaged debate",             0.05),
]


def main():
    rng = np.random.default_rng(RNG_SEED)  # not used; reserved for future stochastic variants
    _ = rng  # silence unused warning

    names = [s[0] for s in SCENARIOS]
    descriptions = [s[1] for s in SCENARIOS]
    optimal = np.array([s[2] for s in SCENARIOS])

    balanced = np.full_like(optimal, 0.5)
    appropriate = optimal.copy()
    compromise = (balanced + appropriate) / 2.0

    def score(name, response):
        abs_err = np.abs(response - optimal)
        return {
            "responder": name,
            "per_scenario_response": response.tolist(),
            "per_scenario_abs_error": abs_err.tolist(),
            "mean_absolute_error": float(abs_err.mean()),
            "max_absolute_error": float(abs_err.max()),
            "fraction_within_0_05_of_optimal": float(
                (abs_err <= 0.05).mean()
            ),
        }

    scores = [
        score("Balanced (always 0.5)", balanced),
        score("Appropriate (matches optimal)", appropriate),
        score("Compromise (avg of 0.5 and optimal)", compromise),
    ]

    n_scenarios = len(SCENARIOS)
    n_symmetric = int(np.sum(optimal == 0.5))
    n_asymmetric = n_scenarios - n_symmetric

    diagnostic = {
        "n_scenarios": n_scenarios,
        "n_symmetric_scenarios": n_symmetric,
        "n_asymmetric_scenarios": n_asymmetric,
        "mae_balanced": next(
            s["mean_absolute_error"] for s in scores
            if s["responder"].startswith("Balanced")
        ),
        "mae_appropriate": next(
            s["mean_absolute_error"] for s in scores
            if s["responder"].startswith("Appropriate")
        ),
        "mae_compromise": next(
            s["mean_absolute_error"] for s in scores
            if s["responder"].startswith("Compromise")
        ),
        "interpretation": (
            "Balanced (always 0.5) is OPTIMAL for the symmetric scenarios "
            "and POORLY-FIT for the asymmetric ones. The appropriate "
            "response is the one that matches the situation; balance "
            "happens to be the appropriate response when the situation "
            "is symmetric, and is harmful when the situation is "
            "asymmetric. The Compromise strategy (averaging balance and "
            "the optimal) reduces the worst-case error of pure-balance "
            "but is still strictly worse than appropriateness on the "
            "asymmetric scenarios. The structural point of URB #814 is "
            "that 'balance' as a context-free prescription is the wrong "
            "policy whenever situations have any underlying asymmetry."
        ),
    }

    report = {
        "config": {
            "rng_seed": RNG_SEED,
            "scenarios": [
                {"name": n, "description": d, "optimal_weight_side_a": float(o)}
                for n, d, o in SCENARIOS
            ],
        },
        "scores": scores,
        "diagnostic": diagnostic,
    }

    print("=" * 72)
    print("URB #814 — Balance Is Not Appropriateness — demonstration")
    print("=" * 72)
    print(f"\n{n_scenarios} scenarios "
          f"({n_symmetric} symmetric, {n_asymmetric} asymmetric)\n")

    print(f"{'Scenario':<38} {'opt':>5}  {'bal':>5} {'app':>5} {'cmp':>5}")
    print("-" * 64)
    for i, (name, desc, opt) in enumerate(SCENARIOS):
        print(f"{name:<38} {opt:>5.2f}  "
              f"{balanced[i]:>5.2f} {appropriate[i]:>5.2f} "
              f"{compromise[i]:>5.2f}")

    print("\n--- Mean absolute error vs. optimal ---")
    for s in scores:
        print(f"  {s['responder']:<40} "
              f"MAE={s['mean_absolute_error']:.4f}  "
              f"max={s['max_absolute_error']:.4f}  "
              f"frac-within-0.05={s['fraction_within_0_05_of_optimal']:.2f}")

    print("\n--- Diagnostic ---")
    d = report["diagnostic"]
    print(f"  scenarios: {d['n_scenarios']} "
          f"({d['n_symmetric_scenarios']} symmetric, "
          f"{d['n_asymmetric_scenarios']} asymmetric)")
    print(f"  MAE(Balanced)    = {d['mae_balanced']:.4f}")
    print(f"  MAE(Appropriate) = {d['mae_appropriate']:.4f}")
    print(f"  MAE(Compromise)  = {d['mae_compromise']:.4f}")
    print(f"\n  Interpretation: {d['interpretation']}")

    out_path = "balance_is_not_appropriateness_report.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()

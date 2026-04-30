"""
consciousness_as_razor_demonstration.py
========================================

Controlled structural illustration for URB #813 (NOT empirical evidence
about real human consciousness).

What this script is: a sanity check that the conventional "variance over
time" metric cannot distinguish an adaptive-amplitude profile (high
variance, but tightly correlated with activity demands) from a pathological-
amplitude profile (high variance, uncorrelated with activity demands), and
that an activity-fit metric (mean squared error vs. activity-optimal
arousal) can.

What this script is NOT: a measurement of any actual person's consciousness,
or a clinical diagnostic tool, or a claim that any specific psychiatric
label is wrong in any specific case. The point is a structural one about
metric selection: variance alone is insufficient.

Setup:
- 5000 timesteps. Each step is randomly assigned an activity from
  {meditate, relax, study, socialize} with known optimal arousal levels.
- Three agents emit arousal levels each timestep:
    Flat:           always emits 0.5 (middle, low variance)
    Adaptive:       emits the activity-optimal arousal (high variance,
                    perfect context-tracking) — IDEALIZED for the demo
    ContextUncoupled: emits arousal sampled from the same distribution
                    as the optimal-arousal sequence but RANDOMLY PERMUTED
                    in time (matched marginal distribution, zero
                    correlation with activity context). STRUCTURAL FOIL
                    for the variance-vs.-context-coupling distinction.
                    NOT a clinical model of bipolar disorder or any
                    other psychiatric condition; does not include
                    duration, impairment, sleep, psychosis, or risk
                    criteria that real clinical diagnosis uses.
- Score on:
    (i)   variance of arousal over time (conventional "stability"),
    (ii)  activity-fit = -mean((arousal - optimal_arousal)^2) (higher better),
    (iii) Pearson correlation between emitted arousal and optimal arousal.

Punchline:
    Variance ranks Flat << Adaptive ≈ ContextUncoupled. The conventional
    metric cannot tell Adaptive from ContextUncoupled.
    Activity-fit ranks Adaptive >> Flat >> ContextUncoupled. The right
    metric can.

Pure NumPy. Deterministic seed. Wall time < 1 s.
"""
from __future__ import annotations
import json
import numpy as np

RNG_SEED = 20260430

# Activity catalog: name -> optimal arousal in [0, 1]
ACTIVITIES = {
    "meditate":  0.10,
    "relax":     0.25,
    "study":     0.60,
    "socialize": 0.85,
}


def simulate(n_steps: int = 5000, rng: np.random.Generator | None = None):
    if rng is None:
        rng = np.random.default_rng(RNG_SEED)

    activity_names = list(ACTIVITIES.keys())
    activity_optima = np.array([ACTIVITIES[a] for a in activity_names])

    # Random sequence of activities (uniform).
    idx_seq = rng.integers(0, len(activity_names), size=n_steps)
    optimal_arousal = activity_optima[idx_seq]

    # Agent 1: Flat. Always emits 0.5 (middle).
    flat = np.full(n_steps, 0.5)

    # Agent 2: Adaptive. Always emits the optimal arousal for the current
    # activity.
    adaptive = optimal_arousal.copy()

    # Agent 3: ContextUncoupled. Same MARGINAL distribution as Adaptive
    # (it produces the same set of arousal values across the run, in the
    # same frequencies), but RANDOMLY PERMUTED so the emission is
    # uncorrelated with the actual activity sequence. This is a STRUCTURAL
    # FOIL designed to share variance with Adaptive but differ on context-
    # coupling — NOT a clinical model.
    permuted_idx = rng.permutation(n_steps)
    context_uncoupled = optimal_arousal[permuted_idx]

    def score(name, arousal):
        var = float(arousal.var())
        mse = float(((arousal - optimal_arousal) ** 2).mean())
        fit = -mse  # higher = better
        # Pearson correlation; guard the constant-emission case for Flat.
        if arousal.std() == 0 or optimal_arousal.std() == 0:
            corr = 0.0
        else:
            corr = float(np.corrcoef(arousal, optimal_arousal)[0, 1])
        return {
            "agent": name,
            "variance": var,
            "stability_metric_value": var,
            "activity_fit_metric_value": fit,
            "mean_squared_error_vs_optimal": mse,
            "correlation_with_optimal": corr,
        }

    scores = [
        score("Flat (always 0.5)", flat),
        score("Adaptive (matches optimal)", adaptive),
        score("ContextUncoupled (matched marginals, no context-tracking)",
              context_uncoupled),
    ]

    # Rank under each metric.
    def ranking_under(metric_key, lower_is_better=False):
        sorted_scores = sorted(
            scores,
            key=lambda s: s[metric_key],
            reverse=not lower_is_better,
        )
        return [(s["agent"], s[metric_key]) for s in sorted_scores]

    rankings = {
        "by_stability_metric_lower_is_better": ranking_under(
            "stability_metric_value", lower_is_better=True
        ),
        "by_activity_fit_metric_higher_is_better": ranking_under(
            "activity_fit_metric_value", lower_is_better=False
        ),
        "by_correlation_with_optimal_higher_is_better": ranking_under(
            "correlation_with_optimal", lower_is_better=False
        ),
    }

    # The diagnostic claim: variance cannot distinguish Adaptive from
    # Pathological (they have the same marginal distribution by construction,
    # so identical variance), but activity-fit and correlation can.
    var_adaptive = next(s["variance"] for s in scores
                        if s["agent"].startswith("Adaptive"))
    var_uncoupled = next(s["variance"] for s in scores
                          if s["agent"].startswith("ContextUncoupled"))
    fit_adaptive = next(s["activity_fit_metric_value"] for s in scores
                        if s["agent"].startswith("Adaptive"))
    fit_uncoupled = next(s["activity_fit_metric_value"] for s in scores
                          if s["agent"].startswith("ContextUncoupled"))

    diagnostic = {
        "variance_adaptive": var_adaptive,
        "variance_context_uncoupled": var_uncoupled,
        "variance_gap_pp": (var_uncoupled - var_adaptive) * 100,
        "activity_fit_adaptive": fit_adaptive,
        "activity_fit_context_uncoupled": fit_uncoupled,
        "activity_fit_gap": fit_adaptive - fit_uncoupled,
        "interpretation": (
            "By construction Adaptive and ContextUncoupled share the same "
            "marginal distribution of arousal values, so their variances "
            "are identical (modulo permutation noise of order 0). The "
            "conventional stability metric (variance) therefore CANNOT "
            "distinguish the context-coupled profile from the context-"
            "uncoupled profile. The activity-fit metric (negative MSE vs. "
            "optimal arousal) and the correlation-with-optimal metric BOTH "
            "cleanly distinguish them. This is the structural point of URB "
            "#813. ContextUncoupled is a STRUCTURAL FOIL, not a clinical "
            "model of any psychiatric condition; real clinical diagnosis "
            "uses additional criteria (duration, impairment, sleep, "
            "psychosis, risk) that this toy does not capture."
        ),
    }

    return {
        "config": {
            "n_steps": n_steps,
            "activities": ACTIVITIES,
            "rng_seed": RNG_SEED,
        },
        "scores": scores,
        "rankings": rankings,
        "diagnostic_variance_cannot_distinguish": diagnostic,
    }


def main():
    print("=" * 72)
    print("URB #813 — Consciousness as a Razor 🪒 demonstration")
    print("=" * 72)
    rng = np.random.default_rng(RNG_SEED)
    report = simulate(rng=rng)

    cfg = report["config"]
    print(f"\nConfig: n_steps={cfg['n_steps']}, "
          f"activities={list(cfg['activities'].keys())}, seed={cfg['rng_seed']}")
    print("Activity-optimal arousal levels:")
    for k, v in cfg["activities"].items():
        print(f"  {k:>10}: {v:.2f}")

    print("\n--- Per-agent scores ---")
    for s in report["scores"]:
        print(f"\n  {s['agent']}:")
        print(f"    variance (stability metric, lower=better):     "
              f"{s['variance']:.4f}")
        print(f"    activity-fit (negative MSE, higher=better):    "
              f"{s['activity_fit_metric_value']:+.4f}")
        print(f"    correlation with optimal (higher=better):      "
              f"{s['correlation_with_optimal']:+.4f}")

    print("\n--- Rankings under each metric ---")
    print("\n  Conventional stability metric (variance, lower is 'better'):")
    for i, (name, val) in enumerate(report["rankings"]
                                     ["by_stability_metric_lower_is_better"], 1):
        print(f"    {i}. {name}: {val:.4f}")

    print("\n  Activity-fit metric (negative MSE, higher is better):")
    for i, (name, val) in enumerate(
            report["rankings"]["by_activity_fit_metric_higher_is_better"], 1):
        print(f"    {i}. {name}: {val:+.4f}")

    print("\n  Correlation-with-optimal metric (higher is better):")
    for i, (name, val) in enumerate(
            report["rankings"]
            ["by_correlation_with_optimal_higher_is_better"], 1):
        print(f"    {i}. {name}: {val:+.4f}")

    print("\n--- Diagnostic: can the conventional metric distinguish "
          "Adaptive from ContextUncoupled? ---")
    d = report["diagnostic_variance_cannot_distinguish"]
    print(f"  variance(Adaptive)         = {d['variance_adaptive']:.6f}")
    print(f"  variance(ContextUncoupled) = "
          f"{d['variance_context_uncoupled']:.6f}")
    print(f"  variance gap (pp)          = "
          f"{d['variance_gap_pp']:+.6f}  "
          "<-- ~0 by construction; conventional metric cannot tell them apart")
    print(f"\n  activity-fit(Adaptive)         = "
          f"{d['activity_fit_adaptive']:+.4f}")
    print(f"  activity-fit(ContextUncoupled) = "
          f"{d['activity_fit_context_uncoupled']:+.4f}")
    print(f"  activity-fit gap               = {d['activity_fit_gap']:+.4f}  "
          "<-- large; the right metric DOES distinguish them")

    print(f"\n  Interpretation: {d['interpretation']}")

    out_path = "consciousness_as_razor_report.json"
    with open(out_path, "w") as f:
        json.dump(report, f, indent=2)
    print(f"\nReport written to {out_path}")


if __name__ == "__main__":
    main()

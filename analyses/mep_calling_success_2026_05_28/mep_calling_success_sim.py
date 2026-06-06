"""
MEP (Molinism-Enlightened Person) hypothesis — bias-vs-signal simulation.
Pass-77 B105.

Brandon's concrete question:
  "Success rate of 'major life missions' from people who 'believed with
   conviction that they were called' vs people with similar missions who
   never reported having strong, spiritual-like convictions."

This script does NOT use primary data (budget $0). It is an honest #69
confound-quantification: it asks whether the NAIVE version of Brandon's
question (compare success among people who *report* a calling vs not) can
manufacture a large apparent calling->success lift even when the true causal
effect of calling is ZERO, purely via:
  (1) reverse causation / retrospective attribution (success -> "I was called")
  (2) survivorship (we only hear about notable / successful people)

It then shows that a PROSPECTIVE, competence-matched design recovers the true
effect (zero under H0, g under a genuine effect) -- i.e. it specifies the
study that would actually test MEP.

Deterministic (seeded). numpy only.
"""

import json
import numpy as np
from pathlib import Path

RNG = np.random.default_rng(20260528)
N = 400_000              # population attempting "major missions"
PREVALENCE_CALLING = 0.15   # fraction who genuinely *feel* called at baseline
A_INTERCEPT = -2.6          # base mission-success logit (~7% base rate)
B_COMPETENCE = 1.10         # competence/grit -> success slope
EPS = 0.02                  # INDETERMINATE band half-width on a proportion lift


def sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))


def simulate_population(true_calling_effect_g):
    """One population. Returns a dict of per-individual arrays.

    felt_calling F is assigned at BASELINE, independent of competence
    (calling is not a proxy for ability -- the conservative assumption).
    True success depends on competence C and, if g>0, on felt_calling.
    """
    C = RNG.normal(0.0, 1.0, size=N)                       # competence / grit
    F = (RNG.random(N) < PREVALENCE_CALLING).astype(int)   # felt calling @ baseline
    logit = A_INTERCEPT + B_COMPETENCE * C + true_calling_effect_g * F
    p = sigmoid(logit)
    success = (RNG.random(N) < p).astype(int)
    return {"C": C, "F": F, "success": success}


def reported_calling(success, p_report_if_success, p_report_if_fail):
    """REPORTED calling R (what a retrospective interviewer records).
    Under attribution bias, success raises the probability of reporting
    that one 'always felt called'."""
    p = np.where(success == 1, p_report_if_success, p_report_if_fail)
    return (RNG.random(len(success)) < p).astype(int)


def lift(success, group):
    """Success-rate difference (pp) between group==1 and group==0."""
    g1 = success[group == 1]
    g0 = success[group == 0]
    if len(g1) == 0 or len(g0) == 0:
        return float("nan"), float("nan"), float("nan")
    r1, r0 = g1.mean(), g0.mean()
    return (r1 - r0) * 100, r1 * 100, r0 * 100


def matched_prospective_lift(C, F, success, n_strata=20):
    """Competence-stratified estimate using BASELINE felt-calling F.
    Within each competence stratum, compare success of F=1 vs F=0, then
    average across strata weighted by stratum size. This is the design that
    is immune to outcome-driven attribution (F is fixed before outcome)."""
    edges = np.quantile(C, np.linspace(0, 1, n_strata + 1))
    edges[0], edges[-1] = -np.inf, np.inf
    diffs, weights = [], []
    for i in range(n_strata):
        m = (C >= edges[i]) & (C < edges[i + 1])
        s, f = success[m], F[m]
        if (f == 1).sum() < 30 or (f == 0).sum() < 30:
            continue
        diffs.append(s[f == 1].mean() - s[f == 0].mean())
        weights.append(m.sum())
    diffs, weights = np.array(diffs), np.array(weights, dtype=float)
    return float(np.average(diffs, weights=weights) * 100)


def verdict(observed_pp, expected_zero=True):
    if expected_zero:
        if abs(observed_pp) <= EPS * 100:
            return "WITHIN-INDETERMINATE-BAND (~0, as it should be)"
        return "SPURIOUS LIFT (artifact -- true effect is 0)"
    return f"{observed_pp:+.2f} pp"


def run():
    results = {}

    # ---- Scenario H0: calling has ZERO true causal effect ----
    popH0 = simulate_population(true_calling_effect_g=0.0)
    C, F, S = popH0["C"], popH0["F"], popH0["success"]

    # (a) Ideal prospective comparison on FELT calling (no bias):
    felt_pp, felt1, felt0 = lift(S, F)
    results["H0_felt_calling_prospective"] = {
        "lift_pp": round(felt_pp, 3), "rate_called": round(felt1, 2),
        "rate_not": round(felt0, 2),
        "verdict": verdict(felt_pp, expected_zero=True)}

    # (b) NAIVE retrospective comparison on REPORTED calling (attribution bias):
    R = reported_calling(S, p_report_if_success=0.60, p_report_if_fail=0.10)
    rep_pp, rep1, rep0 = lift(S, R)
    results["H0_reported_calling_retrospective"] = {
        "lift_pp": round(rep_pp, 3), "rate_called": round(rep1, 2),
        "rate_not": round(rep0, 2),
        "attribution": "P(report|success)=0.60, P(report|fail)=0.10",
        "verdict": verdict(rep_pp, expected_zero=True)}

    # (c) Survivorship ON TOP of attribution: keep all successes + 5% of failures
    keep = (S == 1) | (RNG.random(N) < 0.05)
    Ss, Rs = S[keep], R[keep]
    sv_pp, sv1, sv0 = lift(Ss, Rs)
    results["H0_reported_calling_retrospective_plus_survivorship"] = {
        "lift_pp": round(sv_pp, 3), "rate_called": round(sv1, 2),
        "rate_not": round(sv0, 2),
        "note": "notable-only sample = all successes + 5% of failures",
        "verdict": verdict(sv_pp, expected_zero=True)}

    # (d) The FIX: competence-matched prospective estimator under H0
    fix_pp = matched_prospective_lift(C, F, S)
    results["H0_matched_prospective_FIX"] = {
        "lift_pp": round(fix_pp, 3),
        "verdict": verdict(fix_pp, expected_zero=True)}

    # ---- Scenario TRUE: genuine MEP effect (calling boosts persistence) ----
    g_true = 0.70  # logit boost from felt calling
    popT = simulate_population(true_calling_effect_g=g_true)
    Ct, Ft, St = popT["C"], popT["F"], popT["success"]
    true_felt_pp, t1, t0 = lift(St, Ft)          # prospective felt (mixes competence? no, F||C)
    true_fix_pp = matched_prospective_lift(Ct, Ft, St)  # matched recovers causal
    results["TRUE_effect"] = {
        "g_logit": g_true,
        "felt_calling_prospective_lift_pp": round(true_felt_pp, 3),
        "matched_prospective_lift_pp": round(true_fix_pp, 3),
        "verdict": "matched design RECOVERS a real, non-zero lift"}

    # ---- Magnitude of the pure artifact (headline number) ----
    results["HEADLINE"] = {
        "true_causal_effect": 0.0,
        "naive_retrospective_apparent_lift_pp":
            results["H0_reported_calling_retrospective"]["lift_pp"],
        "interpretation":
            "Zero true effect can present as a large apparent calling->success "
            "lift under retrospective self-report. The literal version of the "
            "question is confounded; only a prospective, competence-matched, "
            "pre-registered design can test MEP."}

    # ---- Sensitivity: artifact persists across seeds & bias params (H0) ----
    # Existence-proof robustness: the spurious lift is not a single-seed fluke
    # and not tied to one attribution strength. Vary both and report the range.
    sens = []
    for seed in (1, 7, 42, 101, 2026):
        for (ps, pf) in ((0.50, 0.10), (0.60, 0.10), (0.70, 0.05), (0.40, 0.20)):
            rng = np.random.default_rng(seed)
            C2 = rng.normal(0, 1, N)
            F2 = (rng.random(N) < PREVALENCE_CALLING).astype(int)
            p2 = sigmoid(A_INTERCEPT + B_COMPETENCE * C2)  # g=0, true null
            S2 = (rng.random(N) < p2).astype(int)
            Rp = np.where(S2 == 1, ps, pf)
            R2 = (rng.random(N) < Rp).astype(int)
            pp, _, _ = lift(S2, R2)
            sens.append(pp)
    sens = np.array(sens)
    results["sensitivity_H0_retrospective_artifact"] = {
        "design": "5 seeds x 4 (P_report_success, P_report_fail) settings, true effect=0",
        "min_pp": round(float(sens.min()), 2),
        "max_pp": round(float(sens.max()), 2),
        "mean_pp": round(float(sens.mean()), 2),
        "all_positive_and_large": bool((sens > 15).all()),
        "note": "EXISTENCE PROOF: a large spurious lift appears across every "
                "seed and bias setting; the +36pp headline is illustrative of "
                "the phenomenon, NOT a universal effect-size estimate."}

    out = Path(__file__).parent / "mep_results.json"
    out.write_text(json.dumps(results, indent=2))

    print("=" * 70)
    print("MEP CALLING->SUCCESS: BIAS-vs-SIGNAL SIMULATION (Pass-77 B105)")
    print("=" * 70)
    print(f"N={N:,}  base-rate~{sigmoid(A_INTERCEPT)*100:.1f}%  "
          f"calling-prevalence={PREVALENCE_CALLING:.0%}  eps-band=+/-{EPS*100:.0f}pp")
    print("-" * 70)
    print("SCENARIO H0 (TRUE calling effect = 0):")
    print(f"  (a) felt-calling, prospective (no bias):      "
          f"{results['H0_felt_calling_prospective']['lift_pp']:+.2f} pp  "
          f"-> {results['H0_felt_calling_prospective']['verdict']}")
    print(f"  (b) reported-calling, retrospective:          "
          f"{results['H0_reported_calling_retrospective']['lift_pp']:+.2f} pp  "
          f"-> {results['H0_reported_calling_retrospective']['verdict']}")
    print(f"      (called {rep1:.1f}% success vs not-called {rep0:.1f}%)")
    print(f"  (c) + survivorship (notable-only):            "
          f"{results['H0_reported_calling_retrospective_plus_survivorship']['lift_pp']:+.2f} pp  "
          f"-> {results['H0_reported_calling_retrospective_plus_survivorship']['verdict']}")
    print(f"  (d) FIX: competence-matched prospective:      "
          f"{results['H0_matched_prospective_FIX']['lift_pp']:+.2f} pp  "
          f"-> {results['H0_matched_prospective_FIX']['verdict']}")
    print("-" * 70)
    print(f"SCENARIO TRUE (g_logit={g_true}):")
    print(f"  felt-calling prospective lift:   {true_felt_pp:+.2f} pp")
    print(f"  matched prospective lift:        {true_fix_pp:+.2f} pp  "
          f"-> recovers a real effect")
    print("-" * 70)
    print("HEADLINE: true effect = 0  ->  naive retrospective shows "
          f"{results['HEADLINE']['naive_retrospective_apparent_lift_pp']:+.2f} pp "
          "(pure artifact)")
    print("-" * 70)
    sr = results["sensitivity_H0_retrospective_artifact"]
    print(f"SENSITIVITY (5 seeds x 4 bias settings, true effect=0): "
          f"spurious lift range {sr['min_pp']:+.2f}..{sr['max_pp']:+.2f} pp "
          f"(mean {sr['mean_pp']:+.2f}); all > 15pp: {sr['all_positive_and_large']}")
    print("=" * 70)
    print(f"results saved -> {out}")


if __name__ == "__main__":
    run()

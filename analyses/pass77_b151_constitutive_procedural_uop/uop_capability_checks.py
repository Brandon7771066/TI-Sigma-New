"""
PASS 77 B151 — What the UOP is "truly capable of": the constitutive/procedural split,
outcome-blind GILE determinacy (anti-vacuity), and the credence-vs-proof bound.

No new principle, no ratified candidate (canonical count unchanged 79). Honesty rails:
#69 both-ways, TPS-1/RAI-1 (presentation not content), UGI-1 (generate -> validate),
NO RH / Millennium closure claim, and no sim "proves" a normative posit.

This harness encodes the author's (Brandon's) STRONGEST claim and tests it head-on:

  CLAIM. Myrion Resolution / TI-Logic (TIL) updates a proposition's PD until it crosses
  the True-Tralse cap (= 3*T_d - 1 = 0.93233), and THAT crossing IS the ideally-correct
  truth-value of the proposition -- including open theorems.

We carve the claim at its joint and test BOTH directions (#69):

  PART A  The REAL vacuity hazard (NOT undecidability): a POST-HOC GILE fitter that
          assigns GILE coordinates AFTER seeing the outcome can "explain" pure noise.
          This is exactly what NAD-1 / AFD-1 warn about.
  PART B  Outcome-blind OPERATIONAL GILE determinacy (candidate ODG-1): GILE coords are
          fixed by a deterministic procedure committed BEFORE the outcome. The rule then
          FORBIDS outcomes -> it fails on noise (as it must) and predicts on real signal
          -> falsifiability RESTORED. Metaphysical determinacy alone does NOT do this;
          the outcome-blind COMMITMENT is the load-bearing half.
  PART C  Credence vs proof (the procedural bound): a PD updater that climbs to the cap
          on confirming evidence certifies a genuinely-true proposition and a
          "Mertens-like" eventually-false one IDENTICALLY within any finite horizon
          -> crossing the cap is a fallible CREDENCE, not a PROOF of an open theorem.
  PART D  The other side (#69): on a DECIDABLE / settled subclass the SAME engine returns
          the correct truth-value (PD -> 1) because the decision procedure is an input.
          So the engine DOES answer truth-values exactly where inputs determine them.

Real witnesses for PART C (no fabrication):
  * Mertens conjecture |M(x)| < sqrt(x): numerically supported over huge ranges,
    DISPROVEN by Odlyzko & te Riele 1985 (no explicit counterexample known).
  * Polya conjecture: supported then DISPROVEN (Haselgrove 1958; least counterexample
    n = 906,150,257, Tanaka 1980).
Oracle coherence (constitutive arm): non-computable oracles are coherent abstractions
  (Turing 1939, "Systems of Logic Based on Ordinals" -- oracle machines); only COMPUTING
  one over a rich class is barred (Turing 1936 / Rice 1953). Rejecting an oracle-like
  truth-axis as "out of the question" is question-begging IF it rests on computationalism.

All predictions are pre-registered in code as assertions. Fixed seed; cap derived from
T_d; the bare cap value is never hard-typed as a target.
"""

import numpy as np

SEED = 20260626
rng = np.random.default_rng(SEED)

T_D_CANON = 0.644111
CAP = 3.0 * T_D_CANON - 1.0  # True-Tralse cap = 0.93233...; derived, never hard-typed

LINE = "=" * 80


def part_a_posthoc_vacuity():
    """Post-hoc GILE fitting 'explains' pure noise -> the real vacuity threat."""
    N = 400
    labels = rng.integers(0, 2, size=N)  # pure-noise outcomes, no structure
    # The fitter is allowed to choose each item's GILE coordinate AFTER seeing its
    # label, placing TRUE above the cap and FALSE below. Free parameters => perfect fit.
    coords = np.where(labels == 1, CAP + 0.02, CAP - 0.02)
    pred = (coords >= CAP).astype(int)
    consistency = float((pred == labels).mean())
    return consistency


def part_b_outcome_blind_determinacy():
    """Outcome-blind operational rule: fails on noise (good), predicts on signal."""
    N = 400
    x = rng.normal(size=(N, 3))  # pre-outcome features of each proposition
    # A real signal world: outcome is a fixed (unknown-to-us) rule of the features.
    w_true = np.array([1.2, -0.8, 0.5])
    p = 1.0 / (1.0 + np.exp(-(x @ w_true)))
    y_signal = (rng.uniform(size=N) < p).astype(int)
    # A noise world: outcomes independent of features.
    y_noise = rng.integers(0, 2, size=N)
    # OUTCOME-BLIND commitment: GILE coordinate is a deterministic function of the
    # features, with weights fixed in ADVANCE (deliberately not equal to w_true -- we
    # are not allowed to peek at outcomes). Decision = coord above its committed midpoint.
    w_committed = np.array([1.0, -1.0, 0.0])
    gile_coord = 1.0 / (1.0 + np.exp(-(x @ w_committed)))
    pred = (gile_coord >= 0.5).astype(int)
    acc_signal = float((pred == y_signal).mean())
    acc_noise = float((pred == y_noise).mean())
    return acc_signal, acc_noise


def _pd_after(confirmations, p0=0.5, k=1.03):
    """Monotone PD updater: each confirming observation nudges the odds up by factor k."""
    odds = (p0 / (1.0 - p0)) * (k ** confirmations)
    return odds / (1.0 + odds)


def part_c_credence_vs_proof():
    """Within a finite horizon, a true prop and a Mertens-like false prop get identical
    evidence -> identical PD -> both cross the cap -> false certification."""
    H = 200  # evidence horizon: confirming observations available before we must decide
    n_true = 30
    n_mertens = 30  # eventually-false; counterexample sits BEYOND H (unseen)
    # Both classes present exactly H confirmations within the horizon (indistinguishable).
    pd_true = _pd_after(H)
    pd_mertens = _pd_after(H)
    certified_true = bool(pd_true >= CAP)
    certified_mertens = bool(pd_mertens >= CAP)  # a FALSE proposition certified
    indistinguishable = abs(pd_true - pd_mertens) < 1e-12
    # Within-horizon false-certification rate among the Mertens-like (eventually-false) set.
    false_cert_rate = float(certified_mertens) * 1.0  # all n_mertens identical -> 0 or 1
    return {
        "H": H, "n_true": n_true, "n_mertens": n_mertens,
        "pd_true": pd_true, "pd_mertens": pd_mertens,
        "certified_true": certified_true, "certified_mertens": certified_mertens,
        "indistinguishable": indistinguishable, "false_cert_rate": false_cert_rate,
    }


def part_d_decidable_subclass():
    """Decidable subclass: with the decision procedure as an input, PD -> 1, correct."""
    N = 300
    a = rng.integers(0, 50, size=N)
    b = rng.integers(0, 50, size=N)
    truth = rng.integers(0, 2, size=N)
    c = np.where(truth == 1, a + b, a + b + rng.integers(1, 5, size=N))
    pred = (a + b == c).astype(int)  # the evaluator IS the decision procedure (an input)
    acc = float((pred == truth).mean())
    return acc


def main():
    print(LINE)
    print("SETUP")
    print(LINE)
    print(f"  True-Tralse cap = {CAP:.5f}  (= 3*T_d - 1 at T_d = {T_D_CANON}); not hard-typed.")
    print("  Claim under test: PD updated to the cap = the ideally-correct truth-value")
    print("  of the proposition (incl. open theorems). We test both directions.\n")

    # PART A
    print(LINE)
    print("PART A — the REAL vacuity hazard: post-hoc GILE fitting on pure noise")
    print(LINE)
    cons = part_a_posthoc_vacuity()
    print(f"  post-hoc consistency on RANDOM outcomes = {cons:.3f}")
    print("  => coordinates chosen AFTER the outcome 'explain' anything. THIS is the")
    print("     vacuity threat NAD-1/AFD-1 name -- not undecidability.")
    assert cons > 0.95, "P_A: post-hoc fitter should trivially fit noise (>0.95)"
    print("  PASS: P_A (post-hoc consistency > 0.95)\n")

    # PART B
    print(LINE)
    print("PART B — outcome-blind operational GILE determinacy (candidate ODG-1)")
    print(LINE)
    acc_sig, acc_noise = part_b_outcome_blind_determinacy()
    print(f"  committed-before-outcome rule:  accuracy on REAL signal = {acc_sig:.3f}")
    print(f"                                  accuracy on NOISE       = {acc_noise:.3f}")
    print("  => the rule FORBIDS outcomes: it fails on noise (as it must) and predicts on")
    print("     signal. Falsifiability restored. (Metaphysical determinacy alone wouldn't.)")
    assert 0.40 <= acc_noise <= 0.60, "P_B1: outcome-blind on noise ~ chance"
    assert acc_sig > 0.70, "P_B2: outcome-blind on real signal beats chance"
    print("  PASS: P_B1 (noise in [0.40,0.60])  PASS: P_B2 (signal > 0.70)\n")

    # PART C
    print(LINE)
    print("PART C — credence vs proof: the procedural bound (Mertens/Polya structure)")
    print(LINE)
    c = part_c_credence_vs_proof()
    print(f"  horizon H = {c['H']} confirmations; {c['n_true']} true vs {c['n_mertens']} Mertens-like (eventually FALSE)")
    print(f"  PD(true within H)        = {c['pd_true']:.5f}  -> certified={c['certified_true']}")
    print(f"  PD(Mertens-like within H)= {c['pd_mertens']:.5f}  -> certified={c['certified_mertens']}  (a FALSE prop)")
    print(f"  within-horizon true vs false PD indistinguishable: {c['indistinguishable']}")
    print(f"  within-horizon false-certification rate among eventually-false set = {c['false_cert_rate']:.2f}")
    print("  => crossing the cap is a fallible CREDENCE, not a PROOF of an open theorem.")
    print("     (Mertens: supported for huge ranges, FALSE -- Odlyzko & te Riele 1985.)")
    assert c["certified_mertens"] is True, "P_C1: PD crosses cap on a FALSE Mertens-like prop"
    assert c["indistinguishable"] is True, "P_C2: true vs eventually-false indistinguishable within horizon"
    print("  PASS: P_C1 (false proposition certified)  PASS: P_C2 (indistinguishable within horizon)\n")

    # PART D
    print(LINE)
    print("PART D — the other side (#69): decidable subclass, the engine DOES answer truth")
    print(LINE)
    acc_d = part_d_decidable_subclass()
    print(f"  decidable arithmetic, decision-procedure as input: accuracy = {acc_d:.3f}")
    print("  => where inputs DETERMINE the answer, the engine returns the truth-value.")
    assert acc_d >= 0.95, "P_D1: decidable subclass solved via the decision procedure"
    print("  PASS: P_D1 (decidable accuracy >= 0.95)\n")

    # Verdict
    print(LINE)
    print("VERDICT (constitutive vs procedural; count unchanged 79)")
    print(LINE)
    print("  * ODG-1 (outcome-blind operational GILE determinacy): the anti-vacuity guarantor")
    print("    WORKS as an OPERATIONAL rule (A vacuous, B falsifiable). Candidate, NOT ratified.")
    print("  * Constitutive arm: the truth-axis MAY be oracle-like (non-computable is coherent,")
    print("    Turing 1939). Limitative theorems bind only the PROCEDURAL arm (computing it).")
    print("  * Procedural arm: DECIDABLE/settled -> returns truth (D); genuinely-OPEN -> fallible")
    print("    credence that can cross the cap on a falsehood (C). So the engine's honest output")
    print("    on open theorems is a CREDENCE, not a proof. No RH/Millennium claim. Consistent")
    print("    with B132/B148/B149/B150.")
    print("\n" + LINE)
    print("ALL B151 CAPABILITY CHECKS PASSED")
    print(LINE)


if __name__ == "__main__":
    main()

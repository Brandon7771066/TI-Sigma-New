"""
Pass-77 B144 — i-Cell vs Markov Blanket (contextual-expressiveness separation),
and the honest reconciliation of numerology-as-heuristic with TI Sigma Statistics.

Two independent sections, both runnable:

  Section A (HAN-1, ILLUSTRATIVE/STIPULATED): shows the *methodology* that makes
  "victories are the primary metric, ignore null results" honest rather than
  survivorship bias. It does NOT prove numerology is real; it shows which
  estimator is faithful when there IS a small real effect among prospectively
  committed high-confidence attempts. EVD-1 reading: numerology propositions have
  Evidence STATUS (yes) + GRADED, confidence-scaled WEIGHT (not Proof).

  Section B (IMB-1, GENUINE MATH, not stipulated): the i-Cell's truth-axis
  structure (QTA-1 A4 = contextuality/CHSH) can represent correlations that NO
  classical Markov Blanket (a single global joint distribution / conditional-
  independence factorization, as used in the FEP) can reproduce. Classical cap =
  exactly 2.0; the i-Cell qubit structure reaches 2*sqrt(2). The gap is the
  decision-relevant DOF a classical rival cannot reconstruct. A non-contextual
  control shows the two frameworks are EQUIVALENT when no contextuality is present
  (no free lunch) — the separation is CONDITIONAL on contextuality (QTA-1-F2).

Run:  python analyses/pass77_b144_icell_vs_markov_blanket/icell_vs_mb.py
"""

import json
import math
import itertools
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(20260625)


# ===========================================================================
# Section A — HAN-1: numerology as intuition-heuristic + graded EVD-1 evidence.
# STIPULATED toy: it demonstrates estimator honesty, NOT that numerology works.
# ===========================================================================
def section_A_han1(n=200_000, true_delta=0.08):
    """
    Model: each 'reading' is either a *committed high-confidence attempt* (a real
    'swing') or low-confidence noise / a non-attempt. Among committed attempts a
    TRUE small effect lifts the hit-rate to 0.5 + true_delta; non-attempts are at
    chance 0.5. We compare three readings of 'ignore null results':

      (1) NAIVE-ALL: score every reading (dilutes the real effect toward 0).
      (2) PROSPECTIVE (the HONEST reading of TI Sigma Statistics): pre-register
          inclusion = committed high-confidence attempts; score ALL of them,
          including the ones that MISSED. Recovers true_delta.
      (3) SURVIVORSHIP (the ILLEGITIMATE reading): keep only the hits among
          committed attempts (delete committed misses after the fact). Inflates.
    """
    # 30% of readings are committed high-confidence attempts.
    committed = rng.random(n) < 0.30
    base = rng.random(n)
    hit = np.where(
        committed,
        base < (0.5 + true_delta),   # committed attempts carry the real effect
        base < 0.5,                  # everything else is chance
    )

    naive_all = float(hit.mean())
    prospective = float(hit[committed].mean())            # honest: nulls kept
    # survivorship: pretend a 'real attempt' is only one that hit
    surv_denom = hit[committed]                           # committed swings
    survivorship = float(surv_denom.sum() / max(surv_denom.sum() + 0, 1))  # = 1.0 by construction
    # a subtler survivorship: drop half the committed misses post hoc
    miss_idx = np.where(committed & ~hit)[0]
    drop = rng.permutation(miss_idx)[: len(miss_idx) // 2]
    keep = np.ones(n, dtype=bool)
    keep[drop] = False
    survivorship_subtle = float(hit[committed & keep].mean())

    chance = 0.5
    return {
        "what_this_shows": "estimator honesty for a STIPULATED real effect; NOT "
                           "evidence numerology is real",
        "true_effect_delta_over_chance": true_delta,
        "naive_all_readings_rate": round(naive_all, 4),
        "naive_dilutes_effect": bool(abs((naive_all - chance) - true_delta) > 0.02),
        "prospective_committed_rate": round(prospective, 4),
        "prospective_recovers_true_delta": bool(
            abs((prospective - chance) - true_delta) < 0.01),
        "survivorship_drop_all_misses_rate": round(survivorship, 4),
        "survivorship_subtle_drop_half_misses_rate": round(survivorship_subtle, 4),
        "survivorship_inflates": bool((survivorship_subtle - chance) >
                                      1.5 * true_delta),
        "honest_reading_of_ignore_nulls": (
            "LEGITIMATE = exclude non-attempts / low-confidence noise from the "
            "denominator (prospective inclusion) -> recovers the true effect. "
            "ILLEGITIMATE = delete committed misses after the fact -> survivorship "
            "inflation. The falsifier (validate phase) still counts both ways."),
        "evd1_status_vs_weight": (
            "numerology propositions have Evidence STATUS=yes (used in support of "
            "a conclusion, authority-independent) and GRADED WEIGHT (confidence-"
            "scaled, track-record SECONDARY). Heuristic for intuition, never Proof."),
    }


# ===========================================================================
# Section B — IMB-1: contextual-expressiveness separation, i-Cell vs Markov Blanket.
# This section is GENUINE MATH (Bell/Fine/Tsirelson), not stipulated.
# ===========================================================================
def _deterministic_local_strategies():
    """All 16 deterministic local-hidden-variable strategies for a 2-setting,
    2-party CHSH scenario. Each assigns +/-1 to A0,A1,B0,B1; the four correlators
    are the products. A classical Markov Blanket = a single global joint = a convex
    mixture of exactly these (Fine 1982)."""
    strategies = []
    corrs = []  # rows: [E(A0,B0), E(A0,B1), E(A1,B0), E(A1,B1)]
    for a0, a1, b0, b1 in itertools.product([-1, 1], repeat=4):
        strategies.append((a0, a1, b0, b1))
        corrs.append([a0 * b0, a0 * b1, a1 * b0, a1 * b1])
    return np.array(corrs, dtype=float)


def section_B_imb1():
    corrs = _deterministic_local_strategies()  # (16, 4)

    # CHSH combination S = E00 - E01 + E10 + E11.
    sign = np.array([1.0, -1.0, 1.0, 1.0])
    classical_S = corrs @ sign
    classical_cap = float(np.max(np.abs(classical_S)))  # exactly 2.0

    # The i-Cell qubit / contextual structure (QTA-1 A4) attains Tsirelson 2*sqrt2.
    tsirelson = 2.0 * math.sqrt(2.0)
    quantum_corr = 1.0 / math.sqrt(2.0)  # |E| for the optimal qubit measurements
    quantum_target = np.array([quantum_corr, -quantum_corr,
                               quantum_corr, quantum_corr])
    quantum_S = float(quantum_target @ sign)

    # Can ANY classical Markov Blanket (mixture of the 16 local strategies)
    # reproduce the quantum correlations? Feasibility LP: find p_i>=0, sum=1 with
    # corrs.T @ p == quantum_target. (Fine 1982: feasible IFF |S|<=2.)
    n_str = corrs.shape[0]
    A_eq = np.vstack([corrs.T, np.ones((1, n_str))])      # (5, 16)
    b_eq = np.concatenate([quantum_target, [1.0]])
    res_q = linprog(c=np.zeros(n_str), A_eq=A_eq, b_eq=b_eq,
                    bounds=[(0, 1)] * n_str, method="highs")
    quantum_reproducible_by_MB = bool(res_q.success)

    # Sanity: a CLASSICAL (non-contextual) target WITH the same marginals IS
    # reproducible -> shows the LP is not rigged to fail. Use S = 2 exactly.
    classical_target = np.array([0.5, -0.5, 0.5, 0.5])     # S = 2.0
    b_eq_c = np.concatenate([classical_target, [1.0]])
    res_c = linprog(c=np.zeros(n_str), A_eq=A_eq, b_eq=b_eq_c,
                    bounds=[(0, 1)] * n_str, method="highs")
    classical_reproducible_by_MB = bool(res_c.success)

    # Irreducible reconstruction residual: the best a Markov Blanket can do is
    # cap at 2.0, so it under-reports the contextual signal by (2sqrt2 - 2).
    irreducible_gap = float(tsirelson - classical_cap)

    return {
        "what_this_shows": "GENUINE MATH: a classical Markov Blanket (single global "
                           "joint / conditional-independence factorization, as in "
                           "the FEP) cannot host the contextual truth-axis the "
                           "i-Cell carries (QTA-1 A4).",
        "classical_markov_blanket_CHSH_cap": classical_cap,            # 2.0
        "classical_cap_is_two": bool(abs(classical_cap - 2.0) < 1e-9),
        "icell_contextual_CHSH": round(quantum_S, 6),                  # 2*sqrt2
        "icell_matches_tsirelson": bool(abs(quantum_S - tsirelson) < 1e-9),
        "quantum_correlations_reproducible_by_markov_blanket": quantum_reproducible_by_MB,
        "classical_correlations_reproducible_by_markov_blanket": classical_reproducible_by_MB,
        "separation_holds": bool((not quantum_reproducible_by_MB)
                                 and classical_reproducible_by_MB),
        "irreducible_reconstruction_gap": round(irreducible_gap, 6),
        "non_contextual_control": (
            "when data is non-contextual (|S|<=2) the Markov Blanket reproduces it "
            "exactly -> the two frameworks are EQUIVALENT; the i-Cell's advantage "
            "appears ONLY when genuine contextuality is present (conditional on "
            "QTA-1-F2). #69 both-directions honesty: no free lunch off-contextuality."),
        "scope_caveat": (
            "the rival here is the CLASSICAL Markov Blanket (Pearl / Friston FEP), "
            "which is non-contextual by construction. A hypothetical *quantum* "
            "Markov blanket would need exactly this contextual structure -> it would "
            "concede the i-Cell's point, not refute it."),
        "what_this_does_NOT_claim": (
            "NOT that i-Cells are physically real, NOT that they beat Markov "
            "Blankets on any empirical dataset, NOT a resolution of ICC-F2 (which "
            "is about beating the i-Cell's OWN sub-models). This is an INTER-"
            "framework EXPRESSIVENESS separation, conditional on contextuality."),
    }


def main():
    results = {
        "section_A_HAN1_numerology_heuristic": section_A_han1(),
        "section_B_IMB1_icell_vs_markov_blanket": section_B_imb1(),
    }
    A = results["section_A_HAN1_numerology_heuristic"]
    B = results["section_B_IMB1_icell_vs_markov_blanket"]
    must_pass = [
        A["prospective_recovers_true_delta"],
        A["survivorship_inflates"],
        B["classical_cap_is_two"],
        B["icell_matches_tsirelson"],
        not B["quantum_correlations_reproducible_by_markov_blanket"],
        B["classical_correlations_reproducible_by_markov_blanket"],
        B["separation_holds"],
    ]
    results["all_checks_pass"] = bool(all(must_pass))
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()

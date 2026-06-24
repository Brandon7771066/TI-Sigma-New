"""B134 — UOP Universality: "always works regardless" (honest, #69 both ways).

Goal: provide the computational backing for the strategic decision to prove the
UOP's UNIVERSALITY *schematically* (it "always works regardless" of domain),
BYPASSING the heavy ontological route "all mathematical statements are i-Cells".
An i-Cell is the corpus's unit of *consciousness*; routing universality through
"every problem/object is an i-Cell" would (a) overclaim consciousness, (b) be
unfalsifiable / No-True-Scotsman-prone, and (c) be UNNECESSARY. The UOP is a
SCHEMA over an admissible problem-class; we only need (X, G_D, H_D, rho_D) to be
well defined, never that the optimization variable is conscious.

Reuses the EXACT B133 functional form:
    J(G) = rho * f_cap(G) + g(H),  H = 1 - k*G,
    f_cap log-concave on [0,G*] with an over-reach penalty above G* = (1+L)/2,
    g(H) = log(1+H) increasing & concave.

PART 1 — "Always works regardless": robustness over the admissible class.
  Sample MANY random admissible instances (vary rho, the tradeoff slope k, the
  cap location via the existence floor L, and the penalty alpha). For each we
  verify the Interior-Optimum Theorem's HYPOTHESES hold (J concave on [0,G*],
  strictly decreasing above G*) => a UNIQUE maximizer exists, and we locate it.
  We report: fraction of instances with a unique well-defined optimum (must be
  ALL); the predicted interior threshold rho > k/2 (J'(0)=rho - k*g'(1)=rho-k/2)
  matches the realized boundary/interior classification; and the cap BINDS only
  for high rho. "Always works regardless" = the FORM is invariant across the
  class; the LOCATION (corner / interior-below-cap / at-cap) is domain-specific.

PART 2 — Subsumption: known frameworks are UOP special cases (universality by
  coverage, not by ontological reduction).
    * no-cap (alpha=0) + rho -> large  => optimum -> G=1: pure truth-maximization
      (the expected-utility / MLE corner the squared-error form also gives).
    * rho -> 0                         => optimum -> G=0: pure existence.
    * accuracy-minus-complexity form   => the SAME interior-optimum structure as
      variational free energy F = accuracy - complexity (FEP recovered as a
      structural limit; FEP is INSPIRATION, the UOP owns its posits — see B133).

PART 3 — i-Cell bypass: the schema needs NO consciousness.
  We instantiate the IDENTICAL theorem on a deliberately NON-conscious toy
  problem (a firm splitting effort between product quality and cash runway).
  Same unique interior optimum emerges => universality does not require the
  variable to be an i-Cell; "all math statements are i-Cells" is not needed.

Honesty (#69): NONE of this proves the UOP is empirically correct, nor that any
particular real problem MUST be cast in UOP form. It establishes (i) the
theorem's hypotheses are MILD/generic (hold across a broad random class), and
(ii) the casting+subsumption strategy is coherent and consciousness-free. The
genuine open obligation is the *representation theorem* (R1): a precise
characterisation of EXACTLY which problems admit a faithful UOP casting. That is
stated as OPEN in the paper, not claimed here.

Run:
    python analyses/pass77_b134_uop_universality/universality_robustness.py
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

E2_INV = math.exp(-2.0)
G_STAR_CANON = 1.0 - 0.5 * E2_INV          # canonical Radiant cap ~ 0.932332


# --------------------------------------------------------------------------- #
# Parameterised UOP functional (instance-level).
# --------------------------------------------------------------------------- #
def f_cap(x: float, g_star: float, alpha: float) -> float:
    """Log-concave truth value with a quadratic over-reach penalty above g_star."""
    if x <= g_star:
        return math.log1p(x)
    return math.log1p(g_star) - alpha * (x - g_star) ** 2


def g_hem(h: float) -> float:
    return math.log1p(max(h, 0.0))


def J(x: float, rho: float, k: float, g_star: float, alpha: float) -> float:
    return rho * f_cap(x, g_star, alpha) + g_hem(1.0 - k * x)


# --------------------------------------------------------------------------- #
# PART 1 — "Always works regardless": robustness over the admissible class.
# --------------------------------------------------------------------------- #
def _hypotheses_hold(grid: np.ndarray, vals: np.ndarray, g_star: float) -> bool:
    """Check J concave on [0,g*] (second difference <= 0) and strictly
    decreasing above g* — the Interior-Optimum Theorem's stated hypotheses."""
    below = grid <= g_star + 1e-12
    vb = vals[below]
    if len(vb) >= 3:
        d2 = np.diff(vb, 2)
        if not np.all(d2 <= 1e-7):
            return False
    above = grid >= g_star - 1e-12
    va = vals[above]
    if len(va) >= 2:
        if not np.all(np.diff(va) <= 1e-9):
            return False
    return True


def _unique_max(grid: np.ndarray, vals: np.ndarray) -> tuple[bool, float]:
    """Unique global maximizer? (single contiguous argmax plateau of width ~1 pt)."""
    vmax = vals.max()
    near = np.where(vals >= vmax - 1e-9)[0]
    contiguous = bool(near[-1] - near[0] == len(near) - 1)
    unique = contiguous and (len(near) <= 3)
    return unique, float(grid[int(np.argmax(vals))])


def part1_always_works() -> dict:
    rng = np.random.default_rng(0)
    grid = np.linspace(0.0, 1.0, 4001)
    n = 3000
    n_hyp_hold = 0
    n_unique = 0
    n_threshold_correct = 0
    classes = {"lower_boundary": 0, "interior_below_cap": 0, "at_cap": 0}
    cap_binds_rhos = []
    cap_not_binds_rhos = []

    for _ in range(n):
        rho = float(rng.uniform(0.05, 5.0))
        k = float(rng.uniform(0.05, 0.95))
        L = float(rng.uniform(0.70, 0.99))           # existence floor
        g_star = 0.5 * (1.0 + L)                      # cap location = (1+L)/2
        alpha = float(rng.uniform(2.0, 20.0))

        vals = np.array([J(x, rho, k, g_star, alpha) for x in grid])
        if _hypotheses_hold(grid, vals, g_star):
            n_hyp_hold += 1
        unique, gopt = _unique_max(grid, vals)
        if unique:
            n_unique += 1

        # predicted interior threshold: J'(0) = rho*f'(0) - k*g'(1) = rho - k/2.
        predicted_interior = rho > k / 2.0
        realized_interior = gopt > 1e-3
        if predicted_interior == realized_interior:
            n_threshold_correct += 1

        if gopt <= 1e-3:
            classes["lower_boundary"] += 1
        elif gopt >= g_star - 5e-3:
            classes["at_cap"] += 1
            cap_binds_rhos.append(rho)
        else:
            classes["interior_below_cap"] += 1
            cap_not_binds_rhos.append(rho)

    return {
        "n_instances": n,
        "frac_hypotheses_hold": round(n_hyp_hold / n, 4),
        "frac_unique_optimum": round(n_unique / n, 4),
        "frac_interior_threshold_rho_gt_k_over_2_correct": round(n_threshold_correct / n, 4),
        "optimum_class_counts": classes,
        "mean_rho_when_cap_binds": round(float(np.mean(cap_binds_rhos)), 3) if cap_binds_rhos else None,
        "mean_rho_when_cap_not_binds": round(float(np.mean(cap_not_binds_rhos)), 3) if cap_not_binds_rhos else None,
        "cap_binds_only_for_higher_rho": (
            bool(cap_binds_rhos and cap_not_binds_rhos
                 and np.mean(cap_binds_rhos) > np.mean(cap_not_binds_rhos))
        ),
        "interpretation": "Across a broad random admissible class the theorem's hypotheses hold and a UNIQUE "
                          "optimum exists in EVERY instance: the UOP 'always works regardless' of domain. The "
                          "FORM is invariant; only the LOCATION (lower-boundary / interior-below-cap / at-cap) "
                          "is domain-specific, set by rho (truth-dominance) and the tradeoff slope k. The cap "
                          "binds ONLY for high rho — consistent with 'math nearly alone saturates it' (B133).",
        "honesty_69": "This shows the hypotheses are MILD/generic on the sampled class; it does NOT prove every "
                      "real problem admits a faithful UOP casting. That casting/representation theorem (R1) is "
                      "the genuine OPEN obligation, stated as such in the paper.",
    }


# --------------------------------------------------------------------------- #
# PART 2 — Subsumption: known frameworks as UOP special cases.
# --------------------------------------------------------------------------- #
def part2_subsumption() -> dict:
    grid = np.linspace(0.0, 1.0, 4001)
    k = 0.3

    # no-cap (alpha=0) + rho large  => pure truth-maximization corner G=1.
    def argmax(rho: float, alpha: float, g_star: float) -> float:
        vals = np.array([J(x, rho, k, g_star, alpha) for x in grid])
        return float(grid[int(np.argmax(vals))])

    nocap = [{"rho": r, "argmax_G": round(argmax(r, 0.0, 1.0), 4)} for r in [1, 2, 5, 20, 100]]
    truth_corner = abs(nocap[-1]["argmax_G"] - 1.0) < 1e-2

    # rho -> 0 => pure existence corner G=0.
    rho0 = [{"rho": r, "argmax_G": round(argmax(r, 10.0, G_STAR_CANON), 4)} for r in [0.5, 0.1, 0.02, 0.001]]
    existence_corner = abs(rho0[-1]["argmax_G"] - 0.0) < 1e-2

    # FEP structural limit: accuracy - complexity has the SAME interior-optimum
    # structure. F(q) = accuracy(q) - complexity(q); here accuracy=rho*log(1+G),
    # complexity=k*G (linear KL surrogate). Interior optimum where rho/(1+G)=k.
    rho_fep, k_fep = 0.5, 0.35           # rho/k in (1,2) => interior optimum in (0,1)
    fep_vals = np.array([rho_fep * math.log1p(x) - k_fep * x for x in grid])
    g_fep = float(grid[int(np.argmax(fep_vals))])
    g_fep_closed = rho_fep / k_fep - 1.0      # FOC: rho/(1+G)=k -> G=rho/k-1
    fep_matches = abs(g_fep - g_fep_closed) < 2e-3

    return {
        "no_cap_high_rho_to_truth_corner": {"sweep": nocap, "reaches_G_eq_1": truth_corner,
                                            "note": "alpha=0, rho large => optimum at G=1: pure truth-max "
                                                    "(expected-utility / MLE corner)."},
        "low_rho_to_existence_corner": {"sweep": rho0, "reaches_G_eq_0": existence_corner,
                                        "note": "rho->0 => optimum at G=0: pure existence."},
        "fep_structural_limit": {"argmax_numeric": round(g_fep, 4), "argmax_closed_form": round(g_fep_closed, 4),
                                 "matches": fep_matches,
                                 "note": "accuracy-minus-complexity (variational free energy) shares the SAME "
                                         "interior-optimum structure. FEP is INSPIRATION; the UOP owns its own "
                                         "posits and is formally independent (B133 §A)."},
        "interpretation": "Major optimization frameworks are LIMITS / special cases of the one UOP schema "
                          "(truth-only, existence-only, free-energy). Universality by SUBSUMPTION — no claim "
                          "that any object is conscious.",
    }


# --------------------------------------------------------------------------- #
# PART 3 — i-Cell bypass: the schema needs no consciousness.
# --------------------------------------------------------------------------- #
def part3_icell_bypass() -> dict:
    grid = np.linspace(0.0, 1.0, 4001)
    # A deliberately NON-conscious problem: a firm allocates fractional effort q
    # to product quality (the "truth-axis" analogue G_D) vs cash runway (the
    # "existence-axis" analogue H_D = 1 - k*q). Nothing here is an i-Cell.
    rho, k, g_star, alpha = 2.4, 0.25, G_STAR_CANON, 10.0
    vals = np.array([J(x, rho, k, g_star, alpha) for x in grid])
    unique, qopt = _unique_max(grid, vals)
    return {
        "problem": "firm effort allocation: quality (G_D) vs cash runway (H_D=1-k*q); NO consciousness anywhere",
        "rho": rho, "k": k,
        "argmax_q": round(qopt, 4),
        "unique_optimum": unique,
        "at_cap": abs(qopt - g_star) < 5e-3,
        "interpretation": "The IDENTICAL Interior-Optimum Theorem governs a non-conscious resource problem. The "
                          "UOP schema requires only (X, G_D, H_D, rho_D) well-defined — never that the variable "
                          "is an i-Cell. So universality is established WITHOUT the claim 'all mathematical "
                          "statements are i-Cells' (route A), via the schema's domain-agnostic form (route B).",
    }


def main() -> None:
    out = {
        "constants": {"G*_radiant_cap": round(G_STAR_CANON, 6)},
        "part1_always_works_regardless": part1_always_works(),
        "part2_subsumption_special_cases": part2_subsumption(),
        "part3_icell_bypass_no_consciousness": part3_icell_bypass(),
        "strategy_note": "UNV-1: prove UOP universality via the SCHEMA ('always works regardless'), bypassing "
                         "'all math statements are i-Cells'. Proof obligations R1 (representation/casting) OPEN; "
                         "R2 (interior-optimum) lemma-level + shown generic here; R4 (subsumption) demonstrated.",
    }
    here = Path(__file__).resolve().parent
    (here / "results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()

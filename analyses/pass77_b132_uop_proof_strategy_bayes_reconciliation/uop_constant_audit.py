"""B132 — UOP proof-strategy audit (honest, #69 both ways).

Two computational checks behind the B132 paper:

PART 1 — Circularity of the Pass-68 "phase-transition test".
  The Pass-68 model (analyses/uop_phase_transition_v1/model.py) hard-codes the
  kink of f(G) at THRESHOLD = 0.93, then "confirms" that argmax G saturates at
  0.93. We re-run the IDENTICAL optimizer with the breakpoint placed at several
  other thetas. If argmax saturates at whatever theta you insert, the test cannot
  be evidence FOR 0.93 specifically -- it is breakpoint-agnostic, i.e. circular.

PART 2 — Where does 1 - 1/(2e^2) actually come from?
  Canonical constants (URB #523 / #521):
      existence floor  L  = 1 - e^{-2}        ~ 0.8647   (LCC)
      truth floor      G* = 1 - (1/2) e^{-2}  ~ 0.9323   (GILE Radiant)
      P(Great)            = (1/2) e^{-2}      ~ 0.0677
  We show the exact algebraic decomposition G* = (1 + L)/2 (midpoint of the
  existence floor and perfect truth), so the WHOLE e-content reduces to the
  single constant L = 1 - e^{-2}. We then read L as a Poisson survival
  probability P(N >= 1 | lambda) = 1 - e^{-lambda} and sweep lambda to show the
  floors move with it: lambda = 2 ("minimal double corroboration") is a POSITED
  modeling choice, not a forced/derived theorem.

No empirical claims. Pure model-level arithmetic. Run:
    python analyses/pass77_b132_uop_proof_strategy_bayes_reconciliation/uop_constant_audit.py
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

# --------------------------------------------------------------------------- #
# PART 1 — breakpoint-agnostic optimizer (faithful copy of the Pass-68 form).
# --------------------------------------------------------------------------- #
ALPHA_DEFAULT = 10.0


def f_gile(G: float, theta: float, alpha: float = ALPHA_DEFAULT) -> float:
    """Pass-68 functional form, but with the breakpoint theta as a FREE
    parameter instead of the hard-coded 0.93."""
    if G <= theta:
        return float(np.log(1.0 + G))
    return float(np.log(1.0 + theta) - alpha * (G - theta) ** 2)


def g_hem(H: float) -> float:
    return float(np.log(1.0 + H))


def J(G: float, H: float, theta: float, alpha: float = ALPHA_DEFAULT) -> float:
    return f_gile(G, theta, alpha) + g_hem(H)


def argmax_G(B: float, theta: float, grid: int = 4001, alpha: float = ALPHA_DEFAULT) -> float:
    """Grid argmax of G under budget G + H <= B (g_hem increasing => H = H_max)."""
    G_grid = np.linspace(0.0, min(1.0, B), grid)
    best_J, best_G = -np.inf, 0.0
    for G in G_grid:
        H_max = min(1.0, B - G)
        if H_max < 0:
            continue
        val = J(G, H_max, theta, alpha)
        if val > best_J:
            best_J, best_G = val, float(G)
    return best_G


def part1_circularity() -> dict:
    thetas = [0.80, 0.85, 0.90, 0.93, 0.95]

    # Finding A: HEM-saturated regime (B = 2.0). H is pinned at its cap (1.0)
    # for every feasible G, so g(H) is constant and J is maximized by f(G)
    # alone -> argmax sits exactly at the inserted kink theta, for ALL theta.
    rows_A = []
    for th in thetas:
        gstar = argmax_G(2.0, th)
        rows_A.append(
            {
                "breakpoint_theta": th,
                "argmax_G": round(gstar, 4),
                "tracks_theta": abs(gstar - th) < 2.5e-3,
            }
        )
    finding_A = all(r["tracks_theta"] for r in rows_A)

    # Finding B: the canonical Pass-68 budget B = 1.86 = 2 * 0.93. In the
    # trade-off regime the symmetric interior optimum is B/2, so argmax lands
    # on 0.93 whenever the kink sits ABOVE it (theta >= 0.93) -- 0.93 falls out
    # of the BUDGET, independent of the kink. We probe theta = 0.99 (kink well
    # above) at B = 1.86 and expect ~0.93 from B/2 alone.
    gstar_budget_route = argmax_G(1.86, 0.99)

    return {
        "finding_A_kink_circularity": {
            "budget": 2.0,
            "rows": rows_A,
            "all_track_theta": finding_A,
        },
        "finding_B_budget_overdetermination": {
            "budget": 1.86,
            "note": "1.86 = 2 * 0.93; symmetric interior optimum is B/2",
            "theta_probe": 0.99,
            "argmax_G": round(gstar_budget_route, 4),
            "lands_on_0p93_from_budget": abs(gstar_budget_route - 0.93) < 5e-3,
        },
        "verdict": (
            "CIRCULAR (two ways): (A) with H saturated, argmax tracks WHATEVER "
            "kink theta is inserted -> the test confirms the chosen constant, not "
            "0.93 specifically; (B) the canonical budget 1.86 = 2*0.93 makes the "
            "symmetric interior optimum B/2 = 0.93 regardless of the kink. Either "
            "route yields 0.93 by construction; neither DERIVES it."
        ),
    }


# --------------------------------------------------------------------------- #
# PART 2 — decomposition of 1 - 1/(2 e^2) and the posited lambda.
# --------------------------------------------------------------------------- #
def part2_constant_decomposition() -> dict:
    e2_inv = math.exp(-2.0)
    L = 1.0 - e2_inv                       # existence floor (LCC)
    g_star = 1.0 - 0.5 * e2_inv            # truth floor (GILE Radiant)
    p_great = 0.5 * e2_inv
    midpoint = (1.0 + L) / 2.0             # claim: == g_star exactly

    # lambda-sweep: L(lambda) = 1 - e^{-lambda}; g*(lambda) = (1 + L)/2.
    sweep = []
    for lam in [1.0, 1.5, 2.0, 2.5, 3.0]:
        L_lam = 1.0 - math.exp(-lam)
        sweep.append(
            {
                "lambda": lam,
                "existence_floor": round(L_lam, 4),
                "truth_floor_midpoint": round((1.0 + L_lam) / 2.0, 4),
            }
        )

    return {
        "e_minus_2": round(e2_inv, 6),
        "existence_floor_L": round(L, 6),
        "truth_floor_Gstar": round(g_star, 6),
        "P_Great": round(p_great, 6),
        "midpoint_(1+L)/2": round(midpoint, 6),
        "Gstar_equals_midpoint": abs(midpoint - g_star) < 1e-12,
        "poisson_reading": "L = P(N>=1 | lambda=2) = 1 - e^{-2}  (>=1 corroborating link, mean rate 2)",
        "lambda_sweep": sweep,
        "verdict": (
            "G* = 1 - 1/(2e^2) is EXACTLY the midpoint of [L, 1] with L = 1 - e^{-2}; "
            "all e-content reduces to the single constant lambda = 2. That lambda is "
            "POSITED ('minimal double corroboration'), not forced -- the optimum is "
            "conditionally derived from an assumed Poisson/exponential law, mirroring "
            "the FEP grand-claim gap one level down."
        ),
    }


def main() -> None:
    out = {
        "part1_pass68_circularity": part1_circularity(),
        "part2_constant_decomposition": part2_constant_decomposition(),
    }
    here = Path(__file__).resolve().parent
    (here / "results.json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()

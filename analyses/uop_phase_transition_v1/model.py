"""UOP true-tralseness objective J(G, H) with above-threshold GILE penalty.

Mathematical formalization of the GTT-1 + UDT-1 + UHP-1 + TPI-1 stack for
empirical testing of Brandon's Pass-67 batch-7 + Pass-68 batch-1 predictions:

  (P1) Phase transition at G* = 0.93: argmax G saturates at 0.93 once
       resource budget is sufficient; pushing past 0.93 is structurally
       penalized (UDT-1(c) MR2 region operationalized as smooth penalty).

  (P2) Strategic G->H trade above threshold INCREASES J: an agent at
       (G > 0.93, H) can monotonically improve J by trading G down to
       0.93 and reallocating freed budget to H.

  (P3) Pure irrationality (random sub-optimal allocation that degrades
       BOTH G and H from the argmax) DECREASES J. Strategic error
       above-threshold is NOT permission for irrationality below
       threshold; the math distinguishes the two.

  (P4) Moot status of "above-threshold non-shifter" (Brandon's nuance):
       an agent at (G > 0.93, H) is suboptimal in J but still has
       higher G than an agent at (0.93, H + Delta). The "non-shifter"
       is NOT erring (G is strictly higher); they are merely
       suboptimal in the J = GILE-HEM true-tralseness sense.
       MT-B1 Moot status applies.

Functional choices:
  - f(G) = log(1 + G) for G in [0, 0.93]: concave-increasing,
           diminishing marginal returns sub-threshold (calibration
           cost rises with proximity to threshold).
  - f(G) = log(1.93) - ALPHA * (G - 0.93)^2 for G in (0.93, 1]:
           smooth quadratic penalty operationalizing UDT-1(c) MR2
           region. ALPHA = 10.0 default (sensitivity reported).
  - g(H) = log(1 + H) for H in [0, 1]: symmetric concave-increasing.
  - J(G, H) = f(G) + g(H): additive (no coupling assumed; coupling
           would only strengthen the phase transition).

Budget constraint: G + H <= B, G in [0,1], H in [0,1].
Costs assumed equal (c_G = c_H = 1) for clarity. Unequal costs
shift the threshold but preserve the phase-transition structure.
"""
from __future__ import annotations
import numpy as np
from dataclasses import dataclass

THRESHOLD = 0.93
ALPHA_DEFAULT = 10.0


def f_gile(G: float, alpha: float = ALPHA_DEFAULT) -> float:
    """GILE component. Concave-increasing sub-threshold; smooth
    quadratic penalty above threshold (UDT-1(c) MR2 operationalization).
    """
    if G <= THRESHOLD:
        return float(np.log(1.0 + G))
    return float(np.log(1.0 + THRESHOLD) - alpha * (G - THRESHOLD) ** 2)


def g_hem(H: float) -> float:
    """HEM component. Symmetric concave-increasing."""
    return float(np.log(1.0 + H))


def J(G: float, H: float, alpha: float = ALPHA_DEFAULT) -> float:
    """UOP true-tralseness objective."""
    return f_gile(G, alpha) + g_hem(H)


@dataclass
class OptResult:
    G_star: float
    H_star: float
    J_star: float
    budget: float
    binding_threshold: bool


def optimize_under_budget(B: float, grid: int = 4001, alpha: float = ALPHA_DEFAULT) -> OptResult:
    """Grid search over (G, H) with G + H <= B, G in [0, 1], H in [0, 1].
    Returns argmax (G, H) and J value. Fine grid (4001) gives ~2.5e-4
    resolution which is more than enough to detect the 0.93 threshold.
    """
    G_grid = np.linspace(0.0, min(1.0, B), grid)
    best_J = -np.inf
    best_G = 0.0
    best_H = 0.0
    for G in G_grid:
        H_max = min(1.0, B - G)
        if H_max < 0:
            continue
        # J is concave-increasing in H given fixed G and binding budget,
        # so optimal H is at H_max when budget binds (otherwise interior).
        # Since g_hem is strictly increasing, optimum is H = H_max.
        H = H_max
        val = J(G, H, alpha)
        if val > best_J:
            best_J = val
            best_G = float(G)
            best_H = float(H)
    return OptResult(
        G_star=best_G,
        H_star=best_H,
        J_star=float(best_J),
        budget=B,
        binding_threshold=(abs(best_G - THRESHOLD) < 1e-3),
    )


def strategic_trade_above_threshold(G_excess: float, H: float, alpha: float = ALPHA_DEFAULT) -> dict:
    """Test prediction P2: an agent at (G_excess > 0.93, H) trades G down to
    0.93 and reallocates freed budget (G_excess - 0.93) to H. Compute J before
    and after the trade, and the delta.
    """
    assert G_excess > THRESHOLD, "by construction this test is for above-threshold agents"
    J_before = J(G_excess, H, alpha)
    H_after = min(1.0, H + (G_excess - THRESHOLD))
    J_after = J(THRESHOLD, H_after, alpha)
    return {
        "G_before": G_excess,
        "H_before": H,
        "J_before": J_before,
        "G_after": THRESHOLD,
        "H_after": H_after,
        "J_after": J_after,
        "delta_J": J_after - J_before,
        "trade_improves_J": J_after > J_before,
    }


def irrational_perturbation(G_star: float, H_star: float, seed: int, alpha: float = ALPHA_DEFAULT, n: int = 1000) -> dict:
    """Test prediction P3: random perturbations from the optimum that
    degrade BOTH G and H. Compute fraction of perturbations that
    REDUCE J. UHP-1 prediction: ALL such perturbations should reduce J
    (pure irrationality is not permitted by UHP-1's logic).
    """
    rng = np.random.default_rng(seed)
    J_star = J(G_star, H_star, alpha)
    reduced = 0
    deltas = []
    for _ in range(n):
        # Random degradation: both components reduced by U[0, 0.2]
        dG = rng.uniform(0.0, 0.2)
        dH = rng.uniform(0.0, 0.2)
        G_new = max(0.0, G_star - dG)
        H_new = max(0.0, H_star - dH)
        J_new = J(G_new, H_new, alpha)
        if J_new < J_star:
            reduced += 1
        deltas.append(J_new - J_star)
    return {
        "n_perturbations": n,
        "fraction_reducing_J": reduced / n,
        "mean_delta_J": float(np.mean(deltas)),
        "all_irrationality_reduces_J": reduced == n,
    }


def moot_status_check(G_high: float, H_high: float, G_optimal: float, H_optimal: float, alpha: float = ALPHA_DEFAULT) -> dict:
    """Test prediction P4: Moot status of above-threshold non-shifter.
    Compare:
      - Agent A: (G_high > 0.93, H_high) -- above-threshold "non-shifter"
      - Agent B: (0.93, H_optimal)        -- TRUE-TRALSE-move optimum
    Both at same budget. Expected:
      J(B) > J(A)                          [B optimal in UOP sense]
      G_high > 0.93                        [A strictly higher in G sense]
      => A is NOT erring (G-superior), just SUBOPTIMAL in true-tralse sense.
      MT-B1 Moot per MR Truth Labels canonical.
    """
    J_A = J(G_high, H_high, alpha)
    J_B = J(G_optimal, H_optimal, alpha)
    return {
        "agent_A_above_threshold": {"G": G_high, "H": H_high, "J": J_A},
        "agent_B_threshold_shifter": {"G": G_optimal, "H": H_optimal, "J": J_B},
        "B_dominates_in_J": J_B > J_A,
        "A_strictly_higher_G": G_high > G_optimal,
        "moot_status_applies": (J_B > J_A) and (G_high > G_optimal),
        "interpretation": (
            "Agent A is suboptimal in J (UOP true-tralseness sense) "
            "but strictly higher in G alone -- A is NOT erring per "
            "Brandon's canonical nuance, just suboptimal in true-tralse "
            "sense. MT-B1 Moot applies."
        ),
    }

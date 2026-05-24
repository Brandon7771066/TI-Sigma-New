"""Pass-68 batch-1: empirical test of Brandon's 4 predictions on the
UOP true-tralseness objective J(G, H).
"""
from __future__ import annotations
import json
import numpy as np
from model import (
    THRESHOLD,
    ALPHA_DEFAULT,
    f_gile,
    g_hem,
    J,
    optimize_under_budget,
    strategic_trade_above_threshold,
    irrational_perturbation,
    moot_status_check,
)


def sweep_budgets(B_grid: np.ndarray, alpha: float = ALPHA_DEFAULT) -> list[dict]:
    """Sweep over resource budgets and record argmax (G, H) at each."""
    results = []
    for B in B_grid:
        res = optimize_under_budget(float(B), grid=4001, alpha=alpha)
        results.append(
            {
                "B": float(B),
                "G_star": res.G_star,
                "H_star": res.H_star,
                "J_star": res.J_star,
                "binding_threshold": res.binding_threshold,
            }
        )
    return results


def detect_phase_transition(sweep: list[dict]) -> dict:
    """Detect Brandon's predicted P1 phase transition at G* = 0.93.
    The transition is the budget B at which G_star first saturates at
    the threshold and stays there.
    """
    saturated_budget = None
    for r in sweep:
        if r["binding_threshold"]:
            saturated_budget = r["B"]
            break
    # Verify saturation persists for all higher budgets
    if saturated_budget is not None:
        all_above_saturated = all(
            r["binding_threshold"] for r in sweep if r["B"] >= saturated_budget
        )
    else:
        all_above_saturated = False
    return {
        "first_budget_at_threshold": saturated_budget,
        "saturation_persists": all_above_saturated,
        "phase_transition_detected": (saturated_budget is not None) and all_above_saturated,
    }


def main():
    print("=" * 72)
    print("Pass-68 batch-1: UOP phase transition mathematical test")
    print("=" * 72)
    print(f"THRESHOLD = {THRESHOLD}")
    print(f"ALPHA     = {ALPHA_DEFAULT}")
    print(f"Functional form: f(G) = log(1+G) for G<=0.93; "
          f"log(1.93) - alpha*(G-0.93)^2 for G>0.93")
    print(f"                 g(H) = log(1+H); J = f(G) + g(H)")
    print()

    # ----------------------------------------------------------------
    # P1: phase transition at G* = 0.93
    # ----------------------------------------------------------------
    print("-" * 72)
    print("P1: budget sweep -- does argmax G saturate at 0.93?")
    print("-" * 72)
    B_grid = np.arange(0.10, 2.01, 0.05)
    sweep = sweep_budgets(B_grid)
    pt = detect_phase_transition(sweep)
    print(f"  budgets tested: {len(B_grid)} from {B_grid[0]:.2f} to {B_grid[-1]:.2f}")
    print(f"  first budget where G_star reaches 0.93: B = {pt['first_budget_at_threshold']}")
    print(f"  saturation persists for all higher budgets: {pt['saturation_persists']}")
    print(f"  P1 PHASE TRANSITION DETECTED: {pt['phase_transition_detected']}")
    print()
    # Print a few key rows
    print("  budget | G*      | H*      | J*      | at-threshold")
    for r in sweep:
        if r["B"] in [0.5, 0.93, 1.0, 1.2, 1.5, 1.8, 2.0]:
            print(f"  {r['B']:6.2f} | {r['G_star']:7.4f} | {r['H_star']:7.4f} | "
                  f"{r['J_star']:7.4f} | {r['binding_threshold']}")
    print()

    # ----------------------------------------------------------------
    # P2: strategic G->H trade above threshold increases J
    # ----------------------------------------------------------------
    print("-" * 72)
    print("P2: strategic G->H trade above threshold -- does it INCREASE J?")
    print("-" * 72)
    test_cases = [
        (0.95, 0.50),
        (0.97, 0.50),
        (0.99, 0.50),
        (1.00, 0.50),
        (0.99, 0.80),
        (1.00, 0.90),
    ]
    p2_results = []
    all_trades_improve = True
    for G_excess, H in test_cases:
        r = strategic_trade_above_threshold(G_excess, H)
        p2_results.append(r)
        all_trades_improve = all_trades_improve and r["trade_improves_J"]
        print(f"  trade ({G_excess:.2f},{H:.2f}) -> (0.93,{r['H_after']:.2f}) | "
              f"delta_J = {r['delta_J']:+.5f} | improves: {r['trade_improves_J']}")
    print()
    print(f"  P2 ALL TRADES IMPROVE J: {all_trades_improve}")
    print()

    # ----------------------------------------------------------------
    # P3: pure irrationality (degrade both G and H) decreases J
    # ----------------------------------------------------------------
    print("-" * 72)
    print("P3: pure irrationality -- does random degradation always decrease J?")
    print("-" * 72)
    # Use the optimum from B = 1.5 as anchor
    anchor = next(r for r in sweep if abs(r["B"] - 1.5) < 1e-9)
    irr_res = irrational_perturbation(anchor["G_star"], anchor["H_star"], seed=42, n=10000)
    print(f"  anchor: (G*, H*) = ({anchor['G_star']:.4f}, {anchor['H_star']:.4f}) at B=1.5")
    print(f"  J* = {J(anchor['G_star'], anchor['H_star']):.5f}")
    print(f"  perturbations: {irr_res['n_perturbations']}")
    print(f"  fraction reducing J: {irr_res['fraction_reducing_J']:.4f}")
    print(f"  mean delta J: {irr_res['mean_delta_J']:+.5f}")
    print(f"  P3 ALL IRRATIONALITY REDUCES J: {irr_res['all_irrationality_reduces_J']}")
    print()

    # ----------------------------------------------------------------
    # P4: Moot status of above-threshold non-shifter
    # ----------------------------------------------------------------
    print("-" * 72)
    print("P4: Moot status -- above-threshold non-shifter NOT ERRING, just suboptimal")
    print("-" * 72)
    # Agent A: (0.99, 0.51) -- total budget 1.50, above threshold
    # Agent B: (0.93, 0.57) -- total budget 1.50, TRUE-TRALSE optimum
    moot = moot_status_check(G_high=0.99, H_high=0.51, G_optimal=0.93, H_optimal=0.57)
    print(f"  Agent A (above-threshold non-shifter): G=0.99, H=0.51, "
          f"J={moot['agent_A_above_threshold']['J']:.5f}")
    print(f"  Agent B (TRUE-TRALSE shifter):         G=0.93, H=0.57, "
          f"J={moot['agent_B_threshold_shifter']['J']:.5f}")
    print(f"  B dominates in J:        {moot['B_dominates_in_J']}")
    print(f"  A strictly higher in G:  {moot['A_strictly_higher_G']}")
    print(f"  P4 MOOT STATUS APPLIES:  {moot['moot_status_applies']}")
    print()

    # ----------------------------------------------------------------
    # Alpha sensitivity (does the phase transition depend on alpha?)
    # ----------------------------------------------------------------
    print("-" * 72)
    print("Sensitivity check: phase transition under varying ALPHA")
    print("-" * 72)
    alpha_sens = []
    for alpha in [1.0, 2.0, 5.0, 10.0, 25.0, 100.0]:
        sweep_a = sweep_budgets(B_grid, alpha=alpha)
        pt_a = detect_phase_transition(sweep_a)
        alpha_sens.append({"alpha": alpha, **pt_a})
        print(f"  alpha={alpha:6.1f} | first B at threshold: "
              f"{pt_a['first_budget_at_threshold']} | "
              f"phase transition: {pt_a['phase_transition_detected']}")
    print()

    # ----------------------------------------------------------------
    # Bottom line
    # ----------------------------------------------------------------
    print("=" * 72)
    print("BOTTOM LINE")
    print("=" * 72)
    all_predictions = {
        "P1_phase_transition_at_0.93": pt["phase_transition_detected"],
        "P2_strategic_trade_increases_J": all_trades_improve,
        "P3_irrationality_decreases_J": irr_res["all_irrationality_reduces_J"],
        "P4_moot_status_applies": moot["moot_status_applies"],
    }
    for k, v in all_predictions.items():
        print(f"  {k}: {'CONFIRMED' if v else 'REFUTED'}")
    print()
    n_confirmed = sum(all_predictions.values())
    print(f"  {n_confirmed}/4 Brandon predictions CONFIRMED at default ALPHA={ALPHA_DEFAULT}")
    print()

    # Save full results
    out = {
        "threshold": THRESHOLD,
        "alpha_default": ALPHA_DEFAULT,
        "P1_sweep": sweep,
        "P1_phase_transition": pt,
        "P2_strategic_trades": p2_results,
        "P2_all_trades_improve": bool(all_trades_improve),
        "P3_irrationality_test": irr_res,
        "P4_moot_status_test": moot,
        "alpha_sensitivity": alpha_sens,
        "predictions_summary": all_predictions,
        "n_confirmed": int(n_confirmed),
    }
    with open("results.json", "w") as f:
        json.dump(out, f, indent=2, default=str)
    print("  full results saved -> analyses/uop_phase_transition_v1/results.json")


if __name__ == "__main__":
    main()

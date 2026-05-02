"""
URB #828 v2 - Power Curve Simulation

Monte Carlo simulator that compares two pre-registration designs:
  Design A: 8 conditions x N=15 trials  (full ablation, low power per arm)
  Design B: 4 conditions x N=30 trials  (focused: C0/C2/C5/C7, higher power)

Outputs power-vs-effect-size curves under H0 (chance) and H1 (v2 minimum-stack
hypothesis), helping pick the final design at pre-registration LOCK.

Asymmetric-standards #69: report exact thresholds, no fudge factors.
$0 cost. Run: python urb828_power_curve_simulation.py
"""

import argparse
import math
from typing import Dict, List, Tuple

import numpy as np
from scipy import stats


CHANCE = 0.20  # M=5 token set
ALPHA = 0.05  # one-tailed
N_SIMS = 5000

DESIGN_A = {
    "name": "8-cond x 15",
    "conditions": ["C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7"],
    "N_per_condition": 15,
}
DESIGN_B = {
    "name": "4-cond x 30 (focused)",
    "conditions": ["C0", "C2", "C5", "C7"],
    "N_per_condition": 30,
}


def h0_truth() -> Dict[str, float]:
    """Null: every condition at chance."""
    return {c: CHANCE for c in ["C0", "C1", "C2", "C3", "C4", "C5", "C6", "C7"]}


def h1_truth(c5_effect: float, saturation_step: float = 0.04) -> Dict[str, float]:
    """v2 alternative: C5 above chance with monotone non-decreasing saturation curve.

    c5_effect = C5 accuracy - chance. e.g. 0.20 -> C5 = 40%.
    Curve: C0 = chance (mystical-vocab null holds), C1 = chance,
           C2 = chance + 0.4*c5_effect (env-history-only partial),
           C3 = chance + 0.3*c5_effect (v1 minimum, should fail under v2),
           C4 = chance + 0.6*c5_effect (3+1, below v2 minimum),
           C5 = chance + c5_effect (v2 predicted minimum),
           C6 = C5 + saturation_step,
           C7 = C6 + 0.5*saturation_step (saturating).
    """
    c5 = CHANCE + c5_effect
    return {
        "C0": CHANCE,
        "C1": CHANCE,
        "C2": CHANCE + 0.4 * c5_effect,
        "C3": CHANCE + 0.3 * c5_effect,
        "C4": CHANCE + 0.6 * c5_effect,
        "C5": c5,
        "C6": c5 + saturation_step,
        "C7": c5 + saturation_step + 0.5 * saturation_step,
    }


def simulate_design(
    design: Dict, truth: Dict[str, float], n_sims: int = N_SIMS, seed: int = 42
) -> Dict[str, np.ndarray]:
    """Return per-condition empirical accuracy arrays (n_sims x 1)."""
    rng = np.random.default_rng(seed)
    out = {}
    for c in design["conditions"]:
        p = truth[c]
        N = design["N_per_condition"]
        hits = rng.binomial(N, p, size=n_sims)
        out[c] = hits / N
    return out


def power_above_chance(arr: np.ndarray, N: int, alpha: float = ALPHA) -> float:
    """Fraction of sims where binomial test rejects H0 (one-tailed) at alpha."""
    crit_hits = stats.binom.isf(alpha, N, CHANCE)
    return float(np.mean(arr * N > crit_hits))


def power_v2_vs_v1(
    sim: Dict[str, np.ndarray], N: int, gap_threshold: float = 0.10
) -> float:
    """Fraction of sims where C5 - C3 >= gap_threshold (10pp v2-vs-v1 discriminator)."""
    if "C5" not in sim or "C3" not in sim:
        return float("nan")
    return float(np.mean((sim["C5"] - sim["C3"]) >= gap_threshold))


def critical_falsifier_trigger(sim: Dict[str, np.ndarray], threshold: float = 0.35) -> float:
    """Fraction of sims where C0 > 0.35 (false-positive on critical falsifier under H0)."""
    if "C0" not in sim:
        return float("nan")
    return float(np.mean(sim["C0"] > threshold))


def run_curve(c5_effects: List[float], save_csv: str = None) -> List[Dict]:
    rows = []
    for design in [DESIGN_A, DESIGN_B]:
        for eff in [0.0] + c5_effects:
            label = "H0" if eff == 0.0 else f"H1 c5_eff={eff:.2f}"
            truth = h0_truth() if eff == 0.0 else h1_truth(eff)
            sim = simulate_design(design, truth)
            row = {
                "design": design["name"],
                "scenario": label,
                "N_per_cond": design["N_per_condition"],
                "n_conds": len(design["conditions"]),
            }
            if "C5" in sim:
                row["power_C5_>chance"] = power_above_chance(
                    sim["C5"], design["N_per_condition"]
                )
            if "C5" in sim and "C3" in sim:
                row["power_v2_vs_v1"] = power_v2_vs_v1(sim, design["N_per_condition"])
            row["false_C0_trigger"] = critical_falsifier_trigger(sim)
            rows.append(row)
    if save_csv:
        import csv
        keys = sorted({k for r in rows for k in r.keys()})
        with open(save_csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=keys)
            w.writeheader()
            w.writerows(rows)
        print(f"Saved {len(rows)} rows -> {save_csv}")
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--effects",
        type=float,
        nargs="+",
        default=[0.10, 0.15, 0.20, 0.25, 0.30],
        help="C5 effect sizes (above 0.20 chance) to simulate",
    )
    ap.add_argument("--csv", default="data/urb828/power_curve.csv")
    args = ap.parse_args()

    print("URB #828 v2 - Power Curve Simulation")
    print(f"Chance = {CHANCE:.2f}, alpha = {ALPHA}, n_sims = {N_SIMS}")
    print()

    rows = run_curve(args.effects, save_csv=args.csv)

    print(f"{'Design':<22} {'Scenario':<22} {'N':<4} {'Pwr(C5>ch)':<11} {'Pwr(v2-v1)':<11} {'FalseC0':<8}")
    print("-" * 90)
    for r in rows:
        print(
            f"{r['design']:<22} {r['scenario']:<22} {r['N_per_cond']:<4} "
            f"{r.get('power_C5_>chance', float('nan')):<11.3f} "
            f"{r.get('power_v2_vs_v1', float('nan')):<11.3f} "
            f"{r.get('false_C0_trigger', float('nan')):<8.3f}"
        )

    print()
    print("Recommendation guidance:")
    print("  - If power_C5_>chance < 0.50 at the smallest effect of interest,")
    print("    the design is underpowered; pre-register honest framing.")
    print("  - Focused design (B) typically improves power_C5 by ~10-15pp vs full design (A).")
    print("  - power_v2_vs_v1 is the critical v2-vs-v1 discriminator power; <0.40 means")
    print("    the discriminator cannot reliably tell v1 from v2.")
    print("  - false_C0_trigger should be <= alpha; if larger, the C0 threshold (35%)")
    print("    needs raising.")


if __name__ == "__main__":
    main()

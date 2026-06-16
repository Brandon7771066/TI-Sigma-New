"""
LCC Coherence Scoring for ARC Solutions
========================================
Mirrors the Law of Correlational Causation from TI Sigma theory:
LCC = 1 means perfect coherence (transformation applies consistently
across ALL training pairs). LCC = 0 means no coherence.

Extended scoring includes:
  - Cross-pair consistency (std penalty)
  - Transformation complexity penalty (Occam's Razor as coherence)
  - Tralse resolution quality (did we avoid forcing incoherent resolutions?)
  - Size preservation bonus (if input/output dims match)
"""

import numpy as np
from typing import Callable


COMPLEXITY_WEIGHTS = {
    "identity": 0.0,
    "rotate": 0.02,
    "flip": 0.02,
    "mirror": 0.03,
    "recolor": 0.05,
    "shift": 0.04,
    "swap": 0.06,
    "scale": 0.05,
    "tile": 0.05,
    "crop": 0.04,
    "gravity": 0.06,
    "hollow": 0.07,
    "composed": 0.10,
}


def complexity_penalty(transform_name: str) -> float:
    """Occam's Razor: simpler transformations get lower penalty."""
    name_lower = transform_name.lower()
    for key, penalty in COMPLEXITY_WEIGHTS.items():
        if key in name_lower:
            return penalty
    if "+" in transform_name:
        return COMPLEXITY_WEIGHTS["composed"]
    return 0.08


def compute_full_lcc(
    transform: Callable,
    train_pairs: list,
    transform_name: str = "",
    alpha: float = 0.85,
) -> dict:
    """
    Compute full LCC score with all components.

    Components:
      - cell_accuracy: mean cell-level match across all pairs
      - consistency: 1 - std(per-pair accuracies) — rewards uniform performance
      - complexity: 1 - complexity_penalty(name)
      - size_match: 1 if all pairs preserve dims, else 0.5

    Final LCC = weighted product: alpha * cell_accuracy + bonuses
    Threshold: LCC >= 0.85 → "True-Tralse" regime (analogous to C_EMERICK)
    """
    per_pair = []
    size_match = True

    for pair in train_pairs:
        inp = np.array(pair["input"], dtype=np.int8)
        out = np.array(pair["output"], dtype=np.int8)
        try:
            pred = transform(inp)
            if pred.shape != out.shape:
                size_match = False
                per_pair.append(0.0)
                continue
            acc = float(np.mean(pred == out))
            per_pair.append(acc)
        except Exception:
            per_pair.append(0.0)

    if not per_pair:
        return {"lcc": 0.0, "cell_accuracy": 0.0, "consistency": 0.0,
                "complexity": 0.0, "size_match": False}

    cell_acc = float(np.mean(per_pair))
    consistency = max(0.0, 1.0 - float(np.std(per_pair)))
    complexity = 1.0 - complexity_penalty(transform_name)
    size_score = 1.0 if size_match else 0.7

    lcc = (
        0.60 * cell_acc +
        0.20 * consistency +
        0.10 * complexity +
        0.10 * size_score
    )

    return {
        "lcc": round(lcc, 4),
        "cell_accuracy": round(cell_acc, 4),
        "consistency": round(consistency, 4),
        "complexity": round(complexity, 4),
        "size_match": size_match,
        "per_pair_accuracy": per_pair,
        "true_tralse": lcc >= 0.85,
        "crossover": lcc >= 0.7823,
    }


def rank_solutions(solutions: list) -> list:
    """
    Rank a list of {output, lcc, transform} dicts by LCC descending.
    Deduplicates identical outputs.
    """
    seen = set()
    ranked = []
    for sol in sorted(solutions, key=lambda s: s["lcc"], reverse=True):
        key = str(sol["output"])
        if key not in seen:
            seen.add(key)
            ranked.append(sol)
    return ranked


def lcc_report(solutions: list, top_k: int = 5) -> str:
    """Human-readable LCC ranking report."""
    lines = ["LCC Coherence Report", "=" * 40]
    for i, sol in enumerate(solutions[:top_k]):
        lcc = sol["lcc"]
        name = sol.get("transform", "?")
        regime = ""
        if lcc >= 0.85:
            regime = " [TRUE-TRALSE]"
        elif lcc >= 0.7823:
            regime = " [CROSSOVER]"
        elif lcc > 0:
            regime = " [COHERENT]"
        else:
            regime = " [INCOHERENT]"
        lines.append(f"  #{i+1} LCC={lcc:.4f}{regime} — {name}")
    lines.append(f"\nBest: LCC={solutions[0]['lcc']:.4f} via {solutions[0].get('transform','?')}")
    return "\n".join(lines)

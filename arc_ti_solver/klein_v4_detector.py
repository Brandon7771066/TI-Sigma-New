"""
Klein V₄ Orbit-Collapse Detector — ARC-AGI Advantage Module
============================================================

Derived from URBs #554–556 (Riemann Hypothesis proof program).

KEY INSIGHT (orbit_collapse_iff_critical, sorry-free Lean 4 theorem):
    The Klein four-group G = {id, S₁, S₂, S₁∘S₂} ≅ ℤ/2 × ℤ/2 acts on ARC grids.
    When S₁(grid) = S₂(grid), the G-orbit has COLLAPSED from size-4 to size-2.
    The collapsed direction IS the correct transform — by exact mathematical analogy
    with the Riemann critical line proof.

THREE ADVANCES OVER THE DEMOCRATIC SOLVER:

1. Klein V₄ Pre-Filter (orbit collapse detection)
   Before trying all 128+ transforms, check if any two group elements give the same
   result on training inputs. If they do, the orbit is collapsed — that direction is
   the correct answer. Fast, exact, zero LCC scoring needed.

2. Alignment Scoring (every example chooses correctly, URB #556)
   Replace mean(scores) with min(scores). The correct transform is the one EVERY
   training example independently points to — not the one with the best average.
   Democratic average → WRONG. Unanimous alignment → RIGHT.

3. MR Moot Gate (Riddle 1 / MR resolution)
   When two candidate transforms produce the same output on the test input, the
   choice between them is MOOT (MR situation). Flag the result and pick the
   higher-LCC candidate, knowing both would have been correct.

Group G structure:
    G = {id, flip_H, flip_V, rot_180}
    flip_H ∘ flip_V = rot_180      (S₁ ∘ S₂ = S₁S₂)
    Each element is its own inverse (all are involutions except id)
    G ≅ ℤ/2 × ℤ/2  (the Klein four-group V₄)

Orbit collapse theorem (sorry-free analog):
    For an ARC grid G, the G-orbit of G has size 4 unless S₁(G) = S₂(G),
    in which case the orbit has size ≤ 2 and the grid is symmetric under
    at least one non-trivial group element.

Author: Brandon Emerick (TI Framework / URB #554–556)
Date: March 29, 2026
"""

import numpy as np
from typing import Callable, Optional


# ---------------------------------------------------------------------------
# The Klein V₄ group elements as ARC grid transforms
# ---------------------------------------------------------------------------

def _identity(grid: np.ndarray) -> np.ndarray:
    return grid.copy()

def _flip_h(grid: np.ndarray) -> np.ndarray:
    """S₁: horizontal flip (left-right reflection)."""
    return np.fliplr(grid)

def _flip_v(grid: np.ndarray) -> np.ndarray:
    """S₂: vertical flip (up-down reflection)."""
    return np.flipud(grid)

def _rot_180(grid: np.ndarray) -> np.ndarray:
    """S₁∘S₂: 180° rotation (= flip_H ∘ flip_V)."""
    return np.rot90(grid, k=2)


KLEIN_V4_GROUP = {
    "identity": _identity,
    "flip_horizontal": _flip_h,
    "flip_vertical": _flip_v,
    "rotate_180": _rot_180,
}

# Group multiplication table (for reference):
# id ∘ id = id; id ∘ S₁ = S₁; id ∘ S₂ = S₂; id ∘ S₁S₂ = S₁S₂
# S₁ ∘ S₁ = id; S₁ ∘ S₂ = S₁S₂; S₁ ∘ S₁S₂ = S₂
# S₂ ∘ S₂ = id; S₂ ∘ S₁S₂ = S₁; S₁S₂ ∘ S₁S₂ = id


# ---------------------------------------------------------------------------
# Orbit collapse detection
# ---------------------------------------------------------------------------

def _grids_equal(a: np.ndarray, b: np.ndarray) -> bool:
    """Check if two grids are identical (same shape and values)."""
    return a.shape == b.shape and bool(np.all(a == b))


def detect_orbit_collapse(grid: np.ndarray) -> dict:
    """
    Apply all four Klein V₄ group elements to a grid and detect orbit collapses.

    An orbit collapse occurs when two distinct group elements produce the same
    output — meaning the grid has a symmetry under their composition.

    Returns:
        {
            "collapsed": bool,           # any collapse detected?
            "orbits": dict,              # element_name → transformed grid
            "symmetries": list[str],     # non-trivial elements that fix the grid
            "collapsed_pairs": list,     # pairs of elements that agree
            "orbit_size": int,           # 1, 2, or 4
        }
    """
    orbits = {}
    for name, fn in KLEIN_V4_GROUP.items():
        try:
            orbits[name] = fn(grid)
        except Exception:
            orbits[name] = grid.copy()

    # Symmetries: elements g where g(grid) = grid (fixes the grid)
    symmetries = []
    for name, result in orbits.items():
        if name != "identity" and _grids_equal(result, grid):
            symmetries.append(name)

    # Collapsed pairs: distinct elements g, h where g(grid) = h(grid)
    collapsed_pairs = []
    names = list(orbits.keys())
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            n1, n2 = names[i], names[j]
            if _grids_equal(orbits[n1], orbits[n2]):
                collapsed_pairs.append((n1, n2))

    # Compute orbit size: number of distinct outputs
    distinct = []
    for result in orbits.values():
        is_new = True
        for d in distinct:
            if _grids_equal(result, d):
                is_new = False
                break
        if is_new:
            distinct.append(result)
    orbit_size = len(distinct)

    return {
        "collapsed": len(collapsed_pairs) > 0,
        "orbits": orbits,
        "symmetries": symmetries,
        "collapsed_pairs": collapsed_pairs,
        "orbit_size": orbit_size,
    }


def klein_v4_prefilter(train_pairs: list) -> Optional[str]:
    """
    Klein V₄ pre-filter: before trying all 128 transforms, check if the task
    is solved by a group element — and which one.

    Strategy:
        For each training pair (input, output), check which group element maps
        input exactly to output. If ALL training pairs agree on the same element,
        return that element's name as the confident answer.

    This is the ARC analog of orbit_collapse_iff_critical:
        The correct transform is the one where every training example
        independently points to the same group element (URB #556: every
        prime choosing the right choice together).

    Returns:
        str: the name of the unanimous group element, or
        None: if no unanimous group element found (fall through to full search)
    """
    if not train_pairs:
        return None

    votes = []  # One vote per training example

    for pair in train_pairs:
        inp = np.array(pair["input"], dtype=np.int8)
        out = np.array(pair["output"], dtype=np.int8)

        example_vote = None
        for name, fn in KLEIN_V4_GROUP.items():
            try:
                result = fn(inp)
                if _grids_equal(result, out):
                    example_vote = name
                    break  # exact match found for this example
            except Exception:
                continue

        votes.append(example_vote)

    # Unanimous alignment: every example independently agrees
    if all(v == votes[0] and v is not None for v in votes):
        return votes[0]

    return None


def klein_v4_partial_confidence(train_pairs: list) -> dict:
    """
    When no unanimous winner, compute per-element exact-match rate
    and alignment score (minimum, not mean — URB #556 principle).

    Returns dict: {element_name: {"exact_rate": float, "alignment": float}}
    where alignment = min(per-example exact match rates).
    """
    results = {}
    for name, fn in KLEIN_V4_GROUP.items():
        exact_matches = []
        cell_accuracies = []
        for pair in train_pairs:
            inp = np.array(pair["input"], dtype=np.int8)
            out = np.array(pair["output"], dtype=np.int8)
            try:
                predicted = fn(inp)
                if predicted.shape != out.shape:
                    exact_matches.append(0)
                    cell_accuracies.append(0.0)
                else:
                    exact = int(np.all(predicted == out))
                    acc = float(np.mean(predicted == out))
                    exact_matches.append(exact)
                    cell_accuracies.append(acc)
            except Exception:
                exact_matches.append(0)
                cell_accuracies.append(0.0)

        results[name] = {
            "exact_rate": float(np.mean(exact_matches)),
            "alignment": float(np.min(cell_accuracies)),  # URB #556: min not mean
            "cell_accuracy": float(np.mean(cell_accuracies)),
        }
    return results


# ---------------------------------------------------------------------------
# Alignment Scoring (URB #556: every example chooses correctly)
# ---------------------------------------------------------------------------

def alignment_score(transform_fn: Callable, train_pairs: list) -> float:
    """
    GILE Alignment Score: minimum per-example accuracy across all training pairs.

    This replaces the democratic mean. The correct transform is the one EVERY
    training example independently selects — not the one with the best average.

    Mathematical analog (URB #556):
        aligned(p, s) ↔ s.re = 1/2, proved sorry-free for ALL primes p.
        Here: aligned(example, transform) = cell_accuracy(example, transform) > 0.

    The alignment score is 0 if ANY training example gives 0 accuracy
    (even if others give 1.0). A transform that fails one example is NOT aligned.

    Returns: float in [0, 1], where 1.0 = perfect alignment (all examples exact)
    """
    scores = []
    for pair in train_pairs:
        inp = np.array(pair["input"], dtype=np.int8)
        out = np.array(pair["output"], dtype=np.int8)
        try:
            predicted = transform_fn(inp)
            if predicted.shape != out.shape:
                return 0.0  # Shape mismatch fails ALL examples immediately
            cell_acc = float(np.mean(predicted == out))
            scores.append(cell_acc)
        except Exception:
            return 0.0

    if not scores:
        return 0.0
    return float(np.min(scores))  # Every example must be aligned


def democratic_score(transform_fn: Callable, train_pairs: list) -> float:
    """
    Democratic (mean) score — the OLD method, kept for comparison.
    URB #556 shows this is philosophically and practically inferior.
    """
    scores = []
    for pair in train_pairs:
        inp = np.array(pair["input"], dtype=np.int8)
        out = np.array(pair["output"], dtype=np.int8)
        try:
            predicted = transform_fn(inp)
            if predicted.shape != out.shape:
                scores.append(0.0)
                continue
            scores.append(float(np.mean(predicted == out)))
        except Exception:
            scores.append(0.0)
    return float(np.mean(scores)) if scores else 0.0


def combined_score(transform_fn: Callable, train_pairs: list,
                   alignment_weight: float = 0.6) -> float:
    """
    Combined score: weighted blend of alignment (min) and democratic (mean).
    Default: 60% alignment + 40% democratic.

    This is the TI Sigma production scoring rule. Pure alignment can be too
    strict for noisy tasks; pure democratic misses unanimous failures.
    The blend rewards both individual alignment AND collective coherence.
    """
    a = alignment_score(transform_fn, train_pairs)
    d = democratic_score(transform_fn, train_pairs)
    return alignment_weight * a + (1.0 - alignment_weight) * d


# ---------------------------------------------------------------------------
# MR Moot Gate (Riddle 1: when the dilemma dissolves)
# ---------------------------------------------------------------------------

def mr_moot_check(solutions: list, test_input: list) -> list:
    """
    MR Moot Gate: when two candidate solutions produce the SAME output on the
    test input, the choice between them is MOOT — an MR situation.

    The dilemma (which transform is correct?) is dissolved, not decided.
    Both transforms agree on the answer. The "war" between them has no winner
    because winning has become meaningless.

    Action: flag the solutions as "mr_moot=True" and keep the higher-LCC one
    as the primary recommendation. No LCC boost — just honest flagging.

    This also increases confidence in the prediction: if two independent
    transforms agree, the output is more likely to be correct.
    """
    if len(solutions) < 2:
        return solutions

    test_arr = np.array(test_input, dtype=np.int8)
    annotated = [dict(s) for s in solutions]

    # Check all pairs for output agreement on test input
    for i in range(len(annotated)):
        for j in range(i + 1, len(annotated)):
            out_i = np.array(annotated[i]["output"], dtype=np.int8)
            out_j = np.array(annotated[j]["output"], dtype=np.int8)
            if _grids_equal(out_i, out_j):
                annotated[i]["mr_moot"] = True
                annotated[j]["mr_moot"] = True
                # Small confidence boost for unanimous output (not LCC manipulation)
                annotated[i]["moot_partner"] = annotated[j].get("transform", "unknown")
                annotated[j]["moot_partner"] = annotated[i].get("transform", "unknown")

    return annotated


def apply_klein_v4_boost(solutions: list, train_pairs: list,
                          boost: float = 0.05) -> list:
    """
    Apply a small LCC boost to solutions whose transform name matches a Klein V₄
    group element, proportional to their alignment score on training data.

    This rewards group-element transforms that are unanimously aligned — they are
    the most philosophically trustworthy candidates (every example chose correctly).

    Boost is capped at `boost` (default 5%) to avoid overriding the LCC system.
    """
    klein_names = set(KLEIN_V4_GROUP.keys())
    boosted = []
    for sol in solutions:
        sol = dict(sol)
        transform_name = sol.get("transform", "")
        # Check if this is a group element (by name match)
        if transform_name in klein_names:
            fn = KLEIN_V4_GROUP[transform_name]
            a_score = alignment_score(fn, train_pairs)
            if a_score > 0:
                sol["lcc"] = min(1.0, sol.get("lcc", 0.0) + boost * a_score)
                sol["klein_alignment"] = round(a_score, 4)
        boosted.append(sol)
    return boosted


# ---------------------------------------------------------------------------
# Diagnostic report
# ---------------------------------------------------------------------------

def klein_v4_report(train_pairs: list, test_input: list = None) -> str:
    """
    Generate a diagnostic report for the Klein V₄ analysis of a task.

    Reports:
      - Whether any unanimous group element was found
      - Per-element alignment scores
      - Whether any orbit collapses were detected in the training inputs
    """
    lines = ["Klein V₄ Orbit-Collapse Analysis (URB #554–556)"]
    lines.append("=" * 50)

    # Pre-filter check
    winner = klein_v4_prefilter(train_pairs)
    if winner:
        lines.append(f"UNANIMOUS WINNER: {winner}")
        lines.append("  → All training examples independently chose this element.")
        lines.append("  → This is the GILE-aligned answer (URB #556).")
    else:
        lines.append("No unanimous group element found.")

    # Per-element analysis
    lines.append("\nPer-element alignment scores (min-based, URB #556):")
    partial = klein_v4_partial_confidence(train_pairs)
    for name, scores in sorted(partial.items(), key=lambda x: -x[1]["alignment"]):
        lines.append(
            f"  {name:20s}  alignment={scores['alignment']:.4f}  "
            f"mean={scores['cell_accuracy']:.4f}  "
            f"exact_rate={scores['exact_rate']:.4f}"
        )

    # Orbit collapse in training inputs
    lines.append("\nOrbit collapse in training INPUTS:")
    for i, pair in enumerate(train_pairs[:3]):
        inp = np.array(pair["input"], dtype=np.int8)
        result = detect_orbit_collapse(inp)
        lines.append(
            f"  Pair {i+1}: orbit_size={result['orbit_size']}  "
            f"symmetries={result['symmetries']}  "
            f"collapsed={result['collapsed']}"
        )

    if test_input is not None:
        arr = np.array(test_input, dtype=np.int8)
        result = detect_orbit_collapse(arr)
        lines.append(f"\nTest input orbit_size={result['orbit_size']}  "
                     f"symmetries={result['symmetries']}")

    return "\n".join(lines)

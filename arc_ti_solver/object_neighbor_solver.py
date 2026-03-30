"""
Domain 3: Per-Object Neighborhood Rule Solver — ARC-AGI
=======================================================

Handles tasks where each "seed" color gets a unique neighborhood pattern.

Example (`0ca9ddb6`):
  - Color 1 (blue) → 4 cross neighbors become color 7
  - Color 2 (red)  → 4 diagonal neighbors become color 4
  - Color 8 stays unchanged (no rule for it)

This is exactly the G-dimension reasoning (constraint satisfaction):
  For each color, learn what pattern appears around it in the output.
  Then apply those patterns to the test input.

TI Sigma framing:
  Each seed color is a "grain" in polycrystalline terms (URB #539).
  Its neighborhood is the "grain boundary" — the interface zone around it.
  The rule defines how the grain broadcasts its identity into the boundary.
  The GILE Love (L) dimension: each object "reaches out" to its neighbors.

Author: Brandon Emerick (TI Sigma / ARC Domain Solver)
Date: March 30, 2026
"""

import numpy as np
from typing import Optional


# ── Neighborhood offsets ────────────────────────────────────────────────────

CROSS_4    = [(-1,0),(1,0),(0,-1),(0,1)]
DIAGONAL_4 = [(-1,-1),(-1,1),(1,-1),(1,1)]
ALL_8      = CROSS_4 + DIAGONAL_4
KING_1     = ALL_8   # same as all_8

# Common named neighborhood patterns
NAMED_NEIGHBORHOODS = {
    "cross":     CROSS_4,
    "diagonal":  DIAGONAL_4,
    "king":      ALL_8,
    "right":     [(0,1)],
    "left":      [(0,-1)],
    "up":        [(-1,0)],
    "down":      [(1,0)],
    "right2":    [(0,1),(0,2)],
    "left2":     [(0,-1),(0,-2)],
    "up2":       [(-1,0),(-2,0)],
    "down2":     [(1,0),(2,0)],
}


def _extract_neighborhood_delta(
    inp: np.ndarray, out: np.ndarray, seed_color: int, bg_color: int
) -> Optional[dict]:
    """
    For a given seed_color, find what new cells appear around it in the output.

    Returns: {(dr, dc): new_color} for cells that are bg in input but
    non-bg at offset (dr,dc) from seed positions in output.
    Returns None if the seed is not present in this pair.
    """
    seed_positions = list(zip(*np.where(inp == seed_color)))
    if not seed_positions:
        return None

    delta = {}
    rows, cols = inp.shape

    for (r, c) in seed_positions:
        for dr in range(-3, 4):
            for dc in range(-3, 4):
                if dr == 0 and dc == 0:
                    continue
                nr, nc = r + dr, c + dc
                if 0 <= nr < rows and 0 <= nc < cols:
                    inp_val = int(inp[nr, nc])
                    out_val = int(out[nr, nc])
                    if inp_val == bg_color and out_val != bg_color:
                        # A new color appeared at offset (dr, dc)
                        if (dr, dc) in delta:
                            if delta[(dr, dc)] != out_val:
                                return None  # inconsistent
                        else:
                            delta[(dr, dc)] = out_val

    return delta


def learn_neighborhood_rules(train_pairs: list) -> Optional[dict]:
    """
    Learn per-color neighborhood rules from training pairs.

    Returns: {seed_color: {(dr, dc): neighbor_color}}
    Returns None if the rules are inconsistent across pairs.
    """
    if not train_pairs:
        return None

    # Detect background color (most frequent in inputs)
    all_counts = np.zeros(10, dtype=int)
    for pair in train_pairs:
        vals, cnts = np.unique(np.array(pair["input"]), return_counts=True)
        for v, c in zip(vals, cnts):
            if 0 <= v < 10:
                all_counts[v] += c
    bg_color = int(np.argmax(all_counts))

    # Detect all seed colors (non-background colors that appear in inputs)
    all_seed_colors = set()
    for pair in train_pairs:
        inp = np.array(pair["input"])
        for c in np.unique(inp):
            if c != bg_color:
                all_seed_colors.add(int(c))

    # Learn rules per color
    rules = {}  # {seed_color: {(dr,dc): neighbor_color}}

    for seed_color in all_seed_colors:
        color_deltas = []

        for pair in train_pairs:
            inp = np.array(pair["input"])
            out = np.array(pair["output"])
            if inp.shape != out.shape:
                return None  # This solver requires size preservation

            delta = _extract_neighborhood_delta(inp, out, seed_color, bg_color)
            if delta is not None:
                color_deltas.append(delta)

        if not color_deltas:
            continue  # Color doesn't appear in any pair — skip

        # Unify deltas: must be consistent across all pairs where color appears
        unified = {}
        for delta in color_deltas:
            for offset, new_color in delta.items():
                if offset in unified:
                    if unified[offset] != new_color:
                        return None  # Inconsistent neighborhood rule
                else:
                    unified[offset] = new_color

        rules[seed_color] = unified

    return rules if rules else None


def apply_neighborhood_rules(
    grid: list, rules: dict, bg_color: Optional[int] = None
) -> list:
    """
    Apply per-color neighborhood rules to a grid.

    For each seed position in the grid, place the neighbor colors at the
    specified offsets. Seed colors themselves are preserved.
    """
    inp = np.array(grid)
    result = inp.copy()
    rows, cols = inp.shape

    if bg_color is None:
        all_counts = np.bincount(inp.flatten(), minlength=10)
        bg_color = int(np.argmax(all_counts))

    for seed_color, delta in rules.items():
        positions = list(zip(*np.where(inp == seed_color)))
        for (r, c) in positions:
            for (dr, dc), neighbor_color in delta.items():
                nr, nc = r + dr, c + dc
                if 0 <= nr < rows and 0 <= nc < cols:
                    # Only write to background cells (don't overwrite other seeds)
                    if result[nr, nc] == bg_color:
                        result[nr, nc] = neighbor_color

    return result.tolist()


def solve_object_neighbor(task: dict) -> Optional[dict]:
    """
    Attempt to solve an ARC task using per-object neighborhood rules.

    Returns dict with output + metadata, or None if not applicable.
    """
    train_pairs = task.get("train", [])
    test_pairs = task.get("test", [])

    if not train_pairs or not test_pairs:
        return None

    # All pairs must preserve size
    for pair in train_pairs:
        if np.array(pair["input"]).shape != np.array(pair["output"]).shape:
            return None

    # Learn rules
    rules = learn_neighborhood_rules(train_pairs)
    if not rules:
        return None

    # Validate on training pairs (Unanimous Alignment)
    # Detect background
    all_counts = np.zeros(10, dtype=int)
    for pair in train_pairs:
        vals, cnts = np.unique(np.array(pair["input"]), return_counts=True)
        for v, c in zip(vals, cnts):
            if 0 <= v < 10:
                all_counts[v] += c
    bg_color = int(np.argmax(all_counts))

    train_scores = []
    for pair in train_pairs:
        predicted = np.array(apply_neighborhood_rules(
            pair["input"], rules, bg_color
        ))
        actual = np.array(pair["output"])
        if predicted.shape != actual.shape:
            return None
        correct = float(np.mean(predicted == actual))
        train_scores.append(correct)

    # Unanimous: every pair must score above threshold (min-score, not mean)
    min_score = min(train_scores)
    if min_score < 0.80:  # At least 80% accurate on every training pair
        return None

    # Apply to test
    test_inp = test_pairs[0]["input"]
    predicted_output = apply_neighborhood_rules(test_inp, rules, bg_color)

    lcc = float(np.mean(train_scores)) * min_score  # conservative LCC

    return {
        "output": predicted_output,
        "lcc": lcc,
        "method": "object_neighbor_solver",
        "rules": {str(k): v for k, v in rules.items()},
        "train_scores": train_scores,
        "min_train_score": min_score,
    }


def is_object_neighbor_task(task: dict) -> bool:
    """
    Quick classifier: does this look like a per-object neighborhood task?

    Heuristics:
    1. All pairs preserve size
    2. Output has MORE non-background cells than input (neighbors were added)
    3. Seed colors in input are present in output (seeds preserved)
    4. New colors appear in output that weren't in input (or sparse colors expand)
    """
    train = task.get("train", [])
    if not train:
        return False

    for pair in train:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        if inp.shape != out.shape:
            return False

        # Count non-background cells
        bg = int(np.bincount(inp.flatten(), minlength=10).argmax())
        n_inp = int(np.sum(inp != bg))
        n_out = int(np.sum(out != bg))
        if n_out <= n_inp:
            return False  # Output doesn't have more cells — not this pattern

    return True

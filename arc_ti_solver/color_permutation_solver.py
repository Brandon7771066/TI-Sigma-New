"""
Domain 2: Color Permutation Solver — ARC-AGI
============================================

Handles tasks where the rule is a CONSISTENT color mapping (permutation):
  Every pixel of input color A → output color f(A) for a fixed function f.

TI Sigma framing:
  A color permutation IS a 5-valued relabeling of the grid's truth values.
  The mapping is learned from training pairs as a consistent function.
  If the learned mapping is unanimous across all training pairs (Unanimous
  Alignment, URB #556, min-score not mean-score), it is applied to the test.

Handles:
  - Full permutation tables (any color → any color)
  - Partial tables (only some colors change)
  - Background preservation (most common color usually maps to itself)
  - Inconsistent mappings → returns None (DOUBLE_TRALSE, discard)

Author: Brandon Emerick (TI Sigma / ARC Domain Solver)
Date: March 30, 2026
"""

import numpy as np
from typing import Optional


def learn_color_permutation(train_pairs: list) -> Optional[dict]:
    """
    Learn a global color permutation from training pairs.

    For each training pair, build: {input_color → output_color}
    For every position in the grid, the output color at that position
    must be consistent with the mapping.

    Returns:
        dict {input_color: output_color} if a consistent mapping exists,
        None if the mapping is inconsistent (DOUBLE_TRALSE — discard).
    """
    mapping = {}

    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])

        # Size must be preserved for a pure color permutation
        if inp.shape != out.shape:
            return None

        # For every (position), learn input_color → output_color
        for color in np.unique(inp):
            color = int(color)
            positions = (inp == color)
            output_colors_at_positions = out[positions]
            unique_outputs = np.unique(output_colors_at_positions)

            # A pure color permutation maps one color to exactly one other
            if len(unique_outputs) != 1:
                return None  # One input color maps to multiple outputs → not a permutation

            target = int(unique_outputs[0])

            # Check consistency with prior pairs
            if color in mapping:
                if mapping[color] != target:
                    return None  # Inconsistent across pairs → DOUBLE_TRALSE
            else:
                mapping[color] = target

    return mapping if mapping else None


def apply_color_permutation(grid: list, mapping: dict) -> list:
    """
    Apply a color permutation mapping to a grid.
    Colors not in the mapping are left unchanged.
    """
    arr = np.array(grid)
    result = arr.copy()
    for src_color, dst_color in mapping.items():
        result[arr == src_color] = dst_color
    return result.tolist()


def solve_color_permutation(task: dict) -> Optional[dict]:
    """
    Attempt to solve an ARC task using the Color Permutation Solver.

    Returns:
        dict with keys: 'output' (list of lists), 'lcc' (float), 'method' (str)
        None if the task cannot be solved by this method.
    """
    train_pairs = task.get("train", [])
    test_pairs = task.get("test", [])

    if not train_pairs or not test_pairs:
        return None

    # Learn the permutation
    mapping = learn_color_permutation(train_pairs)
    if mapping is None:
        return None

    # Verify the permutation on ALL training pairs (Unanimous Alignment)
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        if inp.shape != out.shape:
            return None
        predicted = np.array(apply_color_permutation(pair["input"], mapping))
        if not np.array_equal(predicted, out):
            return None  # Doesn't perfectly reconstruct → not this rule

    # Apply to test
    test_inp = test_pairs[0]["input"]
    predicted_output = apply_color_permutation(test_inp, mapping)

    # LCC = 1.0 if the mapping is unanimous across all training pairs
    lcc = 1.0

    return {
        "output": predicted_output,
        "lcc": lcc,
        "method": "color_permutation",
        "mapping": mapping,
    }


def is_color_permutation_task(task: dict) -> bool:
    """
    Quick classifier: is this likely a color permutation task?

    Heuristics:
    1. All training pairs preserve grid size
    2. The set of unique colors changes (not identity transform)
    3. No shape changes — just recoloring
    """
    train = task.get("train", [])
    if not train:
        return False

    # All pairs must preserve size
    for pair in train:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        if inp.shape != out.shape:
            return False

    # At least one pair should have color changes
    has_color_change = False
    for pair in train:
        inp_colors = set(np.array(pair["input"]).flatten().tolist())
        out_colors = set(np.array(pair["output"]).flatten().tolist())
        if inp_colors != out_colors:
            has_color_change = True
            break

    return has_color_change

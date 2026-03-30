"""
ARC Task Domain Classifier — TI Sigma Phase 5
==============================================

Classifies each ARC task into one of 5 domains and routes to the
appropriate specialist solver.

Five TI Sigma Domains (mapped to GILE dimensions):

  Domain 1 — SYMMETRY & TRANSFORMS [G-dimension]
    Rotation, reflection, translation, Klein V4 symmetry.
    Handled by: MyrionSolver + KleinV4Detector (existing Phase 4)

  Domain 2 — COLOR PERMUTATION RULES [E-dimension]
    Each color → another color by a fixed global permutation.
    Handled by: ColorPermutationSolver (new)

  Domain 3 — PER-OBJECT NEIGHBORHOOD [L-dimension: each object "reaches"]
    Each seed color generates a specific neighbor pattern.
    Handled by: ObjectNeighborSolver (new)

  Domain 4 — RESIZE / SCALE TRANSFORMS [I-dimension: new size emergent]
    Output size ≠ input size; upscale, tile, compact, extract.
    Handled by: ScaleSolver (new)

  Domain 5 — COMPLEX REASONING [G+Tralse: multi-step, requires MR]
    Object detection, spatial propagation, counting, arithmetic rules.
    Handled by: MyrionSolver (existing, best attempt with TRALSE flagging)

Routing priority:
  1. If resize → try Domain 4 first, then fallback to Domain 5
  2. If same-size + color permutation → Domain 2
  3. If same-size + neighborhood expansion → Domain 3
  4. If same-size → Domain 1 (existing), fallback Domain 5

Author: Brandon Emerick (TI Sigma / ARC Domain Router)
Date: March 30, 2026
"""

import numpy as np
from typing import Optional

from arc_ti_solver.color_permutation_solver import (
    solve_color_permutation, is_color_permutation_task
)
from arc_ti_solver.object_neighbor_solver import (
    solve_object_neighbor, is_object_neighbor_task
)
from arc_ti_solver.scale_solver import solve_scale, is_resize_task
from arc_ti_solver.connected_component_solver import solve_connected_components


DOMAIN_NAMES = {
    1: "Symmetry & Transforms",
    2: "Color Permutation Rules",
    3: "Per-Object Neighborhood",
    4: "Resize / Scale Transforms",
    5: "Complex Multi-Step Reasoning",
}


def classify_domain(task: dict) -> int:
    """
    Classify an ARC task into one of the 5 TI Sigma domains.

    Returns domain number (1-5).
    """
    train = task.get("train", [])
    if not train:
        return 5

    # Check for resize
    if is_resize_task(task):
        return 4

    # Check for per-object neighborhood (must check before color permutation
    # because neighborhoods add new cells, not just recolor existing ones)
    if is_object_neighbor_task(task):
        return 3

    # Check for color permutation
    if is_color_permutation_task(task):
        return 2

    # Default: symmetry/transforms (handled by existing solver)
    # Distinguish domain 1 (clean transforms) from domain 5 (complex)
    # Heuristic: if all pairs have same number of unique colors → likely transform
    same_color_count = True
    for pair in train:
        inp_colors = len(np.unique(np.array(pair["input"])))
        out_colors = len(np.unique(np.array(pair["output"])))
        if inp_colors != out_colors:
            same_color_count = False
            break

    return 1 if same_color_count else 5


def route_to_domain_solver(task: dict, task_id: str = "?") -> Optional[dict]:
    """
    Route a task to the appropriate domain solver.

    Returns the solver result dict or None if the specialist solver fails.
    (Falling back to the existing MyrionSolver is handled in the main pipeline.)

    Result format:
        {
            'output': list[list[int]],
            'lcc': float,
            'method': str,
            'domain': int,
            'domain_name': str,
        }
    """
    domain = classify_domain(task)

    result = None

    if domain == 4:
        # Resize/Scale — try ScaleSolver
        result = solve_scale(task)
        if result is None:
            # Some resize tasks are actually color permutations with resize
            result = solve_color_permutation(task)
            if result:
                domain = 2

    elif domain == 2:
        # Pure color permutation
        result = solve_color_permutation(task)

    elif domain == 3:
        # Per-object neighborhood rules
        result = solve_object_neighbor(task)

        if result is None:
            # Connected component patterns (gravity, border/interior, size-recolor)
            cc = solve_connected_components(task)
            # Only trust gravity/border patterns (component_recolor has false positives)
            if cc and cc.get("pattern", "") in ("gravity_down", "gravity_up",
                                                  "gravity_left", "gravity_right",
                                                  "border_vs_interior_recolor"):
                result = cc

        if result is None:
            # Also try color permutation on Domain 3 tasks (some are hybrid)
            result = solve_color_permutation(task)
            if result:
                domain = 2

    elif domain == 1:
        # Domain 1 (symmetry/transforms) — check gravity first (preserves color count)
        # Gravity tasks are classified Domain 1 because they preserve color distribution.
        cc = solve_connected_components(task)
        if cc and cc.get("pattern", "") in ("gravity_down", "gravity_up",
                                              "gravity_left", "gravity_right"):
            result = cc  # Gravity is exact-match verified — safe to trust

    # Domain 5: always let Myrion handle (complex multi-step reasoning)

    if result is None:
        # No specialist result — return None and let MyrionSolver handle it
        return None

    # Tag result with domain info
    result["domain"] = domain
    result["domain_name"] = DOMAIN_NAMES.get(domain, "Unknown")
    return result


def get_domain_stats(task: dict) -> dict:
    """
    Return diagnostic stats about a task useful for reporting.
    """
    train = task.get("train", [])
    if not train:
        return {}

    sizes_match = all(
        np.array(p["input"]).shape == np.array(p["output"]).shape
        for p in train
    )
    is_resize = is_resize_task(task)
    is_neighbor = is_object_neighbor_task(task) if not is_resize else False
    is_color_perm = is_color_permutation_task(task) if not is_resize else False
    domain = classify_domain(task)

    return {
        "domain": domain,
        "domain_name": DOMAIN_NAMES.get(domain, "Unknown"),
        "is_resize": is_resize,
        "is_neighbor_expansion": is_neighbor,
        "is_color_permutation": is_color_perm,
        "sizes_match": sizes_match,
        "n_train": len(train),
    }

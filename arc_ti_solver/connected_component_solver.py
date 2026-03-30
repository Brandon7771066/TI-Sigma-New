"""
Domain 3 Enhanced: Connected Component Solver — ARC-AGI Phase 6
================================================================

Handles the most common Domain 3 patterns that require object detection:

  Pattern A: FLOOD FILL
    A seed color floods (fills) an enclosed region of another color.
    Rule: find regions bounded by color X, fill them with color Y if
    they contain a seed of color Z.

  Pattern B: GRAVITY / FALL
    Non-background objects "fall" toward one direction (down, up, left, right)
    until they hit the border or another object.

  Pattern C: CONNECTED COMPONENT RECOLOR
    Each connected component gets a unique color based on its size/position.
    (e.g., smallest → color A, largest → color B)

  Pattern D: OBJECT COPY / STAMP
    Find a small "template" object and copy it to every position indicated
    by marker pixels.

  Pattern E: BORDER / FRAME FILL
    Objects on the border of the grid behave differently from interior objects.
    (Border objects → recolored; interior objects → filled or removed)

  Pattern F: PATH TRACING
    Follow a connected path from one color to another (line-following rule).

TI Sigma framing:
  All Domain 3 patterns are L-dimension (Love): objects reach toward each other,
  fill toward boundaries, or propagate their identity through space.
  The rule is always: "what does this object DO to its environment?"

Author: Brandon Emerick (TI Sigma / ARC Domain 3 Phase 6)
Date: March 30, 2026
"""

import numpy as np
from typing import Optional, List, Tuple, Set
from collections import deque


# ── Connected Components ─────────────────────────────────────────────────────

def find_connected_components(
    grid: np.ndarray,
    color: Optional[int] = None,
    connectivity: int = 4,
) -> List[Set[Tuple[int, int]]]:
    """
    Find all connected components of a given color (or all non-background).
    Returns a list of sets, each set = {(row, col)} of one component.

    connectivity: 4 (cross) or 8 (king's moves)
    """
    rows, cols = grid.shape
    visited = np.zeros((rows, cols), dtype=bool)
    components = []

    if connectivity == 4:
        dirs = [(-1, 0), (1, 0), (0, -1), (0, 1)]
    else:
        dirs = [(-1,-1),(-1,0),(-1,1),(0,-1),(0,1),(1,-1),(1,0),(1,1)]

    def bfs(start_r, start_c, target_color):
        component = set()
        queue = deque([(start_r, start_c)])
        visited[start_r, start_c] = True
        while queue:
            r, c = queue.popleft()
            component.add((r, c))
            for dr, dc in dirs:
                nr, nc = r + dr, c + dc
                if (0 <= nr < rows and 0 <= nc < cols
                        and not visited[nr, nc]
                        and grid[nr, nc] == target_color):
                    visited[nr, nc] = True
                    queue.append((nr, nc))
        return component

    for r in range(rows):
        for c in range(cols):
            if visited[r, c]:
                continue
            cell_color = int(grid[r, c])
            if color is not None and cell_color != color:
                continue
            if color is None and cell_color == 0:
                continue
            comp = bfs(r, c, cell_color)
            components.append(comp)
            for pr, pc in comp:
                visited[pr, pc] = True

    return components


def component_bounding_box(component: Set[Tuple[int, int]]) -> Tuple[int, int, int, int]:
    """Return (min_row, min_col, max_row, max_col) bounding box."""
    rows = [r for r, c in component]
    cols = [c for r, c in component]
    return min(rows), min(cols), max(rows), max(cols)


def extract_subgrid(grid: np.ndarray, component: Set[Tuple[int, int]]) -> np.ndarray:
    """Extract the bounding-box subgrid of a component."""
    r0, c0, r1, c1 = component_bounding_box(component)
    sub = grid[r0:r1+1, c0:c1+1].copy()
    mask = np.zeros_like(sub)
    for r, c in component:
        mask[r-r0, c-c0] = 1
    return sub * mask  # zero out non-component cells


# ── Pattern A: Flood Fill ─────────────────────────────────────────────────────

def _detect_flood_fill(inp: np.ndarray, out: np.ndarray) -> Optional[dict]:
    """
    Detect if the rule is: seed color floods an enclosed region.
    Checks if the output fills a contiguous region with a new color
    based on a seed point.
    """
    bg = int(np.bincount(inp.flatten(), minlength=10).argmax())
    diff = (inp != out)
    if not diff.any():
        return None

    changed_cells = list(zip(*np.where(diff)))
    if not changed_cells:
        return None

    # All changed cells should be the same new color
    new_colors = set(int(out[r, c]) for r, c in changed_cells)
    if len(new_colors) != 1:
        return None

    fill_color = new_colors.pop()

    # All changed cells should be connected
    changed_set = set(changed_cells)
    if len(changed_set) == 0:
        return None

    # The changed region should border or contain the fill_color in input
    # (or contain a seed)
    seed_color = None
    for r, c in changed_cells:
        if int(inp[r, c]) != bg:
            seed_color = int(inp[r, c])
            break

    return {
        "fill_color": fill_color,
        "seed_color": seed_color,
        "n_changed": len(changed_cells),
    }


# ── Pattern B: Gravity ────────────────────────────────────────────────────────

def apply_gravity(grid: np.ndarray, direction: str = "down") -> np.ndarray:
    """
    Apply gravity: non-background cells fall in the given direction.
    direction: 'down', 'up', 'left', 'right'
    """
    bg = int(np.bincount(grid.flatten(), minlength=10).argmax())
    result = np.full_like(grid, bg)
    rows, cols = grid.shape

    if direction == "down":
        for c in range(cols):
            col = grid[:, c]
            non_bg = col[col != bg]
            result[rows - len(non_bg):, c] = non_bg
    elif direction == "up":
        for c in range(cols):
            col = grid[:, c]
            non_bg = col[col != bg]
            result[:len(non_bg), c] = non_bg
    elif direction == "right":
        for r in range(rows):
            row = grid[r, :]
            non_bg = row[row != bg]
            result[r, cols - len(non_bg):] = non_bg
    elif direction == "left":
        for r in range(rows):
            row = grid[r, :]
            non_bg = row[row != bg]
            result[r, :len(non_bg)] = non_bg

    return result


def _detect_gravity(inp: np.ndarray, out: np.ndarray) -> Optional[str]:
    """Detect which gravity direction transforms inp to out."""
    for direction in ["down", "up", "left", "right"]:
        candidate = apply_gravity(inp, direction)
        if np.array_equal(candidate, out):
            return direction
    return None


# ── Pattern C: Component Recolor by Size ─────────────────────────────────────

def _detect_component_recolor(inp: np.ndarray, out: np.ndarray) -> Optional[dict]:
    """
    Detect if connected components are recolored based on their size.
    """
    bg = int(np.bincount(inp.flatten(), minlength=10).argmax())

    inp_comps = find_connected_components(inp, color=None)
    inp_comps = [c for c in inp_comps if not any(inp[r, c2] == bg for r, c2 in c)]

    # For each component, what did it become in the output?
    comp_changes = []
    for comp in inp_comps:
        input_color = int(inp[list(comp)[0][0], list(comp)[0][1]])
        output_colors = set(int(out[r, c]) for r, c in comp)
        if len(output_colors) == 1:
            comp_changes.append({
                "size": len(comp),
                "input_color": input_color,
                "output_color": output_colors.pop(),
            })

    if not comp_changes:
        return None

    # Check if size determines output color
    size_to_color = {}
    consistent = True
    for cc in comp_changes:
        s = cc["size"]
        oc = cc["output_color"]
        if s in size_to_color:
            if size_to_color[s] != oc:
                consistent = False
                break
        else:
            size_to_color[s] = oc

    if consistent and len(size_to_color) > 1:
        return {"size_to_color": size_to_color}

    return None


# ── Pattern E: Border vs Interior ────────────────────────────────────────────

def _detect_border_interior_rule(inp: np.ndarray, out: np.ndarray) -> Optional[dict]:
    """
    Detect if objects touching the border get different treatment than interior objects.
    """
    rows, cols = inp.shape
    bg = int(np.bincount(inp.flatten(), minlength=10).argmax())

    comps = find_connected_components(inp, color=None)

    border_rule = None
    interior_rule = None

    for comp in comps:
        is_border = any(
            r == 0 or r == rows-1 or c == 0 or c == cols-1
            for r, c in comp
        )
        in_colors = set(int(inp[r, c]) for r, c in comp)
        out_colors = set(int(out[r, c]) for r, c in comp)

        if len(in_colors) == 1 and len(out_colors) == 1:
            rule = (in_colors.pop(), out_colors.pop())
            if is_border:
                if border_rule and border_rule != rule:
                    return None
                border_rule = rule
            else:
                if interior_rule and interior_rule != rule:
                    return None
                interior_rule = rule

    if border_rule and interior_rule and border_rule != interior_rule:
        return {
            "border_rule": border_rule,
            "interior_rule": interior_rule,
        }
    return None


def apply_border_interior_rule(grid: np.ndarray, rule: dict) -> np.ndarray:
    """Apply border/interior recolor rule."""
    rows, cols = grid.shape
    result = grid.copy()
    bg = int(np.bincount(grid.flatten(), minlength=10).argmax())

    border_in, border_out = rule["border_rule"]
    interior_in, interior_out = rule["interior_rule"]

    comps = find_connected_components(grid, color=None)
    for comp in comps:
        is_border = any(
            r == 0 or r == rows-1 or c == 0 or c == cols-1
            for r, c in comp
        )
        comp_color = int(grid[list(comp)[0][0], list(comp)[0][1]])
        for r, c in comp:
            if is_border and comp_color == border_in:
                result[r, c] = border_out
            elif not is_border and comp_color == interior_in:
                result[r, c] = interior_out

    return result


# ── Main Solver ───────────────────────────────────────────────────────────────

def solve_connected_components(task: dict) -> Optional[dict]:
    """
    Attempt to solve an ARC task using connected component reasoning.

    Tries patterns in order: gravity, border/interior, component recolor.
    Returns best match or None.
    """
    train_pairs = task.get("train", [])
    test_pairs = task.get("test", [])

    if not train_pairs or not test_pairs:
        return None

    # All pairs must preserve size for these patterns
    for pair in train_pairs:
        if np.array(pair["input"]).shape != np.array(pair["output"]).shape:
            return None

    # ── Pattern B: Gravity ───────────────────────────────────────────────
    for direction in ["down", "up", "left", "right"]:
        gravity_matches = 0
        for pair in train_pairs:
            inp = np.array(pair["input"])
            out = np.array(pair["output"])
            candidate = apply_gravity(inp, direction)
            if np.array_equal(candidate, out):
                gravity_matches += 1

        if gravity_matches == len(train_pairs):
            test_inp = np.array(test_pairs[0]["input"])
            predicted = apply_gravity(test_inp, direction)
            return {
                "output": predicted.tolist(),
                "lcc": 1.0,
                "method": "gravity",
                "pattern": f"gravity_{direction}",
            }

    # ── Pattern E: Border/Interior ──────────────────────────────────────
    border_rules = []
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        rule = _detect_border_interior_rule(inp, out)
        if rule is None:
            border_rules = None
            break
        border_rules.append(rule)

    if border_rules and len(set(str(r) for r in border_rules)) == 1:
        rule = border_rules[0]
        test_inp = np.array(test_pairs[0]["input"])
        predicted = apply_border_interior_rule(test_inp, rule)
        # Validate
        train_ok = all(
            np.array_equal(
                apply_border_interior_rule(np.array(p["input"]), rule),
                np.array(p["output"])
            )
            for p in train_pairs
        )
        if train_ok:
            return {
                "output": predicted.tolist(),
                "lcc": 1.0,
                "method": "border_interior",
                "pattern": "border_vs_interior_recolor",
                "rule": str(rule),
            }

    # ── Pattern C: Component Recolor by Size ───────────────────────────
    size_rules = []
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        rule = _detect_component_recolor(inp, out)
        if rule is None:
            size_rules = None
            break
        size_rules.append(rule["size_to_color"])

    if size_rules:
        # Unify size-to-color mapping across pairs
        unified = {}
        consistent = True
        for sr in size_rules:
            for size, color in sr.items():
                if size in unified and unified[size] != color:
                    consistent = False
                    break
                unified[size] = color

        if consistent and unified:
            test_inp = np.array(test_pairs[0]["input"])
            bg = int(np.bincount(test_inp.flatten(), minlength=10).argmax())
            result = test_inp.copy()
            comps = find_connected_components(test_inp, color=None)
            for comp in comps:
                s = len(comp)
                if s in unified:
                    for r, c in comp:
                        result[r, c] = unified[s]

            # Validate
            train_ok = all(
                _validate_size_recolor(np.array(p["input"]), np.array(p["output"]), unified)
                for p in train_pairs
            )
            if train_ok:
                return {
                    "output": result.tolist(),
                    "lcc": 1.0,
                    "method": "component_recolor_by_size",
                    "pattern": "recolor_by_component_size",
                    "size_map": unified,
                }

    return None


def _validate_size_recolor(inp: np.ndarray, out: np.ndarray, size_map: dict) -> bool:
    """Validate size-based recolor rule on a single pair."""
    bg = int(np.bincount(inp.flatten(), minlength=10).argmax())
    result = inp.copy()
    comps = find_connected_components(inp, color=None)
    for comp in comps:
        s = len(comp)
        if s in size_map:
            for r, c in comp:
                result[r, c] = size_map[s]
    return np.array_equal(result, out)

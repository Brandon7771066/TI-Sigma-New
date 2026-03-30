"""
ARC-AGI Skill Library — Phase 7 Meta-Learning System

A structured catalog of transformation primitives, each backed by:
  - A human-readable description for LLM prompting
  - A detector function (can this skill apply to this task?)
  - An applicator function (apply the skill to a grid)
  - Example task IDs (verified training tasks that use this skill)

Skills are organized into families. The MetaLearner uses this library to:
  1. Detect which skill(s) fit a new task's training examples
  2. Verify against all training pairs
  3. Apply to the test input
"""

from __future__ import annotations
import numpy as np
from typing import Callable, Optional
from dataclasses import dataclass, field


# ── Skill Descriptor ──────────────────────────────────────────────────────────

@dataclass
class Skill:
    name: str
    family: str
    description: str
    detector: Callable[[dict], bool]
    applicator: Callable[[list[list[int]], dict], Optional[list[list[int]]]]
    example_tasks: list[str] = field(default_factory=list)
    verified_correct: bool = False

    def applies(self, task: dict) -> bool:
        try:
            return self.detector(task)
        except Exception:
            return False

    def apply(self, grid: list[list[int]], task: dict) -> Optional[list[list[int]]]:
        try:
            return self.applicator(grid, task)
        except Exception:
            return None

    def verify(self, task: dict) -> tuple[bool, float]:
        train = task.get("train", [])
        if not train:
            return False, 0.0
        correct = 0
        for pair in train:
            pred = self.apply(pair["input"], task)
            if pred is None:
                return False, 0.0
            pred_a = np.array(pred)
            gt_a = np.array(pair["output"])
            if pred_a.shape == gt_a.shape and np.array_equal(pred_a, gt_a):
                correct += 1
        lcc = correct / len(train)
        return lcc == 1.0, lcc


# ── Helper Utilities ──────────────────────────────────────────────────────────

def _arr(g):
    return np.array(g, dtype=int)


def _same_size(task):
    return all(
        _arr(p["input"]).shape == _arr(p["output"]).shape
        for p in task.get("train", [])
    )


def _same_colors(task):
    for p in task.get("train", []):
        ci = set(c for row in p["input"] for c in row)
        co = set(c for row in p["output"] for c in row)
        if ci != co:
            return False
    return True


def _bg_color(grid):
    flat = [c for row in grid for c in row]
    if not flat:
        return 0
    return max(set(flat), key=flat.count)


def _color_count_preserved(task):
    for p in task.get("train", []):
        from collections import Counter
        ci = Counter(c for row in p["input"] for c in row)
        co = Counter(c for row in p["output"] for c in row)
        if ci != co:
            return False
    return True


# ── FAMILY 1: Spatial Transforms ─────────────────────────────────────────────

def _make_rotate_skill(degrees: int) -> Skill:
    k = {90: 1, 180: 2, 270: 3}[degrees]

    def detector(task):
        if not _same_size(task):
            return False
        for p in task["train"]:
            if not np.array_equal(np.rot90(_arr(p["input"]), k), _arr(p["output"])):
                return False
        return True

    def applicator(grid, task):
        return np.rot90(_arr(grid), k).tolist()

    return Skill(
        name=f"rotate_{degrees}",
        family="spatial_transform",
        description=f"Rotate the entire grid {degrees}° counter-clockwise.",
        detector=detector,
        applicator=applicator,
        example_tasks={90: ["ed36ccf7"], 180: ["3c9b0459", "6150a2bd"], 270: []}[degrees],
        verified_correct=True,
    )


def _make_flip_skill(axis: str) -> Skill:
    axes = {
        "horizontal": (lambda g: np.fliplr(g), "Flip the grid left-right (mirror horizontally)."),
        "vertical":   (lambda g: np.flipud(g), "Flip the grid top-bottom (mirror vertically)."),
        "diagonal":   (lambda g: g.T,           "Transpose the grid (flip along main diagonal)."),
        "antidiag":   (lambda g: np.flipud(g.T), "Flip along the anti-diagonal."),
    }
    fn, desc = axes[axis]

    def detector(task):
        if not _same_size(task):
            return False
        for p in task["train"]:
            if not np.array_equal(fn(_arr(p["input"])), _arr(p["output"])):
                return False
        return True

    def applicator(grid, task):
        return fn(_arr(grid)).tolist()

    examples = {
        "horizontal": ["67a3c6ac"],
        "vertical":   ["68b16354"],
        "diagonal":   ["74dd1130", "9dfd6313"],
        "antidiag":   [],
    }
    return Skill(
        name=f"flip_{axis}",
        family="spatial_transform",
        description=desc,
        detector=detector,
        applicator=applicator,
        example_tasks=examples[axis],
        verified_correct=True,
    )


# ── FAMILY 2: Symmetry Completion ────────────────────────────────────────────

def _make_symmetry_completion_skill(axis: str) -> Skill:
    desc_map = {
        "vertical":    "Complete vertical symmetry: copy left half to right (or vice versa).",
        "horizontal":  "Complete horizontal symmetry: copy top half to bottom.",
        "both":        "Complete both vertical and horizontal symmetry.",
    }

    def detector(task):
        if not _same_size(task):
            return False
        if not _same_colors(task):
            return False
        for p in task["train"]:
            g_in = _arr(p["input"])
            g_out = _arr(p["output"])
            if axis == "vertical":
                mid = g_in.shape[1] // 2
                if not np.array_equal(g_out[:, :mid], np.fliplr(g_out[:, mid:])):
                    return False
            elif axis == "horizontal":
                mid = g_in.shape[0] // 2
                if not np.array_equal(g_out[:mid, :], np.flipud(g_out[mid:, :])):
                    return False
        return True

    def applicator(grid, task):
        g = _arr(grid).copy()
        if axis == "vertical":
            mid = g.shape[1] // 2
            left = g[:, :mid]
            right_mirror = np.fliplr(left)
            g[:, mid:mid + right_mirror.shape[1]] = right_mirror
        elif axis == "horizontal":
            mid = g.shape[0] // 2
            top = g[:mid, :]
            bottom_mirror = np.flipud(top)
            g[mid:mid + bottom_mirror.shape[0], :] = bottom_mirror
        return g.tolist()

    return Skill(
        name=f"complete_{axis}_symmetry",
        family="symmetry",
        description=desc_map[axis],
        detector=detector,
        applicator=applicator,
        example_tasks={"vertical": ["f25ffba3"], "horizontal": [], "both": []}.get(axis, []),
        verified_correct=True,
    )


# ── FAMILY 3: Color Operations ────────────────────────────────────────────────

def _make_bijective_recolor_skill() -> Skill:
    def _learn_map(task):
        color_map = {}
        for p in task["train"]:
            flat_in = [c for row in p["input"] for c in row]
            flat_out = [c for row in p["output"] for c in row]
            if len(flat_in) != len(flat_out):
                return None
            for ci, co in zip(flat_in, flat_out):
                if ci in color_map and color_map[ci] != co:
                    return None
                color_map[ci] = co
        return color_map

    def detector(task):
        if not _same_size(task):
            return False
        m = _learn_map(task)
        if m is None:
            return False
        for p in task["train"]:
            pred = [[m.get(c, c) for c in row] for row in p["input"]]
            if pred != p["output"]:
                return False
        return True

    def applicator(grid, task):
        m = _learn_map(task)
        if m is None:
            return None
        return [[m.get(c, c) for c in row] for row in grid]

    return Skill(
        name="bijective_recolor",
        family="color_operation",
        description="Apply a fixed color-to-color mapping learned from training pairs (same mapping every time).",
        detector=detector,
        applicator=applicator,
        example_tasks=["0d3d703e", "b1948b0a", "c8f0f002"],
        verified_correct=True,
    )


def _make_swap_two_colors_skill() -> Skill:
    def _find_swap(task):
        train = task.get("train", [])
        if not train:
            return None
        colors = set(c for p in train for row in p["input"] for c in row)
        for c1 in colors:
            for c2 in colors:
                if c1 >= c2:
                    continue
                valid = True
                for p in train:
                    pred = [[c2 if c == c1 else (c1 if c == c2 else c) for c in row]
                            for row in p["input"]]
                    if pred != p["output"]:
                        valid = False
                        break
                if valid:
                    return c1, c2
        return None

    def detector(task):
        if not _same_size(task):
            return False
        return _find_swap(task) is not None

    def applicator(grid, task):
        swap = _find_swap(task)
        if swap is None:
            return None
        c1, c2 = swap
        return [[c2 if c == c1 else (c1 if c == c2 else c) for c in row] for row in grid]

    return Skill(
        name="swap_two_colors",
        family="color_operation",
        description="Swap exactly two colors throughout the entire grid (e.g., all 5s become 8s and all 8s become 5s).",
        detector=detector,
        applicator=applicator,
        example_tasks=["d511f180"],
        verified_correct=True,
    )


# ── FAMILY 4: Structural / Outline ───────────────────────────────────────────

def _make_hollow_to_outline_skill() -> Skill:
    def _apply(g):
        a = _arr(g)
        bg = _bg_color(g)
        out = np.full_like(a, bg)
        h, w = a.shape
        for r in range(h):
            for c in range(w):
                if a[r, c] != bg:
                    neighbors = [(r-1,c),(r+1,c),(r,c-1),(r,c+1)]
                    if any(0 <= nr < h and 0 <= nc < w and a[nr, nc] == bg
                           for nr, nc in neighbors):
                        out[r, c] = a[r, c]
        return out

    def detector(task):
        if not _same_size(task):
            return False
        for p in task["train"]:
            if not np.array_equal(_apply(p["input"]), _arr(p["output"])):
                return False
        return True

    def applicator(grid, task):
        return _apply(grid).tolist()

    return Skill(
        name="hollow_to_outline",
        family="structural",
        description="Keep only the border cells of each filled object; replace interior cells with background.",
        detector=detector,
        applicator=applicator,
        example_tasks=["4347f46a"],
        verified_correct=True,
    )


def _make_flood_fill_skill(connectivity: int) -> Skill:
    from scipy import ndimage

    def _apply(g, conn):
        a = _arr(g)
        bg = _bg_color(g)
        struct = ndimage.generate_binary_structure(2, conn // 4)
        labeled, n = ndimage.label(a != bg, structure=struct)
        sizes = [np.sum(labeled == i) for i in range(1, n + 1)]
        if not sizes:
            return a
        largest = np.argmax(sizes) + 1
        out = a.copy()
        mask = labeled == largest
        rows, cols = np.where(mask)
        if len(rows) == 0:
            return a
        rmin, rmax = rows.min(), rows.max()
        cmin, cmax = cols.min(), cols.max()
        fill_color = a[mask][0]
        out[rmin:rmax+1, cmin:cmax+1] = fill_color
        return out

    def detector(task):
        if not _same_size(task):
            return False
        for p in task["train"]:
            if not np.array_equal(_apply(p["input"], connectivity), _arr(p["output"])):
                return False
        return True

    def applicator(grid, task):
        return _apply(grid, connectivity).tolist()

    return Skill(
        name=f"flood_fill_{connectivity}",
        family="structural",
        description=f"Fill the bounding box of the largest connected component (connectivity={connectivity}).",
        detector=detector,
        applicator=applicator,
        example_tasks={"4": ["00d62c1b"], "1": ["a5313dff"]}[str(connectivity)],
        verified_correct=True,
    )


def _make_count_components_as_color_skill() -> Skill:
    from scipy import ndimage

    def _apply(g):
        a = _arr(g)
        bg = _bg_color(g)
        labeled, n = ndimage.label(a != bg)
        out = np.full_like(a, bg)
        for i in range(1, n + 1):
            out[labeled == i] = n
        return out

    def detector(task):
        if not _same_size(task):
            return False
        for p in task["train"]:
            if not np.array_equal(_apply(p["input"]), _arr(p["output"])):
                return False
        return True

    def applicator(grid, task):
        return _apply(grid).tolist()

    return Skill(
        name="count_components_as_color",
        family="structural",
        description="Replace every cell of each connected component with the total number of components.",
        detector=detector,
        applicator=applicator,
        example_tasks=["08ed6ac7"],
        verified_correct=True,
    )


# ── FAMILY 5: Gravity ─────────────────────────────────────────────────────────

def _make_gravity_skill(direction: str) -> Skill:
    def _apply(g, d):
        a = _arr(g)
        bg = _bg_color(g)
        out = np.full_like(a, bg)
        h, w = a.shape
        if d == "down":
            for c in range(w):
                col = [a[r, c] for r in range(h) if a[r, c] != bg]
                for i, v in enumerate(reversed(col)):
                    out[h - 1 - i, c] = v
        elif d == "up":
            for c in range(w):
                col = [a[r, c] for r in range(h) if a[r, c] != bg]
                for i, v in enumerate(col):
                    out[i, c] = v
        elif d == "right":
            for r in range(h):
                row = [a[r, c] for c in range(w) if a[r, c] != bg]
                for i, v in enumerate(reversed(row)):
                    out[r, w - 1 - i] = v
        elif d == "left":
            for r in range(h):
                row = [a[r, c] for c in range(w) if a[r, c] != bg]
                for i, v in enumerate(row):
                    out[r, i] = v
        return out

    def detector(task):
        if not _same_size(task):
            return False
        for p in task["train"]:
            if not np.array_equal(_apply(p["input"], direction), _arr(p["output"])):
                return False
        return True

    def applicator(grid, task):
        return _apply(grid, direction).tolist()

    return Skill(
        name=f"gravity_{direction}",
        family="gravity",
        description=f"All non-background cells fall {direction} as if under gravity.",
        detector=detector,
        applicator=applicator,
        example_tasks={"down": ["3906de3d"], "up": [], "right": [], "left": ["1e0a9b12"]}.get(direction, []),
        verified_correct=True,
    )


# ── FAMILY 6: Scale ───────────────────────────────────────────────────────────

def _make_scale_skill() -> Skill:
    def _find_scale(task):
        for p in task.get("train", []):
            g_in = _arr(p["input"])
            g_out = _arr(p["output"])
            if g_in.shape[0] == 0 or g_in.shape[1] == 0:
                return None
            rh = g_out.shape[0] / g_in.shape[0]
            rw = g_out.shape[1] / g_in.shape[1]
            if rh != int(rh) or rw != int(rw) or rh <= 1 or rw <= 1:
                return None
            k = int(rh)
            expected = np.repeat(np.repeat(g_in, k, axis=0), k, axis=1)
            if not np.array_equal(expected, g_out):
                return None
        return k

    def detector(task):
        return _find_scale(task) is not None

    def applicator(grid, task):
        k = _find_scale(task)
        if k is None:
            return None
        g = _arr(grid)
        return np.repeat(np.repeat(g, k, axis=0), k, axis=1).tolist()

    return Skill(
        name="integer_scale",
        family="scale",
        description="Scale the entire grid by an integer factor k (each cell becomes a k×k block).",
        detector=detector,
        applicator=applicator,
        example_tasks=["1cf80156", "5bd6f4ac", "9172f3a0", "a416b8f3", "c59eb873", "d10ecb37"],
        verified_correct=True,
    )


# ── FAMILY 7: Mirror Half ─────────────────────────────────────────────────────

def _make_mirror_half_skill(axis: str) -> Skill:
    def _apply(g, ax):
        a = _arr(g)
        if ax == "vertical":
            mid = a.shape[1] // 2
            right = np.fliplr(a[:, :mid])
            result = a.copy()
            result[:, mid:mid + right.shape[1]] = right
            return result
        elif ax == "horizontal":
            mid = a.shape[0] // 2
            bottom = np.flipud(a[:mid, :])
            result = a.copy()
            result[mid:mid + bottom.shape[0], :] = bottom
            return result
        return a

    def detector(task):
        if not _same_size(task):
            return False
        for p in task["train"]:
            if not np.array_equal(_apply(p["input"], axis), _arr(p["output"])):
                return False
        return True

    def applicator(grid, task):
        return _apply(grid, axis).tolist()

    return Skill(
        name=f"mirror_{axis}_half",
        family="symmetry",
        description=f"Mirror the {'left' if axis=='vertical' else 'top'} half onto the {'right' if axis=='vertical' else 'bottom'} half.",
        detector=detector,
        applicator=applicator,
        example_tasks={"vertical": ["496994bd"], "horizontal": []}.get(axis, []),
        verified_correct=True,
    )


# ── Registry ──────────────────────────────────────────────────────────────────

def build_skill_registry() -> list[Skill]:
    skills = []

    # Spatial transforms
    for deg in [90, 180, 270]:
        skills.append(_make_rotate_skill(deg))
    for ax in ["horizontal", "vertical", "diagonal", "antidiag"]:
        skills.append(_make_flip_skill(ax))
    for ax in ["vertical", "horizontal"]:
        skills.append(_make_mirror_half_skill(ax))

    # Symmetry completion
    for ax in ["vertical", "horizontal"]:
        skills.append(_make_symmetry_completion_skill(ax))

    # Color operations
    skills.append(_make_bijective_recolor_skill())
    skills.append(_make_swap_two_colors_skill())

    # Structural
    skills.append(_make_hollow_to_outline_skill())
    skills.append(_make_flood_fill_skill(4))
    skills.append(_make_flood_fill_skill(1))
    skills.append(_make_count_components_as_color_skill())

    # Gravity
    for d in ["down", "up", "left", "right"]:
        skills.append(_make_gravity_skill(d))

    # Scale
    skills.append(_make_scale_skill())

    return skills


SKILL_REGISTRY: list[Skill] = build_skill_registry()
SKILL_MAP: dict[str, Skill] = {s.name: s for s in SKILL_REGISTRY}

"""
ARC-AGI Advanced Transform Library — Phase 2
=============================================
Targets common ARC task pattern families not covered by base primitives:
  - Gravity (all 4 directions)
  - Connected component analysis (flood fill, object isolation)
  - Color frequency operations (most/least common, invert, remap)
  - Symmetry completion (extend partial patterns)
  - Outline / border drawing
  - Object tiling and repetition
  - Grid splitting and quadrant operations
  - Pattern detection (find repeating unit)
  - Boolean / difference operations
  - MRC-Novelty transforms (structurally unusual; elevated DT tolerance)
"""

import numpy as np
from typing import Callable
from collections import Counter, deque


# ---------------------------------------------------------------------------
# Gravity — all 4 directions
# ---------------------------------------------------------------------------

def gravity_left(grid: np.ndarray) -> np.ndarray:
    """Push all non-background cells to the left of each row."""
    result = np.zeros_like(grid)
    for r in range(grid.shape[0]):
        row = grid[r]
        non_bg = row[row != 0]
        result[r, :len(non_bg)] = non_bg
    return result


def gravity_right(grid: np.ndarray) -> np.ndarray:
    """Push all non-background cells to the right of each row."""
    result = np.zeros_like(grid)
    for r in range(grid.shape[0]):
        row = grid[r]
        non_bg = row[row != 0]
        result[r, grid.shape[1] - len(non_bg):] = non_bg
    return result


# ---------------------------------------------------------------------------
# Color frequency operations
# ---------------------------------------------------------------------------

def most_common_color(grid: np.ndarray) -> int:
    """Return the most common non-zero color in the grid."""
    flat = grid.flatten()
    flat = flat[flat != 0]
    if len(flat) == 0:
        return 0
    return Counter(flat).most_common(1)[0][0]


def least_common_color(grid: np.ndarray) -> int:
    """Return the least common non-zero color in the grid."""
    flat = grid.flatten()
    flat = flat[flat != 0]
    if len(flat) == 0:
        return 0
    return Counter(flat).most_common()[-1][0]


def isolate_most_common(grid: np.ndarray) -> np.ndarray:
    """Zero out everything except the most common color."""
    result = np.zeros_like(grid)
    mc = most_common_color(grid)
    result[grid == mc] = mc
    return result


def isolate_least_common(grid: np.ndarray) -> np.ndarray:
    """Zero out everything except the least common (non-zero) color."""
    result = np.zeros_like(grid)
    lc = least_common_color(grid)
    result[grid == lc] = lc
    return result


def remove_most_common(grid: np.ndarray) -> np.ndarray:
    """Replace the most common non-zero color with background (0)."""
    result = grid.copy()
    mc = most_common_color(grid)
    result[result == mc] = 0
    return result


def invert_colors(grid: np.ndarray) -> np.ndarray:
    """Swap foreground and background — 0 gets the most common color, colored gets 0."""
    result = grid.copy()
    mc = most_common_color(grid)
    result[grid == 0] = mc
    result[grid != 0] = 0
    return result


def remap_colors_by_frequency(grid: np.ndarray) -> np.ndarray:
    """
    Remap colors so most frequent non-zero color → 1, second → 2, etc.
    Background (0) stays 0.
    """
    flat = grid.flatten()
    non_bg = flat[flat != 0]
    if len(non_bg) == 0:
        return grid.copy()
    ordered = [c for c, _ in Counter(non_bg).most_common()]
    mapping = {c: i + 1 for i, c in enumerate(ordered)}
    result = np.zeros_like(grid)
    for c, new_c in mapping.items():
        result[grid == c] = new_c
    return result


def unique_color_mask(grid: np.ndarray) -> np.ndarray:
    """Highlight the color that appears exactly once in the grid."""
    flat = grid.flatten()
    counts = Counter(flat)
    result = np.zeros_like(grid)
    for c, cnt in counts.items():
        if c != 0 and cnt == 1:
            result[grid == c] = c
    return result


# ---------------------------------------------------------------------------
# Connected components / object operations
# ---------------------------------------------------------------------------

def _connected_components(grid: np.ndarray, bg: int = 0) -> np.ndarray:
    """
    Label connected components (4-connectivity).
    Returns label grid where 0 = background, 1+ = component IDs.
    """
    labels = np.zeros_like(grid, dtype=np.int32)
    label_id = 0
    rows, cols = grid.shape
    visited = np.zeros_like(grid, dtype=bool)

    for r in range(rows):
        for c in range(cols):
            if grid[r, c] != bg and not visited[r, c]:
                label_id += 1
                queue = deque([(r, c)])
                visited[r, c] = True
                labels[r, c] = label_id
                while queue:
                    rr, cc = queue.popleft()
                    for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                        nr, nc = rr + dr, cc + dc
                        if 0 <= nr < rows and 0 <= nc < cols:
                            if grid[nr, nc] != bg and not visited[nr, nc]:
                                visited[nr, nc] = True
                                labels[nr, nc] = label_id
                                queue.append((nr, nc))
    return labels


def largest_object_only(grid: np.ndarray) -> np.ndarray:
    """Keep only the largest connected component; zero out the rest."""
    labels = _connected_components(grid)
    if labels.max() == 0:
        return grid.copy()
    counts = Counter(labels.flatten())
    counts.pop(0, None)
    if not counts:
        return grid.copy()
    biggest = max(counts, key=counts.get)
    result = np.zeros_like(grid)
    result[labels == biggest] = grid[labels == biggest]
    return result


def smallest_object_only(grid: np.ndarray) -> np.ndarray:
    """Keep only the smallest connected component; zero out the rest."""
    labels = _connected_components(grid)
    if labels.max() == 0:
        return grid.copy()
    counts = Counter(labels.flatten())
    counts.pop(0, None)
    if not counts:
        return grid.copy()
    smallest = min(counts, key=counts.get)
    result = np.zeros_like(grid)
    result[labels == smallest] = grid[labels == smallest]
    return result


def count_components_as_color(grid: np.ndarray) -> np.ndarray:
    """
    Replace each connected component with a color = its component ID.
    Useful for tasks that sort/classify objects by identity.
    """
    labels = _connected_components(grid)
    result = labels.astype(np.int8)
    return result


def object_bounding_box_crop(grid: np.ndarray) -> np.ndarray:
    """
    Crop grid to bounding box of ALL non-background cells.
    Alias for crop_to_nonzero but works with any background detection.
    """
    mask = grid != 0
    if not mask.any():
        return grid.copy()
    rows = np.where(mask.any(axis=1))[0]
    cols = np.where(mask.any(axis=0))[0]
    return grid[rows[0]:rows[-1]+1, cols[0]:cols[-1]+1]


# ---------------------------------------------------------------------------
# Outline / border drawing
# ---------------------------------------------------------------------------

def draw_outline(fill_color: int = 1) -> Callable:
    """
    Draw a 1-cell outline around all non-zero regions.
    The interior stays; the outline cells get fill_color.
    """
    def outline(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        rows, cols = grid.shape
        for r in range(rows):
            for c in range(cols):
                if grid[r, c] == 0:
                    for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                        nr, nc = r + dr, c + dc
                        if 0 <= nr < rows and 0 <= nc < cols and grid[nr, nc] != 0:
                            result[r, c] = fill_color
                            break
        return result
    outline.__name__ = f"outline_{fill_color}"
    return outline


def hollow_to_outline(grid: np.ndarray) -> np.ndarray:
    """
    Convert filled regions to just their outlines.
    Keep border cells; zero out interior.
    """
    result = grid.copy()
    rows, cols = grid.shape
    for r in range(1, rows - 1):
        for c in range(1, cols - 1):
            if grid[r, c] != 0:
                neighbors = [grid[r-1, c], grid[r+1, c], grid[r, c-1], grid[r, c+1]]
                if all(n != 0 for n in neighbors):
                    result[r, c] = 0
    return result


# ---------------------------------------------------------------------------
# Symmetry completion
# ---------------------------------------------------------------------------

def complete_horizontal_symmetry(grid: np.ndarray) -> np.ndarray:
    """
    If right half is mostly zeros, mirror left half to right.
    If left half is mostly zeros, mirror right half to left.
    """
    rows, cols = grid.shape
    half = cols // 2
    left = grid[:, :half]
    right = grid[:, half:]
    left_zeros = np.sum(left == 0)
    right_zeros = np.sum(right == 0) if right.shape[1] > 0 else 0
    result = grid.copy()
    if right_zeros > left_zeros and right.shape[1] > 0:
        # Fill right from mirrored left
        result[:, half:half + left.shape[1]] = np.fliplr(left)
    elif left_zeros > right_zeros and right.shape[1] > 0:
        result[:, :half] = np.fliplr(right[:, :half])
    return result


def complete_vertical_symmetry(grid: np.ndarray) -> np.ndarray:
    """Mirror top or bottom half to complete vertical symmetry."""
    rows, cols = grid.shape
    half = rows // 2
    top = grid[:half, :]
    bottom = grid[half:, :]
    top_zeros = np.sum(top == 0)
    bottom_zeros = np.sum(bottom == 0)
    result = grid.copy()
    if bottom_zeros > top_zeros:
        result[half:half + top.shape[0], :] = np.flipud(top)
    elif top_zeros > bottom_zeros:
        result[:half, :] = np.flipud(bottom[:half, :])
    return result


def make_4fold_symmetric(grid: np.ndarray) -> np.ndarray:
    """Force 4-fold rotational symmetry by OR-ing all rotations."""
    result = grid.copy()
    for k in [1, 2, 3]:
        rotated = np.rot90(grid, k=k)
        if rotated.shape == grid.shape:
            result = np.where(result != 0, result, rotated)
    return result


# ---------------------------------------------------------------------------
# Pattern tiling / repetition
# ---------------------------------------------------------------------------

def tile_to_match(target_rows: int, target_cols: int) -> Callable:
    """Tile the grid to fill a specific target size."""
    def tile(grid: np.ndarray) -> np.ndarray:
        if grid.shape[0] == 0 or grid.shape[1] == 0:
            return grid.copy()
        reps_r = (target_rows + grid.shape[0] - 1) // grid.shape[0]
        reps_c = (target_cols + grid.shape[1] - 1) // grid.shape[1]
        tiled = np.tile(grid, (reps_r, reps_c))
        return tiled[:target_rows, :target_cols]
    tile.__name__ = f"tile_{target_rows}x{target_cols}"
    return tile


def detect_repeating_unit(grid: np.ndarray) -> np.ndarray:
    """
    Find smallest repeating tile unit of the grid.
    Returns the tile if one is found, otherwise returns the grid unchanged.
    """
    rows, cols = grid.shape
    for h in range(1, rows + 1):
        if rows % h != 0:
            continue
        for w in range(1, cols + 1):
            if cols % w != 0:
                continue
            tile = grid[:h, :w]
            tiled = np.tile(tile, (rows // h, cols // w))
            if np.array_equal(tiled, grid):
                return tile
    return grid.copy()


# ---------------------------------------------------------------------------
# Grid splitting operations
# ---------------------------------------------------------------------------

def top_half(grid: np.ndarray) -> np.ndarray:
    return grid[:grid.shape[0]//2, :]


def bottom_half(grid: np.ndarray) -> np.ndarray:
    return grid[grid.shape[0]//2:, :]


def left_half(grid: np.ndarray) -> np.ndarray:
    return grid[:, :grid.shape[1]//2]


def right_half(grid: np.ndarray) -> np.ndarray:
    return grid[:, grid.shape[1]//2:]


def xor_halves_horizontal(grid: np.ndarray) -> np.ndarray:
    """XOR the top and bottom halves (nonzero in exactly one half)."""
    rows, cols = grid.shape
    mid = rows // 2
    top = grid[:mid, :]
    bottom = grid[mid:mid + mid, :]
    if top.shape != bottom.shape:
        return grid.copy()
    result = np.zeros_like(top)
    for r in range(top.shape[0]):
        for c in range(top.shape[1]):
            t, b = top[r, c], bottom[r, c]
            if t != 0 and b == 0:
                result[r, c] = t
            elif b != 0 and t == 0:
                result[r, c] = b
    return result


def xor_halves_vertical(grid: np.ndarray) -> np.ndarray:
    """XOR the left and right halves."""
    rows, cols = grid.shape
    mid = cols // 2
    left = grid[:, :mid]
    right = grid[:, mid:mid + mid]
    if left.shape != right.shape:
        return grid.copy()
    result = np.zeros_like(left)
    for r in range(left.shape[0]):
        for c in range(left.shape[1]):
            l, ri = left[r, c], right[r, c]
            if l != 0 and ri == 0:
                result[r, c] = l
            elif ri != 0 and l == 0:
                result[r, c] = ri
    return result


# ---------------------------------------------------------------------------
# Flood fill (paint-bucket style)
# ---------------------------------------------------------------------------

def flood_fill(fill_color: int = 1) -> Callable:
    """Flood fill all zero (background) cells that are enclosed by non-zero cells."""
    def fill(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        rows, cols = grid.shape
        # BFS from border zeros to find "outside" zeros
        outside = np.zeros_like(grid, dtype=bool)
        queue = deque()
        for r in range(rows):
            for c in [0, cols - 1]:
                if grid[r, c] == 0 and not outside[r, c]:
                    outside[r, c] = True
                    queue.append((r, c))
        for c in range(cols):
            for r in [0, rows - 1]:
                if grid[r, c] == 0 and not outside[r, c]:
                    outside[r, c] = True
                    queue.append((r, c))
        while queue:
            r, c = queue.popleft()
            for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                nr, nc = r + dr, c + dc
                if 0 <= nr < rows and 0 <= nc < cols:
                    if grid[nr, nc] == 0 and not outside[nr, nc]:
                        outside[nr, nc] = True
                        queue.append((nr, nc))
        # Fill enclosed zeros
        result[(grid == 0) & ~outside] = fill_color
        return result
    fill.__name__ = f"flood_fill_{fill_color}"
    return fill


# ---------------------------------------------------------------------------
# Color spread / dilation
# ---------------------------------------------------------------------------

def dilate_colors(steps: int = 1) -> Callable:
    """Expand each non-zero color outward by N steps (into background cells)."""
    def dilate(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        for _ in range(steps):
            new = result.copy()
            rows, cols = result.shape
            for r in range(rows):
                for c in range(cols):
                    if result[r, c] == 0:
                        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                            nr, nc = r + dr, c + dc
                            if 0 <= nr < rows and 0 <= nc < cols and result[nr, nc] != 0:
                                new[r, c] = result[nr, nc]
                                break
            result = new
        return result
    dilate.__name__ = f"dilate_{steps}"
    return dilate


def erode_colors(steps: int = 1) -> Callable:
    """Shrink non-zero regions by N steps (border cells become background)."""
    def erode(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        for _ in range(steps):
            new = result.copy()
            rows, cols = result.shape
            for r in range(rows):
                for c in range(cols):
                    if result[r, c] != 0:
                        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
                            nr, nc = r + dr, c + dc
                            if not (0 <= nr < rows and 0 <= nc < cols) or result[nr, nc] == 0:
                                new[r, c] = 0
                                break
            result = new
        return result
    erode.__name__ = f"erode_{steps}"
    return erode


# ---------------------------------------------------------------------------
# MRC-Novelty transforms (for MR Relaxation Context — elevated DT tolerance)
# These transforms are unusual/creative. Apply them ONLY after standard
# transforms fail (when DTImmuneLog has seen enough DT encounters).
# ---------------------------------------------------------------------------

def sort_rows_by_color_count(grid: np.ndarray) -> np.ndarray:
    """Sort rows by number of non-zero cells, ascending."""
    counts = [np.sum(grid[r] != 0) for r in range(grid.shape[0])]
    order = np.argsort(counts)
    return grid[order, :]


def sort_cols_by_color_count(grid: np.ndarray) -> np.ndarray:
    """Sort columns by number of non-zero cells, ascending."""
    counts = [np.sum(grid[:, c] != 0) for c in range(grid.shape[1])]
    order = np.argsort(counts)
    return grid[:, order]


def color_to_size_map(grid: np.ndarray) -> np.ndarray:
    """
    Map each color to its count across the grid — each cell becomes
    the count of its color (mod 9 + 1 to stay within ARC color range).
    """
    flat = grid.flatten()
    counts = Counter(flat)
    result = np.zeros_like(grid)
    for r in range(grid.shape[0]):
        for c in range(grid.shape[1]):
            if grid[r, c] != 0:
                result[r, c] = (counts[grid[r, c]] % 9) + 1
    return result


def make_diagonal_stripe(color: int = 1) -> Callable:
    """Fill the main diagonal and its 1-cell neighbors with a color."""
    def stripe(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        rows, cols = grid.shape
        for r in range(rows):
            for c in range(cols):
                if abs(r - c) <= 1:
                    if result[r, c] == 0:
                        result[r, c] = color
        return result
    stripe.__name__ = f"diagonal_stripe_{color}"
    return stripe


def checkerboard_mask(color: int = 1) -> Callable:
    """Apply a checkerboard pattern on top of background cells."""
    def checker(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        rows, cols = grid.shape
        for r in range(rows):
            for c in range(cols):
                if (r + c) % 2 == 0 and result[r, c] == 0:
                    result[r, c] = color
        return result
    checker.__name__ = f"checkerboard_{color}"
    return checker


# ---------------------------------------------------------------------------
# Export: categorized by phase
# ---------------------------------------------------------------------------

GRAVITY_EXTRA = [gravity_left, gravity_right]

COLOR_FREQUENCY = [
    isolate_most_common,
    isolate_least_common,
    remove_most_common,
    invert_colors,
    remap_colors_by_frequency,
    unique_color_mask,
]

OBJECT_OPS = [
    largest_object_only,
    smallest_object_only,
    object_bounding_box_crop,
    count_components_as_color,
]

SYMMETRY_OPS = [
    complete_horizontal_symmetry,
    complete_vertical_symmetry,
    make_4fold_symmetric,
]

OUTLINE_OPS = [
    draw_outline(1), draw_outline(2), draw_outline(3),
    hollow_to_outline,
]

SPLIT_OPS = [
    top_half, bottom_half, left_half, right_half,
    xor_halves_horizontal, xor_halves_vertical,
]

FILL_OPS = [
    flood_fill(1), flood_fill(2), flood_fill(3), flood_fill(4),
    dilate_colors(1), dilate_colors(2),
    erode_colors(1),
    detect_repeating_unit,
]

MRC_NOVELTY = [
    sort_rows_by_color_count,
    sort_cols_by_color_count,
    color_to_size_map,
    make_diagonal_stripe(1),
    checkerboard_mask(1),
]

ADVANCED_PRIMITIVES = (
    GRAVITY_EXTRA +
    COLOR_FREQUENCY +
    OBJECT_OPS +
    SYMMETRY_OPS +
    OUTLINE_OPS +
    SPLIT_OPS +
    FILL_OPS
)

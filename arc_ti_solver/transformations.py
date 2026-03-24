"""
ARC Primitive Transformation Library
Generates candidate input→output transformations.
Each transformation is a function: grid (np.ndarray) → grid (np.ndarray).
"""

import numpy as np
from itertools import product
from typing import Callable, Optional


def identity(grid: np.ndarray) -> np.ndarray:
    return grid.copy()


def rotate_90(grid: np.ndarray) -> np.ndarray:
    return np.rot90(grid, k=1)


def rotate_180(grid: np.ndarray) -> np.ndarray:
    return np.rot90(grid, k=2)


def rotate_270(grid: np.ndarray) -> np.ndarray:
    return np.rot90(grid, k=3)


def flip_horizontal(grid: np.ndarray) -> np.ndarray:
    return np.fliplr(grid)


def flip_vertical(grid: np.ndarray) -> np.ndarray:
    return np.flipud(grid)


def flip_diagonal(grid: np.ndarray) -> np.ndarray:
    return np.transpose(grid)


def flip_antidiagonal(grid: np.ndarray) -> np.ndarray:
    return np.transpose(np.rot90(grid, k=2))


def make_recolor(src_color: int, dst_color: int) -> Callable:
    def recolor(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        result[result == src_color] = dst_color
        return result
    recolor.__name__ = f"recolor_{src_color}_to_{dst_color}"
    return recolor


def make_shift(dr: int, dc: int, fill: int = 0) -> Callable:
    def shift(grid: np.ndarray) -> np.ndarray:
        result = np.full_like(grid, fill)
        rows, cols = grid.shape
        src_r = slice(max(-dr, 0), rows + min(-dr, 0))
        src_c = slice(max(-dc, 0), cols + min(-dc, 0))
        dst_r = slice(max(dr, 0), rows + max(dr, 0))
        dst_c = slice(max(dc, 0), cols + max(dc, 0))
        dst_r = slice(max(dr, 0), rows)
        dst_c = slice(max(dc, 0), cols)
        try:
            result[dst_r, dst_c] = grid[src_r, src_c]
        except Exception:
            pass
        return result
    shift.__name__ = f"shift_{dr}_{dc}"
    return shift


def crop_to_nonzero(grid: np.ndarray) -> np.ndarray:
    """Crop to bounding box of non-zero cells."""
    rows = np.any(grid != 0, axis=1)
    cols = np.any(grid != 0, axis=0)
    if not rows.any() or not cols.any():
        return grid.copy()
    rmin, rmax = np.where(rows)[0][[0, -1]]
    cmin, cmax = np.where(cols)[0][[0, -1]]
    return grid[rmin:rmax+1, cmin:cmax+1]


def tile_2x2(grid: np.ndarray) -> np.ndarray:
    return np.tile(grid, (2, 2))


def make_color_swap(c1: int, c2: int) -> Callable:
    def swap(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        mask1 = (grid == c1)
        mask2 = (grid == c2)
        result[mask1] = c2
        result[mask2] = c1
        return result
    swap.__name__ = f"swap_{c1}_{c2}"
    return swap


def mirror_vertical_half(grid: np.ndarray) -> np.ndarray:
    """Mirror top half to bottom half."""
    rows, cols = grid.shape
    half = rows // 2
    result = grid.copy()
    result[half:, :] = np.flipud(grid[:half, :])
    return result


def mirror_horizontal_half(grid: np.ndarray) -> np.ndarray:
    """Mirror left half to right half."""
    rows, cols = grid.shape
    half = cols // 2
    result = grid.copy()
    result[:, half:] = np.fliplr(grid[:, :half])
    return result


def hollow_out(fill: int = 0) -> Callable:
    """Replace interior cells with fill color."""
    def hollow(grid: np.ndarray) -> np.ndarray:
        result = grid.copy()
        rows, cols = grid.shape
        if rows > 2 and cols > 2:
            result[1:-1, 1:-1] = fill
        return result
    hollow.__name__ = f"hollow_{fill}"
    return hollow


def make_scale(factor: int) -> Callable:
    def scale(grid: np.ndarray) -> np.ndarray:
        return np.repeat(np.repeat(grid, factor, axis=0), factor, axis=1)
    scale.__name__ = f"scale_{factor}x"
    return scale


def gravity_down(grid: np.ndarray) -> np.ndarray:
    """Drop all non-background cells to bottom of each column."""
    result = np.zeros_like(grid)
    rows, cols = grid.shape
    for c in range(cols):
        col = grid[:, c]
        non_bg = col[col != 0]
        result[rows - len(non_bg):, c] = non_bg
    return result


def gravity_up(grid: np.ndarray) -> np.ndarray:
    result = np.zeros_like(grid)
    rows, cols = grid.shape
    for c in range(cols):
        col = grid[:, c]
        non_bg = col[col != 0]
        result[:len(non_bg), c] = non_bg
    return result


def compose(f: Callable, g: Callable) -> Callable:
    """Compose two transformations: apply f then g."""
    def composed(grid):
        return g(f(grid))
    composed.__name__ = f"{f.__name__}+{g.__name__}"
    return composed


# Canonical set of primitives for initial search
BASE_PRIMITIVES = [
    identity,
    rotate_90,
    rotate_180,
    rotate_270,
    flip_horizontal,
    flip_vertical,
    flip_diagonal,
    flip_antidiagonal,
    mirror_vertical_half,
    mirror_horizontal_half,
    tile_2x2,
    crop_to_nonzero,
    gravity_down,
    gravity_up,
    make_scale(2),
    make_scale(3),
]

SHIFT_PRIMITIVES = [
    make_shift(dr, dc)
    for dr in (-3, -2, -1, 0, 1, 2, 3)
    for dc in (-3, -2, -1, 0, 1, 2, 3)
    if not (dr == 0 and dc == 0)
]


def generate_recolor_primitives(observed_colors: list) -> list:
    """Generate recolor transforms for all observed color pairs."""
    transforms = []
    for src in observed_colors:
        for dst in observed_colors:
            if src != dst:
                transforms.append(make_recolor(src, dst))
    for c1, c2 in combinations_pair(observed_colors):
        transforms.append(make_color_swap(c1, c2))
    return transforms


def combinations_pair(lst):
    for i in range(len(lst)):
        for j in range(i+1, len(lst)):
            yield lst[i], lst[j]

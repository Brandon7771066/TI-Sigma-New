"""
Domain 4: Scale / Resize Solver — ARC-AGI
==========================================

Handles tasks where input and output have different sizes.

Common resize patterns in ARC:
  1. UPSCALE_UNIFORM: Each cell → N×N block of same color (zoom in)
  2. TILE: Output = input tiled M×N times
  3. EXTRACT: Output = a sub-region of input (zoom out / crop)
  4. SCALE_AND_RECOLOR: Upscale + apply color rules
  5. COUNT_TO_SIZE: Output size is determined by counting input cells
  6. COMPACT: Remove background rows/columns (shrink)

TI Sigma framing:
  Resize tasks are the "INDETERMINATE" category of ARC:
  the output size is genuinely different — the solver must understand
  the SIZE RULE, not just the TRANSFORM rule. This is G-dimension reasoning:
  constraint satisfaction over a structural rule.

Author: Brandon Emerick (TI Sigma / ARC Domain Solver)
Date: March 30, 2026
"""

import numpy as np
from typing import Optional, Tuple


# ── Pattern detectors ───────────────────────────────────────────────────────

def _detect_upscale_factor(
    inp: np.ndarray, out: np.ndarray
) -> Optional[Tuple[int, int]]:
    """Check if out = pixelated upscale of inp by integer (row, col) factors."""
    if out.shape[0] % inp.shape[0] != 0 or out.shape[1] % inp.shape[1] != 0:
        return None
    scale_r = out.shape[0] // inp.shape[0]
    scale_c = out.shape[1] // inp.shape[1]
    # Verify: every N×M block in out should be uniform = corresponding inp cell
    for r in range(inp.shape[0]):
        for c in range(inp.shape[1]):
            block = out[r*scale_r:(r+1)*scale_r, c*scale_c:(c+1)*scale_c]
            if not np.all(block == inp[r, c]):
                return None
    return (scale_r, scale_c)


def _detect_tile(
    inp: np.ndarray, out: np.ndarray
) -> Optional[Tuple[int, int]]:
    """Check if out = inp tiled (tile_r, tile_c) times."""
    if out.shape[0] % inp.shape[0] != 0 or out.shape[1] % inp.shape[1] != 0:
        return None
    tile_r = out.shape[0] // inp.shape[0]
    tile_c = out.shape[1] // inp.shape[1]
    expected = np.tile(inp, (tile_r, tile_c))
    if np.array_equal(expected, out):
        return (tile_r, tile_c)
    return None


def _detect_extract(
    inp: np.ndarray, out: np.ndarray
) -> Optional[Tuple[int, int, int, int]]:
    """
    Check if out = a sub-region of inp.
    Returns (r_start, r_end, c_start, c_end) or None.
    """
    or_, oc = out.shape
    ir, ic = inp.shape
    if or_ > ir or oc > ic:
        return None
    for r0 in range(ir - or_ + 1):
        for c0 in range(ic - oc + 1):
            if np.array_equal(inp[r0:r0+or_, c0:c0+oc], out):
                return (r0, r0+or_, c0, c0+oc)
    return None


def _detect_compact(inp: np.ndarray, out: np.ndarray) -> bool:
    """
    Check if out = inp with background-only rows/columns removed.
    Background = most frequent color.
    """
    bg = int(np.bincount(inp.flatten()).argmax())
    # Find non-background rows and columns in inp
    non_bg_rows = [r for r in range(inp.shape[0]) if np.any(inp[r] != bg)]
    non_bg_cols = [c for c in range(inp.shape[1]) if np.any(inp[:, c] != bg)]
    if not non_bg_rows or not non_bg_cols:
        return False
    extracted = inp[np.ix_(non_bg_rows, non_bg_cols)]
    return np.array_equal(extracted, out)


def _apply_compact(inp: np.ndarray) -> np.ndarray:
    """Remove background-only rows and columns."""
    bg = int(np.bincount(inp.flatten()).argmax())
    non_bg_rows = [r for r in range(inp.shape[0]) if np.any(inp[r] != bg)]
    non_bg_cols = [c for c in range(inp.shape[1]) if np.any(inp[:, c] != bg)]
    if not non_bg_rows or not non_bg_cols:
        return inp
    return inp[np.ix_(non_bg_rows, non_bg_cols)]


def _apply_upscale(inp: np.ndarray, scale_r: int, scale_c: int) -> np.ndarray:
    """Pixelate upscale inp by (scale_r, scale_c)."""
    return np.repeat(np.repeat(inp, scale_r, axis=0), scale_c, axis=1)


def _apply_tile(inp: np.ndarray, tile_r: int, tile_c: int) -> np.ndarray:
    """Tile inp (tile_r, tile_c) times."""
    return np.tile(inp, (tile_r, tile_c))


# ── Pattern type enum ────────────────────────────────────────────────────────

class ScalePattern:
    UPSCALE  = "upscale_uniform"
    TILE     = "tile"
    EXTRACT  = "extract_subregion"
    COMPACT  = "compact_remove_bg"
    UNKNOWN  = "unknown"


# ── Main solver ──────────────────────────────────────────────────────────────

def solve_scale(task: dict) -> Optional[dict]:
    """
    Attempt to solve a resize/scale ARC task.

    Returns:
        dict: {'output': list, 'lcc': float, 'method': str, 'pattern': str}
        None if no pattern is detected.
    """
    train_pairs = task.get("train", [])
    test_pairs = task.get("test", [])

    if not train_pairs or not test_pairs:
        return None

    # Check that this is actually a resize task (or handle same-size scale too)
    # Try each pattern in order of simplicity

    # ── Pattern 1: Uniform upscale ─────────────────────────────────────────
    upscale_factors = []
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        f = _detect_upscale_factor(inp, out)
        if f is None:
            upscale_factors = None
            break
        upscale_factors.append(f)

    if upscale_factors and len(set(upscale_factors)) == 1:
        scale_r, scale_c = upscale_factors[0]
        test_inp = np.array(test_pairs[0]["input"])
        predicted = _apply_upscale(test_inp, scale_r, scale_c)
        return {
            "output": predicted.tolist(),
            "lcc": 1.0,
            "method": "scale_solver",
            "pattern": ScalePattern.UPSCALE,
            "scale": (scale_r, scale_c),
        }

    # ── Pattern 2: Tile ───────────────────────────────────────────────────
    tile_factors = []
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        f = _detect_tile(inp, out)
        if f is None:
            tile_factors = None
            break
        tile_factors.append(f)

    if tile_factors and len(set(tile_factors)) == 1:
        tile_r, tile_c = tile_factors[0]
        test_inp = np.array(test_pairs[0]["input"])
        predicted = _apply_tile(test_inp, tile_r, tile_c)
        return {
            "output": predicted.tolist(),
            "lcc": 1.0,
            "method": "scale_solver",
            "pattern": ScalePattern.TILE,
            "tile": (tile_r, tile_c),
        }

    # ── Pattern 3: Compact (remove background rows/cols) ─────────────────
    compact_matches = []
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        if _detect_compact(inp, out):
            compact_matches.append(True)
        else:
            compact_matches = None
            break

    if compact_matches and all(compact_matches):
        test_inp = np.array(test_pairs[0]["input"])
        predicted = _apply_compact(test_inp)
        return {
            "output": predicted.tolist(),
            "lcc": 1.0,
            "method": "scale_solver",
            "pattern": ScalePattern.COMPACT,
        }

    # ── Pattern 4: Extract subregion (consistent offset) ────────────────
    extract_params = []
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        params = _detect_extract(inp, out)
        if params is None:
            extract_params = None
            break
        extract_params.append(params)

    if extract_params:
        # Check if all pairs extract the same relative subregion
        # (same start rows/cols, same size)
        first = extract_params[0]
        r_start, r_end, c_start, c_end = first
        out_r = r_end - r_start
        out_c = c_end - c_start
        consistent = all(
            (ep[1]-ep[0] == out_r and ep[3]-ep[2] == out_c)
            for ep in extract_params
        )
        # For consistent offset (same position), check if offsets match
        same_offset = all(
            ep[0] == r_start and ep[2] == c_start
            for ep in extract_params
        )
        if consistent and same_offset:
            test_inp = np.array(test_pairs[0]["input"])
            if (r_end <= test_inp.shape[0] and c_end <= test_inp.shape[1]):
                predicted = test_inp[r_start:r_end, c_start:c_end]
                return {
                    "output": predicted.tolist(),
                    "lcc": 0.85,  # Lower LCC — offset may not generalize
                    "method": "scale_solver",
                    "pattern": ScalePattern.EXTRACT,
                    "region": (r_start, r_end, c_start, c_end),
                }

    # ── Pattern 5: Variable scale (output size = N × non-background count) ─
    # Some ARC tasks scale based on count of non-background cells
    bg_count_scales = []
    for pair in train_pairs:
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        bg = int(np.bincount(inp.flatten()).argmax())
        n_nbs = int(np.sum(inp != bg))  # non-background count
        if n_nbs > 0:
            # Check if output area = n_nbs × some factor
            out_area = out.shape[0] * out.shape[1]
            if out_area % n_nbs == 0:
                bg_count_scales.append(out_area // n_nbs)
            else:
                bg_count_scales = None
                break
        else:
            bg_count_scales = None
            break

    # (This is a heuristic — don't apply blindly; needs further validation)

    return None  # No pattern detected


def is_resize_task(task: dict) -> bool:
    """Return True if any training pair has input size ≠ output size."""
    for pair in task.get("train", []):
        inp = np.array(pair["input"])
        out = np.array(pair["output"])
        if inp.shape != out.shape:
            return True
    return False

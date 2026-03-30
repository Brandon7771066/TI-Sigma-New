"""
Polycrystalline ARC Encoder — TI Sigma Grain Architecture
==========================================================

Derived from URB #539 (Aperiodic Dual — Polycrystalline Computation).

CONCEPTUAL FOUNDATION:
A polycrystalline material has multiple "grains" — domains of local order —
separated by "grain boundaries" — narrow regions of disorder where orientations
transition. Each grain has a different orientation; the material as a whole is
aperiodic (no single orientation dominates globally).

MAPPING TO ARC GRIDS:
  Grain interior   = connected region of coherent truth values (TRUE or FALSE)
                     Low INDETERMINATE density (δ ≈ 0)
                     Like the "bulk" of an orientation domain in a crystal
  Grain boundary   = region adjacent to multiple truth-value types
                     High INDETERMINATE/TRALSE density (δ → 1)
                     Information exchange zone between grains
  INDETERMINATE cells = the "grain boundary material" — held open by MR2
  TRALSE cells     = "defect sites" within a grain — imperfect but local
  DOUBLE_TRALSE    = already collapsed (by FiveValuedCellEncoder) — no DT grains

KLEIN V₄ ORIENTATION:
Each grain is assigned a Klein V₄ orientation based on its dominant transform
symmetry:
  ID     (identity):  grain that is symmetric under no non-trivial transform
  FLIP_H (flip_H):    grain with horizontal mirror symmetry
  FLIP_V (flip_V):    grain with vertical mirror symmetry
  ROT180 (rot_180):   grain with 180° rotational symmetry

When flip_H(grain) = flip_V(grain), the orbit is collapsed — the grain's
orientation is the answer (by exact analogy with the Riemann critical line,
URBs #554–556, and klein_v4_detector.py).

THE δ (INDETERMINATE DENSITY) METRIC:
  δ(region) = #{INDETERMINATE cells in region} / #{total cells in region}
  δ = 0: pure grain interior (all TRUE or all FALSE)
  δ = 1: pure grain boundary (all INDETERMINATE)
  δ intermediate: mixed / defect-rich region

Author: Brandon Emerick (TI Sigma / URB #539)
Date: March 30, 2026
"""

import numpy as np
from typing import Optional
from collections import deque
from arc_ti_solver import (
    FALSE, INDETERMINATE, TRUE, TRALSE, DOUBLE_TRALSE
)
from arc_ti_solver.tralse_encoder import FiveValuedCellEncoder


# ---------------------------------------------------------------------------
# Klein V₄ group elements as 2D array transforms
# (same as klein_v4_detector.py — duplicated here for independence)
# ---------------------------------------------------------------------------

def _flip_h(arr: np.ndarray) -> np.ndarray:
    return np.fliplr(arr)

def _flip_v(arr: np.ndarray) -> np.ndarray:
    return np.flipud(arr)

def _rot180(arr: np.ndarray) -> np.ndarray:
    return np.rot90(arr, 2)

def _identity(arr: np.ndarray) -> np.ndarray:
    return arr

KLEIN_V4_TRANSFORMS = {
    "identity": _identity,
    "flip_H":   _flip_h,
    "flip_V":   _flip_v,
    "rot_180":  _rot180,
}


# ---------------------------------------------------------------------------
# GrainMap dataclass
# ---------------------------------------------------------------------------

class GrainMap:
    """
    Result of polycrystalline encoding of a single ARC grid.

    Attributes
    ----------
    encoded_grid : np.ndarray (int8)
        The 5-valued encoded grid (from FiveValuedCellEncoder).
    grain_labels : np.ndarray (int)
        Connected-component label per cell. 0 = grain boundary material.
        Grain interiors: labels 1, 2, 3, ...
        Grain boundaries: label 0 (the "inter-grain" zone).
    is_boundary : np.ndarray (bool)
        True for cells that are on or between grains (INDETERMINATE or
        adjacent to multiple grain types).
    delta : np.ndarray (float)
        Per-cell δ (INDETERMINATE density) in a 3×3 neighborhood.
        δ=0 = pure grain interior. δ=1 = pure grain boundary material.
    grain_orientations : dict[int, str]
        Maps grain_label → Klein V₄ orientation string.
        "identity", "flip_H", "flip_V", "rot_180", or "collapsed" (orbit
        collapsed — this grain's orientation is dominant).
    orbit_collapsed_grains : list[int]
        Grain labels where S₁(grain) = S₂(grain) → orbit collapsed.
    global_delta : float
        Global INDETERMINATE density for the entire grid.
    summary : dict
        Human-readable summary of the polycrystalline decomposition.
    """

    def __init__(
        self,
        encoded_grid: np.ndarray,
        grain_labels: np.ndarray,
        is_boundary: np.ndarray,
        delta: np.ndarray,
        grain_orientations: dict,
        orbit_collapsed_grains: list,
    ):
        self.encoded_grid = encoded_grid
        self.grain_labels = grain_labels
        self.is_boundary = is_boundary
        self.delta = delta
        self.grain_orientations = grain_orientations
        self.orbit_collapsed_grains = orbit_collapsed_grains
        self.n_grains = int(grain_labels.max()) if grain_labels.size > 0 else 0
        self.global_delta = float(np.mean(encoded_grid == INDETERMINATE))

    @property
    def summary(self) -> dict:
        total = self.encoded_grid.size
        if total == 0:
            return {}
        return {
            "n_grains": self.n_grains,
            "global_delta": round(self.global_delta, 4),
            "boundary_fraction": round(float(self.is_boundary.mean()), 4),
            "orbit_collapsed_grains": self.orbit_collapsed_grains,
            "grain_orientations": self.grain_orientations,
            "truth_value_counts": {
                "FALSE":         int(np.sum(self.encoded_grid == FALSE)),
                "INDETERMINATE": int(np.sum(self.encoded_grid == INDETERMINATE)),
                "TRUE":          int(np.sum(self.encoded_grid == TRUE)),
                "TRALSE":        int(np.sum(self.encoded_grid == TRALSE)),
            },
        }

    def __repr__(self) -> str:
        s = self.summary
        return (
            f"GrainMap(grains={s['n_grains']}, "
            f"δ_global={s['global_delta']:.3f}, "
            f"boundary={s['boundary_fraction']:.3f}, "
            f"collapsed={s['orbit_collapsed_grains']})"
        )


# ---------------------------------------------------------------------------
# Core grain detection functions
# ---------------------------------------------------------------------------

def _connected_components(binary_mask: np.ndarray) -> np.ndarray:
    """
    Simple 4-connected component labeling using BFS.
    Returns label array (0 = not in mask, 1..N = component IDs).
    """
    labels = np.zeros(binary_mask.shape, dtype=np.int32)
    current_label = 0
    rows, cols = binary_mask.shape

    for r in range(rows):
        for c in range(cols):
            if binary_mask[r, c] and labels[r, c] == 0:
                current_label += 1
                queue = deque([(r, c)])
                labels[r, c] = current_label
                while queue:
                    cr, cc = queue.popleft()
                    for dr, dc in [(-1,0),(1,0),(0,-1),(0,1)]:
                        nr, nc = cr+dr, cc+dc
                        if (0 <= nr < rows and 0 <= nc < cols
                                and binary_mask[nr, nc]
                                and labels[nr, nc] == 0):
                            labels[nr, nc] = current_label
                            queue.append((nr, nc))

    return labels


def _compute_delta(encoded_grid: np.ndarray, radius: int = 1) -> np.ndarray:
    """
    Per-cell δ (INDETERMINATE density) in a (2r+1)×(2r+1) neighborhood.

    δ(cell) = #{INDETERMINATE neighbors} / #{total neighbors in patch}

    δ=0 → pure grain interior (no INDETERMINATE in neighborhood)
    δ=1 → pure grain boundary (all neighbors are INDETERMINATE)
    """
    rows, cols = encoded_grid.shape
    delta = np.zeros((rows, cols), dtype=np.float32)

    for r in range(rows):
        for c in range(cols):
            patch_cells = []
            for dr in range(-radius, radius + 1):
                for dc in range(-radius, radius + 1):
                    nr, nc = r + dr, c + dc
                    if 0 <= nr < rows and 0 <= nc < cols:
                        patch_cells.append(encoded_grid[nr, nc])
            if patch_cells:
                n_indet = sum(1 for v in patch_cells if v == INDETERMINATE)
                delta[r, c] = n_indet / len(patch_cells)

    return delta


def _classify_grain_orientation(grain_mask: np.ndarray) -> str:
    """
    Determine the Klein V₄ orientation of a grain by checking
    which non-trivial group element maps the grain to itself.

    Returns the name of the symmetry element the grain is invariant under,
    or "none" if no non-trivial symmetry is found.

    Orbit collapse check: if flip_H(mask) == flip_V(mask), the orbit is
    collapsed — return "collapsed".
    """
    fh = _flip_h(grain_mask)
    fv = _flip_v(grain_mask)
    r2 = _rot180(grain_mask)

    # Orbit collapse: S₁ = S₂ → return collapsed
    if np.array_equal(fh, fv):
        return "collapsed"

    # Check self-symmetry (grain invariant under the transform)
    if np.array_equal(grain_mask, fh):
        return "flip_H"
    if np.array_equal(grain_mask, fv):
        return "flip_V"
    if np.array_equal(grain_mask, r2):
        return "rot_180"

    return "identity"


# ---------------------------------------------------------------------------
# Main encoder
# ---------------------------------------------------------------------------

class PolycrystallineEncoder:
    """
    Encodes a 5-valued ARC grid as a polycrystalline grain map.

    Usage
    -----
    encoder = PolycrystallineEncoder(train_pairs)
    grain_map = encoder.encode(grid)

    Or encode directly from an already-computed 5-valued array:
    grain_map = PolycrystallineEncoder.from_encoded(encoded_array)

    Parameters
    ----------
    train_pairs : list of dicts with "input" and "output" keys
        The ARC training pairs (same format as FiveValuedCellEncoder).
    boundary_delta_threshold : float
        δ threshold above which a cell is classified as "grain boundary"
        material. Default 0.3 (30% INDETERMINATE in neighborhood).
    min_grain_size : int
        Minimum number of cells to be called a grain (smaller connected
        components are treated as grain boundary defects). Default 2.
    """

    def __init__(
        self,
        train_pairs: list,
        boundary_delta_threshold: float = 0.3,
        min_grain_size: int = 2,
    ):
        self.five_encoder = FiveValuedCellEncoder(train_pairs)
        self.boundary_delta_threshold = boundary_delta_threshold
        self.min_grain_size = min_grain_size

    @classmethod
    def from_encoded(
        cls,
        encoded_grid: np.ndarray,
        boundary_delta_threshold: float = 0.3,
        min_grain_size: int = 2,
    ) -> "GrainMap":
        """
        Build a GrainMap directly from a pre-computed 5-valued grid.
        Useful when you already have FiveValuedCellEncoder output.
        """
        return cls._build_grain_map(
            encoded_grid, boundary_delta_threshold, min_grain_size
        )

    def encode(self, grid: list) -> GrainMap:
        """Encode a raw ARC grid (list of lists of ints) into a GrainMap."""
        encoded = self.five_encoder.encode_grid(grid)
        return self._build_grain_map(
            encoded, self.boundary_delta_threshold, self.min_grain_size
        )

    def encode_all(self) -> list:
        """Encode all training pair inputs. Returns list of GrainMaps."""
        results = []
        for pair in self.five_encoder.train_pairs:
            encoded = self.five_encoder.encode_grid(pair["input"])
            gm = self._build_grain_map(
                encoded, self.boundary_delta_threshold, self.min_grain_size
            )
            results.append(gm)
        return results

    @staticmethod
    def _build_grain_map(
        encoded: np.ndarray,
        boundary_delta_threshold: float,
        min_grain_size: int,
    ) -> GrainMap:
        """
        Core algorithm: convert 5-valued encoded grid → GrainMap.

        Steps:
        1. Compute δ (INDETERMINATE density) per cell
        2. Classify boundary vs interior cells (δ > threshold → boundary)
        3. Label connected components of interior cells (= grains)
        4. Merge small components into boundary zone
        5. Determine Klein V₄ orientation per grain
        6. Detect orbit-collapsed grains
        """
        # Step 1: Compute δ per cell
        delta = _compute_delta(encoded, radius=1)

        # Step 2: Interior cells = δ ≤ threshold AND not INDETERMINATE themselves
        # Boundary material = INDETERMINATE cells OR high-δ neighborhood
        is_indeterminate = (encoded == INDETERMINATE)
        high_delta = (delta > boundary_delta_threshold)
        is_boundary_raw = is_indeterminate | high_delta

        # Interior mask: cells that are grain material (TRUE or FALSE dominated)
        is_interior = ~is_boundary_raw

        # Step 3: Label connected components of interior regions
        true_interior  = is_interior & (encoded == TRUE)
        false_interior = is_interior & (encoded == FALSE)
        tralse_interior = is_interior & (encoded == TRALSE)

        # Label each truth-value class separately (different phases)
        true_labels  = _connected_components(true_interior)
        false_labels = _connected_components(false_interior)

        # Offset FALSE labels to avoid ID collision with TRUE labels
        max_true_label = int(true_labels.max()) if true_labels.max() > 0 else 0
        false_labels_offset = np.where(
            false_labels > 0,
            false_labels + max_true_label,
            0
        )

        # TRALSE cells form their own grain phase (offset further)
        tralse_labels = _connected_components(tralse_interior)
        max_false_label = int(false_labels_offset.max()) if false_labels_offset.max() > 0 else 0
        tralse_labels_offset = np.where(
            tralse_labels > 0,
            tralse_labels + max_false_label,
            0
        )

        # Combined grain labels (0 = boundary)
        grain_labels = np.maximum(
            np.maximum(true_labels, false_labels_offset),
            tralse_labels_offset
        )

        # Step 4: Merge small grains into boundary zone
        unique_labels = np.unique(grain_labels)
        unique_labels = unique_labels[unique_labels > 0]
        for lbl in unique_labels:
            mask = (grain_labels == lbl)
            if int(mask.sum()) < min_grain_size:
                grain_labels[mask] = 0

        # Re-label contiguously after merging
        final_labels = np.zeros_like(grain_labels)
        new_label = 0
        for old_lbl in np.unique(grain_labels):
            if old_lbl == 0:
                continue
            new_label += 1
            final_labels[grain_labels == old_lbl] = new_label
        grain_labels = final_labels

        # Step 5: Determine is_boundary (anything not in a grain)
        is_boundary = (grain_labels == 0)

        # Step 6: Klein V₄ orientation per grain
        grain_orientations = {}
        orbit_collapsed_grains = []

        rows, cols = encoded.shape
        for lbl in range(1, int(grain_labels.max()) + 1):
            grain_mask = (grain_labels == lbl).astype(np.float32)
            orientation = _classify_grain_orientation(grain_mask)
            grain_orientations[lbl] = orientation
            if orientation == "collapsed":
                orbit_collapsed_grains.append(lbl)

        return GrainMap(
            encoded_grid=encoded,
            grain_labels=grain_labels,
            is_boundary=is_boundary,
            delta=delta,
            grain_orientations=grain_orientations,
            orbit_collapsed_grains=orbit_collapsed_grains,
        )


# ---------------------------------------------------------------------------
# Integration helper: use GrainMap in the main ARC solver pipeline
# ---------------------------------------------------------------------------

def grain_boundary_lcc_bonus(grain_map: GrainMap, base_lcc: float) -> float:
    """
    Adjust LCC score upward when the polycrystalline structure confirms
    a strong grain configuration.

    Bonuses:
      - Each orbit-collapsed grain: +0.02 (strong symmetry signal)
      - Low global δ: bonus scales with (1 − δ) (coherent interior structure)
      - High n_grains with clear boundaries: modest bonus (rich structure)

    The LCC bonus is capped so the result stays ≤ 1.0.
    """
    bonus = 0.0

    # Orbit collapse bonus
    bonus += len(grain_map.orbit_collapsed_grains) * 0.02

    # Low-δ (coherent interior) bonus
    bonus += 0.05 * (1.0 - grain_map.global_delta)

    # Rich grain structure bonus (capped at 0.03)
    bonus += min(0.03, grain_map.n_grains * 0.005)

    return min(1.0, base_lcc + bonus)


def describe_grain_map(grain_map: GrainMap) -> str:
    """Human-readable description of a GrainMap for logging."""
    s = grain_map.summary
    lines = [
        f"Polycrystalline decomposition:",
        f"  Grains: {s['n_grains']}",
        f"  Global δ (INDETERMINATE density): {s['global_delta']:.3f}",
        f"  Boundary fraction: {s['boundary_fraction']:.3f}",
        f"  Orbit-collapsed grains: {s['orbit_collapsed_grains'] or 'none'}",
        f"  Truth-value counts: {s['truth_value_counts']}",
    ]
    if s['grain_orientations']:
        lines.append(f"  Grain orientations:")
        for lbl, orient in s['grain_orientations'].items():
            marker = " ← COLLAPSED" if orient == "collapsed" else ""
            lines.append(f"    Grain {lbl}: {orient}{marker}")
    return "\n".join(lines)

"""
TralseCellEncoder — 4-valued encoding of ARC grids.

Instead of binary (figure=1 / background=0), each cell receives one of:
  FALSE   (0): definitively background
  TRALSE  (1): ambiguously figure or ground — context resolves it
  TRUE    (2): definitively figure / pattern-relevant
  MR_PEND (3): truth value depends on resolving a downstream constraint

This is the core innovation. Standard approaches commit to one reading
of ambiguous cells immediately and lose the alternative path. 4-valued
encoding holds the ambiguity open until Myrion Resolution propagates
enough constraints to collapse TRALSE → TRUE/FALSE.
"""

import numpy as np
from collections import Counter
from typing import Optional
from arc_ti_solver import FALSE, TRALSE, TRUE, MR_PEND


class TralseCellEncoder:
    """
    Encodes a set of ARC grid pairs into 4-valued tralse state tensors.

    Strategy:
      1. Identify background color (most frequent in inputs across all pairs)
      2. Identify strongly-figure colors (appear in outputs, rare in inputs)
      3. Identify ambiguous colors (vary across pairs)
      4. Assign TRALSE to cells whose role changes across training examples
      5. Assign MR_PEND to cells whose color appears inconsistently in outputs
    """

    def __init__(self, train_pairs: list):
        self.train_pairs = train_pairs
        self.bg_color = self._detect_background()
        self.color_roles = self._analyze_color_roles()

    def _detect_background(self) -> int:
        """Most frequent color across all input grids = background."""
        all_counts = Counter()
        for pair in self.train_pairs:
            for row in pair["input"]:
                all_counts.update(row)
        if not all_counts:
            return 0
        return all_counts.most_common(1)[0][0]

    def _analyze_color_roles(self) -> dict:
        """
        For each color, determine its tralse status across pairs.
        Returns dict: {color: tvalue}
          TRUE    = color appears in outputs consistently
          FALSE   = color appears only as background in inputs
          TRALSE  = color appears in some but not all outputs
          MR_PEND = color appears in inputs AND outputs with changing role
        """
        roles = {}
        all_input_colors = set()
        all_output_colors = set()
        pair_output_colors = [
            {cell for row in p["output"] for cell in row}
            for p in self.train_pairs
        ]
        pair_input_colors = [
            {cell for row in p["input"] for cell in row}
            for p in self.train_pairs
        ]

        for p in self.train_pairs:
            all_input_colors.update({cell for row in p["input"] for cell in row})
            all_output_colors.update({cell for row in p["output"] for cell in row})

        all_colors = all_input_colors | all_output_colors

        for color in all_colors:
            in_all_outputs = all(color in poc for poc in pair_output_colors)
            in_some_outputs = any(color in poc for poc in pair_output_colors)
            in_all_inputs = all(color in pic for pic in pair_input_colors)
            in_some_inputs = any(color in pic for pic in pair_input_colors)

            if color == self.bg_color and not in_some_outputs:
                roles[color] = FALSE
            elif in_all_outputs and not in_some_inputs:
                roles[color] = TRUE
            elif in_all_outputs and in_all_inputs:
                roles[color] = MR_PEND
            elif in_some_outputs and not in_all_outputs:
                roles[color] = TRALSE
            elif in_some_inputs and not in_some_outputs:
                roles[color] = FALSE
            else:
                roles[color] = TRALSE

        return roles

    def encode_grid(self, grid: list) -> np.ndarray:
        """
        Encode a grid → 2D array of tvalues {FALSE, TRALSE, TRUE, MR_PEND}.
        """
        rows = len(grid)
        cols = len(grid[0]) if grid else 0
        result = np.zeros((rows, cols), dtype=np.int8)
        for r, row in enumerate(grid):
            for c, color in enumerate(row):
                result[r, c] = self.color_roles.get(color, TRALSE)
        return result

    def encode_pair(self, pair: dict) -> dict:
        """Encode both input and output of a training pair."""
        return {
            "input": self.encode_grid(pair["input"]),
            "output": self.encode_grid(pair["output"]),
            "input_raw": np.array(pair["input"], dtype=np.int8),
            "output_raw": np.array(pair["output"], dtype=np.int8),
        }

    def encode_all_pairs(self) -> list:
        """Encode all training pairs."""
        return [self.encode_pair(p) for p in self.train_pairs]

    def tralse_density(self, encoded_grid: np.ndarray) -> float:
        """Fraction of cells that are TRALSE or MR_PEND (ambiguous)."""
        total = encoded_grid.size
        ambig = np.sum((encoded_grid == TRALSE) | (encoded_grid == MR_PEND))
        return float(ambig) / total if total > 0 else 0.0

    def resolution_pressure(self, encoded_pairs: list) -> float:
        """
        How urgently does MR1 need to resolve ambiguities?
        Higher = more TRALSE cells = more potential for wrong path.
        Range [0, 1].
        """
        densities = [self.tralse_density(ep["input"]) for ep in encoded_pairs]
        return float(np.mean(densities))

    def candidate_encodings(self, grid: list, n: int = 3) -> list:
        """
        Generate n candidate binary resolutions of TRALSE cells.
        Each candidate is a numpy array where TRALSE/MR_PEND are resolved
        to TRUE or FALSE based on different spatial heuristics.

        Returns list of (encoding, interpretation_name) tuples.
        """
        base = self.encode_grid(grid)
        raw = np.array(grid, dtype=np.int8)
        candidates = []

        # Candidate 1: Spatial majority — resolve tralse by neighbor majority
        c1 = self._resolve_by_neighbor_majority(base.copy())
        candidates.append((c1, "neighbor_majority"))

        # Candidate 2: Color frequency — rare colors → TRUE, common → FALSE
        c2 = self._resolve_by_frequency(base.copy(), raw)
        candidates.append((c2, "frequency_rarity"))

        # Candidate 3: Boundary detection — edge cells → FALSE, interior → TRUE
        c3 = self._resolve_by_boundary(base.copy())
        candidates.append((c3, "boundary_interior"))

        return candidates[:n]

    def _resolve_by_neighbor_majority(self, grid: np.ndarray) -> np.ndarray:
        """Resolve TRALSE cells by 8-neighbor majority vote."""
        result = grid.copy()
        rows, cols = grid.shape
        for r in range(rows):
            for c in range(cols):
                if grid[r, c] in (TRALSE, MR_PEND):
                    neighbors = []
                    for dr in (-1, 0, 1):
                        for dc in (-1, 0, 1):
                            if dr == 0 and dc == 0:
                                continue
                            nr, nc = r + dr, c + dc
                            if 0 <= nr < rows and 0 <= nc < cols:
                                neighbors.append(grid[nr, nc])
                    true_n = sum(1 for v in neighbors if v == TRUE)
                    false_n = sum(1 for v in neighbors if v == FALSE)
                    result[r, c] = TRUE if true_n >= false_n else FALSE
        return result

    def _resolve_by_frequency(self, grid: np.ndarray, raw: np.ndarray) -> np.ndarray:
        """Resolve TRALSE: rare colors → TRUE (figure), frequent → FALSE."""
        result = grid.copy()
        color_counts = Counter(raw.flatten().tolist())
        total = raw.size
        rows, cols = grid.shape
        for r in range(rows):
            for c in range(cols):
                if grid[r, c] in (TRALSE, MR_PEND):
                    freq = color_counts.get(int(raw[r, c]), 0) / total
                    result[r, c] = FALSE if freq > 0.3 else TRUE
        return result

    def _resolve_by_boundary(self, grid: np.ndarray) -> np.ndarray:
        """Resolve TRALSE: boundary cells → FALSE (background edge), interior → TRUE."""
        result = grid.copy()
        rows, cols = grid.shape
        for r in range(rows):
            for c in range(cols):
                if grid[r, c] in (TRALSE, MR_PEND):
                    is_boundary = (r == 0 or r == rows - 1 or c == 0 or c == cols - 1)
                    result[r, c] = FALSE if is_boundary else TRUE
        return result

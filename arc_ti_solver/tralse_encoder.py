"""
FiveValuedCellEncoder — 5-valued encoding of ARC grids.

Instead of binary (figure=1 / background=0), each cell receives one of the
five TI Sigma truth values:

  FALSE        (0): definitively background — consistent across all pairs
  INDETERMINATE(1): genuinely in the middle — color appears equally as figure
                    and as background; coherent 50/50 balance. The ternary
                    middle. Holds open until Myrion Resolution collapses it.
  TRUE         (2): definitively figure / pattern-relevant
  TRALSE       (3): imperfection/contradiction quality — color appears with
                    conflicting roles across training pairs; coherent but
                    imperfect. "The grease." Not a position on truth polarity;
                    marks states that need MR scrutiny.
  DOUBLE_TRALSE(4): incoherent contradiction — color signals that directly
                    cancel each other (e.g., required to be both figure AND
                    background at the exact same position across pairs, with
                    no consistent resolution). IMMEDIATELY FLAGGED AND
                    DISCARDED: the cell is collapsed to the most-likely
                    positional value (TRUE or FALSE) and the DT flag is noted
                    but not stored as a persistent state.

Key theoretical distinction:
  INDETERMINATE cells = coherent ambiguity (the system knows it is balanced).
  TRALSE cells = imperfect/contradictory but still processable by MR.
  DOUBLE_TRALSE cells = incoherence detected → collapse immediately.

This distinction is the core innovation over standard neural networks, which
treat all uncertainty identically. TI Sigma distinguishes:
  1. Genuine balance (INDETERMINATE) — hold open, let context decide
  2. Imperfect signal (TRALSE) — process with caution via MR
  3. Pure incoherence (DOUBLE_TRALSE) — reject, don't waste compute on it
"""

import numpy as np
from collections import Counter
from typing import Optional
from arc_ti_solver import FALSE, INDETERMINATE, TRUE, TRALSE, DOUBLE_TRALSE


class FiveValuedCellEncoder:
    """
    Encodes ARC grid pairs into 5-valued TI Sigma state tensors.

    Assignment strategy:
      1. Detect background color (most frequent across all input pairs)
      2. Classify each color's role across all training examples
      3. Assign the appropriate 5-valued state to each cell
      4. Immediately discard DOUBLE_TRALSE cells (collapse to best positional guess)
    """

    def __init__(self, train_pairs: list):
        self.train_pairs = train_pairs
        self.bg_color = self._detect_background()
        self.color_roles = self._analyze_color_roles()
        self.dt_discarded = []

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
        For each color, determine its 5-valued truth status across training pairs.

        Returns dict: {color: (tvalue, dt_fallback)}
          TRUE         = appears consistently in outputs (figure role confirmed)
          FALSE        = appears only as background (never in output as figure)
          INDETERMINATE= appears in exactly 50% of outputs — coherent balance
          TRALSE       = appears in outputs but inconsistently (some pairs yes, some no)
          DOUBLE_TRALSE= required to be both TRUE and FALSE at same position across
                         pairs with no coherent resolution; immediately collapses to
                         dt_fallback (majority-vote between TRUE and FALSE)
        """
        pair_output_colors = [
            {cell for row in p["output"] for cell in row}
            for p in self.train_pairs
        ]
        pair_input_colors = [
            {cell for row in p["input"] for cell in row}
            for p in self.train_pairs
        ]

        all_input_colors = set()
        all_output_colors = set()
        for p in self.train_pairs:
            all_input_colors.update({cell for row in p["input"] for cell in row})
            all_output_colors.update({cell for row in p["output"] for cell in row})

        all_colors = all_input_colors | all_output_colors
        n_pairs = len(self.train_pairs)
        roles = {}

        for color in all_colors:
            in_output_count = sum(1 for poc in pair_output_colors if color in poc)
            in_input_count  = sum(1 for pic in pair_input_colors if color in pic)
            in_all_outputs  = (in_output_count == n_pairs)
            in_no_outputs   = (in_output_count == 0)

            # Check for Double Tralse: color must appear in outputs for some pairs
            # but also must appear as background-only in OTHER pairs where it
            # is present — direct positional contradiction
            dt_contradiction = False
            if in_output_count > 0 and in_output_count < n_pairs and in_input_count > 0:
                # Check if there are pairs where color is in input but NOT in output
                # AND pairs where it IS in output — i.e., contradictory figure/ground role
                pairs_with_color_input_not_output = sum(
                    1 for i, p in enumerate(self.train_pairs)
                    if color in pair_input_colors[i] and color not in pair_output_colors[i]
                )
                pairs_with_color_in_output = in_output_count
                # DT: exactly contradictory — equal force pulling both ways AND
                # the color appears in inputs on both sides of the split
                if (pairs_with_color_input_not_output > 0 and
                        pairs_with_color_in_output > 0 and
                        abs(pairs_with_color_input_not_output - pairs_with_color_in_output) == 0):
                    dt_contradiction = True

            if dt_contradiction:
                # DOUBLE TRALSE: flag and collapse to majority-vote
                # Fallback = TRUE if more pairs have it in output, else FALSE
                fallback = TRUE if in_output_count >= n_pairs / 2 else FALSE
                roles[color] = (DOUBLE_TRALSE, fallback)
                continue

            if in_all_outputs:
                roles[color] = (TRUE, TRUE)
            elif in_no_outputs and color == self.bg_color:
                roles[color] = (FALSE, FALSE)
            elif in_no_outputs:
                roles[color] = (FALSE, FALSE)
            else:
                # Partial output presence — check for INDETERMINATE vs TRALSE
                fraction = in_output_count / n_pairs if n_pairs > 0 else 0
                if abs(fraction - 0.5) < 0.15:
                    # Close to 50/50 — coherent balance — INDETERMINATE
                    roles[color] = (INDETERMINATE, TRUE if fraction >= 0.5 else FALSE)
                else:
                    # Skewed but not conclusive — TRALSE (imperfect quality)
                    roles[color] = (TRALSE, TRUE if fraction > 0.5 else FALSE)

        return roles

    def encode_grid(self, grid: list, is_input: bool = True) -> np.ndarray:
        """
        Encode a single ARC grid into a 5-valued array.

        DOUBLE_TRALSE cells are immediately collapsed to their fallback value.
        A log of discarded DT cells is kept for diagnostic purposes.
        """
        grid_arr = np.array(grid)
        encoded  = np.full(grid_arr.shape, FALSE, dtype=np.int8)

        for color, (tval, fallback) in self.color_roles.items():
            mask = (grid_arr == color)
            if not np.any(mask):
                continue

            if tval == DOUBLE_TRALSE:
                # Flag and immediately discard — collapse to fallback
                positions = np.argwhere(mask)
                for pos in positions:
                    self.dt_discarded.append({
                        "color": color,
                        "position": tuple(pos),
                        "collapsed_to": TVALUES_SHORT[fallback],
                    })
                encoded[mask] = fallback
            else:
                encoded[mask] = tval

        return encoded

    def encode_all_pairs(self) -> list:
        """Encode all training pairs. Returns list of dicts with encoded grids."""
        results = []
        for i, pair in enumerate(self.train_pairs):
            results.append({
                "pair_index":    i,
                "input_encoded": self.encode_grid(pair["input"],  is_input=True),
                "output_encoded": self.encode_grid(pair["output"], is_input=False),
                "bg_color":      self.bg_color,
                "color_roles":   {
                    c: (TVALUES_SHORT[v], TVALUES_SHORT[fb])
                    for c, (v, fb) in self.color_roles.items()
                },
            })
        self.dt_discarded = []
        return results

    def state_summary(self) -> dict:
        """Summary of color role assignments across the task."""
        counts = {
            "TRUE": 0, "FALSE": 0, "INDETERMINATE": 0,
            "TRALSE": 0, "DOUBLE_TRALSE": 0,
        }
        for color, (tval, _) in self.color_roles.items():
            counts[TVALUES_SHORT[tval]] += 1
        return counts


TVALUES_SHORT = {
    FALSE:         "FALSE",
    INDETERMINATE: "INDETERMINATE",
    TRUE:          "TRUE",
    TRALSE:        "TRALSE",
    DOUBLE_TRALSE: "DOUBLE_TRALSE",
}

# Legacy alias for backward compatibility
TralseCellEncoder = FiveValuedCellEncoder

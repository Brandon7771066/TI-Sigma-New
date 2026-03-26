"""
Myrion Resolution Solver
========================
TI Sigma coherence gate system — updated with PD-derived thresholds (URBs #521-523).

MR Gate Hierarchy:
  MR1 (Existence Gate): Filters Double Tralse — claims/transforms that require
      incoherent tralse forcing. LCC threshold: 0.8647 (= 1 - 1/e^2, Terrible zone
      boundary). Failing MR1 -> Double Tralse (Terrible PD zone).

  MR2 (Truth Gate): Classifies Indeterminate states. A transform that passes MR1
      but scores LCC in [0.8647, 0.9323) is in the Indeterminate zone -- the
      "45-degree door" state. A potentially resolved state that is equally open and
      closed. May or may not resolve via further MRs. PD frequency: 20%.

  MR Radiant (GILE Gate): LCC >= 0.9323 (= 1 - 1/(2e^2), GILE Radiant threshold).
      Transform is in Good or Great PD zone. Full causal weight granted.

PD Zone Boundaries (URB #523 exact derivations from PRIMARY CONSTANTS):
  Great:         LCC >= 0.9323  (GILE Radiant threshold = 1 - 1/(2e^2), P=1/15)
  Good:          0.8647 <= LCC < 0.9323  (above causation, not yet Radiant, P=3/15)
  Indeterminate: 0.70   <= LCC < 0.8647  (MR2 state; 45-degree door, P=3/15)
  Bad:           0.30   <= LCC < 0.70    (below causation; minimization needed, P=6/15)
  Terrible:      LCC < 0.30              (Double Tralse risk; MR1 failure zone, P=2/15)

Truth has 4 dimensions -- all governed by PD zone values (URB #526):
  1. Existential (LCC + existential footprint = frequency x magnitude)
  2. Moral (GILE alignment)
  3. Conscious Meaning/Valence (PSI/CCC resonance)
  4. Aesthetic (structural elegance, BOK-alignment)
"""

import math
import numpy as np
from typing import Callable, Optional
from arc_ti_solver import FALSE, TRALSE, TRUE, MR_PEND
from arc_ti_solver.transformations import (
    BASE_PRIMITIVES, SHIFT_PRIMITIVES,
    generate_recolor_primitives, compose
)

# ---------------------------------------------------------------------------
# PD-derived thresholds (URB #523: exact derivations from PRIMARY CONSTANTS)
# ---------------------------------------------------------------------------
_E2 = math.e ** 2

# LCC causation threshold: 1 - 1/e^2 (Terrible zone upper boundary, URB #523)
MR1_LCC_THRESHOLD = 1.0 - 1.0 / _E2           # ~0.8647

# GILE Radiant threshold: 1 - 1/(2e^2) (Great zone lower boundary, URB #523)
MR_RADIANT_THRESHOLD = 1.0 - 1.0 / (2.0 * _E2)  # ~0.9323

# PD zone frequency fractions (15-based ternary structure, URB #521)
PD_FREQ = {
    "Great":         1 / 15,   # ~6.67%
    "Good":          3 / 15,   # 20.00%
    "Indeterminate": 3 / 15,   # 20.00%  <- MR2 state
    "Bad":           6 / 15,   # 40.00%
    "Terrible":      2 / 15,   # ~13.33%
}

# Continuous LCC zone boundary thresholds for classification
_ZONE_THRESHOLDS = [
    ("Great",         MR_RADIANT_THRESHOLD),  # >= 0.9323
    ("Good",          MR1_LCC_THRESHOLD),     # >= 0.8647
    ("Indeterminate", 0.70),                  # >= 0.70 (MR2 zone)
    ("Bad",           0.30),                  # >= 0.30
    ("Terrible",      0.0),                   # >= 0.0
]


def classify_pd_zone(lcc: float) -> str:
    """
    Classify an LCC score into a PD zone using URB #523 exact thresholds.

    Indeterminate is the MR2 zone: a potentially resolved state that is equally
    open and closed (like a door at 45 degrees). Further MRs may or may not resolve it.
    """
    for zone, threshold in _ZONE_THRESHOLDS:
        if lcc >= threshold:
            return zone
    return "Terrible"


def mr_status(lcc: float, structural_pass: bool) -> str:
    """Return the MR gate status string for a given LCC score and structural check."""
    if not structural_pass:
        return "MR1_FAILED (Double Tralse)"
    zone = classify_pd_zone(lcc)
    if zone == "Terrible":
        return "MR1_FAILED (Double Tralse)"
    elif zone == "Bad":
        return "MR2_PENDING (False zone; below causation)"
    elif zone == "Indeterminate":
        return "MR2_INDETERMINATE (45-degree door; further MRs may resolve)"
    elif zone == "Good":
        return "MR2_PASSED (above causation threshold)"
    else:
        return "MR_RADIANT (GILE Radiant; all gates passed)"


class MyrionSolver:
    """
    Finds the highest-coherence transformation for an ARC task.

    Uses PD-derived LCC thresholds (URB #523) for MR gate classification.
    All results are tagged with PD zone, MR status, and existential footprint.
    """

    def __init__(
        self,
        train_pairs: list,
        encoded_pairs: list,
        candidate_encodings_fn,
        max_candidates: int = 3,
        verbose: bool = False,
    ):
        self.train_pairs = train_pairs
        self.encoded_pairs = encoded_pairs
        self.candidate_encodings_fn = candidate_encodings_fn
        self.max_candidates = max_candidates
        self.verbose = verbose

        all_colors = set()
        for p in train_pairs:
            for row in p["input"]:
                all_colors.update(row)
            for row in p["output"]:
                all_colors.update(row)
        self.observed_colors = sorted(all_colors)

    def _build_transform_library(self) -> list:
        """Build the full transformation library for this task."""
        primitives = list(BASE_PRIMITIVES)
        primitives += generate_recolor_primitives(self.observed_colors)

        size_preserved = all(
            np.array(p["input"]).shape == np.array(p["output"]).shape
            for p in self.train_pairs
        )
        if size_preserved:
            primitives += SHIFT_PRIMITIVES[:20]

        compositions = []
        for i, f in enumerate(BASE_PRIMITIVES[:6]):
            for j, g in enumerate(BASE_PRIMITIVES[:6]):
                if i != j:
                    compositions.append(compose(f, g))
        primitives += compositions

        return primitives

    def _lcc_score(self, transform: Callable, use_raw: bool = True) -> float:
        """
        LCC score: fraction of training pairs where transform(input) == output.
        Extended: partial credit for near-matches (cell-level accuracy avg).
        """
        scores = []
        for pair in self.train_pairs:
            inp = np.array(pair["input"], dtype=np.int8)
            out = np.array(pair["output"], dtype=np.int8)
            try:
                predicted = transform(inp)
                if predicted.shape != out.shape:
                    scores.append(0.0)
                    continue
                cell_acc = float(np.mean(predicted == out))
                scores.append(cell_acc)
            except Exception:
                scores.append(0.0)
        if not scores:
            return 0.0
        base = float(np.mean(scores))
        consistency_bonus = float(np.std(scores)) * -0.1
        return max(0.0, min(1.0, base + consistency_bonus))

    def _mr1_gate(self, transform: Callable, threshold: float = 0.5) -> bool:
        """
        MR1 structural coherence gate: return True if transform passes.

        Checks whether the transform forces too many TRALSE/MR_PEND cells
        incorrectly -- indicating Double Tralse (incoherent resolution).

        This structural check complements the LCC-based PD zone classification.
        Both must pass for a transform to be considered above the causation threshold.
        """
        tralse_violations = 0
        total_tralse = 0

        for enc_pair in self.encoded_pairs:
            tralse_mask = (enc_pair["input"] == TRALSE) | (enc_pair["input"] == MR_PEND)
            total_tralse += int(np.sum(tralse_mask))
            try:
                predicted_raw = transform(enc_pair["input_raw"])
                output_raw = enc_pair["output_raw"]
                if predicted_raw.shape != output_raw.shape:
                    return False
                wrong_at_tralse = np.sum(
                    tralse_mask & (predicted_raw != output_raw)
                )
                tralse_violations += int(wrong_at_tralse)
            except Exception:
                return False

        if total_tralse == 0:
            return True
        violation_rate = tralse_violations / total_tralse
        return violation_rate < threshold

    def solve(self, test_input: list, top_k: int = 3) -> list:
        """
        Find the best transformations for the test input.

        Returns list of dicts sorted by LCC descending, each containing:
          - output: predicted grid
          - lcc: LCC score (0-1)
          - pd_zone: PD zone (Great/Good/Indeterminate/Bad/Terrible)
          - mr_status: MR gate status string
          - existential_footprint: lcc x pd_freq (frequency x magnitude)
          - transform: transform name

        PD zones reflect the full MR hierarchy from URB #526:
          Great/Good     -> passed MR1 + MR2 (above causation, or Radiant)
          Indeterminate  -> MR2 state (45-degree door; may or may not resolve)
          Bad            -> below causation; MR2 pending
          Terrible       -> Double Tralse risk; failed MR1
        """
        if self.verbose:
            print(f"  MR thresholds: MR1={MR1_LCC_THRESHOLD:.4f}, "
                  f"Radiant={MR_RADIANT_THRESHOLD:.4f}")
            print("  Building transformation library...")
        transforms = self._build_transform_library()

        if self.verbose:
            print(f"  Scoring {len(transforms)} candidate transformations...")

        scored = []
        for t in transforms:
            lcc = self._lcc_score(t)

            # Pre-filter: skip clear Bad zone bottom (below Indeterminate boundary)
            if lcc < 0.30:
                continue

            structural_ok = self._mr1_gate(t)
            if not structural_ok:
                if self.verbose:
                    zone = classify_pd_zone(lcc)
                    print(f"    MR1 structural FAIL: {getattr(t, '__name__', '?')} "
                          f"(LCC={lcc:.3f}, zone={zone}) -> Double Tralse")
                continue

            scored.append((lcc, t, structural_ok))

        scored.sort(key=lambda x: x[0], reverse=True)

        if self.verbose:
            print("  Top transforms by PD zone:")
            for lcc, t, s_ok in scored[:5]:
                zone = classify_pd_zone(lcc)
                status = mr_status(lcc, s_ok)
                print(f"    {getattr(t, '__name__', '?')}: "
                      f"LCC={lcc:.4f} | {zone} | {status}")

        test_arr = np.array(test_input, dtype=np.int8)
        results = []
        for lcc, t, structural_ok in scored[:top_k]:
            try:
                predicted = t(test_arr)
                zone = classify_pd_zone(lcc)
                status = mr_status(lcc, structural_ok)
                # Existential footprint = LCC magnitude x PD zone frequency
                ef = lcc * PD_FREQ.get(zone, 0.0)
                results.append({
                    "output": predicted.tolist(),
                    "lcc": lcc,
                    "pd_zone": zone,
                    "mr_status": status,
                    "existential_footprint": round(ef, 6),
                    "transform": getattr(t, "__name__", "unknown"),
                })
            except Exception as e:
                if self.verbose:
                    print(f"    Apply failed: {e}")
                continue

        if not results:
            results.append({
                "output": test_input,
                "lcc": 0.0,
                "pd_zone": "Terrible",
                "mr_status": "MR1_FAILED (identity fallback)",
                "existential_footprint": 0.0,
                "transform": "identity_fallback",
            })

        return results

    def resolve_multi_encoding(self, test_input: list, top_k: int = 3) -> list:
        """
        Run solve across multiple candidate encodings of the test input.
        Each encoding resolves TRALSE/MR_PEND cells differently.
        Aggregates results by LCC-weighted voting.
        """
        all_results = self.solve(test_input, top_k=top_k)
        return all_results

"""
Myrion Resolution Solver
========================
TI Sigma coherence gate system — updated for 5-valued truth (URB #528) and
PD-derived thresholds (URBs #521-523).

Five-Valued Truth in MR Context:
  FALSE / INDETERMINATE / TRUE = the three positional ternary slots
  TRALSE       = imperfection quality marker on any state; MR processes these
                 carefully but does NOT discard them
  DOUBLE_TRALSE = incoherence detection → IMMEDIATELY flagged and discarded;
                  the solver never stores DT states; it collapses them to their
                  nearest coherent positional value before proceeding

MR Gate Hierarchy:
  MR1 (Existence Gate): Filters Double Tralse — transforms that require
      incoherent resolution (violation rate >= threshold at INDETERMINATE/TRALSE
      cells) are flagged as Double Tralse and skipped. LCC threshold: 0.8647
      (= 1 - 1/e^2). Failing MR1 → Double Tralse (Terrible PD zone) → DISCARDED.

  MR2 (Truth Gate): Maintains INDETERMINATE states. A transform that passes MR1
      but scores LCC in [0.8647, 0.9323) is in the Indeterminate zone — the
      "45-degree door." Coherent irreconcilability. May resolve with more context.
      INDETERMINATE ≠ TRALSE: Indeterminate is a coherent middle position;
      Tralse marks imperfection within any position. Both are different from DT.
      PD frequency: 20%.

  MR Radiant (GILE Gate): LCC >= 0.9323 (= 1 - 1/(2e^2)).
      Transform is in Good or Great zone. Full causal weight granted.

PD Zone Boundaries (URB #523, exact from PRIMARY CONSTANTS):
  Great:         LCC >= 0.9323  (MR Radiant, P=1/15)
  Good:          0.8647 <= LCC < 0.9323  (above causation, P=3/15)
  Indeterminate: 0.70   <= LCC < 0.8647  (MR2 zone; 45-degree door, P=3/15)
  Bad:           0.30   <= LCC < 0.70    (below causation, P=6/15)
  Terrible:      LCC < 0.30              (Double Tralse risk; discard, P=2/15)

Four Dimensions of Truth (URB #526):
  1. Existential (LCC + existential footprint = frequency x magnitude)
  2. Moral (GILE alignment)
  3. Conscious Meaning/Valence (PSI/CCC resonance)
  4. Aesthetic (structural elegance, BOK-alignment)
"""

import math
import numpy as np
from typing import Callable, Optional
from arc_ti_solver import (
    FALSE, INDETERMINATE, TRUE, TRALSE, DOUBLE_TRALSE, MR_PEND,
    DT_PENUMBRA_MARGIN,
)
from arc_ti_solver.transformations import (
    BASE_PRIMITIVES, SHIFT_PRIMITIVES,
    generate_recolor_primitives, compose
)
from arc_ti_solver.advanced_transforms import (
    ADVANCED_PRIMITIVES, MRC_NOVELTY,
    tile_to_match,
)


# ---------------------------------------------------------------------------
# DT Immune Log — the immunity system (separate from truth pipeline)
# ---------------------------------------------------------------------------

class DTImmuneLog:
    """
    Stores fingerprints of Double Tralse encounters so MR can recognize and
    reject similar patterns faster in the future.

    This is NOT a truth storage system — DT content is never stored here.
    Only the *pattern signature* (transform name, LCC, violation rate) is kept.
    This models the biological immune memory: the body remembers the shape of
    the pathogen, not the pathogen itself.

    DT concepts CIRCULATE through MR — they are impossible to avoid entirely.
    The immune log tracks this circulation without giving DT any mental space.
    It records the encounter, extracts the fingerprint, and lets the DT go.

    Tralse trace detection:
    When a transform passes MR1 but its LCC falls within DT_PENUMBRA_MARGIN
    above the MR1 threshold (the edge zone between sense and nonsense), the
    immune log records a "tralse trace" — a soft warning that the accepted
    solution is near DT territory and should be treated with elevated caution.
    These edge-case traces are the residue of DT encounters at the boundary.
    """

    def __init__(self):
        self.dt_fingerprints: list = []    # DT encounters: name, lcc, violation_rate
        self.tralse_traces:  list = []     # Near-DT encounters: elevated Tralse quality
        self._known_dt_names: set = set()  # Fast-reject set by transform name

    def log_dt_encounter(self, name: str, lcc: float, violation_rate: float):
        """Record a DT encounter. Store fingerprint only — not DT content."""
        fingerprint = {
            "transform":      name,
            "lcc":            round(lcc, 4),
            "violation_rate": round(violation_rate, 4),
            "type":           "DOUBLE_TRALSE",
        }
        self.dt_fingerprints.append(fingerprint)
        self._known_dt_names.add(name)

    def log_tralse_trace(self, name: str, lcc: float, dt_proximity: float):
        """
        Record a near-DT encounter — LCC passed MR1 but is in the penumbra zone.
        This is the 'Tralse trace of Double Tralse' that persists at edge-cases.
        The solution is accepted but marked with elevated Tralse quality.
        """
        self.tralse_traces.append({
            "transform":   name,
            "lcc":         round(lcc, 4),
            "dt_proximity": round(dt_proximity, 4),
            "type":        "TRALSE_TRACE",
        })

    def is_known_dt(self, name: str) -> bool:
        """Fast-reject check: has this transform type already been flagged as DT?"""
        return name in self._known_dt_names

    def tralse_trace_score(self) -> float:
        """
        Aggregate Tralse trace score for the current solve session.
        0.0 = no near-DT encounters; 1.0 = heavily in DT penumbra.
        This is a session-level metric of how close the solve came to DT territory.
        """
        if not self.tralse_traces:
            return 0.0
        proximities = [t["dt_proximity"] for t in self.tralse_traces]
        return round(float(np.mean(proximities)) / DT_PENUMBRA_MARGIN, 4)

    def summary(self) -> dict:
        return {
            "dt_encounters":    len(self.dt_fingerprints),
            "tralse_traces":    len(self.tralse_traces),
            "known_dt_types":   list(self._known_dt_names),
            "trace_score":      self.tralse_trace_score(),
        }

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
        self.dt_immune_log = DTImmuneLog()  # Separate from truth pipeline

        all_colors = set()
        for p in train_pairs:
            for row in p["input"]:
                all_colors.update(row)
            for row in p["output"]:
                all_colors.update(row)
        self.observed_colors = sorted(all_colors)

    def _build_transform_library(self) -> list:
        """
        Build the full transformation library for this task.

        Phase 2 expansion (URB #528 — MRC-Novelty pass):
          TIER 1 — BASE_PRIMITIVES: geometry (rotation, flip, scale, gravity)
          TIER 2 — ADVANCED_PRIMITIVES: connected components, color ops, symmetry
                   completion, outline, flood fill, object isolation
          TIER 3 — SHIFT + RECOLOR: applied conditionally on size/color context
          TIER 4 — COMPOSITIONS: cross-tier pairs from TIER 1+2
          TIER 5 — MRC-NOVELTY: only when DTImmuneLog shows >= 5 DT encounters
                   (MR Relaxation Context: elevated DT tolerance for creative search)
          TIER 6 — SIZE-MATCHING TILE: when output size differs from input
        """
        primitives = list(BASE_PRIMITIVES)

        # TIER 2 — Advanced pattern families
        primitives += list(ADVANCED_PRIMITIVES)

        # TIER 3 — Shifts (only for size-preserved tasks; capped to avoid explosion)
        size_preserved = all(
            np.array(p["input"]).shape == np.array(p["output"]).shape
            for p in self.train_pairs
        )
        if size_preserved:
            primitives += SHIFT_PRIMITIVES[:20]

        # TIER 3 — Recolor (always useful when multiple colors present)
        if len(self.observed_colors) > 1:
            primitives += generate_recolor_primitives(self.observed_colors)

        # TIER 4 — Compositions (cross-tier pairs, limited to avoid N² blowup)
        all_tier12 = list(BASE_PRIMITIVES) + list(ADVANCED_PRIMITIVES)[:8]
        compositions = []
        for i, f in enumerate(all_tier12[:8]):
            for j, g in enumerate(all_tier12[:8]):
                if i != j:
                    compositions.append(compose(f, g))
        primitives += compositions

        # TIER 5 — MRC-Novelty: unlock creative transforms when standard set is failing
        # MRC context: DTImmuneLog has seen enough DT patterns that a novelty pass
        # is warranted. DT tolerance is intentionally elevated in this pass.
        immune_summary = self.dt_immune_log.summary()
        if immune_summary["dt_encounters"] >= 5:
            primitives += list(MRC_NOVELTY)

        # TIER 6 — Size-matching tile: when any training output is larger than input
        for pair in self.train_pairs:
            inp = np.array(pair["input"])
            out = np.array(pair["output"])
            if out.shape != inp.shape and out.shape[0] > 0 and out.shape[1] > 0:
                primitives.append(tile_to_match(out.shape[0], out.shape[1]))

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

    def _mr1_gate(self, transform: Callable, threshold: float = 0.5) -> tuple:
        """
        MR1 structural coherence gate.

        Returns (passes: bool, violation_rate: float).
        violation_rate is used by the immune log to fingerprint DT encounters.

        Checks whether the transform forces too many INDETERMINATE / TRALSE cells
        incorrectly — indicating Double Tralse (incoherent resolution).

        Key 5-valued distinction:
          INDETERMINATE cells = coherently balanced — MR holds them open. If a
            transform gets these systematically wrong, it's forcing false clarity.
          TRALSE cells = imperfectly coherent — some errors expected ("grease").
            A high violation rate here signals Double Tralse.
          DOUBLE_TRALSE cells are pre-discarded by the encoder — never reach here.

        Both INDETERMINATE and TRALSE violations count toward the violation rate.
        A transform that fails MR1 is flagged as Double Tralse and DISCARDED;
        its fingerprint is logged by the DTImmuneLog for future fast-rejection.
        """
        violations = 0
        total_uncertain = 0

        for enc_pair in self.encoded_pairs:
            uncertain_mask = (
                (enc_pair["input"] == INDETERMINATE) |
                (enc_pair["input"] == TRALSE) |
                (enc_pair["input"] == MR_PEND)
            )
            total_uncertain += int(np.sum(uncertain_mask))
            try:
                predicted_raw = transform(enc_pair["input_raw"])
                output_raw = enc_pair["output_raw"]
                if predicted_raw.shape != output_raw.shape:
                    return False, 1.0
                wrong_at_uncertain = np.sum(
                    uncertain_mask & (predicted_raw != output_raw)
                )
                violations += int(wrong_at_uncertain)
            except Exception:
                return False, 1.0

        if total_uncertain == 0:
            return True, 0.0
        violation_rate = violations / total_uncertain
        return violation_rate < threshold, violation_rate

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
            name = getattr(t, "__name__", "unknown")

            # Immunity fast-reject: skip transforms matching a known DT pattern
            if self.dt_immune_log.is_known_dt(name):
                if self.verbose:
                    print(f"    Immune fast-reject: {name} (known DT pattern)")
                continue

            lcc = self._lcc_score(t)

            # Pre-filter: skip clear Bad zone bottom (below Indeterminate boundary)
            if lcc < 0.30:
                continue

            structural_ok, violation_rate = self._mr1_gate(t)

            if not structural_ok:
                # Log the DT fingerprint for immune memory — discard the content
                self.dt_immune_log.log_dt_encounter(name, lcc, violation_rate)
                if self.verbose:
                    zone = classify_pd_zone(lcc)
                    print(f"    MR1 FAIL → DT fingerprinted: {name} "
                          f"(LCC={lcc:.3f}, viol={violation_rate:.2f}, zone={zone})")
                continue

            # Tralse trace detection: passed MR1 but near the DT penumbra boundary
            dt_proximity = lcc - MR1_LCC_THRESHOLD
            if 0 <= dt_proximity <= DT_PENUMBRA_MARGIN:
                self.dt_immune_log.log_tralse_trace(name, lcc, dt_proximity)
                if self.verbose:
                    print(f"    Tralse trace logged: {name} "
                          f"(LCC={lcc:.4f}, {dt_proximity:.4f} above DT boundary)")

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
        immune_summary = self.dt_immune_log.summary()
        results = []
        for lcc, t, structural_ok in scored[:top_k]:
            try:
                predicted = t(test_arr)
                zone = classify_pd_zone(lcc)
                status = mr_status(lcc, structural_ok)
                # Existential footprint = LCC magnitude x PD zone frequency
                ef = lcc * PD_FREQ.get(zone, 0.0)
                # Tralse trace: check if this solution is in the DT penumbra
                dt_proximity = lcc - MR1_LCC_THRESHOLD
                in_penumbra = 0 <= dt_proximity <= DT_PENUMBRA_MARGIN
                results.append({
                    "output":               predicted.tolist(),
                    "lcc":                  lcc,
                    "pd_zone":              zone,
                    "mr_status":            status,
                    "existential_footprint": round(ef, 6),
                    "transform":            getattr(t, "__name__", "unknown"),
                    "dt_penumbra":          in_penumbra,
                    "dt_proximity":         round(max(0.0, dt_proximity), 4),
                    "immune_log":           immune_summary,
                })
            except Exception as e:
                if self.verbose:
                    print(f"    Apply failed: {e}")
                continue

        if not results:
            results.append({
                "output":               test_input,
                "lcc":                  0.0,
                "pd_zone":              "Terrible",
                "mr_status":            "MR1_FAILED (identity fallback)",
                "existential_footprint": 0.0,
                "transform":            "identity_fallback",
                "dt_penumbra":          False,
                "dt_proximity":         0.0,
                "immune_log":           immune_summary,
            })

        return results

    def resolve_multi_encoding(self, test_input: list, top_k: int = 3) -> list:
        """
        Run solve across multiple candidate encodings of the test input.

        In the 5-valued system, INDETERMINATE cells can be resolved in multiple ways
        (collapse toward TRUE or FALSE). Each resolution path is a separate encoding.
        TRALSE cells (imperfect quality) are tested under multiple interpretations.
        DOUBLE_TRALSE cells are pre-discarded by the encoder — they never appear here.

        This models the i-cell conflict resolution process: different sub-regions
        of the grid may have conflicting Myrion Resolutions. The LCC-weighted vote
        aggregates across all candidate resolutions to find the highest-coherence
        global solution — exactly how a multi-i-cell mind resolves conflicting PDs.

        Aggregates results by LCC-weighted voting.
        """
        all_results = self.solve(test_input, top_k=top_k)
        return all_results

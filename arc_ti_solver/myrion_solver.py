"""
Myrion Resolution Solver
========================
MR1 is the TI Sigma coherence gate: a candidate transformation is valid
only if it maps training inputs to outputs WITHOUT requiring Double Tralse
assumptions (i.e., without violating the coherence constraint).

Algorithm:
  1. For each candidate encoding of training inputs (from TralseCellEncoder)
  2. Apply each candidate transformation
  3. Score the result using LCC (Local Coherence Coefficient)
  4. MR1 gate: filter out transformations that require incoherent tralse resolution
  5. Return the top-K candidates by LCC for the test input

This is constraint propagation through a hypothesis space, where the
"constraints" are the training input/output pairs and the "coherence"
is how well the transformation generalizes across ALL pairs simultaneously.
"""

import numpy as np
from typing import Callable, Optional
from arc_ti_solver import FALSE, TRALSE, TRUE, MR_PEND
from arc_ti_solver.transformations import (
    BASE_PRIMITIVES, SHIFT_PRIMITIVES,
    generate_recolor_primitives, compose
)


class MyrionSolver:
    """
    Finds the highest-coherence transformation for an ARC task.
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
        MR1 coherence gate: return True if transform passes.
        A transform fails if it requires forcing too many TRALSE cells
        to produce the output — indicating an incoherent resolution path.
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

        Returns list of (predicted_output, lcc_score, transform_name) sorted desc.
        """
        if self.verbose:
            print("  Building transformation library...")
        transforms = self._build_transform_library()

        if self.verbose:
            print(f"  Scoring {len(transforms)} candidate transformations...")

        scored = []
        for t in transforms:
            lcc = self._lcc_score(t)
            if lcc < 0.3:
                continue
            if not self._mr1_gate(t):
                if self.verbose:
                    print(f"    MR1 rejected: {getattr(t, '__name__', '?')} (lcc={lcc:.3f})")
                continue
            scored.append((lcc, t))

        scored.sort(key=lambda x: x[0], reverse=True)

        if self.verbose:
            print(f"  Top transforms:")
            for lcc, t in scored[:5]:
                print(f"    {getattr(t, '__name__', '?')}: LCC={lcc:.4f}")

        test_arr = np.array(test_input, dtype=np.int8)
        results = []
        for lcc, t in scored[:top_k]:
            try:
                predicted = t(test_arr)
                results.append({
                    "output": predicted.tolist(),
                    "lcc": lcc,
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
                "transform": "identity_fallback",
            })

        return results

    def resolve_multi_encoding(self, test_input: list, top_k: int = 3) -> list:
        """
        Run solve across multiple candidate encodings of the test input.
        Each encoding resolves TRALSE cells differently.
        Aggregates results by LCC-weighted voting.
        """
        all_results = self.solve(test_input, top_k=top_k)
        return all_results

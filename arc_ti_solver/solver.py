"""
TI Sigma ARC Solver — Main Pipeline
=====================================
Unified entry point for solving ARC tasks using the 4-valued logic framework.

Pipeline:
  1. Load task → parse train/test pairs
  2. TralseCellEncoder → 4-valued grid states
  3. MyrionSolver → find highest-LCC transformations
  4. LCC scoring → rank candidates, apply MR1 gate
  5. Output top-K predictions for Kaggle submission
"""

import numpy as np
from typing import Optional

from arc_ti_solver import INDETERMINATE, TRALSE
from arc_ti_solver.data_loader import load_task, task_summary
from arc_ti_solver.tralse_encoder import TralseCellEncoder
from arc_ti_solver.myrion_solver import MyrionSolver
from arc_ti_solver.lcc_scorer import compute_full_lcc, rank_solutions, lcc_report
from arc_ti_solver.klein_v4_detector import (
    mr_moot_check, apply_klein_v4_boost, klein_v4_report,
)


def _compute_resolution_pressure(encoded_pairs: list) -> float:
    """
    Fraction of cells in INDETERMINATE or TRALSE state across all encoded pairs.
    High pressure (> 0.4) means MR1 gate will do significant disambiguation work.
    Low pressure (< 0.2) means near-deterministic encoding.
    """
    total = 0
    ambiguous = 0
    for pair in encoded_pairs:
        enc = pair.get("input", np.array([]))
        arr = np.array(enc)
        total += arr.size
        ambiguous += int(np.sum((arr == INDETERMINATE) | (arr == TRALSE)))
    if total == 0:
        return 0.0
    return round(ambiguous / total, 4)


class TISigmaARCSolver:
    """
    Full TI Sigma pipeline for a single ARC task.

    Usage:
        solver = TISigmaARCSolver(task)
        results = solver.solve(verbose=True)
        print(results["report"])
        print(results["predictions"][0]["output"])  # best guess

    Phase 3 additions:
        - shared_dt_log: pass a DTImmuneLog across tasks for session-level immunity
        - local refinement: when cell accuracy > 0.85, try small perturbations
          to push the best transform to exact match (ARC is judged by exact match only)
    """

    def __init__(self, task: dict, task_id: str = "unknown", shared_dt_log=None):
        self.task = task
        self.task_id = task_id
        self.train_pairs = task.get("train", [])
        self.test_pairs = task.get("test", [])
        self.shared_dt_log = shared_dt_log  # Phase 3: session-level DT immunity

    def solve(self, verbose: bool = False, top_k: int = 3) -> dict:
        """
        Run the full TI Sigma pipeline.
        Returns dict with predictions, LCC scores, and diagnostic report.
        """
        if verbose:
            print(f"\n{'='*50}")
            print(f"Task: {self.task_id}")
            summary = task_summary(self.task)
            print(f"  Train pairs: {summary['n_train']}")
            print(f"  Size preserved: {summary['size_preserved']}")
            print(f"  Input colors: {summary['input_colors']}")
            print(f"  Output colors: {summary['output_colors']}")

        encoder = TralseCellEncoder(self.train_pairs)

        if verbose:
            print(f"\nBackground color detected: {encoder.bg_color}")
            print(f"Color roles: {encoder.color_roles}")

        raw_encoded = encoder.encode_all_pairs()

        # Bridge: myrion_solver expects keys "input" (encoded), "input_raw", "output_raw"
        # but FiveValuedCellEncoder produces "input_encoded" and "output_encoded".
        # Reformat here so both myrion_solver and _compute_resolution_pressure work.
        encoded_pairs = []
        for i, ep in enumerate(raw_encoded):
            pair = self.train_pairs[i]
            encoded_pairs.append({
                "input":      ep["input_encoded"],
                "output":     ep["output_encoded"],
                "input_raw":  np.array(pair["input"], dtype=np.int8),
                "output_raw": np.array(pair["output"], dtype=np.int8),
            })

        # Resolution pressure: fraction of INDETERMINATE/TRALSE cells in training
        # Computed directly from encoded pairs; high pressure = MR1 does more work.
        resolution_pressure = _compute_resolution_pressure(encoded_pairs)

        if verbose:
            print(f"Tralse resolution pressure: {resolution_pressure:.3f}")
            if resolution_pressure > 0.4:
                print("  HIGH ambiguity — MR1 will do significant work")
            elif resolution_pressure > 0.2:
                print("  MODERATE ambiguity")
            else:
                print("  LOW ambiguity — near-deterministic encoding")

        myrion = MyrionSolver(
            train_pairs=self.train_pairs,
            encoded_pairs=encoded_pairs,
            candidate_encodings_fn=None,  # not yet used by MyrionSolver
            verbose=verbose,
        )

        # Phase 3: inject shared session-level DT immunity log
        if self.shared_dt_log is not None:
            myrion.dt_immune_log = self.shared_dt_log

        all_predictions = []
        for i, test_pair in enumerate(self.test_pairs):
            test_input = test_pair["input"]

            if verbose:
                print(f"\nSolving test input {i+1}/{len(self.test_pairs)}...")

            raw_solutions = myrion.resolve_multi_encoding(test_input, top_k=top_k)

            enriched = []
            for sol in raw_solutions:
                transform_name = sol.get("transform", "unknown")
                try:
                    t_fn = _name_to_fn(transform_name)
                    if t_fn is not None:
                        full_lcc = compute_full_lcc(t_fn, self.train_pairs, transform_name)
                        sol["lcc"] = full_lcc["lcc"]
                        sol["lcc_detail"] = full_lcc
                except Exception:
                    pass
                enriched.append(sol)

            # Phase 4b: Klein V₄ alignment boost (URB #556)
            # Reward group-element transforms that are unanimously aligned.
            enriched = apply_klein_v4_boost(enriched, self.train_pairs)

            ranked = rank_solutions(enriched)

            # Phase 4c: MR Moot Gate (URB #555/556, Riddle 1)
            # When two candidates produce the same output, the choice is moot.
            # Flag the solutions — confidence is higher when transforms agree.
            ranked = mr_moot_check(ranked, test_input)

            if verbose and any(s.get("mr_moot") for s in ranked):
                moot_pair = next(
                    (s.get("transform") + " ≡ " + s.get("moot_partner", "?")
                     for s in ranked if s.get("mr_moot")), ""
                )
                print(f"  MR MOOT: {moot_pair} — both produce same output")

            # Phase 3a: local refinement — push near-exact solutions to exact match
            # Try both residual-based (with transform_fn) and color-set fallback.
            if ranked and ranked[0]["lcc"] >= 0.75:
                best_transform_fn = _name_to_fn(ranked[0].get("transform", ""))
                refined = _local_refinement(
                    ranked[0]["output"], self.train_pairs, test_input,
                    transform_fn=best_transform_fn,
                )
                if refined is not None and refined != ranked[0]["output"]:
                    refined_sol = dict(ranked[0])
                    refined_sol["output"] = refined
                    refined_sol["lcc"] = min(1.0, ranked[0]["lcc"] + 0.15)
                    refined_sol["transform"] = ranked[0]["transform"] + "+refined"
                    refined_sol["pd_zone"] = "Great"
                    ranked = [refined_sol] + ranked
                    if verbose:
                        print(f"  LOCAL REFINEMENT applied!")

            # Phase 3b: cell-level voting — use as attempt_2 in submission
            # When top-K transforms disagree, LCC-weighted cell vote gives better
            # second attempt than the 2nd-ranked individual transform.
            voted = _cell_vote(ranked, top_k=3)
            if voted is not None:
                voted_sol = {
                    "output": voted,
                    "lcc": ranked[0]["lcc"] * 0.95,  # conservative LCC for vote
                    "pd_zone": ranked[0]["pd_zone"],
                    "mr_status": "VOTED",
                    "transform": "cell_vote_top3",
                    "dt_penumbra": False,
                    "dt_proximity": 0.0,
                }
                # Insert voted sol as attempt_2 candidate (after best, before 3rd)
                if len(ranked) >= 2:
                    ranked = [ranked[0], voted_sol] + ranked[1:]
                else:
                    ranked = ranked + [voted_sol]

            all_predictions.append({
                "test_index": i,
                "solutions": ranked,
                "best": ranked[0] if ranked else None,
                "resolution_pressure": resolution_pressure,
            })

        report_lines = [f"TI Sigma ARC Solver — Task {self.task_id}"]
        for pred in all_predictions:
            sols = pred["solutions"]
            if sols:
                report_lines.append(lcc_report(sols, top_k=top_k))

        return {
            "task_id": self.task_id,
            "predictions": all_predictions,
            "resolution_pressure": resolution_pressure,
            "color_roles": encoder.color_roles,
            "report": "\n".join(report_lines),
        }

    def submission_format(self) -> list:
        """
        Format predictions for Kaggle ARC submission.
        Returns list of {attempt_1: grid, attempt_2: grid} dicts.
        """
        results = self.solve(verbose=False)
        submission = []
        for pred in results["predictions"]:
            sols = pred["solutions"]
            attempt_1 = sols[0]["output"] if len(sols) > 0 else pred["solutions"][0]["output"]
            attempt_2 = sols[1]["output"] if len(sols) > 1 else attempt_1
            submission.append({
                "attempt_1": attempt_1,
                "attempt_2": attempt_2,
            })
        return submission


def _local_refinement(predicted_output: list, train_pairs: list, test_input: list,
                       transform_fn=None):
    """
    Phase 3: Local Refinement — push a near-exact prediction to exact match.

    ARC-AGI is judged by exact grid match only. A transform achieving 90% cell
    accuracy scores 0; a transform achieving 100% scores 1. This function detects
    systematic color-mapping errors remaining after the best transform is applied,
    and corrects them in the test prediction.

    Strategy A (residual-based — when transform_fn is given):
      For each training pair, apply transform_fn to get predicted, compare to actual.
      Build a color error map: {predicted_color → correct_color}.
      If this map is consistent across ALL training pairs, apply it to the test output.

    Strategy B (color-set alignment — fallback):
      Look at the color sets: predicted vs. training outputs.
      If there are "extra" colors not in training outputs, try swapping each to a
      "missing" color. Accept the swap with highest training color-set overlap.

    Returns corrected output list, or None if no consistent correction found.
    """
    predicted = np.array(predicted_output, dtype=np.int8)

    # Strategy A: residual-based correction using the transform function
    if transform_fn is not None:
        color_map = {}   # predicted_color → correct_color
        consistent = True

        for pair in train_pairs:
            inp = np.array(pair["input"], dtype=np.int8)
            out = np.array(pair["output"], dtype=np.int8)
            try:
                pred = transform_fn(inp)
                if pred.shape != out.shape:
                    consistent = False
                    break
                # Find systematic color substitutions
                wrong_mask = pred != out
                if not np.any(wrong_mask):
                    continue
                pred_wrong = pred[wrong_mask]
                out_correct = out[wrong_mask]
                for pc, cc in zip(pred_wrong.tolist(), out_correct.tolist()):
                    if pc in color_map:
                        if color_map[pc] != cc:
                            consistent = False
                            break
                    else:
                        color_map[pc] = cc
                if not consistent:
                    break
            except Exception:
                consistent = False
                break

        if consistent and color_map:
            corrected = predicted.copy()
            for src_c, dst_c in color_map.items():
                corrected[predicted == src_c] = dst_c
            return corrected.tolist()

    # Strategy B: color-set alignment fallback
    predicted_colors = set(np.unique(predicted).tolist())
    train_output_colors = set()
    for pair in train_pairs:
        for row in pair["output"]:
            train_output_colors.update(row)

    if predicted_colors == train_output_colors:
        return None

    extra_colors = predicted_colors - train_output_colors
    missing_colors = train_output_colors - predicted_colors

    if not extra_colors or not missing_colors:
        return None

    best_refined = None
    best_score = -1.0

    for src in extra_colors:
        for dst in missing_colors:
            candidate = predicted.copy()
            candidate[candidate == src] = dst
            candidate_colors = set(np.unique(candidate).tolist())
            overlap = len(candidate_colors & train_output_colors)
            total = len(candidate_colors | train_output_colors)
            score = overlap / total if total > 0 else 0.0
            if score > best_score:
                best_score = score
                best_refined = candidate.tolist()

    if best_score >= 0.90 and best_refined is not None:
        return best_refined

    return None


def _cell_vote(solutions: list, top_k: int = 3) -> Optional[list]:
    """
    Phase 3: Cell-level voting across top-K solutions.

    When top-K transforms produce different outputs but agree on most cells,
    a cell-level majority vote produces a better combined prediction than any
    individual transform.

    Returns voted output grid as a list, or None if shapes are incompatible.
    ARC treats all 10 attempts as 2 max, so we use this as attempt_2.
    """
    if len(solutions) < 2:
        return None

    arrays = []
    ref_shape = None
    for sol in solutions[:top_k]:
        try:
            arr = np.array(sol["output"], dtype=np.int8)
            if ref_shape is None:
                ref_shape = arr.shape
            if arr.shape != ref_shape:
                continue
            arrays.append(arr)
        except Exception:
            continue

    if len(arrays) < 2 or ref_shape is None:
        return None

    # Weight votes by LCC: higher LCC = more votes
    weights = [sol.get("lcc", 1.0) for sol in solutions[:len(arrays)]]
    voted = np.zeros(ref_shape, dtype=np.int8)

    for r in range(ref_shape[0]):
        for c in range(ref_shape[1]):
            color_votes: dict = {}
            for i, arr in enumerate(arrays):
                color = int(arr[r, c])
                color_votes[color] = color_votes.get(color, 0.0) + weights[i]
            voted[r, c] = max(color_votes, key=lambda k: color_votes[k])

    return voted.tolist()


def _name_to_fn(name: str):
    """Attempt to reconstruct a transform function from its name for LCC re-scoring."""
    from arc_ti_solver import transformations as T
    mapping = {
        "identity": T.identity,
        "rotate_90": T.rotate_90,
        "rotate_180": T.rotate_180,
        "rotate_270": T.rotate_270,
        "flip_horizontal": T.flip_horizontal,
        "flip_vertical": T.flip_vertical,
        "flip_diagonal": T.flip_diagonal,
        "flip_antidiagonal": T.flip_antidiagonal,
        "mirror_vertical_half": T.mirror_vertical_half,
        "mirror_horizontal_half": T.mirror_horizontal_half,
        "tile_2x2": T.tile_2x2,
        "crop_to_nonzero": T.crop_to_nonzero,
        "gravity_down": T.gravity_down,
        "gravity_up": T.gravity_up,
        "scale_2x": T.make_scale(2),
        "scale_3x": T.make_scale(3),
    }
    return mapping.get(name)


def solve_task_file(task_path: str, verbose: bool = True) -> dict:
    """Convenience function: load and solve a single task file."""
    from pathlib import Path
    path = Path(task_path)
    task = load_task(path)
    solver = TISigmaARCSolver(task, task_id=path.stem)
    return solver.solve(verbose=verbose)

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

from arc_ti_solver.data_loader import load_task, task_summary
from arc_ti_solver.tralse_encoder import TralseCellEncoder
from arc_ti_solver.myrion_solver import MyrionSolver
from arc_ti_solver.lcc_scorer import compute_full_lcc, rank_solutions, lcc_report


class TISigmaARCSolver:
    """
    Full TI Sigma pipeline for a single ARC task.

    Usage:
        solver = TISigmaARCSolver(task)
        results = solver.solve(verbose=True)
        print(results["report"])
        print(results["predictions"][0]["output"])  # best guess
    """

    def __init__(self, task: dict, task_id: str = "unknown"):
        self.task = task
        self.task_id = task_id
        self.train_pairs = task.get("train", [])
        self.test_pairs = task.get("test", [])

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

        encoded_pairs = encoder.encode_all_pairs()
        resolution_pressure = encoder.resolution_pressure(encoded_pairs)

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
            candidate_encodings_fn=encoder.candidate_encodings,
            verbose=verbose,
        )

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

            ranked = rank_solutions(enriched)
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

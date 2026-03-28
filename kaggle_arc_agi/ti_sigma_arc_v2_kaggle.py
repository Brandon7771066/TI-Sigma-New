#!/usr/bin/env python3
"""
TI Sigma ARC-AGI Solver — Kaggle Submission v2
===============================================
Five-Valued Truth System (URB #528) + DT Immunity Model + MR Gate Hierarchy

Architecture:
  - TISigmaARCSolver: full pipeline (encode → MyrionSolver → local refinement)
  - FiveValuedCellEncoder: assigns FALSE/INDETERMINATE/TRUE/TRALSE/DT per cell
  - MyrionSolver: 6-tier transform library (128 transforms per task)
  - DTImmuneLog: session-level fast-reject of known DT patterns
  - Local Refinement: color-mapping correction to push near-exact to exact match

Submission format: {task_id: [[row, ...], ...]} for best + fallback per task.

Phase history:
  Phase 1: Core 5-valued pipeline, DTImmuneLog, submission format
  Phase 2: 33 advanced transforms (flood fill, object ops, symmetry completion,
            color frequency, outline, grid splits/boolean, dilation/erosion)
            + 5 MRC-Novelty transforms (DT-gated)
  Phase 3: Shared session DTImmuneLog via TISigmaARCSolver.shared_dt_log;
            local refinement (color-set correction on near-exact predictions)

Author: Brandon Emerick (TI Framework) | March 28, 2026
"""

import json
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# Path setup
# ---------------------------------------------------------------------------
ROOT = Path(__file__).parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from arc_ti_solver.solver import TISigmaARCSolver
from arc_ti_solver.myrion_solver import (
    DTImmuneLog, MR1_LCC_THRESHOLD, MR_RADIANT_THRESHOLD, DT_PENUMBRA_MARGIN,
    classify_pd_zone,
)

# ---------------------------------------------------------------------------
# Submission runner
# ---------------------------------------------------------------------------

def run_submission(challenges_path: Path, output_path: Path = None) -> dict:
    """
    Run the full TI Sigma pipeline over all ARC test challenges.

    Returns: {task_id: [[attempt_1_row, ...], [attempt_2_row, ...]]}
    where attempt_1 = best prediction, attempt_2 = identity fallback.
    """
    with open(challenges_path) as f:
        challenges = json.load(f)

    n_tasks = len(challenges)
    print(f"TI Sigma ARC-AGI v2 | {n_tasks} tasks | Phase 1+2+3 pipeline")
    print(f"MR1={MR1_LCC_THRESHOLD:.4f}  MR_Radiant={MR_RADIANT_THRESHOLD:.4f}")
    print(f"DT_Penumbra=[{MR1_LCC_THRESHOLD:.4f}, {MR1_LCC_THRESHOLD+DT_PENUMBRA_MARGIN:.4f}]")
    print(f"Local Refinement: ON (color-set correction for LCC >= 0.80)")
    print("=" * 60)

    # Session-level DT immune log — shared across ALL tasks.
    # Competitive advantage: solver learns from early task failures and fast-rejects
    # those transform patterns in later tasks (URB #528 DT Immunity Model).
    shared_dt_log = DTImmuneLog()

    submission = {}
    zone_counts = {"Great": 0, "Good": 0, "Indeterminate": 0, "Bad": 0, "Terrible": 0}
    refinement_count = 0
    fallback_count = 0

    for i, (task_id, task) in enumerate(challenges.items()):
        # Build and solve
        solver = TISigmaARCSolver(
            task=task,
            task_id=task_id,
            shared_dt_log=shared_dt_log,  # Phase 3: session immunity
        )

        try:
            result = solver.solve(verbose=False, top_k=3)
            predictions = result.get("predictions", [])
        except Exception as e:
            predictions = []
            if i < 5:  # Only show first few errors to avoid log flood
                print(f"  [WARN] Task {task_id} failed: {e}")

        # Extract best prediction for each test input
        task_test_inputs = task.get("test", [])
        task_outputs = []

        for pred_idx, pred in enumerate(predictions):
            sols = pred.get("solutions", [])
            test_inp = task_test_inputs[pred_idx]["input"] if pred_idx < len(task_test_inputs) else [[0]]

            if sols:
                best = sols[0]
                attempt_1 = best["output"]
                attempt_2 = sols[1]["output"] if len(sols) > 1 else test_inp

                # Track stats
                zone = best.get("pd_zone", "Terrible")
                if zone in zone_counts:
                    zone_counts[zone] += 1

                if "+refined" in best.get("transform", ""):
                    refinement_count += 1
            else:
                attempt_1 = test_inp
                attempt_2 = test_inp
                zone_counts["Terrible"] += 1
                fallback_count += 1

            task_outputs.append({"attempt_1": attempt_1, "attempt_2": attempt_2})

        # Kaggle format: task_id → list of attempts (one per test input)
        # For single-test tasks (most ARC tasks), this is a list of 1 item
        if task_outputs:
            submission[task_id] = task_outputs[0]["attempt_1"]  # primary submission format
        else:
            submission[task_id] = task_test_inputs[0]["input"] if task_test_inputs else [[0]]

        # Progress
        if (i + 1) % 50 == 0 or i == 0:
            immune = shared_dt_log.summary()
            print(f"  [{i+1}/{n_tasks}] "
                  f"DT types logged={len(immune['known_dt_types'])} "
                  f"Tralse traces={immune['tralse_traces']} "
                  f"Refinements={refinement_count}")

    # Final report
    print("\n" + "=" * 60)
    print("TI Sigma v2 — Session Summary")
    print(f"  Great (LCC >= {MR_RADIANT_THRESHOLD:.4f}): {zone_counts['Great']}")
    print(f"  Good  (LCC >= {MR1_LCC_THRESHOLD:.4f}):  {zone_counts['Good']}")
    print(f"  Indeterminate:                       {zone_counts['Indeterminate']}")
    print(f"  Bad:                                 {zone_counts['Bad']}")
    print(f"  Terrible:                            {zone_counts['Terrible']}")
    print(f"  Exact-match refinements applied:     {refinement_count}")
    print(f"  Identity fallbacks:                  {fallback_count}")
    immune_final = shared_dt_log.summary()
    print(f"  DT immune fingerprints:              {len(immune_final['known_dt_types'])}")
    print(f"  Session Tralse trace score:          {immune_final['trace_score']:.4f}")
    print("=" * 60)

    if output_path:
        with open(output_path, "w") as f:
            json.dump(submission, f)
        print(f"Submission written: {output_path}")

    return submission


# ---------------------------------------------------------------------------
# Entry point — auto-detects Kaggle vs. local environment
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    kaggle_test = Path("/kaggle/input/arc-prize-2025/arc-agi_test_challenges.json")

    if kaggle_test.exists():
        # Running on Kaggle
        challenges_path = kaggle_test
        output_path = Path("/kaggle/working/submission.json")
    else:
        # Running locally — build combined dict from evaluation split
        local_data = Path("arc_ti_solver/data/evaluation")
        if not local_data.exists():
            print("No local ARC data. Run: python -m arc_ti_solver.run --download")
            sys.exit(1)

        tasks = {}
        for f in sorted(local_data.glob("*.json")):
            with open(f) as fp:
                tasks[f.stem] = json.load(fp)

        combined = Path("/tmp/arc_local_combined.json")
        with open(combined, "w") as fp:
            json.dump(tasks, fp)

        challenges_path = combined
        output_path = Path("/tmp/ti_sigma_v2_submission.json")

    submission = run_submission(challenges_path, output_path)
    print(f"\nTotal tasks submitted: {len(submission)}")

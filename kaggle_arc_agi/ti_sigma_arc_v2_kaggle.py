#!/usr/bin/env python3
"""
TI Sigma ARC-AGI Solver — Kaggle Submission v2
===============================================
Five-Valued Truth System (URB #528) + DT Immunity Model + MR Gate Hierarchy

Architecture:
  - FiveValuedCellEncoder: assigns FALSE/INDETERMINATE/TRUE/TRALSE/DT to each grid cell
  - MyrionSolver: MR1 (0.8647) + MR Radiant (0.9323) gate hierarchy
  - DTImmuneLog: fast-rejects known Double Tralse transform patterns
  - MR Relaxation: permissive novelty pass before strict MR evaluation

Submission format: {task_id: [[row, ...], ...]} for best prediction per task.

Author: Brandon Emerick (TI Framework) | March 28, 2026
"""

import json
import os
import sys
import numpy as np
from pathlib import Path

# ---------------------------------------------------------------------------
# Add project root to path so arc_ti_solver can be imported on Kaggle
# ---------------------------------------------------------------------------
ROOT = Path(__file__).parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from arc_ti_solver import FALSE, INDETERMINATE, TRUE, TRALSE, DOUBLE_TRALSE
from arc_ti_solver.myrion_solver import (
    MyrionSolver, classify_pd_zone, mr_status, DTImmuneLog,
    MR1_LCC_THRESHOLD, MR_RADIANT_THRESHOLD, DT_PENUMBRA_MARGIN,
)
from arc_ti_solver.tralse_encoder import FiveValuedCellEncoder

# ---------------------------------------------------------------------------
# Dataset paths (Kaggle competition environment)
# ---------------------------------------------------------------------------
KAGGLE_INPUT = Path("/kaggle/input")
ARC_DATA_PATH = (
    KAGGLE_INPUT / "arc-prize-2025" / "arc-agi_test_challenges.json"
    if (KAGGLE_INPUT / "arc-prize-2025").exists()
    else Path("arc_ti_solver/data/evaluation")
)

# ---------------------------------------------------------------------------
# Core solve loop
# ---------------------------------------------------------------------------

def solve_task(task: dict, task_id: str, dt_immune_log=None, verbose: bool = False) -> dict:
    """
    Solve a single ARC task using the TI Sigma 5-valued truth pipeline.

    Returns dict with keys:
      - best_output: list[list[int]] — best predicted output grid
      - lcc: float — LCC score of best prediction
      - pd_zone: str — PD zone of best prediction
      - mr_status: str — MR status string
      - dt_penumbra: bool — whether solution is in DT penumbra zone
      - immune_log: dict — summary of DT immune encounters in this solve
    """
    train_pairs = task.get("train", [])
    test_inputs = task.get("test", [])

    if not train_pairs or not test_inputs:
        return {"best_output": [[0]], "lcc": 0.0, "pd_zone": "Terrible",
                "mr_status": "NO_DATA", "dt_penumbra": False, "immune_log": {}}

    # Encode training pairs through 5-valued system
    encoder = FiveValuedCellEncoder()
    for pair in train_pairs:
        inp = np.array(pair["input"], dtype=np.int8)
        out = np.array(pair["output"], dtype=np.int8)
        encoder.observe(inp, out)

    # Build solver with shared DT immune log (accumulates across tasks)
    solver = MyrionSolver(verbose=verbose)
    if dt_immune_log is not None:
        solver.dt_immune_log = dt_immune_log

    # Solve for each test input
    results = []
    for test_pair in test_inputs:
        test_input = test_pair["input"]
        train_inputs = [p["input"] for p in train_pairs]
        train_outputs = [p["output"] for p in train_pairs]

        preds = solver.solve(
            train_inputs=train_inputs,
            train_outputs=train_outputs,
            test_input=test_input,
            top_k=3,
        )

        if preds:
            best = preds[0]
            results.append({
                "best_output": best["output"],
                "lcc": best["lcc"],
                "pd_zone": best["pd_zone"],
                "mr_status": best["mr_status"],
                "dt_penumbra": best.get("dt_penumbra", False),
                "dt_proximity": best.get("dt_proximity", 0.0),
                "immune_log": best.get("immune_log", {}),
            })
        else:
            results.append({
                "best_output": test_input,  # Identity fallback
                "lcc": 0.0,
                "pd_zone": "Terrible",
                "mr_status": "IDENTITY_FALLBACK",
                "dt_penumbra": False,
                "dt_proximity": 0.0,
                "immune_log": {},
            })

    return results[0] if results else {"best_output": [[0]], "lcc": 0.0,
                                        "pd_zone": "Terrible", "mr_status": "NO_RESULT",
                                        "dt_penumbra": False, "immune_log": {}}


def run_submission(challenges_path: Path, output_path: Path = None) -> dict:
    """
    Run the full submission pipeline over all test challenges.

    Returns: {task_id: [[row, ...], ...]} in Kaggle submission format.
    """
    with open(challenges_path) as f:
        challenges = json.load(f)

    print(f"TI Sigma ARC-AGI v2 | {len(challenges)} tasks | 5-valued truth pipeline")
    print(f"MR1={MR1_LCC_THRESHOLD:.4f}  MR_Radiant={MR_RADIANT_THRESHOLD:.4f}")
    print(f"DT_Penumbra=[{MR1_LCC_THRESHOLD:.4f}, {MR1_LCC_THRESHOLD+DT_PENUMBRA_MARGIN:.4f}]")
    print("=" * 60)

    # Shared DT immune log — accumulates across ALL tasks in the session
    # This is the competitive advantage: the solver learns from early task failures
    # and fast-rejects those transform patterns in later tasks (URB #528 immunity)
    shared_immune_log = DTImmuneLog()

    submission = {}
    stats = {"radiant": 0, "good": 0, "indeterminate": 0, "bad": 0, "terrible": 0,
             "penumbra": 0, "immune_rejects": 0}

    for i, (task_id, task) in enumerate(challenges.items()):
        result = solve_task(task, task_id, dt_immune_log=shared_immune_log)

        # Format for Kaggle: list of attempts (we submit 2 — best + identity fallback)
        best_output = result["best_output"]
        submission[task_id] = [best_output, task["test"][0]["input"]]  # attempt 1 + attempt 2

        # Track stats
        zone = result["pd_zone"].lower().replace(" ", "_")
        if zone in stats:
            stats[zone] += 1
        if result.get("dt_penumbra"):
            stats["penumbra"] += 1

        # Progress reporting
        if (i + 1) % 50 == 0 or i == 0:
            immune = shared_immune_log.summary()
            print(f"  [{i+1}/{len(challenges)}] "
                  f"DT encounters={immune['dt_encounters']} "
                  f"DT types={len(immune['known_dt_types'])} "
                  f"Tralse traces={immune['tralse_traces']} "
                  f"trace_score={immune['trace_score']:.3f}")

    # Final report
    print("\n" + "=" * 60)
    print("TI Sigma v2 — Solve Summary")
    print(f"  Radiant (≥{MR_RADIANT_THRESHOLD:.4f}): {stats['radiant']}")
    print(f"  Good (≥{MR1_LCC_THRESHOLD:.4f}):    {stats['good']}")
    print(f"  Indeterminate:                      {stats['indeterminate']}")
    print(f"  Bad:                                {stats['bad']}")
    print(f"  Terrible:                           {stats['terrible']}")
    print(f"  DT Penumbra zone:                   {stats['penumbra']}")
    immune_final = shared_immune_log.summary()
    print(f"  DT immune fingerprints:             {len(immune_final['known_dt_types'])}")
    print(f"  Session Tralse trace score:         {immune_final['trace_score']:.4f}")
    print("=" * 60)

    if output_path:
        with open(output_path, "w") as f:
            json.dump(submission, f)
        print(f"Submission written to: {output_path}")

    return submission


# ---------------------------------------------------------------------------
# Kaggle notebook entry point
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    # Auto-detect Kaggle vs local environment
    if Path("/kaggle/input/arc-prize-2025").exists():
        challenges_path = Path("/kaggle/input/arc-prize-2025/arc-agi_test_challenges.json")
        output_path = Path("/kaggle/working/submission.json")
    else:
        # Local: use evaluation split
        local_data = Path("arc_ti_solver/data/evaluation")
        if not local_data.exists():
            print("No local ARC data found. Run: python -m arc_ti_solver.run --download")
            sys.exit(1)

        # Assemble local tasks into one dict for compatibility
        tasks = {}
        for f in sorted(local_data.glob("*.json")):
            with open(f) as fp:
                tasks[f.stem] = json.load(fp)

        # Write temp combined file
        temp = Path("/tmp/arc_local_combined.json")
        with open(temp, "w") as fp:
            json.dump(tasks, fp)
        challenges_path = temp
        output_path = Path("/tmp/ti_sigma_arc_v2_submission.json")

    submission = run_submission(challenges_path, output_path)
    print(f"\nTotal tasks in submission: {len(submission)}")

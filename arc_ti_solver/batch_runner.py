"""
Batch Runner — Solve all ARC tasks and generate Kaggle submission.
"""

import json
import time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Optional

from arc_ti_solver.data_loader import load_all_tasks, download_arc_dataset
from arc_ti_solver.solver import TISigmaARCSolver


def solve_all(
    split: str = "training",
    local_dir: Optional[str] = None,
    max_workers: int = 4,
    limit: Optional[int] = None,
    verbose_first: int = 3,
) -> dict:
    """
    Solve all tasks in a split.
    Returns {task_id: result_dict}
    """
    tasks = load_all_tasks(split=split, local_dir=local_dir)
    task_items = list(tasks.items())
    if limit:
        task_items = task_items[:limit]

    print(f"\nSolving {len(task_items)} ARC tasks ({split}) with {max_workers} workers...")

    results = {}
    start = time.time()

    def solve_one(item):
        task_id, task = item
        verbose = len(results) < verbose_first
        solver = TISigmaARCSolver(task, task_id=task_id)
        return task_id, solver.solve(verbose=verbose)

    with ThreadPoolExecutor(max_workers=max_workers) as exe:
        futures = {exe.submit(solve_one, item): item[0] for item in task_items}
        for i, fut in enumerate(as_completed(futures)):
            try:
                task_id, result = fut.result()
                results[task_id] = result
                if (i + 1) % 50 == 0 or i < 5:
                    elapsed = time.time() - start
                    print(f"  [{i+1}/{len(task_items)}] {task_id} | "
                          f"LCC={result['predictions'][0]['best']['lcc']:.3f} | "
                          f"{elapsed:.1f}s elapsed")
            except Exception as e:
                task_id = futures[fut]
                print(f"  FAILED: {task_id} — {e}")
                results[task_id] = {"error": str(e)}

    elapsed = time.time() - start
    print(f"\nDone. {len(results)} tasks solved in {elapsed:.1f}s")
    return results


def generate_submission(results: dict, output_path: str = "submission.json") -> dict:
    """
    Generate Kaggle ARC submission JSON.
    Format: {task_id: [{attempt_1: grid, attempt_2: grid}, ...]}
    """
    submission = {}
    lcc_scores = []

    for task_id, result in results.items():
        if "error" in result:
            submission[task_id] = [{"attempt_1": [[0]], "attempt_2": [[0]]}]
            continue

        task_submission = []
        for pred in result.get("predictions", []):
            sols = pred.get("solutions", [])
            attempt_1 = sols[0]["output"] if len(sols) > 0 else [[0]]
            attempt_2 = sols[1]["output"] if len(sols) > 1 else attempt_1
            task_submission.append({
                "attempt_1": attempt_1,
                "attempt_2": attempt_2,
            })
            if sols:
                lcc_scores.append(sols[0]["lcc"])
        submission[task_id] = task_submission

    avg_lcc = sum(lcc_scores) / len(lcc_scores) if lcc_scores else 0
    print(f"\nSubmission stats:")
    print(f"  Tasks: {len(submission)}")
    print(f"  Avg LCC: {avg_lcc:.4f}")
    print(f"  Perfect (LCC≥0.85): {sum(1 for s in lcc_scores if s >= 0.85)}/{len(lcc_scores)}")

    Path(output_path).write_text(json.dumps(submission, indent=2))
    print(f"  Saved → {output_path}")
    return submission


def benchmark_report(results: dict) -> str:
    """Generate a summary report of solver performance."""
    lines = ["TI Sigma ARC-AGI Benchmark Report", "=" * 50]
    lcc_all = []
    exact_matches = 0

    for task_id, result in results.items():
        if "error" in result:
            continue
        for pred in result.get("predictions", []):
            if pred.get("best"):
                lcc = pred["best"]["lcc"]
                lcc_all.append(lcc)
                if lcc >= 1.0:
                    exact_matches += 1

    if lcc_all:
        lines.append(f"Tasks solved: {len(results)}")
        lines.append(f"Avg LCC:      {sum(lcc_all)/len(lcc_all):.4f}")
        lines.append(f"True-Tralse (≥0.85): {sum(1 for l in lcc_all if l >= 0.85)}")
        lines.append(f"Crossover (≥0.7823): {sum(1 for l in lcc_all if l >= 0.7823)}")
        lines.append(f"Exact matches (=1.0): {exact_matches}")
        lines.append(f"\nLCC Distribution:")
        for threshold in [0.9, 0.8, 0.7, 0.5, 0.3]:
            count = sum(1 for l in lcc_all if l >= threshold)
            pct = 100 * count / len(lcc_all)
            lines.append(f"  ≥{threshold:.1f}: {count}/{len(lcc_all)} ({pct:.1f}%)")

    return "\n".join(lines)

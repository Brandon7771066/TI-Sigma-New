"""
CLI entry point for TI Sigma ARC Solver.

Usage:
    python -m arc_ti_solver.run --download
    python -m arc_ti_solver.run --task data/training/007bbfb7.json
    python -m arc_ti_solver.run --batch --split training --limit 20
    python -m arc_ti_solver.run --batch --split evaluation --submit
"""

import argparse
import json
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description="TI Sigma ARC-AGI Solver")
    parser.add_argument("--download", action="store_true",
                        help="Download ARC dataset from GitHub")
    parser.add_argument("--task", type=str,
                        help="Path to a single task JSON file")
    parser.add_argument("--batch", action="store_true",
                        help="Run on all tasks in a split")
    parser.add_argument("--split", type=str, default="training",
                        choices=["training", "evaluation"],
                        help="Dataset split to use")
    parser.add_argument("--limit", type=int, default=None,
                        help="Max tasks to solve in batch mode")
    parser.add_argument("--submit", action="store_true",
                        help="Generate Kaggle submission JSON")
    parser.add_argument("--local-dir", type=str, default=None,
                        help="Local directory with task JSON files")
    parser.add_argument("--verbose", action="store_true",
                        help="Verbose output")
    args = parser.parse_args()

    if args.download:
        from arc_ti_solver.data_loader import download_arc_dataset
        download_arc_dataset("training")
        download_arc_dataset("evaluation")
        print("Download complete.")
        return

    if args.task:
        from arc_ti_solver.solver import solve_task_file
        result = solve_task_file(args.task, verbose=True)
        print("\n" + result["report"])
        if result["predictions"]:
            best = result["predictions"][0]["best"]
            if best:
                print(f"\nBest prediction (LCC={best['lcc']:.4f}):")
                for row in best["output"]:
                    print("  " + " ".join(str(c) for c in row))
        return

    if args.batch:
        from arc_ti_solver.batch_runner import solve_all, generate_submission, benchmark_report
        results = solve_all(
            split=args.split,
            local_dir=args.local_dir,
            limit=args.limit,
            verbose_first=5 if args.verbose else 1,
        )
        print("\n" + benchmark_report(results))
        if args.submit:
            generate_submission(results, output_path="arc_submission.json")
        return

    parser.print_help()


if __name__ == "__main__":
    main()

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run TI Sigma Stage A v3 mock-only pipeline")
    parser.add_argument("--attempts", type=int, default=3, help="Attempts per item (default: 3)")
    parser.add_argument(
        "--output-jsonl",
        default="experiments/eight_c_goodness_pilot/results/ratings/ti_sigma_stage_a_v3_mock_ratings.jsonl",
        help="Output JSONL path, relative to repo root unless absolute",
    )
    parser.add_argument(
        "--output-metrics-json",
        default="experiments/eight_c_goodness_pilot/results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json",
        help="Output reproducibility JSON path, relative to repo root unless absolute",
    )
    parser.add_argument(
        "--output-report-md",
        default="experiments/eight_c_goodness_pilot/results/reports/ti_sigma_stage_a_v3_mock_reproducibility.md",
        help="Output markdown summary path, relative to repo root unless absolute",
    )
    parser.add_argument(
        "--seed-strategy",
        choices=["vary_by_attempt", "fixed"],
        default="vary_by_attempt",
        help="Deterministic seed strategy for attempts",
    )
    parser.add_argument(
        "--base-seed",
        default="TI_SIGMA_STAGE_A_V3_MOCK",
        help="Optional deterministic base seed prefix",
    )
    return parser


def resolve_path(repo_root: Path, value: str) -> Path:
    candidate = Path(value)
    if candidate.is_absolute():
        return candidate
    return repo_root / candidate


def render_reproducibility_markdown(metrics: dict) -> str:
    c_scores = metrics.get("mean_abs_diff", {}).get("C_scores", {})
    contradictions = metrics.get("mean_abs_diff", {}).get("contradictions", {})

    lines = [
        "# TI Sigma Stage A v3 Mock Reproducibility Summary",
        "",
        "> These ratings are synthetic engineering outputs generated to test pipeline behavior. They are not empirical observations and must not be used to evaluate the Eight-C framework.",
        "",
        f"- attempts_per_item: {metrics.get('attempts_per_item')}",
        f"- item_groups: {metrics.get('item_groups')}",
        f"- exact_match_rate: {metrics.get('exact_match_rate'):.6f}",
        f"- mean_abs_diff.goodness: {metrics.get('mean_abs_diff', {}).get('goodness', 0.0):.6f}",
        "",
        "## Mean Absolute Difference - Eight Cs",
        "",
        "| Dimension | Mean Abs Diff |",
        "|---|---:|",
    ]
    for key in sorted(c_scores.keys()):
        lines.append(f"| {key} | {c_scores[key]:.6f} |")

    lines.extend(
        [
            "",
            "## Mean Absolute Difference - Contradictions",
            "",
            "| Dimension | Mean Abs Diff |",
            "|---|---:|",
        ]
    )
    for key in sorted(contradictions.keys()):
        lines.append(f"| {key} | {contradictions[key]:.6f} |")

    lines.extend(
        [
            "",
            "Notes:",
            "- This report is generated from mock-only deterministic ratings.",
            "- Values are reproducibility diagnostics, not empirical model-performance claims.",
        ]
    )

    return "\n".join(lines) + "\n"


def main() -> None:
    args = build_arg_parser().parse_args()

    repo_root = Path(__file__).resolve().parents[3]
    repo_root_str = str(repo_root)
    if repo_root_str not in sys.path:
        sys.path.insert(0, repo_root_str)

    from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import run_mock_pipeline

    pilot_root = repo_root / "experiments" / "eight_c_goodness_pilot"

    items_csv = pilot_root / "data" / "items" / "ti_sigma_stage_a_v3_items.csv"
    metadata_csv = pilot_root / "data" / "metadata" / "ti_sigma_stage_a_v3_metadata.csv"
    output_jsonl = resolve_path(repo_root, args.output_jsonl)
    output_metrics_json = resolve_path(repo_root, args.output_metrics_json)
    output_report_md = resolve_path(repo_root, args.output_report_md)

    summary = run_mock_pipeline(
        items_csv,
        metadata_csv,
        output_jsonl,
        attempts_per_item=args.attempts,
        output_metrics_json=output_metrics_json,
        seed_strategy=args.seed_strategy,
        base_seed=args.base_seed,
    )

    metrics = json.loads(output_metrics_json.read_text(encoding="utf-8"))
    output_report_md.parent.mkdir(parents=True, exist_ok=True)
    output_report_md.write_text(render_reproducibility_markdown(metrics), encoding="utf-8")

    print("MOCK_PIPELINE_SUMMARY")
    print(f"items={summary['items']}")
    print(f"metadata={summary['metadata']}")
    print(f"attempts_per_item={summary['attempts_per_item']}")
    print(f"seed_strategy={summary['seed_strategy']}")
    print(f"base_seed={summary['base_seed']}")
    print(f"written={summary['written']}")
    print(f"exact_match_rate={summary['reproducibility']['exact_match_rate']}")
    print(f"output={output_jsonl}")
    print(f"reproducibility_metrics={output_metrics_json}")
    print(f"reproducibility_report={output_report_md}")


if __name__ == "__main__":
    main()
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def _repo_root_from_script() -> Path:
    return Path(__file__).resolve().parents[3]


def _resolve(path_like: str, repo_root: Path) -> Path:
    candidate = Path(path_like)
    if candidate.is_absolute():
        return candidate
    return repo_root / candidate


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="TI Sigma Stage A v3 mock release CLI")
    sub = parser.add_subparsers(dest="command", required=True)

    def common_paths(cmd: argparse.ArgumentParser) -> None:
        cmd.add_argument(
            "--config",
            default="experiments/eight_c_goodness_pilot/config/stage_a_v3.yaml",
            help="Path to frozen Stage A v3 config (.yaml JSON-compatible)",
        )
        cmd.add_argument(
            "--freeze-manifest",
            default="experiments/eight_c_goodness_pilot/data/manifests/stage_a_v3_freeze_manifest.yaml",
            help="Path to freeze manifest (.yaml JSON-compatible)",
        )
        cmd.add_argument(
            "--experiments-dir",
            default="experiments/eight_c_goodness_pilot/results/experiments",
            help="Root directory for experiment outputs",
        )

    freeze_cmd = sub.add_parser("freeze-check", help="Verify frozen hashes without rewriting them")
    common_paths(freeze_cmd)
    freeze_cmd.add_argument("--strict", action="store_true", help="Exit nonzero when mismatches exist")

    corpus_cmd = sub.add_parser("corpus-summary", help="Show frozen corpus and plan summary")
    common_paths(corpus_cmd)

    collection_cmd = sub.add_parser("collection-check", help="Preflight collection settings and freeze state")
    common_paths(collection_cmd)
    collection_cmd.add_argument("--mock", action="store_true", help="Require mock mode")

    cost_cmd = sub.add_parser("cost-estimate", help="Compute attempt bounds and mock cost estimate")
    common_paths(cost_cmd)
    cost_cmd.add_argument("--mock", action="store_true", help="Use mock mode estimate")

    run_cmd = sub.add_parser("run", help="Execute registered Stage A v3 collection plan")
    common_paths(run_cmd)
    run_cmd.add_argument("--experiment-id", required=True, help="Experiment identifier")
    run_cmd.add_argument("--mock", action="store_true", help="Run in mock mode")
    run_cmd.add_argument(
        "--attempts",
        type=int,
        default=None,
        help="Development override placeholder. Ignored for registered Stage A v3 plan.",
    )

    validate_cmd = sub.add_parser("validate", help="Validate terminal logical ratings and emit rectangular ratings file")
    common_paths(validate_cmd)
    validate_cmd.add_argument("--experiment-id", required=True, help="Experiment identifier")

    seal_cmd = sub.add_parser("seal", help="Create or verify seal manifest for experiment artifacts")
    common_paths(seal_cmd)
    seal_cmd.add_argument("--experiment-id", required=True, help="Experiment identifier")
    seal_cmd.add_argument("--dev-override", action="store_true", help="Allow replacing an existing seal manifest")
    seal_cmd.add_argument("--verify", action="store_true", help="Verify existing seal manifest only")

    report_cmd = sub.add_parser("report", help="Generate engineering diagnostics report")
    common_paths(report_cmd)
    report_cmd.add_argument("--experiment-id", required=True, help="Experiment identifier")

    return parser


def _load_stage_module(repo_root: Path):
    repo_root_str = str(repo_root)
    if repo_root_str not in sys.path:
        sys.path.insert(0, repo_root_str)
    from experiments.eight_c_goodness_pilot.src.ti_sigma_pipeline import stage_a_v3

    return stage_a_v3


def _build_paths(stage, args, repo_root: Path):
    experiments_dir = _resolve(args.experiments_dir, repo_root)
    paths = stage.build_default_paths(repo_root, experiments_root=experiments_dir)
    paths.config_path = _resolve(args.config, repo_root)
    paths.freeze_manifest_path = _resolve(args.freeze_manifest, repo_root)
    return paths


def _print_json(payload: dict) -> None:
    print(json.dumps(payload, indent=2))


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    repo_root = _repo_root_from_script()
    stage = _load_stage_module(repo_root)

    try:
        paths = _build_paths(stage, args, repo_root)
        config = stage.load_config(paths.config_path)

        if args.command == "freeze-check":
            result = stage.freeze_check(paths, strict=args.strict)
            _print_json(result)
            return

        if args.command == "corpus-summary":
            result = stage.corpus_summary(paths, config)
            _print_json(result)
            return

        if args.command == "collection-check":
            result = stage.collection_check(paths, config, mock=args.mock)
            _print_json(result)
            return

        if args.command == "cost-estimate":
            result = stage.cost_estimate(config, mock=args.mock)
            _print_json(result)
            return

        if args.command == "run":
            if not args.mock:
                raise ValueError("run requires --mock in current release gate")
            result = stage.run_mock_collection(
                paths,
                config,
                experiment_id=args.experiment_id,
                strict_freeze=True,
                dev_attempts_override=args.attempts,
            )
            _print_json(result)
            return

        if args.command == "validate":
            result = stage.validate_experiment(paths, config, experiment_id=args.experiment_id)
            _print_json(result)
            return

        if args.command == "seal":
            result = stage.seal_experiment(
                paths,
                config,
                experiment_id=args.experiment_id,
                dev_override=args.dev_override,
                verify_only=args.verify,
            )
            _print_json(result)
            return

        if args.command == "report":
            result = stage.build_engineering_report(paths, config, experiment_id=args.experiment_id)
            _print_json(result)
            return

        raise ValueError(f"Unsupported command: {args.command}")
    except Exception as exc:  # noqa: BLE001
        print(json.dumps({"error": str(exc), "command": args.command}, indent=2), file=sys.stderr)
        raise SystemExit(1) from exc


if __name__ == "__main__":
    main()
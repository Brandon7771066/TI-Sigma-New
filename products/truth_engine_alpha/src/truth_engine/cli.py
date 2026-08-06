from __future__ import annotations

import argparse
import json
from pathlib import Path

from .engine import (
    analyze_file,
    benchmark_suite,
    compare_results,
    render_report,
    validate_input,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog='truth-engine', description='Truth Engine Alpha CLI')
    subparsers = parser.add_subparsers(dest='command', required=True)

    analyze_parser = subparsers.add_parser('analyze', help='Analyze claims or documents')
    analyze_parser.add_argument('--input', required=True)
    analyze_parser.add_argument('--output', required=True)
    analyze_parser.add_argument('--mode', choices=['standard', 'ti_sigma'], default='standard')
    analyze_parser.add_argument('--seed', type=int, default=0)

    validate_parser = subparsers.add_parser('validate', help='Validate inputs or result files')
    validate_parser.add_argument('--input', required=True)

    benchmark_parser = subparsers.add_parser('benchmark', help='Run benchmark cases')
    benchmark_parser.add_argument('--input', required=False)
    benchmark_parser.add_argument('--output', required=True)

    report_parser = subparsers.add_parser('report', help='Render a report from a result file')
    report_parser.add_argument('--input', required=True)
    report_parser.add_argument('--output', required=True)

    compare_parser = subparsers.add_parser('compare', help='Compare two result files')
    compare_parser.add_argument('--left', required=True)
    compare_parser.add_argument('--right', required=True)

    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()

    if args.command == 'validate':
        result = validate_input(Path(args.input))
    elif args.command == 'benchmark':
        result = benchmark_suite(Path(args.input) if args.input else None, Path(args.output))
    elif args.command == 'analyze':
        result = analyze_file(Path(args.input), Path(args.output), mode=args.mode, seed=args.seed)
    elif args.command == 'report':
        result = render_report(Path(args.input), Path(args.output))
    elif args.command == 'compare':
        result = compare_results(Path(args.left), Path(args.right))
    else:
        raise SystemExit(f'Unknown command: {args.command}')

    print(json.dumps(result, indent=2))

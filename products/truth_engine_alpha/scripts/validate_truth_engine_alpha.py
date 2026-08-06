from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / 'src'
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from truth_engine.cli import build_parser
from truth_engine.engine import analyze_file, benchmark_suite, validate_input


def main() -> None:
    outputs_root = ROOT / 'results' / 'reports' / 'validation_run'
    outputs_root.mkdir(parents=True, exist_ok=True)

    help_text = build_parser().format_help()
    (outputs_root / 'cli_help.txt').write_text(help_text, encoding='utf-8')

    sample_input = ROOT / 'data' / 'inputs' / 'faah_claims.jsonl'
    analysis_dir = ROOT / 'results' / 'reports' / 'faah_alpha_demo'
    result = analyze_file(sample_input, analysis_dir, mode='standard')

    benchmark_dir = ROOT / 'results' / 'benchmarks'
    benchmark_result = benchmark_suite(None, benchmark_dir)

    validate_result = validate_input(sample_input)

    checks = [
        ('validate_input', validate_result['valid'] is True and validate_result['item_count'] == 3),
        ('analysis_id', result['analysis_id'] == 'faah_claims'),
        ('output_written', (analysis_dir / 'full_result.json').exists()),
        ('benchmark_count', benchmark_result['benchmark_count'] == 20),
        ('cli_help_has_analyze', 'analyze' in help_text),
        ('cli_help_has_benchmark', 'benchmark' in help_text),
        ('cli_help_has_report', 'report' in help_text),
    ]
    passed = all(ok for _, ok in checks)

    lines = ['Truth Engine Alpha validation run', '']
    for name, ok in checks:
        lines.append(f'{name}: {"PASS" if ok else "FAIL"}')
    lines.append(f'overall: {"PASS" if passed else "FAIL"}')

    (outputs_root / 'test_output.txt').write_text('\n'.join(lines) + '\n', encoding='utf-8')
    (outputs_root / 'test_exit_code.txt').write_text('0\n' if passed else '1\n', encoding='utf-8')
    (outputs_root / 'cli_help.json').write_text(json.dumps({'help': help_text}, indent=2), encoding='utf-8')

    print('\n'.join(lines))
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()

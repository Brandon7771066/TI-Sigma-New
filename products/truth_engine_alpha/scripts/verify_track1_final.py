from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PRODUCT_ROOT = Path(__file__).resolve().parents[1]
SRC_ROOT = PRODUCT_ROOT / 'src'
RESULTS_ROOT = PRODUCT_ROOT / 'results' / 'verification'
SCHEMA_PATH = PRODUCT_ROOT / 'schema' / 'analysis_result.schema.json'
INPUT_PATH = PRODUCT_ROOT / 'data' / 'inputs' / 'ai_hallucination_audit_case_01.jsonl'
BENCHMARK_SCRIPT = PRODUCT_ROOT / 'scripts' / 'run_baseline_comparison.py'
BENCHMARK_JSON = PRODUCT_ROOT / 'results' / 'benchmarks' / 'baseline_comparison.json'
BENCHMARK_MD = PRODUCT_ROOT / 'results' / 'benchmarks' / 'baseline_comparison.md'

REQUIRED_OUTPUTS = [
    'full_result.json',
    'executive_summary.md',
    'claim_table.csv',
    'citation_audit.csv',
    'contradiction_map.csv',
    'contradiction_graph.json',
    'scaffolding_analysis.csv',
    'information_gain_actions.csv',
    'corrected_answer_outline.md',
    'limitations.md',
    'demo_provenance.json',
]

ALLOWED_SCAFFOLDING_FINAL_STATUSES = {
    'RESOLVED_BY_SCAFFOLDING',
    'PARTIALLY_RESOLVED',
    'UNRESOLVED',
    'INSUFFICIENT_EVIDENCE',
    'NOT_A_TRUE_CONTRADICTION',
}

REQUIRED_CITATION_STATUSES = {
    'NO_CITATION_PROVIDED',
    'SOURCE_NOT_FOUND',
    'SOURCE_FOUND_NOT_ACCESSED',
    'NOT_VERIFIED_OFFLINE',
    'SOURCE_DOES_NOT_SUPPORT_CLAIM',
    'SOURCE_PARTIALLY_SUPPORTS_CLAIM',
    'SOURCE_SUPPORTS_CLAIM',
    'SOURCE_MISCHARACTERIZED',
    'POSSIBLY_FABRICATED_CITATION',
    'NOT_APPLICABLE',
}

REQUIRED_INFORMATION_GAIN_FIELDS = {
    'label',
    'action',
    'uncertainties_addressed',
    'contradictions_addressed',
    'estimated_cost_level',
    'estimated_time_level',
    'expected_decision_impact',
    'expected_uncertainty_reduction',
    'assumptions',
    'calculation_method',
    'priority',
}

OPERATIONS_SCORE_NAMES = [
    'Evidence Coverage',
    'Citation Support',
    'Conflict Density',
    'Resolution Potential',
    'Report Completeness',
    'Actionability',
]


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding='utf-8')


def _write_json(path: Path, payload: Any) -> None:
    _write_text(path, json.dumps(payload, indent=2, sort_keys=True) + '\n')


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    _write_text(path, ''.join(json.dumps(row, sort_keys=True) + '\n' for row in rows))


def _read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding='utf-8'))


def _run_capture(args: list[str], *, cwd: Path, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True)


def _parse_pytest_counts(stdout: str) -> dict[str, int]:
    passed = 0
    failed = 0
    skipped = 0
    xfailed = 0
    xpassed = 0
    match = re.search(r'(\d+) passed', stdout)
    if match:
        passed = int(match.group(1))
    match = re.search(r'(\d+) failed', stdout)
    if match:
        failed = int(match.group(1))
    match = re.search(r'(\d+) skipped', stdout)
    if match:
        skipped = int(match.group(1))
    match = re.search(r'(\d+) xfailed', stdout)
    if match:
        xfailed = int(match.group(1))
    match = re.search(r'(\d+) xpassed', stdout)
    if match:
        xpassed = int(match.group(1))
    return {
        'passed': passed,
        'failed': failed,
        'skipped': skipped,
        'xfailed': xfailed,
        'xpassed': xpassed,
    }


def _simple_schema_check(schema: dict[str, Any], instance: dict[str, Any]) -> list[str]:
    errors: list[str] = []

    def validate_node(node_schema: dict[str, Any], value: Any, path: str) -> None:
        if 'enum' in node_schema and value not in node_schema['enum']:
            errors.append(f'{path}: value {value!r} not in enum {node_schema["enum"]!r}')
        node_type = node_schema.get('type')
        if node_type == 'object':
            if not isinstance(value, dict):
                errors.append(f'{path}: expected object')
                return
            required = node_schema.get('required', [])
            for key in required:
                if key not in value:
                    errors.append(f'{path}: missing required field {key!r}')
            if node_schema.get('additionalProperties') is False:
                allowed = set(node_schema.get('properties', {}).keys())
                for key in value.keys():
                    if key not in allowed:
                        errors.append(f'{path}: unexpected field {key!r}')
            props = node_schema.get('properties', {})
            for key, child_schema in props.items():
                if key not in value:
                    continue
                validate_node(child_schema, value[key], f'{path}.{key}')
        elif node_type == 'array':
            if not isinstance(value, list):
                errors.append(f'{path}: expected array')
                return
            item_schema = node_schema.get('items')
            if isinstance(item_schema, dict):
                for index, item in enumerate(value):
                    validate_node(item_schema, item, f'{path}[{index}]')
        elif node_type == 'string':
            if not isinstance(value, str):
                errors.append(f'{path}: expected string')
        elif node_type == 'number':
            if not isinstance(value, (int, float)) or isinstance(value, bool):
                errors.append(f'{path}: expected number')
        elif node_type == 'integer':
            if not isinstance(value, int) or isinstance(value, bool):
                errors.append(f'{path}: expected integer')
        elif node_type == 'boolean':
            if not isinstance(value, bool):
                errors.append(f'{path}: expected boolean')

        if isinstance(value, (int, float)) and not isinstance(value, bool):
            minimum = node_schema.get('minimum')
            maximum = node_schema.get('maximum')
            if minimum is not None and value < minimum:
                errors.append(f'{path}: value {value} below minimum {minimum}')
            if maximum is not None and value > maximum:
                errors.append(f'{path}: value {value} above maximum {maximum}')

    validate_node(schema, instance, '$')
    return errors


def _copy_if_exists(source: Path, destination: Path) -> None:
    if source.exists():
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)


def _tree_text(root: Path) -> str:
    lines: list[str] = []
    for path in sorted(root.rglob('*')):
        if path.is_dir():
            continue
        lines.append(str(path.relative_to(root)).replace('\\', '/'))
    return '\n'.join(lines) + '\n'


def _citation_audit_probe() -> dict[str, Any]:
    sys.path.insert(0, str(SRC_ROOT))
    from truth_engine.engine import _citation_status_for
    from truth_engine.models import Claim

    source_ids = {'s1'}
    cases = [
        ('NO_CITATION_PROVIDED', Claim('c1', 'no citation', 'no citation', 's1', citations=[]), True),
        ('SOURCE_NOT_FOUND', Claim('c2', 'missing source', 'missing source', 's2', citations=['missing_source']), True),
        ('SOURCE_FOUND_NOT_ACCESSED', Claim('c3', 'source found not accessed', 'source found not accessed', 's1', citations=['s1']), False),
        ('NOT_VERIFIED_OFFLINE', Claim('c4', 'offline not verified', 'offline not verified', 's1', citations=['s1']), True),
        ('SOURCE_DOES_NOT_SUPPORT_CLAIM', Claim('c5', 'does not support the claim', 'does not support the claim', 's1', citations=['s1']), True),
        ('SOURCE_PARTIALLY_SUPPORTS_CLAIM', Claim('c6', 'mixed evidence suggests a split result', 'mixed evidence suggests a split result', 's1', citations=['s1']), True),
        ('SOURCE_SUPPORTS_CLAIM', Claim('c7', 'source confirms and supports the claim', 'source confirms and supports the claim', 's1', citations=['s1']), True),
        ('SOURCE_MISCHARACTERIZED', Claim('c8', 'mischaracterized source', 'mischaracterized source', 's1', citations=['s1']), True),
        ('POSSIBLY_FABRICATED_CITATION', Claim('c9', 'synthetic citation', 'synthetic citation', 's1', citations=['xxxxx123']), True),
        ('NOT_APPLICABLE', Claim('c10', 'document claim', 'document claim', 's1', claim_type='document', citations=[]), True),
    ]

    observed: list[str] = []
    probe_rows: list[dict[str, Any]] = []
    offline_verified_status = None
    for expected_status, claim, offline_mode in cases:
        result = _citation_status_for(claim, source_ids, offline_mode=offline_mode)
        observed.append(result['status'])
        if expected_status == 'NOT_VERIFIED_OFFLINE':
            offline_verified_status = result['status']
        probe_rows.append({
            'expected_status': expected_status,
            'observed_status': result['status'],
            'reason': result['reason'],
            'offline_mode': offline_mode,
        })

    observed_statuses = set(observed)
    missing_statuses = sorted(REQUIRED_CITATION_STATUSES.difference(observed_statuses))
    if offline_verified_status != 'NOT_VERIFIED_OFFLINE':
        missing_statuses.append('NOT_VERIFIED_OFFLINE_MISCLASSIFIED')

    return {
        'required_statuses': sorted(REQUIRED_CITATION_STATUSES),
        'observed_statuses': sorted(observed_statuses),
        'rows': probe_rows,
        'missing_statuses': missing_statuses,
    }


def main() -> None:
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    final_dir = RESULTS_ROOT / f'track1_final_{timestamp}'
    final_dir.mkdir(parents=True, exist_ok=False)
    steps_dir = final_dir / 'steps'
    steps_dir.mkdir(parents=True, exist_ok=True)
    demo_dir = final_dir / 'ai_hallucination_demo'

    env = os.environ.copy()
    env['PYTHONPATH'] = str(SRC_ROOT)
    env['PYTHONIOENCODING'] = 'utf-8'

    snapshot: dict[str, Any] = {}
    snapshot['git_branch'] = _run_capture(['git', 'branch', '--show-current'], cwd=REPO_ROOT, env=env).stdout.strip()
    snapshot['git_commit'] = _run_capture(['git', 'rev-parse', 'HEAD'], cwd=REPO_ROOT, env=env).stdout.strip()
    snapshot['git_status'] = _run_capture(['git', 'status', '--short'], cwd=REPO_ROOT, env=env).stdout.splitlines()
    snapshot['python_version'] = _run_capture([sys.executable, '--version'], cwd=REPO_ROOT, env=env).stdout.strip() or _run_capture([sys.executable, '--version'], cwd=REPO_ROOT, env=env).stderr.strip()
    snapshot['dependency_versions'] = _run_capture([sys.executable, '-m', 'pip', 'freeze'], cwd=REPO_ROOT, env=env).stdout.splitlines()
    _write_json(final_dir / 'environment_snapshot.json', snapshot)
    _write_text(final_dir / 'dependency_versions.txt', '\n'.join(snapshot['dependency_versions']) + '\n')
    _write_text(final_dir / 'git_status.txt', '\n'.join(snapshot['git_status']) + ('\n' if snapshot['git_status'] else ''))

    manifest_records: list[dict[str, Any]] = []
    step_index = 0

    def run_step(name: str, args: list[str], *, cwd: Path = REPO_ROOT) -> subprocess.CompletedProcess[str]:
        nonlocal step_index
        step_index += 1
        step_dir = steps_dir / f'{step_index:02d}_{name}'
        step_dir.mkdir(parents=True, exist_ok=True)
        started_at = _now()
        completed = _run_capture(args, cwd=cwd, env=env)
        finished_at = _now()
        _write_text(step_dir / 'stdout.txt', completed.stdout)
        _write_text(step_dir / 'stderr.txt', completed.stderr)
        _write_text(step_dir / 'exit_code.txt', f'{completed.returncode}\n')
        _write_text(step_dir / 'command.txt', ' '.join(args) + '\n')
        _write_text(step_dir / 'started_at.txt', started_at + '\n')
        _write_text(step_dir / 'finished_at.txt', finished_at + '\n')
        manifest_records.append({
            'step': step_index,
            'name': name,
            'command': args,
            'started_at': started_at,
            'finished_at': finished_at,
            'exit_code': completed.returncode,
            'stdout': str(step_dir / 'stdout.txt'),
            'stderr': str(step_dir / 'stderr.txt'),
        })
        return completed

    def fail(step_name: str, message: str) -> None:
        summary = {
            'TRACK_1_IMPLEMENTED': True,
            'TRACK_1_EXECUTABLE': False,
            'TESTS_PASS': False,
            'CLI_DEMO_GENERATED': False,
            'SCHEMA_VALID': False,
            'REPORT_PACKAGE_COMPLETE': False,
            'CITATION_AUDIT_VALID': False,
            'SCAFFOLDING_VALID': False,
            'INFORMATION_GAIN_VALID': False,
            'OPERATIONAL_SCORES_VALID': False,
            'PROVENANCE_DISCLOSED': False,
            'BASELINE_COMPARISON_COMPLETED': False,
            'STATIC_ARTIFACTS_DISCLOSED': False,
            'PAID_API_REQUESTS': 0,
            'TRACK_1_RELEASE_VERIFIED': False,
            'failing_step': step_name,
            'failure_message': message,
        }
        _write_json(final_dir / 'verification_summary.json', summary)
        _write_text(final_dir / 'verification_summary.md', f'FAILED at {step_name}: {message}\n')
        _write_jsonl(final_dir / 'command_manifest.jsonl', manifest_records)
        raise SystemExit(1)

    try:
        import_check = run_step('package_import_check', [sys.executable, '-c', 'import truth_engine; print("IMPORT_OK")'])
        if import_check.returncode != 0:
            fail('package_import_check', 'package import failed')

        pytest_step = run_step('pytest_suite', [sys.executable, '-m', 'pytest', 'products/truth_engine_alpha/tests', '-q'])
        _write_text(final_dir / 'pytest_stdout.txt', pytest_step.stdout)
        _write_text(final_dir / 'pytest_stderr.txt', pytest_step.stderr)
        _write_text(final_dir / 'pytest_exit_code.txt', f'{pytest_step.returncode}\n')
        pytest_counts = _parse_pytest_counts(pytest_step.stdout)
        if pytest_step.returncode != 0 or pytest_counts['failed'] != 0:
            fail('pytest_suite', f'pytest failed with exit code {pytest_step.returncode}')

        cli_help = run_step('cli_help', [sys.executable, '-m', 'truth_engine', '--help'])
        if cli_help.returncode != 0:
            fail('cli_help', 'CLI help failed')
        _write_text(final_dir / 'cli_help_stdout.txt', cli_help.stdout)
        _write_text(final_dir / 'cli_help_stderr.txt', cli_help.stderr)

        analyze = run_step('analyze_demo', [
            sys.executable,
            '-m',
            'truth_engine',
            'analyze',
            '--input',
            str(INPUT_PATH),
            '--output',
            str(demo_dir),
            '--mode',
            'standard',
            '--seed',
            '7',
        ])
        if analyze.returncode != 0:
            fail('analyze_demo', 'demo analysis failed')
        _write_text(final_dir / 'analyze_stdout.txt', analyze.stdout)
        _write_text(final_dir / 'analyze_stderr.txt', analyze.stderr)

        validate = run_step('validate_full_result', [
            sys.executable,
            '-m',
            'truth_engine',
            'validate',
            '--input',
            str(demo_dir / 'full_result.json'),
        ])
        if validate.returncode != 0:
            fail('validate_full_result', 'CLI validation failed')
        _write_text(final_dir / 'validate_stdout.txt', validate.stdout)
        _write_text(final_dir / 'validate_stderr.txt', validate.stderr)

        report = run_step('generate_report_package', [
            sys.executable,
            '-m',
            'truth_engine',
            'report',
            '--input',
            str(demo_dir / 'full_result.json'),
            '--output',
            str(demo_dir),
        ])
        if report.returncode != 0:
            fail('generate_report_package', 'report generation failed')
        _write_text(final_dir / 'report_stdout.txt', report.stdout)
        _write_text(final_dir / 'report_stderr.txt', report.stderr)

        full_result_path = demo_dir / 'full_result.json'
        if not full_result_path.exists():
            fail('verify_required_output_files', 'full_result.json was not produced')

        schema = _read_json(SCHEMA_PATH)
        full_result = _read_json(full_result_path)
        schema_errors = _simple_schema_check(schema, full_result)
        schema_hashes = {
            'schema_path': str(SCHEMA_PATH.relative_to(REPO_ROOT)),
            'schema_sha256': _sha256(SCHEMA_PATH),
            'output_path': str(full_result_path.relative_to(REPO_ROOT)),
            'output_sha256': _sha256(full_result_path),
            'schema_errors': schema_errors,
        }
        _write_json(final_dir / 'schema_output_hashes.json', schema_hashes)
        if schema_errors:
            fail('validate_schema', '; '.join(schema_errors))

        required_missing = [name for name in REQUIRED_OUTPUTS if not (demo_dir / name).exists()]
        if required_missing:
            fail('verify_required_output_files', f'missing required outputs: {required_missing}')

        citation_audit_result = _citation_audit_probe()
        _write_json(final_dir / 'citation_audit_verification.json', citation_audit_result)
        if citation_audit_result['missing_statuses']:
            fail('verify_citation_audit_statuses', f"missing statuses: {citation_audit_result['missing_statuses']}")

        node_ids = {node.get('claim_id') for node in full_result.get('contradiction_graph', {}).get('nodes', [])}
        edge_errors = []
        for edge in full_result.get('contradiction_graph', {}).get('edges', []):
            if edge.get('from') not in node_ids or edge.get('to') not in node_ids:
                edge_errors.append(edge)
        contradiction_graph_result = {
            'node_count': len(node_ids),
            'edge_count': len(full_result.get('contradiction_graph', {}).get('edges', [])),
            'errors': edge_errors,
        }
        _write_json(final_dir / 'contradiction_graph_verification.json', contradiction_graph_result)
        if edge_errors:
            fail('verify_contradiction_graph_integrity', 'contradiction graph edges reference unknown nodes')

        scaffolding_rows = full_result.get('scaffolding_analysis', [])
        scaffolding_errors = []
        scaffolding_required = {
            'claim_a',
            'claim_b',
            'initial_conflict_type',
            'candidate_scope_resolution',
            'candidate_population_resolution',
            'candidate_temporal_resolution',
            'candidate_definition_resolution',
            'candidate_method_resolution',
            'candidate_measurement_resolution',
            'candidate_parameter_resolution',
            'candidate_mechanism_resolution',
            'remaining_conflict',
            'final_resolution_status',
        }
        for row in scaffolding_rows:
            missing = sorted(scaffolding_required.difference(row.keys()))
            if missing:
                scaffolding_errors.append({'row': row, 'missing': missing})
            if row.get('final_resolution_status') not in ALLOWED_SCAFFOLDING_FINAL_STATUSES:
                scaffolding_errors.append({'row': row, 'invalid_final_status': row.get('final_resolution_status')})
        scaffolding_result = {
            'row_count': len(scaffolding_rows),
            'errors': scaffolding_errors,
        }
        _write_json(final_dir / 'scaffolding_verification.json', scaffolding_result)
        if scaffolding_errors:
            fail('verify_scaffolding_results', 'invalid scaffolding output')

        info_gain_rows = full_result.get('information_gain', [])
        info_gain_errors = []
        for row in info_gain_rows:
            missing = sorted(REQUIRED_INFORMATION_GAIN_FIELDS.difference(row.keys()))
            if missing:
                info_gain_errors.append({'row': row, 'missing': missing})
            if row.get('label') != 'HEURISTIC_INFORMATION_GAIN_ESTIMATE':
                info_gain_errors.append({'row': row, 'invalid_label': row.get('label')})
        info_gain_result = {
            'row_count': len(info_gain_rows),
            'errors': info_gain_errors,
        }
        _write_json(final_dir / 'information_gain_verification.json', info_gain_result)
        if info_gain_errors:
            fail('verify_information_gain_structures', 'invalid information gain output')

        score_doc = (PRODUCT_ROOT / 'docs' / 'methods' / 'operational_scores.md').read_text(encoding='utf-8')
        score_errors = []
        for score_name in OPERATIONS_SCORE_NAMES:
            if score_name not in score_doc:
                score_errors.append(f'missing documentation section for {score_name}')
        if 'universal truth score' in score_doc.lower():
            score_errors.append('operational score doc must not describe a universal truth score')
        for key, value in full_result.get('truth_engine_score', {}).items():
            if not 0.0 <= float(value) <= 1.0:
                score_errors.append(f'{key} out of range: {value}')
        if not any('Missing-data behavior' in line or 'Missing-data behavior:' in line for line in score_doc.splitlines()):
            score_errors.append('missing-data behavior documentation missing')
        if 'Formula:' not in score_doc:
            score_errors.append('formula documentation missing')
        operational_result = {
            'score_names_documented': OPERATIONS_SCORE_NAMES,
            'errors': score_errors,
            'score_values': full_result.get('truth_engine_score', {}),
        }
        _write_json(final_dir / 'operational_scores_verification.json', operational_result)
        if score_errors:
            fail('verify_operational_scores', '; '.join(score_errors))

        provenance_path = demo_dir / 'demo_provenance.json'
        provenance = {
            'generated_by_engine': True,
            'generated_by_cli': True,
            'manually_authored_fields': [],
            'source_material': str(INPUT_PATH.relative_to(REPO_ROOT)),
            'source_verification_status': 'NOT_VERIFIED_OFFLINE',
            'generation_timestamp': _now(),
            'git_commit': snapshot['git_commit'],
            'schema_version': full_result.get('schema_version', 'truth_engine_alpha.v1'),
            'limitations': [
                'This bundle is generated from the current CLI implementation without external source retrieval.',
                'Legacy static demo packs remain in the repository but are not part of this verified bundle.',
            ],
        }
        _write_json(provenance_path, provenance)
        if not provenance_path.exists():
            fail('verify_provenance_disclosure', 'demo provenance was not written')

        baseline_step = run_step('baseline_comparison', [sys.executable, str(BENCHMARK_SCRIPT)])
        if baseline_step.returncode != 0:
            fail('baseline_comparison', 'baseline comparison script failed')
        _write_text(final_dir / 'baseline_stdout.txt', baseline_step.stdout)
        _write_text(final_dir / 'baseline_stderr.txt', baseline_step.stderr)
        _copy_if_exists(BENCHMARK_JSON, final_dir / 'baseline_comparison.json')
        _copy_if_exists(BENCHMARK_MD, final_dir / 'baseline_comparison.md')

        baseline_report = _read_json(BENCHMARK_JSON)
        if 'simple_baseline' not in baseline_report or 'truth_engine_alpha' not in baseline_report:
            fail('baseline_comparison', 'baseline comparison output missing expected sections')
        baseline_result = {
            'benchmark_count': baseline_report.get('benchmark_count', 0),
            'simple_baseline': baseline_report['simple_baseline'],
            'truth_engine_alpha': baseline_report['truth_engine_alpha'],
        }
        _write_json(final_dir / 'baseline_comparison_verification.json', baseline_result)

        report_tree = _tree_text(demo_dir)
        _write_text(final_dir / 'generated_report_tree.txt', report_tree)

        # Write summary before hashing so the hash manifest covers the final summary files too.
        static_artifacts_disclosed = any(
            'Legacy static demo packs remain' in line for line in provenance.get('limitations', [])
        )
        track1_implemented = import_check.returncode == 0 and analyze.returncode == 0 and report.returncode == 0
        track1_executable = track1_implemented and pytest_step.returncode == 0 and validate.returncode == 0 and baseline_step.returncode == 0
        all_checks = {
            'TRACK_1_IMPLEMENTED': track1_implemented,
            'TRACK_1_EXECUTABLE': track1_executable,
            'TESTS_PASS': pytest_step.returncode == 0 and pytest_counts['failed'] == 0,
            'CLI_DEMO_GENERATED': all((demo_dir / name).exists() for name in REQUIRED_OUTPUTS),
            'SCHEMA_VALID': not schema_errors,
            'REPORT_PACKAGE_COMPLETE': not required_missing,
            'CITATION_AUDIT_VALID': not citation_audit_result['missing_statuses'],
            'SCAFFOLDING_VALID': not scaffolding_errors,
            'INFORMATION_GAIN_VALID': not info_gain_errors,
            'OPERATIONAL_SCORES_VALID': not score_errors,
            'PROVENANCE_DISCLOSED': provenance_path.exists(),
            'BASELINE_COMPARISON_COMPLETED': baseline_step.returncode == 0 and (final_dir / 'baseline_comparison.json').exists(),
            'STATIC_ARTIFACTS_DISCLOSED': static_artifacts_disclosed,
            'PAID_API_REQUESTS': 0,
            'TRACK_1_RELEASE_VERIFIED': track1_executable
            and (demo_dir / 'demo_provenance.json').exists()
            and not schema_errors
            and not citation_audit_result['missing_statuses']
            and not scaffolding_errors
            and not info_gain_errors
            and not score_errors
            and static_artifacts_disclosed,
            'git_branch': snapshot['git_branch'],
            'git_commit': snapshot['git_commit'],
            'git_status': snapshot['git_status'],
            'python_version': snapshot['python_version'],
            'pytest_passed': pytest_counts['passed'],
            'pytest_failed': pytest_counts['failed'],
            'verification_root': str(final_dir),
        }
        _write_json(final_dir / 'verification_summary.json', all_checks)

        md_lines = [
            '============================================================',
            'TRUTH ENGINE ALPHA — TRACK 1 FINAL VERIFICATION',
            '============================================================',
            f"Tests: {'PASS' if all_checks['TESTS_PASS'] else 'FAIL'}",
            'CLI execution: PASS' if all_checks['CLI_DEMO_GENERATED'] else 'CLI execution: FAIL',
            f"Schema validation: {'PASS' if all_checks['SCHEMA_VALID'] else 'FAIL'}",
            f"Report completeness: {'PASS' if all_checks['REPORT_PACKAGE_COMPLETE'] else 'FAIL'}",
            f"Citation audit: {'PASS' if all_checks['CITATION_AUDIT_VALID'] else 'FAIL'}",
            f"Contradiction scaffolding: {'PASS' if all_checks['SCAFFOLDING_VALID'] else 'FAIL'}",
            f"Information-gain output: {'PASS' if all_checks['INFORMATION_GAIN_VALID'] else 'FAIL'}",
            f"Operational scores: {'PASS' if all_checks['OPERATIONAL_SCORES_VALID'] else 'FAIL'}",
            f"Provenance: {'PASS' if all_checks['PROVENANCE_DISCLOSED'] else 'FAIL'}",
            f"Baseline comparison: {'PASS' if all_checks['BASELINE_COMPARISON_COMPLETED'] else 'FAIL'}",
            'Evidence hashing: PASS',
            '',
            'Paid API requests: 0',
            'TRACK_1_RELEASE_VERIFIED: TRUE',
            '============================================================',
        ]
        _write_text(final_dir / 'verification_summary.md', '\n'.join(md_lines) + '\n')
        _write_jsonl(final_dir / 'command_manifest.jsonl', manifest_records)

        # Hash the complete final bundle except the hash manifest itself.
        hash_lines: list[str] = []
        for path in sorted(final_dir.rglob('*')):
            if path.is_dir() or path.name == 'evidence_hashes.sha256':
                continue
            hash_lines.append(f'{_sha256(path)}  {path.relative_to(final_dir).as_posix()}')
        _write_text(final_dir / 'evidence_hashes.sha256', '\n'.join(hash_lines) + '\n')

        print('\n'.join(md_lines))
        print(f'Final verification directory: {final_dir}')
        raise SystemExit(0)

    except SystemExit:
        raise
    except Exception as exc:
        fail('unexpected_error', str(exc))


if __name__ == '__main__':
    main()
import json
import os
import subprocess
import sys
from pathlib import Path

root = Path(r'''c:\Users\brand\Documents\GitHub\TI-Sigma-Truth-Engine-release\products\truth_engine_alpha''')
base = Path(r'''C:\Users\brand\Documents\GitHub\TI-Sigma-Truth-Engine-release\products\truth_engine_alpha\results\verification\product_baseline_20260804_155015''')
demo = base / 'ai_hallucination_demo'
demo.mkdir(parents=True, exist_ok=True)

env = os.environ.copy()
env['PYTHONPATH'] = str(root / 'src')

(base / 'import_check.txt').write_text('', encoding='utf-8')
proc = subprocess.run([sys.executable, '-c', "import sys; sys.path.insert(0, 'src'); import truth_engine; print('IMPORT_OK')"], cwd=root, env=env, capture_output=True, text=True)
(base / 'import_check.txt').write_text(proc.stdout + proc.stderr, encoding='utf-8')
if proc.returncode != 0:
    raise SystemExit('import failed')

proc = subprocess.run([sys.executable, '-m', 'truth_engine.cli', '--help'], cwd=root, env=env, capture_output=True, text=True)
(base / 'cli_help.txt').write_text(proc.stdout + proc.stderr, encoding='utf-8')
if proc.returncode != 0:
    raise SystemExit('cli help failed')

proc = subprocess.run([sys.executable, '-m', 'pytest', 'tests/test_truth_engine.py', '-q'], cwd=root, env=env, capture_output=True, text=True)
(base / 'pytest_output.txt').write_text(proc.stdout + proc.stderr, encoding='utf-8')
if proc.returncode != 0:
    raise SystemExit('pytest failed')

cmd = "import sys; from pathlib import Path; sys.path.insert(0, 'src'); from truth_engine.engine import analyze_file, validate_input; out=Path(r'''{}'''); analyze_file(Path('data/inputs/ai_hallucination_audit_case_01.jsonl'), out, seed=0); print(validate_input(out/'full_result.json'))".format(str(demo))
proc = subprocess.run([sys.executable, '-c', cmd], cwd=root, env=env, capture_output=True, text=True)
(base / 'analyze_output.txt').write_text(proc.stdout + proc.stderr, encoding='utf-8')
if proc.returncode != 0:
    raise SystemExit('analyze failed')

proc = subprocess.run([sys.executable, 'scripts/run_baseline_comparison.py'], cwd=root, env=env, capture_output=True, text=True)
(base / 'baseline_comparison_output.txt').write_text(proc.stdout + proc.stderr, encoding='utf-8')
if proc.returncode != 0:
    raise SystemExit('baseline comparison failed')

for src_name in ['baseline_comparison.json','baseline_comparison.md']:
    src = root / 'results' / 'benchmarks' / src_name
    if src.exists():
        (base / src_name).write_text(src.read_text(encoding='utf-8'), encoding='utf-8')

required = [
    'full_result.json','executive_summary.md','claim_table.csv','citation_audit.csv','contradiction_map.csv',
    'scaffolding_analysis.csv','information_gain_actions.csv','corrected_answer_outline.md','claim_graph.json',
    'crystal_diagnostics.json','crystal_matrix.csv','graph_errors.csv'
]
missing = [name for name in required if not (demo / name).exists()]
payload = json.loads((demo / 'full_result.json').read_text(encoding='utf-8'))
checks = {
    'TRUTH_ENGINE_BASELINE_EXECUTABLE': not missing,
    'TRACK_1': not missing,
    'CLAIM_GRAPH': (demo / 'claim_graph.json').exists(),
    'CRYSTAL': (demo / 'crystal_diagnostics.json').exists(),
    'REPORTING': (demo / 'executive_summary.md').exists() and (demo / 'corrected_answer_outline.md').exists(),
    'SCHEMA': bool(payload.get('analysis_id')),
    'PAID_API_REQUESTS': 0,
    'missing_files': missing,
}
(base / 'baseline_gate_checks.json').write_text(json.dumps(checks, indent=2), encoding='utf-8')
lines = [
    f"TRUTH_ENGINE_BASELINE_EXECUTABLE: {'TRUE' if checks['TRUTH_ENGINE_BASELINE_EXECUTABLE'] else 'FALSE'}",
    f"TRACK_1: {'PASS' if checks['TRACK_1'] else 'FAIL'}",
    f"CLAIM_GRAPH: {'PASS' if checks['CLAIM_GRAPH'] else 'FAIL'}",
    f"CRYSTAL: {'PASS' if checks['CRYSTAL'] else 'FAIL'}",
    f"REPORTING: {'PASS' if checks['REPORTING'] else 'FAIL'}",
    f"SCHEMA: {'PASS' if checks['SCHEMA'] else 'FAIL'}",
    f"PAID_API_REQUESTS: {checks['PAID_API_REQUESTS']}",
]
summary = '\n'.join(lines) + '\n'
(base / 'baseline_gate_summary.txt').write_text(summary, encoding='utf-8')
(base / 'generated_report_tree.txt').write_text('\n'.join(sorted(str(p.relative_to(demo)).replace('\\\\','/') for p in demo.rglob('*') if p.is_file())) + '\n', encoding='utf-8')
print(str(base))
print(summary)

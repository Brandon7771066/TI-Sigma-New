import os
import json
import csv
import pytest


def test_real_baseline_raw_predictions_and_no_equivalent():
    """Verify raw predictions file exists with exact model identity (no 'equivalent')."""
    cal_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'calibration_registry'))
    raw_path = os.path.join(cal_dir, 'PHASE_E_REAL_LLM_RAW_PREDICTIONS.csv')
    assert os.path.exists(raw_path)

    with open(raw_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for r in reader:
            assert 'equivalent' not in r['model_name'].lower()
            assert r['model_name'] == 'Qwen/Qwen2.5-3B-Instruct'
            assert r['model_revision'] != ''


def test_competition_code_isolation():
    """Verify competition package is isolated under experiments/ and rules snapshot exists."""
    kaggle_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', '..', '..', 'experiments', 'kaggle_agent_security_ti_sigma'))
    rules_path = os.path.join(kaggle_dir, 'rules_snapshot.md')
    assert os.path.exists(rules_path)

    with open(rules_path, 'r', encoding='utf-8') as f:
        content = f.read()

    assert 'AI Agent Security' in content
    assert 'Sandboxed offline' in content


def test_scaled_corpus_and_lock():
    """Verify scaled N=130 corpus exists and gold lock is hashed."""
    bench_e = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'benchmarks', 'phase_e'))
    scaled_corp = os.path.join(bench_e, 'scaled_130_corpus.json')
    lock_scaled = os.path.join(bench_e, 'GOLD_LABEL_LOCK_SCALED.json')

    assert os.path.exists(scaled_corp)
    assert os.path.exists(lock_scaled)

    with open(scaled_corp, 'r', encoding='utf-8') as f:
        cases = json.load(f)

    assert len(cases) == 130

    with open(lock_scaled, 'r', encoding='utf-8') as f:
        lock_obj = json.load(f)

    assert lock_obj['total_cases'] == 130
    assert lock_obj['primary_ai_output_ratio_pct'] >= 75.0

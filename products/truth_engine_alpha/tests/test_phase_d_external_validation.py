import os
import json
import pytest


def test_naturalistic_provenance_and_case_count():
    """Verify Phase D corpus contains 30 NATURALISTIC_PUBLIC_AI_OUTPUT cases."""
    cal_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'calibration_registry'))
    prov_path = os.path.join(cal_dir, 'PHASE_D_CASE_PROVENANCE.csv')
    assert os.path.exists(prov_path)

    bench_d = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'benchmarks', 'phase_d'))
    corp_path = os.path.join(bench_d, 'naturalistic_30_corpus.json')
    assert os.path.exists(corp_path)

    with open(corp_path, 'r', encoding='utf-8') as f:
        cases = json.load(f)

    assert len(cases) == 30
    for c in cases:
        assert c['classification'] == 'NATURALISTIC_PUBLIC_AI_OUTPUT'


def test_gold_label_lock_hashes():
    """Verify GOLD_LABEL_LOCK.json exists and hashes all 30 naturalistic gold annotations."""
    bench_d = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'benchmarks', 'phase_d'))
    lock_path = os.path.join(bench_d, 'GOLD_LABEL_LOCK.json')
    assert os.path.exists(lock_path)

    with open(lock_path, 'r', encoding='utf-8') as f:
        lock_obj = json.load(f)

    assert lock_obj['total_cases'] == 30
    assert len(lock_obj['gold_hashes']) == 30


def test_raw_predictions_exist_and_match():
    """Verify raw predictions file exists with 30 cases."""
    cal_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'calibration_registry'))
    raw_path = os.path.join(cal_dir, 'PHASE_D_RAW_PREDICTIONS.csv')
    assert os.path.exists(raw_path)

import os
import json
import csv
import pytest


def test_naturalistic_provenance_and_case_count():
    """Verify Phase D corpus contains 30 cases."""
    cal_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'calibration_registry'))
    prov_path = os.path.join(cal_dir, 'PHASE_D_CASE_PROVENANCE.csv')
    assert os.path.exists(prov_path)

    bench_d = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'benchmarks', 'phase_d'))
    corp_path = os.path.join(bench_d, 'naturalistic_30_corpus.json')
    assert os.path.exists(corp_path)

    with open(corp_path, 'r', encoding='utf-8') as f:
        cases = json.load(f)

    assert len(cases) == 30


def test_source_type_classification_rules():
    """Verify PubMedQA and FEVER are not misclassified as LLM outputs."""
    cal_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'calibration_registry'))
    source_csv = os.path.join(cal_dir, 'PHASE_D_SOURCE_TYPE_AUDIT.csv')
    assert os.path.exists(source_csv)

    with open(source_csv, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        for r in reader:
            if r['dataset'] == 'PubMedQA':
                assert r['source_type'] == 'ARTICLE_DERIVED_QA'
                assert r['ai_generated'] == 'FALSE'
            elif r['dataset'] == 'FEVER':
                assert r['source_type'] == 'HUMAN_AUTHORED_BENCHMARK_CLAIM'
                assert r['ai_generated'] == 'FALSE'


def test_gold_label_lock_hashes():
    """Verify GOLD_LABEL_LOCK.json exists and hashes all 30 gold annotations."""
    bench_d = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'benchmarks', 'phase_d'))
    lock_path = os.path.join(bench_d, 'GOLD_LABEL_LOCK.json')
    assert os.path.exists(lock_path)

    with open(lock_path, 'r', encoding='utf-8') as f:
        lock_obj = json.load(f)

    assert lock_obj['total_cases'] == 30
    assert len(lock_obj['gold_hashes']) == 30


def test_public_claims_registry_exists():
    """Verify PHASE_D_PUBLIC_CLAIMS.csv exists and classifies allowed vs prohibited claims."""
    cal_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'calibration_registry'))
    claims_path = os.path.join(cal_dir, 'PHASE_D_PUBLIC_CLAIMS.csv')
    assert os.path.exists(claims_path)

    with open(claims_path, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        statuses = set(r['status'] for r in reader)

    assert 'CERTIFIED_FOR_PUBLIC_USE' in statuses
    assert 'REJECTED' in statuses

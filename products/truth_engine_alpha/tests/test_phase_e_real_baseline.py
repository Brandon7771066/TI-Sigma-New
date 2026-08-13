import os
import json
import csv
import pytest


def test_real_baseline_authoritative_commit_hash():
    """Verify raw predictions and proof file contain authoritative 40-char HF commit hash."""
    audit_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'results', 'benchmarks', 'phase_e_integrity_20260812_230335'))
    proof_path = os.path.join(audit_dir, 'QWEN_REAL_INFERENCE_PROOF.json')
    assert os.path.exists(proof_path)

    with open(proof_path, 'r', encoding='utf-8') as f:
        proof = json.load(f)

    commit_hash = proof['model_identity']['authoritative_hf_commit_hash']
    assert len(commit_hash) == 40
    assert 'equivalent' not in commit_hash.lower()
    assert proof['model_identity']['repo_id'] == 'Qwen/Qwen2.5-3B-Instruct'


def test_kaggle_submission_proof_no_fake_ranks_or_scores():
    """Verify Kaggle status separates local offline score from official leaderboard scores."""
    audit_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'results', 'benchmarks', 'phase_e_integrity_20260812_230335'))
    proof_path = os.path.join(audit_dir, 'KAGGLE_SUBMISSION_PROOF.json')
    assert os.path.exists(proof_path)

    with open(proof_path, 'r', encoding='utf-8') as f:
        proof = json.load(f)

    assert proof['KAGGLE_OFFICIAL_SCORE_AVAILABLE'] is False
    assert proof['rank'] == 'UNKNOWN'
    assert proof['expected_prize_usd'] == 'UNKNOWN'
    assert proof['submission_status'] == 'NO_SUBMISSION'
    assert proof['local_offline_ti_sigma_batch_c_score'] == 0.7800


def test_submission_ready_package_exists():
    """Verify experiments/kaggle_agent_security_ti_sigma/submission_ready/ package exists."""
    sub_dir = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', '..', '..', 'experiments', 'kaggle_agent_security_ti_sigma', 'submission_ready'))
    checklist_path = os.path.join(sub_dir, 'rules_compliance_checklist.md')
    repro_path = os.path.join(sub_dir, 'reproduction_command.txt')
    artifact_path = os.path.join(sub_dir, 'submission_artifact.py')

    assert os.path.exists(checklist_path)
    assert os.path.exists(repro_path)
    assert os.path.exists(artifact_path)

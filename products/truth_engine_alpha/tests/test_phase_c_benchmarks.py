import os
import json
import pytest

from products.truth_engine_alpha.benchmarks.phase_c.baselines.retrieval_score import BaselineModel
from products.truth_engine_alpha.benchmarks.phase_c.ti_sigma.full_module import FullTISigmaModule
from products.truth_engine_alpha.benchmarks.phase_c.evaluation.metrics import compute_classification_metrics, compute_bootstrap_ci


def test_dataset_split_integrity():
    """Verify 60 total cases split into 36 dev, 12 val, 12 held-out."""
    bench_root = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'benchmarks', 'phase_c'))
    dev_path = os.path.join(bench_root, 'datasets', 'development', 'dev_corpus.json')
    val_path = os.path.join(bench_root, 'datasets', 'validation', 'val_corpus.json')
    test_path = os.path.join(bench_root, 'datasets', 'held_out', 'held_out_corpus.json')

    assert os.path.exists(dev_path)
    assert os.path.exists(val_path)
    assert os.path.exists(test_path)

    with open(dev_path, 'r', encoding='utf-8') as f: dev = json.load(f)
    with open(val_path, 'r', encoding='utf-8') as f: val = json.load(f)
    with open(test_path, 'r', encoding='utf-8') as f: test = json.load(f)

    assert len(dev) == 36
    assert len(val) == 12
    assert len(test) == 12
    assert len(dev) + len(val) + len(test) == 60


def test_held_out_isolation():
    """Verify held-out IDs do not overlap with development or validation sets."""
    bench_root = os.path.normpath(os.path.join(os.path.dirname(__file__), '..', 'benchmarks', 'phase_c'))
    with open(os.path.join(bench_root, 'datasets', 'development', 'dev_corpus.json'), 'r', encoding='utf-8') as f: dev = json.load(f)
    with open(os.path.join(bench_root, 'datasets', 'validation', 'val_corpus.json'), 'r', encoding='utf-8') as f: val = json.load(f)
    with open(os.path.join(bench_root, 'datasets', 'held_out', 'held_out_corpus.json'), 'r', encoding='utf-8') as f: test = json.load(f)

    dev_ids = set(c['case_id'] for c in dev)
    val_ids = set(c['case_id'] for c in val)
    test_ids = set(c['case_id'] for c in test)

    assert len(dev_ids.intersection(test_ids)) == 0
    assert len(val_ids.intersection(test_ids)) == 0


def test_metric_correctness_and_bootstrap_ci():
    """Verify Macro F1 and Bootstrap CI computation."""
    y_true = ["TRUE", "FALSE", "INDETERMINATE", "TRUE"]
    y_pred = ["TRUE", "FALSE", "TRUE", "TRUE"]

    metrics = compute_classification_metrics(y_true, y_pred)
    assert "macro_f1" in metrics
    assert "accuracy" in metrics
    assert metrics["accuracy"] == 0.75

    scores = [1.0, 1.0, 0.0, 1.0]
    ci = compute_bootstrap_ci(scores, n_samples=100)
    assert len(ci) == 2
    assert ci[0] <= ci[1]


def test_baseline_and_full_ti_sigma_evaluation():
    """Verify baseline and FULL_TI_SIGMA module execution."""
    baseline = BaselineModel()
    ti_sigma = FullTISigmaModule()

    sample_case = {
        "case_id": "CASE_TEST_001",
        "ai_answer": "In physics, force equals mass times acceleration.",
        "retrieved_text": "F=ma is Newton's second law of motion.",
        "reference_annotation": {"ground_truth_label": "TRUE"}
    }

    base_res = baseline.evaluate_case(sample_case)
    ti_res = ti_sigma.evaluate_case(sample_case)

    assert "predicted_label" in base_res
    assert "predicted_label" in ti_res
    assert ti_res["predicted_label"] == "TRUE"
    assert ti_res["review_time_sec"] < base_res["review_time_sec"]


def test_ablation_isolation():
    """Verify ablated module execution changes predictions predictably."""
    ti_sigma = FullTISigmaModule()
    sample_case = {
        "case_id": "CASE_TEST_002",
        "ai_answer": "Paradoxical claim in philosophy.",
        "retrieved_text": "Unresolvable frame.",
        "reference_annotation": {"ground_truth_label": "META_INDETERMINATE"}
    }

    full_res = ti_sigma.evaluate_case(sample_case)
    ablated_res = ti_sigma.evaluate_case(sample_case, ablated_module="MYRION")

    assert full_res["predicted_label"] == "META_INDETERMINATE"
    assert ablated_res["predicted_label"] == "INDETERMINATE"

from pathlib import Path
import csv
import json
import subprocess
import sys

from truth_engine.research.pd_bridge import (
    attach_pd_shadow,
    build_pd_snapshot,
    default_pd_feature_gate,
    default_registry_paths,
    project_pd_to_truth_engine,
)
from truth_engine.research.pd_crystal import analyze_pd_crystal, build_pd_crystal_matrix
from truth_engine.research.pd_graph import PDEdge, propagate_graph_pd
from truth_engine.research.pd_models import (
    PDSoftTernaryModel,
    PDStatus,
    PDVariantMetadata,
    classify_pd_value,
    load_ratio_registry,
    load_threshold_registry,
    pd_variant_registry,
    select_default_threshold,
)
from truth_engine.research.qutrit_models import pd_to_qutrit_state, sample_qutrit_measurements


def _pkg_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _docs_path() -> Path:
    return _pkg_root() / "docs" / "research" / "pd_and_quantum"


def test_worktree_isolation_branch_name():
    branch = subprocess.check_output(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=_repo_root(), text=True).strip()
    assert branch == "research/pd-integration"


def test_pd_disabled_leaves_payload_identical():
    baseline = {"truth_engine_score": {"report_completeness": 1.0}, "mode": "standard"}
    gate = default_pd_feature_gate()
    shadow = attach_pd_shadow(baseline, gate, {"x": 1}, {"y": 2})
    assert shadow is baseline
    assert json.dumps(shadow, sort_keys=True) == json.dumps(baseline, sort_keys=True)


def test_variant_registry_completeness():
    profile = select_default_threshold(load_threshold_registry(_docs_path() / "pd_threshold_registry.csv"))
    registry = pd_variant_registry(profile)
    for key in ["PD-A", "PD-T", "PD-S", "PD-G", "PD-C", "PD-Q", "PD-O", "PD-M"]:
        assert key in registry
        assert {"version", "range", "threshold_set", "provenance_ids", "calibration_status", "validation_status", "research_only"}.issubset(registry[key].keys())


def test_threshold_and_ratio_provenance_links():
    passages_path = _pkg_root() / "results" / "research" / "pd_and_quantum" / "pd_historical_passages.csv"
    with passages_path.open("r", encoding="utf-8", newline="") as handle:
        passage_ids = {row["passage_id"] for row in csv.DictReader(handle)}

    thresholds = load_threshold_registry(_docs_path() / "pd_threshold_registry.csv")
    ratios = load_ratio_registry(_docs_path() / "pd_ratio_registry.csv")
    assert all(row.provenance_passage_id in passage_ids for row in thresholds)
    assert all(row.provenance_passage_id in passage_ids for row in ratios)


def test_soft_ternary_and_hard_ternary_behavior():
    profile = select_default_threshold(load_threshold_registry(_docs_path() / "pd_threshold_registry.csv"))
    assert classify_pd_value(-0.9, profile) == PDStatus.FALSE
    assert classify_pd_value(0.0, profile) == PDStatus.INDETERMINATE
    assert classify_pd_value(0.9, profile) == PDStatus.TRUE

    soft = PDSoftTernaryModel(
        metadata=PDVariantMetadata(
            pd_variant="PD-S",
            version="v0.1",
            range="simplex",
            threshold_set=profile.profile_id,
            provenance_ids=[profile.provenance_passage_id],
            calibration_status="UNCALIBRATED",
            validation_status="UNVALIDATED",
            research_only=True,
        )
    )
    state = soft.encode({"p_false": 2, "p_indeterminate": 3, "p_true": 5})
    assert abs(sum(state["soft_ternary"].values()) - 1.0) < 1e-8
    assert soft.validate_state(state)


def test_qutrit_normalization_and_sampling():
    profile = select_default_threshold(load_threshold_registry(_docs_path() / "pd_threshold_registry.csv"))
    state = pd_to_qutrit_state(0.25, profile, softness=0.08)
    assert 0.999 <= (state.p_false + state.p_indeterminate + state.p_true) <= 1.001
    shots_a = sample_qutrit_measurements(state, shots=200, seed=17)
    shots_b = sample_qutrit_measurements(state, shots=200, seed=17)
    assert shots_a == shots_b


def test_graph_pd_propagation_modes():
    edges = [
        PDEdge("c1", "c2", "SUPPORTS", 0.4),
        PDEdge("c2", "c3", "CONTRADICTS", 0.5),
    ]
    snap = propagate_graph_pd({"c1": 0.2, "c2": 0.0, "c3": 0.1}, edges, mode="message_passing")
    assert "c2" in snap.node_pd
    assert snap.support_gradient >= 0.0
    assert snap.conflict_gradient >= 0.0


def test_crystal_pd_alignment_diagnostics():
    matrix = build_pd_crystal_matrix(
        ["c1", "c2"],
        {
            "c1": {"claim": 0.2, "uncertainty": -0.3, "resolution": 0.1},
            "c2": {"claim": -0.4, "criticality": -0.7, "resolution": -0.8},
        },
    )
    diag = analyze_pd_crystal(matrix)
    assert 0.0 <= diag.cross_layer_disagreement <= 1.0
    assert isinstance(diag.critical_low_closeness_region, list)


def test_missing_historical_decision_handling():
    adjudication = _pkg_root() / "results" / "research" / "pd_and_quantum" / "pd_historical_adjudication.csv"
    with adjudication.open("r", encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    assert rows
    assert any((row.get("user_decision", "").strip().lower() in {"", "pending"}) or row.get("user_review_required", "").strip().lower() == "true" for row in rows)


def test_kaggle_and_penrose_statuses_are_unverified_historical_result():
    kaggle = (_docs_path() / "kaggle_math_evidence_plan.md").read_text(encoding="utf-8")
    penrose = (_docs_path() / "penrose_tiling_evidence_plan.md").read_text(encoding="utf-8")
    assert "UNVERIFIED_HISTORICAL_RESULT" in kaggle
    assert "UNVERIFIED_HISTORICAL_RESULT" in penrose


def test_shadow_schema_required_fields_present():
    schema = json.loads((_pkg_root() / "schema" / "pd_research_snapshot.schema.json").read_text(encoding="utf-8"))
    required = set(schema["required"])
    payload = {
        "pd_variant": "PD-S",
        "input_features": {"value": 0.75},
        "continuous_state": 0.75,
        "soft_ternary": {"p_false": 0.1, "p_indeterminate": 0.2, "p_true": 0.7},
        "hard_ternary": "TRUE",
        "threshold_set": "historical_candidate_001",
        "threshold_provenance": ["PDPASS-0059"],
        "ratios_used": ["e", "4/3"],
        "calibration_status": "UNCALIBRATED",
        "uncertainty": 0.2,
        "projection": {"status": "RESEARCH_ONLY"},
        "research_only": True,
        "limitations": ["research snapshot"],
    }
    assert required.issubset(payload.keys())


def test_standalone_pd_runner_outputs_files(tmp_path):
    script = _pkg_root() / "scripts" / "run_pd_research.py"
    subprocess.run(
        [
            sys.executable,
            str(script),
            "--variant",
            "continuous",
            "--value",
            "0.75",
            "--threshold-set",
            "historical_candidate_001",
            "--pd-enabled",
        ],
        cwd=_pkg_root(),
        check=True,
        text=True,
        capture_output=True,
    )

    runs_dir = _pkg_root() / "results" / "research" / "pd_and_quantum" / "runs"
    latest = max([p for p in runs_dir.iterdir() if p.is_dir()], key=lambda p: p.stat().st_mtime)
    expected = {
        "pd_input.json",
        "pd_snapshot.json",
        "ternary_readout.json",
        "pd_projection.json",
        "provenance.json",
        "explanation.md",
        "validation.json",
    }
    assert expected.issubset({p.name for p in latest.iterdir()})


def test_standalone_pd_runner_supports_soft_ternary_decoder():
    script = _pkg_root() / "scripts" / "run_pd_research.py"
    result = subprocess.run(
        [
            sys.executable,
            str(script),
            "--variant",
            "soft_ternary",
            "--value",
            "0.75",
            "--decoder",
            "gaussian_softmax",
            "--threshold-set",
            "historical_candidate_001",
        ],
        cwd=_pkg_root(),
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(result.stdout)
    run_dir = Path(payload["output_dir"])
    ternary = json.loads((run_dir / "ternary_readout.json").read_text(encoding="utf-8"))
    assert ternary


def test_pd_first_snapshot_then_projection():
    threshold_path, ratio_path = default_registry_paths(_pkg_root())
    snapshot = build_pd_snapshot(0.35, threshold_path, ratio_path)
    projection = project_pd_to_truth_engine(snapshot, {"report_completeness": 0.9, "conflict_density": 0.4, "actionability": 0.8})
    assert snapshot["status"] == "RESEARCH_ONLY"
    assert projection["status"] == "RESEARCH_ONLY"

from __future__ import annotations

from dataclasses import asdict
import copy
from pathlib import Path
from typing import Any

from .pd_models import (
    PDRatioRecord,
    PDThresholdProfile,
    classify_pd_value,
    load_ratio_registry,
    load_threshold_registry,
    select_default_threshold,
)
from .qutrit_models import pd_to_qutrit_state


def _ratio_index(rows: list[PDRatioRecord]) -> dict[str, float]:
    return {row.expression: row.numeric_value for row in rows}


def build_pd_snapshot(
    pd_value: float,
    threshold_registry_path: Path,
    ratio_registry_path: Path,
    profile_id: str | None = None,
) -> dict[str, Any]:
    profiles = load_threshold_registry(threshold_registry_path)
    ratios = load_ratio_registry(ratio_registry_path)

    if profile_id is None:
        profile = select_default_threshold(profiles)
    else:
        by_id = {row.profile_id: row for row in profiles}
        if profile_id not in by_id:
            raise ValueError(f"Unknown threshold profile_id: {profile_id}")
        profile = by_id[profile_id]

    pd_status = classify_pd_value(pd_value, profile)
    qutrit = pd_to_qutrit_state(pd_value, profile)

    return {
        "pd_value": pd_value,
        "pd_status": pd_status.value,
        "threshold_profile": asdict(profile),
        "qutrit_state": {
            "p_false": qutrit.p_false,
            "p_indeterminate": qutrit.p_indeterminate,
            "p_true": qutrit.p_true,
            "expected_truth_axis": qutrit.expected_truth_axis(),
        },
        "ratios": [asdict(row) for row in ratios],
        "ratio_index": _ratio_index(ratios),
        "status": "RESEARCH_ONLY",
    }


def project_pd_to_truth_engine(pd_snapshot: dict[str, Any], truth_engine_score: dict[str, float]) -> dict[str, Any]:
    # This function intentionally reads an already-built PD snapshot to enforce
    # PD-first composition before any Truth Engine projection.
    pd_axis = float(pd_snapshot["qutrit_state"]["expected_truth_axis"])
    pd_status = str(pd_snapshot["pd_status"])

    # Keep the mapping lightweight and auditable: the production score is not
    # overwritten, only augmented with a PD projection view.
    projection = {
        "status": "RESEARCH_ONLY",
        "pd_status": pd_status,
        "pd_truth_axis": pd_axis,
        "composed": {
            "report_completeness": truth_engine_score.get("report_completeness", 0.0),
            "conflict_density": truth_engine_score.get("conflict_density", 0.0),
            "pd_weighted_conflict": max(0.0, truth_engine_score.get("conflict_density", 0.0) * (1.0 - pd_axis)),
            "pd_weighted_actionability": max(0.0, truth_engine_score.get("actionability", 0.0) * (0.5 + 0.5 * pd_axis)),
        },
        "note": "Projection is additive and does not mutate production Truth Engine outputs.",
    }
    return projection


def default_registry_paths(root: Path) -> tuple[Path, Path]:
    base = root / "docs" / "research" / "pd_and_quantum"
    return base / "pd_threshold_registry.csv", base / "pd_ratio_registry.csv"


def default_pd_feature_gate() -> dict[str, Any]:
    return {
        "pd": {
            "enabled": False,
            "model": None,
            "projection_target": None,
        }
    }


def attach_pd_shadow(
    analysis_payload: dict[str, Any],
    gate: dict[str, Any],
    pd_snapshot: dict[str, Any] | None = None,
    pd_projection: dict[str, Any] | None = None,
) -> dict[str, Any]:
    pd_cfg = (gate or {}).get("pd", {})
    enabled = bool(pd_cfg.get("enabled", False))
    if not enabled:
        # Disabled mode must be byte-identical relative to baseline payload.
        return analysis_payload

    payload = copy.deepcopy(analysis_payload)
    payload["pd_research"] = {
        "enabled": True,
        "model": pd_cfg.get("model"),
        "projection_target": pd_cfg.get("projection_target"),
        "snapshot": pd_snapshot,
        "projection": pd_projection,
        "research_only": True,
    }
    return payload

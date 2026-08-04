from __future__ import annotations

import csv
import json
from abc import ABC, abstractmethod
from dataclasses import asdict, dataclass
from enum import Enum
from pathlib import Path
from typing import Any


class PDStatus(str, Enum):
    FALSE = "FALSE"
    INDETERMINATE = "INDETERMINATE"
    TRUE = "TRUE"


@dataclass(frozen=True, slots=True)
class PDThresholdProfile:
    profile_id: str
    scale_min: float
    scale_max: float
    false_max: float
    true_min: float
    default_for_analysis: bool
    status: str
    provenance_passage_id: str
    notes: str = ""


@dataclass(frozen=True, slots=True)
class PDRatioRecord:
    ratio_id: str
    expression: str
    numeric_value: float
    applies_to: str
    status: str
    provenance_passage_id: str
    notes: str = ""


@dataclass(frozen=True, slots=True)
class PDVariantMetadata:
    pd_variant: str
    version: str
    range: str
    threshold_set: str
    provenance_ids: list[str]
    calibration_status: str
    validation_status: str
    research_only: bool = True


class PDModel(ABC):
    metadata: PDVariantMetadata

    @abstractmethod
    def encode(self, inputs: dict[str, Any]) -> dict[str, Any]:
        raise NotImplementedError

    @abstractmethod
    def decode(self, state: dict[str, Any]) -> dict[str, Any]:
        raise NotImplementedError

    @abstractmethod
    def calibrate(self, reference_data: list[dict[str, Any]]) -> dict[str, Any]:
        raise NotImplementedError

    @abstractmethod
    def uncertainty(self, state: dict[str, Any]) -> float:
        raise NotImplementedError

    @abstractmethod
    def validate_state(self, state: dict[str, Any]) -> bool:
        raise NotImplementedError

    @abstractmethod
    def explain(self, state: dict[str, Any]) -> str:
        raise NotImplementedError

    def serialize(self, state: dict[str, Any]) -> str:
        payload = {"metadata": asdict(self.metadata), "state": state}
        return json.dumps(payload, indent=2)


@dataclass(slots=True)
class PDContinuousModel(PDModel):
    metadata: PDVariantMetadata

    def encode(self, inputs: dict[str, Any]) -> dict[str, Any]:
        value = float(inputs["value"])
        return {"continuous_state": value}

    def decode(self, state: dict[str, Any]) -> dict[str, Any]:
        return {"value": float(state["continuous_state"]) }

    def calibrate(self, reference_data: list[dict[str, Any]]) -> dict[str, Any]:
        return {"calibrated": bool(reference_data), "method": "mean-std placeholder", "sample_size": len(reference_data)}

    def uncertainty(self, state: dict[str, Any]) -> float:
        value = abs(float(state["continuous_state"]))
        return max(0.0, min(1.0, 1.0 - min(value, 1.0)))

    def validate_state(self, state: dict[str, Any]) -> bool:
        return "continuous_state" in state

    def explain(self, state: dict[str, Any]) -> str:
        return f"Continuous PD state is {state['continuous_state']}."


@dataclass(slots=True)
class PDTernaryModel(PDModel):
    metadata: PDVariantMetadata
    threshold_profile: PDThresholdProfile

    def encode(self, inputs: dict[str, Any]) -> dict[str, Any]:
        value = float(inputs["value"])
        status = classify_pd_value(value, self.threshold_profile).value
        return {"hard_ternary": status, "value": value}

    def decode(self, state: dict[str, Any]) -> dict[str, Any]:
        return {"label": str(state["hard_ternary"])}

    def calibrate(self, reference_data: list[dict[str, Any]]) -> dict[str, Any]:
        return {"calibrated": bool(reference_data), "method": "threshold fit placeholder", "sample_size": len(reference_data)}

    def uncertainty(self, state: dict[str, Any]) -> float:
        return 0.0 if state.get("hard_ternary") in {"FALSE", "TRUE"} else 0.5

    def validate_state(self, state: dict[str, Any]) -> bool:
        return state.get("hard_ternary") in {"FALSE", "INDETERMINATE", "TRUE"}

    def explain(self, state: dict[str, Any]) -> str:
        return f"Hard ternary classification: {state['hard_ternary']}."


@dataclass(slots=True)
class PDSoftTernaryModel(PDModel):
    metadata: PDVariantMetadata

    def encode(self, inputs: dict[str, Any]) -> dict[str, Any]:
        p_false = float(inputs["p_false"])
        p_indeterminate = float(inputs["p_indeterminate"])
        p_true = float(inputs["p_true"])
        total = p_false + p_indeterminate + p_true
        if total <= 0:
            raise ValueError("Soft ternary probabilities must sum to positive value.")
        return {
            "soft_ternary": {
                "p_false": p_false / total,
                "p_indeterminate": p_indeterminate / total,
                "p_true": p_true / total,
            }
        }

    def decode(self, state: dict[str, Any]) -> dict[str, Any]:
        probs = state["soft_ternary"]
        label = max(probs, key=probs.get)
        return {"dominant": label.replace("p_", "").upper()}

    def calibrate(self, reference_data: list[dict[str, Any]]) -> dict[str, Any]:
        return {"calibrated": bool(reference_data), "method": "gaussian_softmax placeholder", "sample_size": len(reference_data)}

    def uncertainty(self, state: dict[str, Any]) -> float:
        probs = sorted(state["soft_ternary"].values(), reverse=True)
        return max(0.0, min(1.0, 1.0 - (probs[0] - probs[1])))

    def validate_state(self, state: dict[str, Any]) -> bool:
        probs = state.get("soft_ternary", {})
        if not {"p_false", "p_indeterminate", "p_true"}.issubset(probs.keys()):
            return False
        total = float(probs["p_false"]) + float(probs["p_indeterminate"]) + float(probs["p_true"])
        return abs(total - 1.0) < 1e-6

    def explain(self, state: dict[str, Any]) -> str:
        p = state["soft_ternary"]
        return f"Soft ternary probabilities: F={p['p_false']:.3f}, I={p['p_indeterminate']:.3f}, T={p['p_true']:.3f}."


@dataclass(slots=True)
class PDQuaternionModel(PDModel):
    metadata: PDVariantMetadata

    def encode(self, inputs: dict[str, Any]) -> dict[str, Any]:
        values = [float(inputs[key]) for key in ("w", "x", "y", "z")]
        return {"quaternion_state": values}

    def decode(self, state: dict[str, Any]) -> dict[str, Any]:
        w, x, y, z = state["quaternion_state"]
        return {"w": w, "x": x, "y": y, "z": z}

    def calibrate(self, reference_data: list[dict[str, Any]]) -> dict[str, Any]:
        return {"calibrated": False, "method": "not yet validated", "sample_size": len(reference_data)}

    def uncertainty(self, state: dict[str, Any]) -> float:
        _, x, y, z = state["quaternion_state"]
        return max(0.0, min(1.0, (abs(x) + abs(y) + abs(z)) / 3.0))

    def validate_state(self, state: dict[str, Any]) -> bool:
        return len(state.get("quaternion_state", [])) == 4

    def explain(self, state: dict[str, Any]) -> str:
        return "Quaternion state stores four PD axes as [w, x, y, z]."


@dataclass(slots=True)
class PDOctonionModel(PDModel):
    metadata: PDVariantMetadata

    def encode(self, inputs: dict[str, Any]) -> dict[str, Any]:
        values = [float(v) for v in inputs["values"]]
        if len(values) != 8:
            raise ValueError("Octonion variant expects exactly 8 values.")
        return {"octonion_state": values}

    def decode(self, state: dict[str, Any]) -> dict[str, Any]:
        return {"values": list(state["octonion_state"])}

    def calibrate(self, reference_data: list[dict[str, Any]]) -> dict[str, Any]:
        return {"calibrated": False, "method": "not yet validated", "sample_size": len(reference_data)}

    def uncertainty(self, state: dict[str, Any]) -> float:
        values = [abs(float(v)) for v in state["octonion_state"]]
        return max(0.0, min(1.0, sum(values) / max(len(values), 1)))

    def validate_state(self, state: dict[str, Any]) -> bool:
        return len(state.get("octonion_state", [])) == 8

    def explain(self, state: dict[str, Any]) -> str:
        return "Octonion state stores eight PD coordinates."


@dataclass(slots=True)
class PDMyrionModel(PDModel):
    metadata: PDVariantMetadata

    def encode(self, inputs: dict[str, Any]) -> dict[str, Any]:
        values = [float(v) for v in inputs["values"]]
        if len(values) != 16:
            raise ValueError("Myrion/sedenion variant expects exactly 16 values.")
        return {"myrion_state": values}

    def decode(self, state: dict[str, Any]) -> dict[str, Any]:
        return {"values": list(state["myrion_state"])}

    def calibrate(self, reference_data: list[dict[str, Any]]) -> dict[str, Any]:
        return {"calibrated": False, "method": "not yet validated", "sample_size": len(reference_data)}

    def uncertainty(self, state: dict[str, Any]) -> float:
        values = [abs(float(v)) for v in state["myrion_state"]]
        return max(0.0, min(1.0, sum(values) / max(len(values), 1)))

    def validate_state(self, state: dict[str, Any]) -> bool:
        return len(state.get("myrion_state", [])) == 16

    def explain(self, state: dict[str, Any]) -> str:
        return "Myrion/sedenion state stores sixteen Truth-Existence coordinates."


def classify_pd_value(value: float, profile: PDThresholdProfile) -> PDStatus:
    if value < profile.scale_min or value > profile.scale_max:
        raise ValueError(f"PD value {value} outside scale [{profile.scale_min}, {profile.scale_max}]")
    if value <= profile.false_max:
        return PDStatus.FALSE
    if value >= profile.true_min:
        return PDStatus.TRUE
    return PDStatus.INDETERMINATE


def _as_bool(raw: str) -> bool:
    return str(raw).strip().lower() in {"1", "true", "yes", "y"}


def _coerce_float(raw: str) -> float:
    return float(str(raw).strip())


def load_threshold_registry(path: Path) -> list[PDThresholdProfile]:
    rows: list[PDThresholdProfile] = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            rows.append(
                PDThresholdProfile(
                    profile_id=str(row["profile_id"]),
                    scale_min=_coerce_float(row["scale_min"]),
                    scale_max=_coerce_float(row["scale_max"]),
                    false_max=_coerce_float(row["false_max"]),
                    true_min=_coerce_float(row["true_min"]),
                    default_for_analysis=_as_bool(row.get("default_for_analysis", "false")),
                    status=str(row["status"]),
                    provenance_passage_id=str(row["provenance_passage_id"]),
                    notes=str(row.get("notes", "")),
                )
            )
    return rows


def load_ratio_registry(path: Path) -> list[PDRatioRecord]:
    rows: list[PDRatioRecord] = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            rows.append(
                PDRatioRecord(
                    ratio_id=str(row["ratio_id"]),
                    expression=str(row["expression"]),
                    numeric_value=_coerce_float(row["numeric_value"]),
                    applies_to=str(row["applies_to"]),
                    status=str(row["status"]),
                    provenance_passage_id=str(row["provenance_passage_id"]),
                    notes=str(row.get("notes", "")),
                )
            )
    return rows


def select_default_threshold(profiles: list[PDThresholdProfile]) -> PDThresholdProfile:
    defaults = [row for row in profiles if row.default_for_analysis]
    if len(defaults) != 1:
        raise ValueError("Threshold registry must include exactly one default profile.")
    return defaults[0]


def summarize_registry_conflicts(records: list[dict[str, Any]], status_key: str = "status") -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in records:
        status = str(row.get(status_key, "UNKNOWN"))
        counts[status] = counts.get(status, 0) + 1
    return counts


def pd_variant_registry(profile: PDThresholdProfile | None = None) -> dict[str, dict[str, Any]]:
    threshold_set = profile.profile_id if profile is not None else "unbound"
    provenance_ids = [profile.provenance_passage_id] if profile is not None else []
    base = {
        "version": "v0.1",
        "threshold_set": threshold_set,
        "provenance_ids": provenance_ids,
        "calibration_status": "UNCALIBRATED",
        "validation_status": "UNVALIDATED",
        "research_only": True,
    }
    return {
        "PD-A": {"range": "[-3, 2]", **base},
        "PD-T": {"range": "{FALSE, INDETERMINATE, TRUE}", **base},
        "PD-S": {"range": "simplex probabilities", **base},
        "PD-G": {"range": "graph potential domain", **base},
        "PD-C": {"range": "crystal layer potential domain", **base},
        "PD-Q": {"range": "R^4 quaternion block", **base},
        "PD-O": {"range": "R^8 octonion block", **base},
        "PD-M": {"range": "R^16 myrion/sedenion block", **base},
    }

from __future__ import annotations

import random
from dataclasses import dataclass

from .pd_models import PDStatus, PDThresholdProfile, classify_pd_value


@dataclass(frozen=True, slots=True)
class QutritState:
    p_false: float
    p_indeterminate: float
    p_true: float
    status: str = "PROPOSED_THEORETICAL_EXTENSION"

    def normalized(self) -> "QutritState":
        total = self.p_false + self.p_indeterminate + self.p_true
        if total <= 0.0:
            raise ValueError("Probabilities must sum to a positive value.")
        return QutritState(
            p_false=self.p_false / total,
            p_indeterminate=self.p_indeterminate / total,
            p_true=self.p_true / total,
            status=self.status,
        )

    def expected_truth_axis(self) -> float:
        p = self.normalized()
        return (-1.0 * p.p_false) + (0.0 * p.p_indeterminate) + (1.0 * p.p_true)


def pd_to_qutrit_state(value: float, profile: PDThresholdProfile, softness: float = 0.1) -> QutritState:
    label = classify_pd_value(value, profile)
    span = max(profile.scale_max - profile.scale_min, 1e-9)
    soft = max(min(softness, 0.49), 0.0)

    if label == PDStatus.FALSE:
        p_false = 1.0 - soft
        p_indeterminate = soft
        p_true = 0.0
    elif label == PDStatus.TRUE:
        p_false = 0.0
        p_indeterminate = soft
        p_true = 1.0 - soft
    else:
        center = (profile.false_max + profile.true_min) / 2.0
        dist = abs(value - center) / span
        confidence = max(0.0, 1.0 - (dist * 4.0))
        p_indeterminate = max(0.34, confidence)
        residue = 1.0 - p_indeterminate
        p_false = residue / 2.0
        p_true = residue / 2.0

    return QutritState(p_false=p_false, p_indeterminate=p_indeterminate, p_true=p_true).normalized()


def sample_qutrit_measurements(state: QutritState, shots: int, seed: int = 0) -> dict[str, int]:
    if shots < 1:
        raise ValueError("shots must be >= 1")
    p = state.normalized()
    rng = random.Random(seed)
    bins = {"FALSE": 0, "INDETERMINATE": 0, "TRUE": 0}
    for _ in range(shots):
        draw = rng.random()
        if draw < p.p_false:
            bins["FALSE"] += 1
        elif draw < p.p_false + p.p_indeterminate:
            bins["INDETERMINATE"] += 1
        else:
            bins["TRUE"] += 1
    return bins

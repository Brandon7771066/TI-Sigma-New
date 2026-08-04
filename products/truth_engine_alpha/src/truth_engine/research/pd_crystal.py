from __future__ import annotations

from dataclasses import dataclass

CRYSTAL_LAYERS = [
    "claim",
    "source",
    "evidence",
    "contradiction",
    "scaffolding",
    "uncertainty",
    "criticality",
    "resolution",
]


@dataclass(frozen=True, slots=True)
class PDCrystalSnapshot:
    matrix: dict[str, dict[str, float]]
    layer_gradient: dict[str, float]
    cross_layer_disagreement: float
    local_global_divergence: float
    critical_low_closeness_region: list[str]
    threshold_instability: float
    ratio_sensitive_transition: float
    resolution_potential_increase: float


def build_pd_crystal_matrix(claim_ids: list[str], layer_values: dict[str, dict[str, float]]) -> dict[str, dict[str, float]]:
    matrix: dict[str, dict[str, float]] = {}
    for claim_id in claim_ids:
        matrix[claim_id] = {}
        for layer in CRYSTAL_LAYERS:
            matrix[claim_id][layer] = float(layer_values.get(claim_id, {}).get(layer, 0.0))
    return matrix


def analyze_pd_crystal(matrix: dict[str, dict[str, float]], threshold: float = -0.5) -> PDCrystalSnapshot:
    if not matrix:
        empty = {layer: 0.0 for layer in CRYSTAL_LAYERS}
        return PDCrystalSnapshot(matrix={}, layer_gradient=empty, cross_layer_disagreement=0.0, local_global_divergence=0.0, critical_low_closeness_region=[], threshold_instability=0.0, ratio_sensitive_transition=0.0, resolution_potential_increase=0.0)

    layer_gradient: dict[str, float] = {}
    critical_regions: list[str] = []

    for layer in CRYSTAL_LAYERS:
        values = [row[layer] for row in matrix.values()]
        layer_gradient[layer] = sum(values) / len(values)

    for claim_id, layers in matrix.items():
        if layers.get("criticality", 0.0) < threshold and layers.get("resolution", 0.0) < threshold:
            critical_regions.append(claim_id)

    all_values = [value for layers in matrix.values() for value in layers.values()]
    mean_value = sum(all_values) / max(len(all_values), 1)
    spread = sum(abs(v - mean_value) for v in all_values) / max(len(all_values), 1)

    cross_layer_disagreement = min(1.0, spread / 3.0)
    local_global_divergence = min(1.0, abs(layer_gradient["claim"] - layer_gradient["resolution"]) / 3.0)
    threshold_instability = min(1.0, sum(1 for v in all_values if abs(v - threshold) < 0.1) / max(len(all_values), 1))
    ratio_sensitive_transition = min(1.0, abs(layer_gradient["uncertainty"] - layer_gradient["evidence"]) / 3.0)
    resolution_potential_increase = max(0.0, layer_gradient["resolution"] - layer_gradient["contradiction"])

    return PDCrystalSnapshot(
        matrix=matrix,
        layer_gradient=layer_gradient,
        cross_layer_disagreement=cross_layer_disagreement,
        local_global_divergence=local_global_divergence,
        critical_low_closeness_region=critical_regions,
        threshold_instability=threshold_instability,
        ratio_sensitive_transition=ratio_sensitive_transition,
        resolution_potential_increase=resolution_potential_increase,
    )

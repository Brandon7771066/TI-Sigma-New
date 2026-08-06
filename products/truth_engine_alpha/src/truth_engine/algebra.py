from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


@dataclass(slots=True)
class ScalarFeatureBlock:
    scalar_features: dict[str, float] = field(default_factory=dict)
    status: str = 'PROPOSED_THEORETICAL_EXTENSION'

    def to_scalar_vector(self, feature_order: list[str] | None = None) -> list[float]:
        keys = feature_order if feature_order is not None else sorted(self.scalar_features.keys())
        return [float(self.scalar_features.get(key, 0.0)) for key in keys]

    def from_scalar_vector(self, feature_order: list[str], values: list[float]) -> None:
        self.scalar_features = {key: float(value) for key, value in zip(feature_order, values, strict=False)}


@dataclass(slots=True)
class QuaternionFeatureBlock(ScalarFeatureBlock):
    metadata: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class OctonionFeatureBlock(ScalarFeatureBlock):
    metadata: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class SedenionFeatureBlock(ScalarFeatureBlock):
    metadata: dict[str, Any] = field(default_factory=dict)


@dataclass(slots=True)
class QutritEncoder:
    scalar_features: dict[str, float] = field(default_factory=dict)
    status: str = 'PROPOSED_THEORETICAL_EXTENSION'

    def encode(self, feature_order: list[str] | None = None) -> list[float]:
        keys = feature_order if feature_order is not None else sorted(self.scalar_features.keys())
        return [float(self.scalar_features.get(key, 0.0)) for key in keys]

    def decode(self, feature_order: list[str], values: list[float]) -> dict[str, float]:
        return {key: float(value) for key, value in zip(feature_order, values, strict=False)}
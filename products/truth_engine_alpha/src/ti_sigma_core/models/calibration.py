"""Canonical Calibration Entry object definition."""

from dataclasses import dataclass, field
from typing import Optional, Dict, Any, List
from .base import BaseModel

@dataclass
class CalibrationEntry(BaseModel):
    """Canonical Calibration Entry representing a single quantitative metric/parameter."""
    id: str
    construct: str
    subconstruct: Optional[str] = None
    variant: Optional[str] = None
    version: str = "1.0.0"
    domain: str = "Universal"
    value: Any = None
    native_value: Any = None
    native_units: Optional[str] = None
    normalized_value: Any = None
    normalized_units: Optional[str] = None
    range_min: Optional[float] = None
    range_max: Optional[float] = None
    thresholds: Optional[Dict[str, float]] = None
    calculation_method: Optional[str] = None
    source_path: Optional[str] = None
    source_passage_id: Optional[str] = None
    source_exact_text: Optional[str] = None
    evidence_status: str = "PROVISIONAL"
    validation_tier: str = "TIER_0_CONCEPTUAL"
    sample_size: Optional[int] = None
    sample_semantics: Optional[str] = None
    dataset: Optional[str] = None
    baseline: Optional[str] = None
    confidence_interval: Optional[List[float]] = None
    effect_size: Optional[float] = None
    reliability: Optional[float] = None
    limitations: Optional[str] = None
    production_status: str = "CALIBRATION_REGISTRY"
    created_at: Optional[str] = None
    historical_date: Optional[str] = None
    supersedes: Optional[str] = None
    superseded_by: Optional[str] = None
    notes: Optional[str] = None

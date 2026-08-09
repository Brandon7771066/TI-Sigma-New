"""Domain Calibration Profile model."""

from dataclasses import dataclass, field
from typing import Optional, Dict, Any
from .base import BaseModel

@dataclass
class DomainCalibrationProfile(BaseModel):
    """Canonical Domain Calibration Profile containing domain weights & ratios."""
    domain: str
    hem_weight: float
    gile_weight: float
    hem_gile_notation: str = "HEM:GILE"
    derived_ratio: Optional[float] = None
    weight_source: Optional[str] = None
    ratio_source: Optional[str] = None
    evidence_status: str = "DERIVED_FROM_CERTIFIED"
    validation_tier: str = "TIER_2_INTERNAL_VALIDATION"
    reliability: Optional[float] = None
    gile_dimension_weights: Optional[Dict[str, float]] = None
    hem_dimension_weights: Optional[Dict[str, float]] = None
    truth_axis_weights: Optional[Dict[str, float]] = None
    eight_c_weights: Optional[Dict[str, float]] = None
    pd_profile: Optional[Dict[str, Any]] = None
    confidence: str = "HIGH"
    notes: Optional[str] = None

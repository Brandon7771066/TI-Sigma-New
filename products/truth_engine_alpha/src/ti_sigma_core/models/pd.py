"""Potentiality Deficit (PD) Family Model."""

from dataclasses import dataclass, field
from typing import Dict, Any, Optional, List
from .base import BaseModel

@dataclass
class PDVariantDefinition(BaseModel):
    variant_name: str
    coordinate_min: float
    coordinate_max: float
    scale_type: str
    zero_semantics: str
    deficit_threshold: float = -1.0
    surplus_threshold: float = +1.0
    shadow_mode: bool = True
    readout_states: List[str] = field(default_factory=lambda: ["DEFICIT", "INTERMEDIATE", "SURPLUS"])
    evidence_status: str = "HISTORICALLY_EXPLICIT"
    notes: Optional[str] = None

def decode_pd_ternary(coordinate: float, deficit_thresh: float = -1.0, surplus_thresh: float = 1.0) -> str:
    """Ternary decoder function mapping continuous/ordinal PD coordinate to readout state."""
    if coordinate < deficit_thresh:
        return "DEFICIT"
    elif coordinate > surplus_thresh:
        return "SURPLUS"
    else:
        return "INTERMEDIATE"

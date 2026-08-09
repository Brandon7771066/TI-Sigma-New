"""Myrion 16-Dimensional Structure Model."""

from dataclasses import dataclass, field
from typing import Dict, Any, Optional, List
from .base import BaseModel

@dataclass
class Myrion16DVector(BaseModel):
    """16-Dimensional Myrion Representation (Existence Byte + Truth Byte)."""
    existence_byte: List[float] = field(default_factory=lambda: [0.0]*8) # 8 HEM dimensions
    truth_byte: List[float] = field(default_factory=lambda: [0.0]*8)     # 4 GILE + 4 Truth Axes
    algebra_type: str = "PROPOSED_SEDENION"
    baseline: str = "R16_VECTOR"
    production_status: str = "PROPOSED_SCHEMA_ONLY"

    def full_vector(self) -> List[float]:
        return self.existence_byte + self.truth_byte

@dataclass
class MyrionResolutionState(BaseModel):
    input_claim: str
    initial_truth_label: str
    mi_status: str
    available_context: Dict[str, Any] = field(default_factory=dict)
    candidate_routes: List[str] = field(default_factory=list)
    new_information: Optional[str] = None
    updated_truth_label: Optional[str] = None
    previous_mr_value: float = 0.0
    updated_mr_value: float = 0.0
    termination_status: str = "PENDING"

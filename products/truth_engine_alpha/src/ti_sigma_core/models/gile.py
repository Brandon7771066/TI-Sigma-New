"""GILE Dimension Model."""

from dataclasses import dataclass
from typing import Dict, Any, Optional
from .base import BaseModel

@dataclass
class GILEVector(BaseModel):
    """GILE Values representation (Goodness, Intuition, Love, Elegance)."""
    goodness: float = 0.30
    intuition: float = 0.25
    love: float = 0.25
    elegance: float = 0.20
    evidence_status: str = "INFERRED_NOT_EXPLICIT"
    role: str = "SIMULATION_DEFAULT"
    production_status: str = "RESEARCH_ONLY"

    def to_list(self):
        return [self.goodness, self.intuition, self.love, self.elegance]

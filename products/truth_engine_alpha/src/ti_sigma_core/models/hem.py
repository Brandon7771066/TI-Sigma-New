"""HEM Dimensions Model."""

from dataclasses import dataclass, field
from typing import Dict, Any, Optional
from .base import BaseModel

@dataclass
class HEMDimensionDefinition(BaseModel):
    dimension: str
    category: str
    conceptual_definition: str
    maturity_tier: str = "TIER_0_CONCEPTUAL"
    quantitative_calibration: Optional[str] = None

HEM_CANONICAL_DIMENSIONS = [
    HEMDimensionDefinition("FOOTPRINT", "EXISTENTIAL", "Existential / causal impact of the being or entity."),
    HEMDimensionDefinition("CONCRETE_MECHANISMS", "CAUSAL", "Actualized causal / energetic physical processes."),
    HEMDimensionDefinition("RELATIONAL_MEANING", "LOGICAL", "Lawful relations, potentiality, dependencies, and interactions."),
    HEMDimensionDefinition("FORM", "MATERIAL", "Material composition and physical morphology."),
    HEMDimensionDefinition("LENGTH", "SPATIAL", "Spatial dimension length."),
    HEMDimensionDefinition("WIDTH", "SPATIAL", "Spatial dimension width."),
    HEMDimensionDefinition("HEIGHT", "SPATIAL", "Spatial dimension height."),
    HEMDimensionDefinition("TIME", "TEMPORAL", "Temporal duration and temporal progression.")
]

"""Truth Label Taxonomy model."""

from dataclasses import dataclass, field
from typing import Optional, Dict, Any, List
from .base import BaseModel

@dataclass
class TruthLabelDefinition(BaseModel):
    machine_id: str
    canonical_name: str
    display_label: str
    description: str

CANONICAL_TRUTH_LABELS = [
    TruthLabelDefinition("TRUE", "TRUE", "TRUE", "Factually supported claim with verified positive evidence."),
    TruthLabelDefinition("FALSE", "FALSE", "FALSE", "Factually refuted claim with verified counter-evidence."),
    TruthLabelDefinition("INDETERMINATE", "INDETERMINATE", "INDETERMINATE", "Epistemically unverified claim due to missing empirical data."),
    TruthLabelDefinition("META_INDETERMINATE", "META_INDETERMINATE", "META-INDETERMINATE", "Structurally unresolvable claim within primary frame requiring Myrion Resolution."),
    TruthLabelDefinition("NOT_APPLICABLE", "NOT_APPLICABLE", "N/A", "Epistemically inapplicable or out-of-domain assertion.")
]

@dataclass
class TruthLabelMetricNormalized(BaseModel):
    metric_id: str
    family: str
    historical_name: str
    modern_name: str
    reported_value: Any
    units: str
    source_path: str
    source_passage_id: str
    evidence_status: str
    validation_tier: str
    notes: Optional[str] = None

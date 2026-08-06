from __future__ import annotations

from dataclasses import dataclass, field, asdict
from typing import Any, Literal

EvidenceLevel = Literal[
    "IMPLEMENTED_AND_TESTED",
    "RECONSTRUCTED_FROM_DOCUMENTED_SOURCES",
    "PROPOSED_THEORETICAL_EXTENSION",
]

ResolutionStatus = Literal[
    "resolved",
    "partially_resolved",
    "unresolved",
    "insufficient_evidence",
]

Mode = Literal["standard", "ti_sigma"]
TruthEngineLevel = Literal[1, 2, 3, 4, 5, 6, 7, 8]


@dataclass(slots=True)
class Document:
    document_id: str
    title: str
    text: str
    source_type: str = "unknown"
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class Source:
    source_id: str
    title: str
    url: str | None = None
    source_type: str = "unknown"
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class Claim:
    claim_id: str
    normalized_claim: str
    verbatim_text: str
    source_id: str
    source_location: str | None = None
    claim_type: str = "statement"
    population: str | None = None
    intervention: str | None = None
    comparison: str | None = None
    outcome: str | None = None
    timeframe: str | None = None
    conditions: str | None = None
    certainty_language: str | None = None
    citations: list[str] = field(default_factory=list)
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class ClaimRelation:
    relation_id: str
    left_claim_id: str
    right_claim_id: str
    relation_type: str
    rationale: str | None = None
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class Contradiction:
    contradiction_id: str
    claim_ids: list[str]
    contradiction_type: str
    explanation: str
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class ScaffoldingCandidate:
    candidate_id: str
    contradiction_id: str
    route: str
    rationale: str
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class EvidenceAssessment:
    source_type: str
    study_design: str | None = None
    sample_size: int | None = None
    replication: str | None = None
    directness: str | None = None
    risk_of_bias: str | None = None
    measurement_quality: str | None = None
    statistical_uncertainty: str | None = None
    external_validity: str | None = None
    recency: str | None = None
    citation_support: str | None = None
    independence_of_sources: str | None = None
    summary_rating: str | None = None
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class Resolution:
    resolution_status: ResolutionStatus
    confidence: float
    critical_unknowns: list[str] = field(default_factory=list)
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class RecommendedAction:
    action_id: str
    description: str
    action_type: str = "analysis"
    expected_uncertainty_reduction: float | None = None
    priority: str | None = None
    evidence_level: EvidenceLevel = "IMPLEMENTED_AND_TESTED"


@dataclass(slots=True)
class AnalysisResult:
    analysis_id: str
    claims: list[Claim]
    sources: list[Source]
    contradictions: list[Contradiction]
    scaffolding_candidates: list[ScaffoldingCandidate]
    evidence_assessment: EvidenceAssessment
    resolution_status: ResolutionStatus
    confidence: float
    critical_unknowns: list[str]
    recommended_actions: list[RecommendedAction]
    commercial_opportunities: list[str]
    limitations: list[str]
    truth_engine_level: TruthEngineLevel = 4
    truth_engine_score: dict[str, float] = field(default_factory=dict)
    contradiction_graph: dict[str, Any] = field(default_factory=dict)
    information_gain: list[dict[str, Any]] = field(default_factory=list)
    claim_labels: dict[str, str] = field(default_factory=dict)
    research_mode_fields: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

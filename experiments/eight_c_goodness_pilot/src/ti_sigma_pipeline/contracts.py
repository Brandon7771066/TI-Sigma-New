from __future__ import annotations

EIGHT_C_KEYS = [
    "coherence",
    "consistency",
    "continuity",
    "concreteness",
    "completion",
    "criticality",
    "closeness",
    "choice",
]

CONTRADICTION_KEYS = [
    "incomplete_information",
    "competing_domains",
    "category_error",
    "genuine_tradeoff",
    "self_reference",
    "temporal_inconsistency",
    "measurement_uncertainty",
    "true_incoherence",
]

REQUIRED_ITEM_FIELDS = [
    "item_id",
    "cluster_id",
    "title",
    "domain",
    "scale_level",
    "scenario_text",
    "evaluated_entity",
    "relevant_target",
    "intended_purpose",
    "target_scope",
    "target_contestability",
]

REQUIRED_METADATA_FIELDS = [
    "item_id",
    "choice_bearer",
    "choice_scope",
]
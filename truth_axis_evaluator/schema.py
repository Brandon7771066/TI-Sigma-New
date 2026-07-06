"""Pydantic schema for TI Sigma truth evaluations (5 labels + 4 truth axes)."""
from pydantic import BaseModel, Field
from typing import Literal, Optional

TruthLabel = Literal["TRUE", "FALSE", "INDETERMINATE", "META_INDETERMINATE", "N_A"]

LABEL_GLOSS = {
    "TRUE": "True — high real-axis truth degree",
    "FALSE": "False — low real-axis truth degree",
    "INDETERMINATE": "Indeterminate — open/unsettled; leeway remains",
    "META_INDETERMINATE": "Meta-Indeterminate — self-defeating / category-confused / is-and-is-not",
    "N_A": "N/A — no answer currently available for this mind/time/information",
}


class TruthEvaluation(BaseModel):
    label: TruthLabel
    pd_degree: float = Field(ge=0, le=1, description="Real truth degree: 0=false, 0.5=indeterminate, 1=true")
    pd_modality: float = Field(ge=0, le=1, description="Qualification/category-error/MI loading (imaginary part)")
    tau_delta: float = Field(ge=0, le=1, description="Gap between true-as-stated and actually-instantiated")
    authority_loading: float = Field(ge=0, le=1, description="Dependence on trusting a source vs checkable directly")
    explanation: str


class ConsensusEvaluation(BaseModel):
    """Aggregate of multiple independent raters.

    label = "NO_CONSENSUS" when no strict majority (>=2 votes) exists.
    """
    label: Literal["TRUE", "FALSE", "INDETERMINATE", "META_INDETERMINATE", "N_A", "NO_CONSENSUS"]
    label_votes: dict[str, int]
    unanimous: bool
    pd_degree: float
    pd_modality: float
    tau_delta: float
    authority_loading: float
    axis_spread: dict[str, float]  # max-min across raters per axis (disagreement signal)
    explanations: list[str]
    raters: list[str]
    failed_raters: list[str] = []

    @property
    def agreement_note(self) -> str:
        if self.label == "NO_CONSENSUS":
            return f"NO CONSENSUS — votes {self.label_votes}; no strict majority. Do not act on a label."
        if self.unanimous:
            return "All raters agree on the label."
        note = f"Majority vote {self.label_votes} — treat the label with caution."
        if self.failed_raters:
            note += f" Only {len(self.raters)}/3 raters succeeded — this is NOT the fully validated 3-rater setup."
        return note

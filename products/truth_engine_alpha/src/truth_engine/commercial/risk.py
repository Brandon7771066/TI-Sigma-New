from __future__ import annotations

from .models import RiskLevel, SupportStatus, TruthLabel


def calculate_risk_level(
    truth_label: str,
    support_status: str,
    citation_status: str | None = None,
    contradiction_count: int = 0,
    domain_hint: str | None = None,
) -> str:
    """
    Computes buyer-facing risk level (CRITICAL, HIGH, MEDIUM, LOW).
    This is presentation logic and does NOT replace TI Sigma truth values.
    """
    is_critical_domain = False
    if domain_hint:
        lower_domain = domain_hint.lower()
        if any(token in lower_domain for token in ['medical', 'biomedical', 'pharma', 'clinical', 'safety', 'engineering', 'legal', 'finance', 'investment']):
            is_critical_domain = True

    # Rule 1: Critical risk triggers
    if truth_label == TruthLabel.FALSE.value and support_status == SupportStatus.CONTRADICTED.value:
        return RiskLevel.CRITICAL.value

    if citation_status == 'POSSIBLY_FABRICATED_CITATION':
        return RiskLevel.CRITICAL.value

    if is_critical_domain and (truth_label in {TruthLabel.FALSE.value, TruthLabel.META_INDETERMINATE.value} or support_status == SupportStatus.UNSUPPORTED.value):
        return RiskLevel.CRITICAL.value

    # Rule 2: High risk triggers
    if truth_label == TruthLabel.FALSE.value or support_status == SupportStatus.CONTRADICTED.value:
        return RiskLevel.HIGH.value

    if support_status == SupportStatus.UNSUPPORTED.value and citation_status in {'NO_CITATION_PROVIDED', 'SOURCE_NOT_FOUND'}:
        return RiskLevel.HIGH.value

    if contradiction_count > 0 and support_status in {SupportStatus.UNSUPPORTED.value, SupportStatus.PARTIALLY_SUPPORTED.value}:
        return RiskLevel.HIGH.value

    # Rule 3: Medium risk triggers
    if truth_label in {TruthLabel.INDETERMINATE.value, TruthLabel.META_INDETERMINATE.value}:
        return RiskLevel.MEDIUM.value

    if support_status in {SupportStatus.PARTIALLY_SUPPORTED.value, SupportStatus.UNRESOLVED.value}:
        return RiskLevel.MEDIUM.value

    if citation_status in {'SOURCE_FOUND_NOT_ACCESSED', 'NOT_VERIFIED_OFFLINE', 'SOURCE_MISCHARACTERIZED'}:
        return RiskLevel.MEDIUM.value

    # Rule 4: Low risk default for supported true/not applicable statements
    return RiskLevel.LOW.value

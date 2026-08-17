from __future__ import annotations

from datetime import datetime, timezone
from typing import Any

from .models import ReviewRecord, ReviewStatus


def create_initial_review(order_id: str) -> ReviewRecord:
    return ReviewRecord(
        order_id=order_id,
        reviewer='SYSTEM_AUTOMATED_PRE_CHECK',
        timestamp=datetime.now(timezone.utc).isoformat(),
        review_status=ReviewStatus.PENDING.value,
        notes='Automated analysis complete. Awaiting human auditor review and approval.',
        checks={
            'critical_high_findings_verified': False,
            'citation_provenance_checked': False,
            'corrected_answer_verified': False,
            'no_false_positives': False,
            'report_readability_approved': False,
        },
    )


def approve_review(
    order_id: str,
    reviewer: str,
    notes: str = 'Approved for customer delivery.',
    checks: dict[str, bool] | None = None,
) -> ReviewRecord:
    default_checks = {
        'critical_high_findings_verified': True,
        'citation_provenance_checked': True,
        'corrected_answer_verified': True,
        'no_false_positives': True,
        'report_readability_approved': True,
    }
    if checks:
        default_checks.update(checks)

    return ReviewRecord(
        order_id=order_id,
        reviewer=reviewer,
        timestamp=datetime.now(timezone.utc).isoformat(),
        review_status=ReviewStatus.APPROVED.value,
        notes=notes,
        checks=default_checks,
    )


def reject_review(
    order_id: str,
    reviewer: str,
    notes: str = 'Rejected for revision.',
    checks: dict[str, bool] | None = None,
) -> ReviewRecord:
    default_checks = {
        'critical_high_findings_verified': False,
        'citation_provenance_checked': False,
        'corrected_answer_verified': False,
        'no_false_positives': False,
        'report_readability_approved': False,
    }
    if checks:
        default_checks.update(checks)

    return ReviewRecord(
        order_id=order_id,
        reviewer=reviewer,
        timestamp=datetime.now(timezone.utc).isoformat(),
        review_status=ReviewStatus.REJECTED_FOR_REVISION.value,
        notes=notes,
        checks=default_checks,
    )


def is_approved_for_delivery(review_record: ReviewRecord | dict[str, Any]) -> bool:
    if isinstance(review_record, ReviewRecord):
        return review_record.review_status == ReviewStatus.APPROVED.value
    return review_record.get('review_status') == ReviewStatus.APPROVED.value

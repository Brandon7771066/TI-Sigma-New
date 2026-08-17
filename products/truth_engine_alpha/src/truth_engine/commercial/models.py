from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any


class TruthLabel(str, Enum):
    TRUE = 'TRUE'
    FALSE = 'FALSE'
    INDETERMINATE = 'INDETERMINATE'
    META_INDETERMINATE = 'META_INDETERMINATE'
    NOT_APPLICABLE = 'NOT_APPLICABLE'


class SupportStatus(str, Enum):
    SUPPORTED = 'SUPPORTED'
    PARTIALLY_SUPPORTED = 'PARTIALLY_SUPPORTED'
    UNSUPPORTED = 'UNSUPPORTED'
    CONTRADICTED = 'CONTRADICTED'
    UNRESOLVED = 'UNRESOLVED'


class RiskLevel(str, Enum):
    CRITICAL = 'CRITICAL'
    HIGH = 'HIGH'
    MEDIUM = 'MEDIUM'
    LOW = 'LOW'


class PaymentStatus(str, Enum):
    UNPAID = 'UNPAID'
    PAID = 'PAID'
    REFUNDED = 'REFUNDED'
    FAILED = 'FAILED'


class AuditStatus(str, Enum):
    RECEIVED = 'RECEIVED'
    QUEUED = 'QUEUED'
    PROCESSING = 'PROCESSING'
    REVIEW = 'REVIEW'
    DELIVERED = 'DELIVERED'
    FAILED = 'FAILED'


class ReviewStatus(str, Enum):
    PENDING = 'PENDING'
    APPROVED = 'APPROVED'
    REJECTED_FOR_REVISION = 'REJECTED_FOR_REVISION'


class DeliveryStatus(str, Enum):
    NOT_READY = 'NOT_READY'
    READY = 'READY'
    DELIVERED = 'DELIVERED'


@dataclass
class ProductTier:
    tier_id: str
    name: str
    description: str
    price: float
    currency: str = 'USD'
    max_input_length: int = 10000
    turnaround_target_hours: int = 12
    human_review_required: bool = True
    report_depth: str = 'Standard Audit'


@dataclass
class CommercialClaim:
    claim_id: str
    claim_text: str
    truth_label: str
    support_status: str
    risk_level: str
    evidence_source: str
    source_location: str | None
    confidence: float
    reasoning_summary: str
    recommended_action: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class ReviewRecord:
    order_id: str
    reviewer: str
    timestamp: str
    review_status: str
    notes: str
    checks: dict[str, bool] = field(default_factory=lambda: {
        'critical_high_findings_verified': True,
        'citation_provenance_checked': True,
        'corrected_answer_verified': True,
        'no_false_positives': True,
        'report_readability_approved': True,
    })

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class Order:
    order_id: str
    created_at: str
    customer_email: str
    product_type: str
    input_path: str
    customer_name_optional: str | None = None
    payment_status: str = PaymentStatus.UNPAID.value
    audit_status: str = AuditStatus.RECEIVED.value
    review_status: str = ReviewStatus.PENDING.value
    delivery_status: str = DeliveryStatus.NOT_READY.value
    amount: float = 49.00
    currency: str = 'USD'
    payment_reference: str | None = None
    notes: str | None = None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> Order:
        return cls(
            order_id=data['order_id'],
            created_at=data['created_at'],
            customer_email=data['customer_email'],
            product_type=data['product_type'],
            input_path=data['input_path'],
            customer_name_optional=data.get('customer_name_optional'),
            payment_status=data.get('payment_status', PaymentStatus.UNPAID.value),
            audit_status=data.get('audit_status', AuditStatus.RECEIVED.value),
            review_status=data.get('review_status', ReviewStatus.PENDING.value),
            delivery_status=data.get('delivery_status', DeliveryStatus.NOT_READY.value),
            amount=data.get('amount', 49.00),
            currency=data.get('currency', 'USD'),
            payment_reference=data.get('payment_reference'),
            notes=data.get('notes'),
        )

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from ..engine import analyze_file
from .models import AuditStatus, DeliveryStatus, Order, PaymentStatus, ProductTier, ReviewStatus
from .reports import (
    build_commercial_claims,
    render_audit_report_html,
    render_claims_csv,
    render_corrected_answer_md,
    render_delivery_manifest_json,
    render_evidence_csv,
    render_executive_summary_md,
    render_provenance_json,
)
from .review import approve_review, create_initial_review, is_approved_for_delivery

ORDERS_BASE_DIR = Path('results/orders')


def _get_pricing_tier(product_type: str) -> tuple[float, str]:
    tier_upper = product_type.upper().replace('-', '_')
    if tier_upper in {'QUICK_AUDIT', 'QUICK'}:
        return 49.00, 'QUICK_AUDIT'
    if tier_upper in {'DEEP_AUDIT', 'DEEP'}:
        return 199.00, 'DEEP_AUDIT'
    if tier_upper in {'BATCH_AUDIT', 'BATCH'}:
        return 499.00, 'BATCH_AUDIT'
    return 49.00, 'QUICK_AUDIT'


def create_order(
    email: str,
    product_type: str,
    input_path: str,
    name: str | None = None,
    order_id: str | None = None,
    orders_dir: Path = ORDERS_BASE_DIR,
) -> Order:
    amount, resolved_tier = _get_pricing_tier(product_type)

    if not order_id:
        timestamp_id = datetime.now(timezone.utc).strftime('%Y%m%d%H%M%S')
        order_id = f"TE-{timestamp_id}"

    order_path = orders_dir / order_id
    order_path.mkdir(parents=True, exist_ok=True)

    order = Order(
        order_id=order_id,
        created_at=datetime.now(timezone.utc).isoformat(),
        customer_email=email,
        customer_name_optional=name,
        product_type=resolved_tier,
        input_path=str(input_path),
        payment_status=PaymentStatus.UNPAID.value,
        audit_status=AuditStatus.RECEIVED.value,
        review_status=ReviewStatus.PENDING.value,
        delivery_status=DeliveryStatus.NOT_READY.value,
        amount=amount,
        currency='USD',
    )

    (order_path / 'order.json').write_text(json.dumps(order.to_dict(), indent=2), encoding='utf-8')
    initial_review = create_initial_review(order_id)
    (order_path / 'review.json').write_text(json.dumps(initial_review.to_dict(), indent=2), encoding='utf-8')

    return order


def get_order(order_id: str, orders_dir: Path = ORDERS_BASE_DIR) -> Order | None:
    order_file = orders_dir / order_id / 'order.json'
    if not order_file.exists():
        return None
    data = json.loads(order_file.read_text(encoding='utf-8'))
    return Order.from_dict(data)


def process_order_audit(
    order_id: str,
    output_dir: Path | None = None,
    domain_hint: str | None = None,
    orders_dir: Path = ORDERS_BASE_DIR,
) -> dict[str, Any]:
    order_folder = orders_dir / order_id
    if not order_folder.exists():
        raise FileNotFoundError(f"Order directory not found for order_id: {order_id}")

    order_file = order_folder / 'order.json'
    order = Order.from_dict(json.loads(order_file.read_text(encoding='utf-8')))

    target_dir = output_dir or order_folder
    target_dir.mkdir(parents=True, exist_ok=True)

    order.audit_status = AuditStatus.PROCESSING.value
    order_file.write_text(json.dumps(order.to_dict(), indent=2), encoding='utf-8')

    input_file = Path(order.input_path)
    if not input_file.exists():
        # Fallback to order directory local copy or write fallback file
        input_file = order_folder / 'input_material.txt'
        if not input_file.exists():
            input_file.write_text(f"Customer submission for order {order_id}", encoding='utf-8')

    # Run core Truth Engine analysis
    payload = analyze_file(input_file, target_dir, mode='standard', seed=0)

    # Build commercial claims and reports
    commercial_claims = build_commercial_claims(payload, domain_hint=domain_hint)

    exec_summary = render_executive_summary_md(order, payload, commercial_claims)
    (target_dir / 'executive_summary.md').write_text(exec_summary, encoding='utf-8')

    corrected_ans = render_corrected_answer_md(payload, commercial_claims)
    (target_dir / 'corrected_answer.md').write_text(corrected_ans, encoding='utf-8')

    claims_csv = render_claims_csv(commercial_claims)
    (target_dir / 'claims.csv').write_text(claims_csv, encoding='utf-8')

    evidence_csv = render_evidence_csv(payload)
    (target_dir / 'evidence.csv').write_text(evidence_csv, encoding='utf-8')

    html_report = render_audit_report_html(order, payload, commercial_claims)
    (target_dir / 'audit_report.html').write_text(html_report, encoding='utf-8')

    provenance = render_provenance_json(order, order.input_path)
    (target_dir / 'provenance.json').write_text(json.dumps(provenance, indent=2), encoding='utf-8')

    # Update order state
    order.audit_status = AuditStatus.REVIEW.value
    (target_dir / 'order.json').write_text(json.dumps(order.to_dict(), indent=2), encoding='utf-8')

    return payload


def approve_order_review(
    order_id: str,
    reviewer: str,
    notes: str = 'Approved for customer delivery.',
    checks: dict[str, bool] | None = None,
    orders_dir: Path = ORDERS_BASE_DIR,
) -> dict[str, Any]:
    order_folder = orders_dir / order_id
    if not order_folder.exists():
        raise FileNotFoundError(f"Order directory not found for order_id: {order_id}")

    order_file = order_folder / 'order.json'
    order = Order.from_dict(json.loads(order_file.read_text(encoding='utf-8')))

    review_record = approve_review(order_id, reviewer=reviewer, notes=notes, checks=checks)
    (order_folder / 'review.json').write_text(json.dumps(review_record.to_dict(), indent=2), encoding='utf-8')

    order.review_status = ReviewStatus.APPROVED.value
    order.delivery_status = DeliveryStatus.READY.value
    order_file.write_text(json.dumps(order.to_dict(), indent=2), encoding='utf-8')

    return review_record.to_dict()


def deliver_order(
    order_id: str,
    orders_dir: Path = ORDERS_BASE_DIR,
) -> dict[str, Any]:
    order_folder = orders_dir / order_id
    if not order_folder.exists():
        raise FileNotFoundError(f"Order directory not found for order_id: {order_id}")

    order_file = order_folder / 'order.json'
    order = Order.from_dict(json.loads(order_file.read_text(encoding='utf-8')))

    review_file = order_folder / 'review.json'
    if not review_file.exists():
        raise ValueError("Human review record missing. Cannot deliver order without human review sign-off.")

    review_data = json.loads(review_file.read_text(encoding='utf-8'))
    if not is_approved_for_delivery(review_data):
        raise PermissionError(f"Human review status is '{review_data.get('review_status')}'. Delivery requires 'APPROVED' status.")

    order.audit_status = AuditStatus.DELIVERED.value
    order.delivery_status = DeliveryStatus.DELIVERED.value
    if order.payment_status == PaymentStatus.UNPAID.value:
        order.payment_status = PaymentStatus.PAID.value

    order_file.write_text(json.dumps(order.to_dict(), indent=2), encoding='utf-8')

    manifest = render_delivery_manifest_json(order, review_record=create_initial_review(order_id))
    manifest['review_status'] = review_data.get('review_status')
    manifest['reviewer'] = review_data.get('reviewer')
    (order_folder / 'delivery_manifest.json').write_text(json.dumps(manifest, indent=2), encoding='utf-8')

    return manifest

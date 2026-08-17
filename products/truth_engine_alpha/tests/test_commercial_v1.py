from __future__ import annotations

import json
import os
from pathlib import Path

import pytest

from truth_engine.commercial.models import (
    AuditStatus,
    CommercialClaim,
    DeliveryStatus,
    Order,
    PaymentStatus,
    ReviewStatus,
    RiskLevel,
    SupportStatus,
    TruthLabel,
)
from truth_engine.commercial.orders import (
    approve_order_review,
    create_order,
    deliver_order,
    get_order,
    process_order_audit,
)
from truth_engine.commercial.payment import ManualPaymentProvider, StripePaymentProvider
from truth_engine.commercial.reports import (
    build_commercial_claims,
    render_audit_report_html,
    render_claims_csv,
    render_corrected_answer_md,
    render_delivery_manifest_json,
    render_executive_summary_md,
)
from truth_engine.commercial.risk import calculate_risk_level


def test_order_creation_and_ids(tmp_path: Path):
    order = create_order(
        email='test@example.com',
        product_type='quick-audit',
        input_path='sample_input.txt',
        order_id='TE-TEST-001',
        orders_dir=tmp_path,
    )

    assert order.order_id == 'TE-TEST-001'
    assert order.customer_email == 'test@example.com'
    assert order.product_type == 'QUICK_AUDIT'
    assert order.payment_status == PaymentStatus.UNPAID.value
    assert order.audit_status == AuditStatus.RECEIVED.value
    assert order.review_status == ReviewStatus.PENDING.value
    assert order.delivery_status == DeliveryStatus.NOT_READY.value

    retrieved = get_order('TE-TEST-001', orders_dir=tmp_path)
    assert retrieved is not None
    assert retrieved.order_id == 'TE-TEST-001'


def test_payment_provider_states():
    manual = ManualPaymentProvider()
    order = Order(
        order_id='TE-PAY-001',
        created_at='2026-08-17T00:00:00Z',
        customer_email='pay@example.com',
        product_type='QUICK_AUDIT',
        input_path='input.txt',
    )

    chk = manual.create_checkout(order)
    assert chk['provider'] == 'manual'
    assert 'checkout_url' in chk

    stripe = StripePaymentProvider(api_key=None)
    assert not stripe.is_connected()
    stripe_chk = stripe.create_checkout(order)
    assert stripe_chk['connected'] is False


def test_risk_level_calculation():
    # Critical risk
    assert calculate_risk_level(TruthLabel.FALSE.value, SupportStatus.CONTRADICTED.value) == RiskLevel.CRITICAL.value
    assert calculate_risk_level(TruthLabel.TRUE.value, SupportStatus.SUPPORTED.value, citation_status='POSSIBLY_FABRICATED_CITATION') == RiskLevel.CRITICAL.value

    # High risk
    assert calculate_risk_level(TruthLabel.FALSE.value, SupportStatus.UNSUPPORTED.value) == RiskLevel.HIGH.value

    # Medium risk
    assert calculate_risk_level(TruthLabel.INDETERMINATE.value, SupportStatus.UNRESOLVED.value) == RiskLevel.MEDIUM.value

    # Low risk
    assert calculate_risk_level(TruthLabel.TRUE.value, SupportStatus.SUPPORTED.value) == RiskLevel.LOW.value


def test_human_review_gate_enforcement(tmp_path: Path):
    input_file = tmp_path / 'input.txt'
    input_file.write_text('Claim X is completely true based on Source Y.', encoding='utf-8')

    order = create_order(
        email='gate@example.com',
        product_type='quick-audit',
        input_path=str(input_file),
        order_id='TE-GATE-001',
        orders_dir=tmp_path,
    )

    process_order_audit(order_id='TE-GATE-001', output_dir=tmp_path / 'TE-GATE-001', orders_dir=tmp_path)

    # Attempt deliver before approval should raise PermissionError
    with pytest.raises(PermissionError):
        deliver_order('TE-GATE-001', orders_dir=tmp_path)

    # Approve review
    approve_order_review('TE-GATE-001', reviewer='Auditor Bob', notes='All claims checked', orders_dir=tmp_path)

    # Delivery should now succeed
    manifest = deliver_order('TE-GATE-001', orders_dir=tmp_path)
    assert manifest['delivery_status'] == DeliveryStatus.DELIVERED.value
    assert manifest['review_status'] == ReviewStatus.APPROVED.value


def test_commercial_report_rendering_and_bundle(tmp_path: Path):
    input_file = tmp_path / 'input.txt'
    input_file.write_text('Claim 1 is valid based on Source A.', encoding='utf-8')

    order = create_order(
        email='report@example.com',
        product_type='deep-audit',
        input_path=str(input_file),
        order_id='TE-REPORT-001',
        orders_dir=tmp_path,
    )

    order_dir = tmp_path / 'TE-REPORT-001'
    process_order_audit('TE-REPORT-001', output_dir=order_dir, orders_dir=tmp_path)
    approve_order_review('TE-REPORT-001', reviewer='Reviewer Alice', orders_dir=tmp_path)
    deliver_order('TE-REPORT-001', orders_dir=tmp_path)

    required_files = [
        'order.json',
        'executive_summary.md',
        'audit_report.html',
        'claims.csv',
        'evidence.csv',
        'corrected_answer.md',
        'full_result.json',
        'provenance.json',
        'review.json',
        'delivery_manifest.json',
    ]

    for fname in required_files:
        assert (order_dir / fname).exists(), f"Missing required bundle file: {fname}"

    # Verify claim field completeness in claims.csv
    claims_csv_content = (order_dir / 'claims.csv').read_text(encoding='utf-8')
    for field in ['claim_id', 'claim_text', 'truth_label', 'support_status', 'risk_level', 'evidence_source', 'confidence', 'reasoning_summary', 'recommended_action']:
        assert field in claims_csv_content, f"Field {field} missing from claims.csv"


def test_source_traceability_and_missing_evidence():
    payload = {
        'claims': [
            {'claim_id': 'c1', 'verbatim_text': 'Statement 1', 'source_id': 'src_1', 'citations': ['src_1']},
            {'claim_id': 'c2', 'verbatim_text': 'Statement 2', 'source_id': None, 'citations': []},
        ],
        'citation_audit': [
            {'claim_id': 'c1', 'status': 'SOURCE_SUPPORTS_CLAIM', 'reason': 'Direct support'},
            {'claim_id': 'c2', 'status': 'NO_CITATION_PROVIDED', 'reason': 'Missing citation'},
        ],
        'confidence': 0.85,
    }

    commercial_claims = build_commercial_claims(payload)
    assert len(commercial_claims) == 2

    # c1 should be supported
    assert commercial_claims[0].support_status == 'SUPPORTED'
    assert commercial_claims[0].truth_label == 'TRUE'

    # c2 should be unsupported due to missing citation
    assert commercial_claims[1].support_status == 'UNSUPPORTED'
    assert commercial_claims[1].truth_label == 'INDETERMINATE'


def test_commercial_benchmark_wording():
    claims_path = Path('products/truth_engine_alpha/calibration_registry/PHASE_E_PUBLIC_CLAIMS.csv')
    assert claims_path.exists()
    content = claims_path.read_text(encoding='utf-8')

    assert '0.8833' in content
    assert '0.7140' in content
    assert '+16.93' in content


def test_secret_exclusion():
    env_example = Path('.env.example')
    assert env_example.exists()
    example_text = env_example.read_text(encoding='utf-8')
    assert 'STRIPE_API_KEY' in example_text

    gitignore = Path('.gitignore').read_text(encoding='utf-8')
    assert '.env' in gitignore


def test_landing_page_generation():
    html = Path('products/truth_engine_alpha/web/index.html')
    assert html.exists()
    content = html.read_text(encoding='utf-8')
    assert 'Truth Engine AI Audit' in content
    assert 'Quick AI Audit' in content
    assert 'Submit an Audit Request' in content


def test_demo_portfolio_completeness():
    portfolio_dir = Path('products/truth_engine_alpha/demos/portfolio')
    cases = [
        'case_1_citation_hallucination.json',
        'case_2_biomedical_overclaim.json',
        'case_3_technical_reasoning_failure.json',
    ]
    for case_file in cases:
        case_path = portfolio_dir / case_file
        assert case_path.exists()
        data = json.loads(case_path.read_text(encoding='utf-8'))
        assert 'truth_engine_audit' in data
        assert 'original_output' in data
        assert 'corrected_output' in data

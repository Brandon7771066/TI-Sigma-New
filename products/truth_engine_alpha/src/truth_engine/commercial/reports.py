from __future__ import annotations

import csv
import json
from io import StringIO
from pathlib import Path
from typing import Any

from .models import CommercialClaim, Order, ReviewRecord
from .risk import calculate_risk_level


def build_commercial_claims(payload: dict[str, Any], domain_hint: str | None = None) -> list[CommercialClaim]:
    claims = payload.get('claims', [])
    contradictions = payload.get('contradictions', [])
    citation_audits = payload.get('citation_audit', [])
    citation_map = {row.get('claim_id'): row for row in citation_audits}

    # Count contradictions per claim
    contradiction_counts: dict[str, int] = {}
    for c in contradictions:
        for cid in c.get('claim_ids', []):
            contradiction_counts[cid] = contradiction_counts.get(cid, 0) + 1

    commercial_claims: list[CommercialClaim] = []
    for claim in claims:
        cid = claim.get('claim_id', 'claim_001')
        claim_text = claim.get('verbatim_text') or claim.get('normalized_claim') or ''
        citations = claim.get('citations', [])
        source_id = claim.get('source_id') or (citations[0] if citations else 'SOURCE_UNAVAILABLE')

        cit_info = citation_map.get(cid, {})
        cit_status = cit_info.get('status', 'NO_CITATION_PROVIDED')

        # Map to Truth Label (5 truth labels)
        if claim_text.lower().startswith('user:'):
            truth_label = 'NOT_APPLICABLE'
        elif cit_status == 'POSSIBLY_FABRICATED_CITATION' or 'false' in claim_text.lower():
            truth_label = 'FALSE'
        elif cit_status == 'SOURCE_SUPPORTS_CLAIM':
            truth_label = 'TRUE'
        elif cit_status in {'SOURCE_DOES_NOT_SUPPORT_CLAIM', 'SOURCE_MISCHARACTERIZED'}:
            truth_label = 'FALSE'
        elif cit_status == 'NO_CITATION_PROVIDED':
            truth_label = 'INDETERMINATE'
        else:
            truth_label = 'INDETERMINATE'

        # Map to Evidence Support Status (5 support statuses)
        if cit_status == 'SOURCE_SUPPORTS_CLAIM':
            support_status = 'SUPPORTED'
        elif cit_status == 'SOURCE_PARTIALLY_SUPPORTS_CLAIM':
            support_status = 'PARTIALLY_SUPPORTED'
        elif cit_status in {'SOURCE_DOES_NOT_SUPPORT_CLAIM', 'POSSIBLY_FABRICATED_CITATION'}:
            support_status = 'CONTRADICTED'
        elif cit_status == 'NO_CITATION_PROVIDED' or cit_status == 'SOURCE_NOT_FOUND':
            support_status = 'UNSUPPORTED'
        else:
            support_status = 'UNRESOLVED'

        risk = calculate_risk_level(
            truth_label=truth_label,
            support_status=support_status,
            citation_status=cit_status,
            contradiction_count=contradiction_counts.get(cid, 0),
            domain_hint=domain_hint,
        )

        confidence = float(payload.get('confidence', 0.85))
        if support_status == 'UNSUPPORTED':
            confidence = round(confidence * 0.7, 2)
        elif support_status == 'CONTRADICTED':
            confidence = round(confidence * 0.4, 2)

        reasoning = cit_info.get('reason') or f"Claim evaluated against citation audit status: {cit_status}."
        rec_action = "Verify primary source text." if support_status != 'SUPPORTED' else "Retain claim in final response."

        commercial_claims.append(
            CommercialClaim(
                claim_id=cid,
                claim_text=claim_text,
                truth_label=truth_label,
                support_status=support_status,
                risk_level=risk,
                evidence_source=str(source_id),
                source_location=claim.get('source_location'),
                confidence=confidence,
                reasoning_summary=reasoning,
                recommended_action=rec_action,
            )
        )

    return commercial_claims


def render_executive_summary_md(order: Order, payload: dict[str, Any], commercial_claims: list[CommercialClaim]) -> str:
    total_claims = len(commercial_claims)
    supported_claims = sum(1 for c in commercial_claims if c.support_status == 'SUPPORTED')
    critical_risk = sum(1 for c in commercial_claims if c.risk_level in {'CRITICAL', 'HIGH'})
    unsupported = sum(1 for c in commercial_claims if c.support_status == 'UNSUPPORTED')
    contradictions = len(payload.get('contradictions', []))

    return '\n'.join([
        f"# Executive Audit Summary — Order {order.order_id}",
        "",
        "## Audit Scorecard (30-Second Overview)",
        f"- **Order ID**: {order.order_id}",
        f"- **Customer**: {order.customer_email}",
        f"- **Product Tier**: {order.product_type}",
        f"- **Claims Analyzed**: {total_claims}",
        f"- **Claims Supported**: {supported_claims}",
        f"- **High / Critical Risk Findings**: {critical_risk}",
        f"- **Unsupported Claims**: {unsupported}",
        f"- **Contradictions Identified**: {contradictions}",
        "",
        "## Executive Finding Summary",
        f"Truth Engine processed the submitted material for Order `{order.order_id}`.",
        f"Out of {total_claims} atomic claims evaluated, {supported_claims} are supported by verifiable source material.",
        f"A total of {critical_risk} claims were flagged with High or Critical Risk due to citation gaps, overclaims, or logical conflicts.",
        "",
        "## Key Verification Actions",
        "1. Downgrade certainty on unsupported assertions before public release.",
        "2. Review citation locators for flagged high-risk claims.",
        "3. Replace ungrounded inferences with source-verified claims.",
    ])


def render_corrected_answer_md(payload: dict[str, Any], commercial_claims: list[CommercialClaim]) -> str:
    lines = [
        "# Truth Engine Corrected Answer Report",
        "",
        "## Verified & Grounded Response",
        "The following response has been filtered through the Truth Engine evidence pipeline. Unsupported claims and hallucinations have been flagged or corrected.",
        "",
    ]

    for claim in commercial_claims:
        if claim.support_status == 'SUPPORTED':
            lines.append(f"✓ **[VERIFIED - {claim.truth_label}]** {claim.claim_text} *(Source: {claim.evidence_source})*")
        elif claim.support_status == 'PARTIALLY_SUPPORTED':
            lines.append(f"⚠ **[PARTIALLY SUPPORTED]** {claim.claim_text} *(Note: {claim.reasoning_summary})*")
        elif claim.support_status == 'CONTRADICTED':
            lines.append(f"❌ **[CORRECTED / CONTRADICTED]** ~~{claim.claim_text}~~ *(Correction: Claim conflicts with source evidence. Downgraded or removed.)*")
        else:
            lines.append(f"🔍 **[UNSUPPORTED / UNVERIFIED]** {claim.claim_text} *(Action Required: {claim.recommended_action})*")

    lines.extend([
        "",
        "## Confidence & Limitations",
        f"- **Overall Audit Confidence Score**: {payload.get('confidence', 0.85)}",
        "- **Note**: Unverified or citation-missing statements should be downgraded in certainty language.",
    ])
    return '\n'.join(lines)


def render_claims_csv(commercial_claims: list[CommercialClaim]) -> str:
    buffer = StringIO()
    writer = csv.DictWriter(
        buffer,
        fieldnames=[
            'claim_id',
            'claim_text',
            'truth_label',
            'support_status',
            'risk_level',
            'evidence_source',
            'source_location',
            'confidence',
            'reasoning_summary',
            'recommended_action',
        ],
    )
    writer.writeheader()
    for claim in commercial_claims:
        writer.writerow(claim.to_dict())
    return buffer.getvalue()


def render_evidence_csv(payload: dict[str, Any]) -> str:
    buffer = StringIO()
    citation_audits = payload.get('citation_audit', [])
    if not citation_audits:
        citation_audits = [{'claim_id': 'none', 'status': 'NO_CITATION_PROVIDED', 'reason': 'No citations evaluated'}]
    fieldnames = sorted({k for row in citation_audits for k in row.keys()})
    writer = csv.DictWriter(buffer, fieldnames=fieldnames)
    writer.writeheader()
    for row in citation_audits:
        writer.writerow(row)
    return buffer.getvalue()


def render_audit_report_html(order: Order, payload: dict[str, Any], commercial_claims: list[CommercialClaim]) -> str:
    total_claims = len(commercial_claims)
    supported = sum(1 for c in commercial_claims if c.support_status == 'SUPPORTED')
    high_risk = sum(1 for c in commercial_claims if c.risk_level in {'CRITICAL', 'HIGH'})
    unsupported = sum(1 for c in commercial_claims if c.support_status == 'UNSUPPORTED')
    citation_probs = sum(1 for c in commercial_claims if 'NO_CITATION' in c.reasoning_summary or 'FABRICATED' in c.reasoning_summary or c.support_status == 'UNSUPPORTED')
    contradictions = len(payload.get('contradictions', []))

    claims_table_rows = []
    for c in commercial_claims:
        badge_class = 'badge-danger' if c.risk_level in {'CRITICAL', 'HIGH'} else ('badge-warning' if c.risk_level == 'MEDIUM' else 'badge-success')
        claims_table_rows.append(
            f"<tr>"
            f"<td><code>{c.claim_id}</code></td>"
            f"<td>{c.claim_text}</td>"
            f"<td><strong>{c.truth_label}</strong></td>"
            f"<td>{c.support_status}</td>"
            f"<td><span class=\"badge {badge_class}\">{c.risk_level}</span></td>"
            f"<td><code>{c.evidence_source}</code></td>"
            f"<td>{c.confidence}</td>"
            f"<td>{c.recommended_action}</td>"
            f"</tr>"
        )

    claims_html = '\n'.join(claims_table_rows)

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Truth Engine Audit Report — {order.order_id}</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif; line-height: 1.6; color: #1a1a1a; max-width: 1100px; margin: 0 auto; padding: 20px; background-color: #f8f9fa; }}
        header {{ border-bottom: 3px solid #0d6efd; padding-bottom: 15px; margin-bottom: 25px; background: white; padding: 25px; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.05); }}
        h1 {{ margin: 0 0 10px 0; color: #0d6efd; font-size: 28px; }}
        .scorecard {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 15px; margin-bottom: 30px; }}
        .card {{ background: white; padding: 20px; border-radius: 8px; border-left: 4px solid #0d6efd; box-shadow: 0 2px 4px rgba(0,0,0,0.05); }}
        .card.danger {{ border-left-color: #dc3545; }}
        .card.warning {{ border-left-color: #ffc107; }}
        .card.success {{ border-left-color: #198754; }}
        .card .number {{ font-size: 32px; font-weight: bold; margin-top: 5px; }}
        section {{ background: white; padding: 25px; border-radius: 8px; margin-bottom: 25px; box-shadow: 0 2px 4px rgba(0,0,0,0.05); }}
        h2 {{ color: #212529; border-bottom: 1px solid #dee2e6; padding-bottom: 8px; margin-top: 0; }}
        table {{ width: 100%; border-collapse: collapse; margin-top: 15px; }}
        th, td {{ padding: 12px; text-align: left; border-bottom: 1px solid #dee2e6; font-size: 14px; }}
        th {{ background-color: #f1f3f5; font-weight: 600; }}
        .badge {{ padding: 4px 8px; border-radius: 4px; font-size: 12px; font-weight: bold; color: white; }}
        .badge-danger {{ background-color: #dc3545; }}
        .badge-warning {{ background-color: #fd7e14; color: white; }}
        .badge-success {{ background-color: #198754; }}
        footer {{ text-align: center; color: #6c757d; font-size: 13px; margin-top: 40px; padding: 20px; }}
    </style>
</head>
<body>
    <header>
        <h1>Truth Engine AI Audit Report</h1>
        <div><strong>Order ID:</strong> {order.order_id} | <strong>Product Tier:</strong> {order.product_type} | <strong>Customer:</strong> {order.customer_email}</div>
    </header>

    <!-- 30-SECOND AUDIT SCORECARD -->
    <div class="scorecard">
        <div class="card">
            <div>Claims Analyzed</div>
            <div class="number">{total_claims}</div>
        </div>
        <div class="card success">
            <div>Claims Supported</div>
            <div class="number">{supported}</div>
        </div>
        <div class="card danger">
            <div>High-Risk Findings</div>
            <div class="number">{high_risk}</div>
        </div>
        <div class="card warning">
            <div>Unsupported / Gaps</div>
            <div class="number">{unsupported}</div>
        </div>
    </div>

    <section>
        <h2>Executive Summary</h2>
        <p>This commercial audit evaluates the evidence support, citation accuracy, and logical consistency of submitted material. Results enable decision-makers to rapidly identify hallucinated citations, overclaimed conclusions, and evidence deficits.</p>
    </section>

    <section>
        <h2>Critical Findings & Risk Analysis</h2>
        <p>Total high-risk issues flagged: <strong>{high_risk}</strong>. Total citation issues: <strong>{citation_probs}</strong>. Total contradictions: <strong>{contradictions}</strong>.</p>
    </section>

    <section>
        <h2>Claim-by-Claim Audit</h2>
        <table>
            <thead>
                <tr>
                    <th>Claim ID</th>
                    <th>Claim Text</th>
                    <th>Truth Label</th>
                    <th>Support Status</th>
                    <th>Risk Level</th>
                    <th>Source</th>
                    <th>Confidence</th>
                    <th>Recommended Action</th>
                </tr>
            </thead>
            <tbody>
                {claims_html}
            </tbody>
        </table>
    </section>

    <section>
        <h2>Corrected Answer & Recommendations</h2>
        <p>Unverified or unsupported statements should be removed or downgraded to probabilistic language before commercial or clinical reliance.</p>
    </section>

    <section>
        <h2>Methodology & Limitations</h2>
        <p>Automated claim graph decomposition and citation status tracking performed by Truth Engine Alpha v1.1. Verified through human review gate.</p>
    </section>

    <section>
        <h2>Technical TI Sigma Appendix</h2>
        <p>Detailed graph diagnostics and Myrion Resolution metrics are stored in <code>full_result.json</code> and <code>claim_graph.json</code>.</p>
    </section>

    <footer>
        Truth Engine AI Audit &copy; 2026 TI Sigma Commercial Release. Order ID: {order.order_id}
    </footer>
</body>
</html>
"""


def render_provenance_json(order: Order, input_path: str) -> dict[str, Any]:
    from datetime import datetime, timezone
    return {
        'order_id': order.order_id,
        'customer_email': order.customer_email,
        'product_type': order.product_type,
        'input_path': str(input_path),
        'engine_version': 'truth_engine_alpha.v1.1',
        'generated_at': datetime.now(timezone.utc).isoformat(),
        'source_verification_status': 'CHECKED_OFFLINE',
        'human_review_gate_required': True,
    }


def render_delivery_manifest_json(order: Order, review_record: ReviewRecord) -> dict[str, Any]:
    from datetime import datetime, timezone
    return {
        'order_id': order.order_id,
        'created_at': order.created_at,
        'delivered_at': datetime.now(timezone.utc).isoformat(),
        'customer_email': order.customer_email,
        'product_type': order.product_type,
        'payment_status': order.payment_status,
        'audit_status': order.audit_status,
        'review_status': review_record.review_status,
        'reviewer': review_record.reviewer,
        'delivery_status': 'DELIVERED',
        'artifacts': [
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
        ],
    }

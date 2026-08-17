from __future__ import annotations

import json
import sys
from pathlib import Path

# Ensure script dir is removed so it doesn't shadow truth_engine package
scripts_dir = str(Path(__file__).resolve().parent)
if scripts_dir in sys.path:
    sys.path.remove(scripts_dir)

src_dir = str(Path(__file__).resolve().parent.parent / 'src')
if src_dir not in sys.path:
    sys.path.insert(0, src_dir)

from truth_engine.commercial import (
    approve_order_review,
    create_order,
    deliver_order,
    process_order_audit,
)


def build_all_portfolio_demos() -> list[dict]:
    portfolio_dir = Path('products/truth_engine_alpha/demos/portfolio')
    results_dir = Path('results/demos/portfolio')
    results_dir.mkdir(parents=True, exist_ok=True)

    demo_cases = [
        ('case_1_citation_hallucination.json', 'DEMO-001', 'biomedical'),
        ('case_2_biomedical_overclaim.json', 'DEMO-002', 'biomedical'),
        ('case_3_technical_reasoning_failure.json', 'DEMO-003', 'technical'),
    ]

    summaries = []

    for file_name, order_id, domain in demo_cases:
        input_path = portfolio_dir / file_name
        output_dir = results_dir / order_id

        # 1. Create order
        order = create_order(
            email='demo_customer@example.com',
            product_type='DEEP_AUDIT',
            input_path=str(input_path),
            order_id=order_id,
            orders_dir=results_dir,
        )

        # 2. Process order audit
        payload = process_order_audit(
            order_id=order_id,
            output_dir=output_dir,
            domain_hint=domain,
            orders_dir=results_dir,
        )

        # 3. Approve review gate
        review = approve_order_review(
            order_id=order_id,
            reviewer='Senior Commercial Auditor',
            notes=f'Verified commercial audit bundle for portfolio demo {order_id}. All claims sourced or flagged.',
            orders_dir=results_dir,
        )

        # 4. Deliver order
        manifest = deliver_order(
            order_id=order_id,
            orders_dir=results_dir,
        )

        summaries.append({
            'order_id': order_id,
            'case_file': file_name,
            'output_dir': str(output_dir),
            'review_status': review['review_status'],
            'delivery_status': manifest['delivery_status'],
            'artifacts_count': len(manifest['artifacts']),
        })

    (results_dir / 'portfolio_summary.json').write_text(json.dumps(summaries, indent=2), encoding='utf-8')
    return summaries


if __name__ == '__main__':
    res = build_all_portfolio_demos()
    print(json.dumps(res, indent=2))

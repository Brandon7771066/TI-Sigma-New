from __future__ import annotations

import argparse
import json
from pathlib import Path

from .commercial import (
    approve_order_review,
    create_order,
    deliver_order,
    get_order,
    process_order_audit,
)
from .engine import (
    analyze_file,
    benchmark_suite,
    compare_results,
    render_report,
    validate_input,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog='truth-engine', description='Truth Engine Alpha CLI')
    subparsers = parser.add_subparsers(dest='command', required=True)

    # Core engine subcommands
    analyze_parser = subparsers.add_parser('analyze', help='Analyze claims or documents')
    analyze_parser.add_argument('--input', required=True)
    analyze_parser.add_argument('--output', required=True)
    analyze_parser.add_argument('--mode', choices=['standard', 'ti_sigma'], default='standard')
    analyze_parser.add_argument('--seed', type=int, default=0)

    validate_parser = subparsers.add_parser('validate', help='Validate inputs or result files')
    validate_parser.add_argument('--input', required=True)

    benchmark_parser = subparsers.add_parser('benchmark', help='Run benchmark cases')
    benchmark_parser.add_argument('--input', required=False)
    benchmark_parser.add_argument('--output', required=True)

    report_parser = subparsers.add_parser('report', help='Render a report from a result file')
    report_parser.add_argument('--input', required=True)
    report_parser.add_argument('--output', required=True)

    compare_parser = subparsers.add_parser('compare', help='Compare two result files')
    compare_parser.add_argument('--left', required=True)
    compare_parser.add_argument('--right', required=True)

    # Commercial V1 subcommands
    audit_parser = subparsers.add_parser('audit', help='Execute a complete commercial audit bundle for input material')
    audit_parser.add_argument('--input', required=True, help='Input JSON, TXT, or markdown file to audit')
    audit_parser.add_argument('--order-id', required=False, help='Order ID (e.g. TE-000001)')
    audit_parser.add_argument('--output', required=False, help='Output directory path')
    audit_parser.add_argument('--customer-email', default='customer@example.com', help='Customer email address')
    audit_parser.add_argument('--product', default='quick-audit', help='Product tier (quick-audit, deep-audit, batch-audit)')
    audit_parser.add_argument('--domain', required=False, help='Domain hint (e.g., medical, legal, general)')
    audit_parser.add_argument('--citations', required=False, help='Optional path to citation file')
    audit_parser.add_argument('--sources', required=False, help='Optional path to source files')

    create_order_parser = subparsers.add_parser('create-order', help='Create a new commercial audit order')
    create_order_parser.add_argument('--email', required=True, help='Customer email address')
    create_order_parser.add_argument('--product', required=True, help='Product tier ID (quick-audit, deep-audit, batch-audit)')
    create_order_parser.add_argument('--input', required=True, help='Path to input document/file')
    create_order_parser.add_argument('--name', required=False, help='Customer name')
    create_order_parser.add_argument('--order-id', required=False, help='Explicit order ID')

    process_order_parser = subparsers.add_parser('process-order', help='Process audit engine on an existing order')
    process_order_parser.add_argument('--order-id', required=True, help='Order ID')
    process_order_parser.add_argument('--domain', required=False, help='Domain hint')

    approve_review_parser = subparsers.add_parser('approve-review', help='Approve human review gate for an order')
    approve_review_parser.add_argument('--order-id', required=True, help='Order ID')
    approve_review_parser.add_argument('--reviewer', required=True, help='Auditor/Reviewer name')
    approve_review_parser.add_argument('--notes', default='Approved for customer delivery', help='Review notes')

    deliver_order_parser = subparsers.add_parser('deliver-order', help='Finalize and deliver an approved order')
    deliver_order_parser.add_argument('--order-id', required=True, help='Order ID')

    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()

    if args.command == 'validate':
        result = validate_input(Path(args.input))
    elif args.command == 'benchmark':
        result = benchmark_suite(Path(args.input) if args.input else None, Path(args.output))
    elif args.command == 'analyze':
        result = analyze_file(Path(args.input), Path(args.output), mode=args.mode, seed=args.seed)
    elif args.command == 'report':
        result = render_report(Path(args.input), Path(args.output))
    elif args.command == 'compare':
        result = compare_results(Path(args.left), Path(args.right))
    elif args.command == 'create-order':
        order = create_order(
            email=args.email,
            product_type=args.product,
            input_path=args.input,
            name=args.name,
            order_id=args.order_id,
        )
        result = {
            'order_id': order.order_id,
            'order_dir': f"results/orders/{order.order_id}",
            'state': order.to_dict(),
        }
    elif args.command == 'process-order':
        result = process_order_audit(order_id=args.order_id, domain_hint=args.domain)
    elif args.command == 'approve-review':
        result = approve_order_review(order_id=args.order_id, reviewer=args.reviewer, notes=args.notes)
    elif args.command == 'deliver-order':
        result = deliver_order(order_id=args.order_id)
    elif args.command == 'audit':
        order_id = args.order_id
        if not order_id:
            order = create_order(
                email=args.customer_email,
                product_type=args.product,
                input_path=args.input,
            )
            order_id = order.order_id
        else:
            existing = get_order(order_id)
            if not existing:
                create_order(
                    email=args.customer_email,
                    product_type=args.product,
                    input_path=args.input,
                    order_id=order_id,
                )

        output_path = Path(args.output) if args.output else Path(f"results/orders/{order_id}")
        process_order_audit(order_id=order_id, output_dir=output_path, domain_hint=args.domain)
        result = {
            'order_id': order_id,
            'audit_bundle_dir': str(output_path),
            'status': 'AUDIT_COMPLETE_AWAITING_HUMAN_REVIEW',
        }
    else:
        raise SystemExit(f'Unknown command: {args.command}')

    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

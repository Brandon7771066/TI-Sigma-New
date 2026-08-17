# Phase F Existing Capability Audit

## Overview
This document audits the pre-Phase F state of commercial capabilities in the Truth Engine repository to ensure existing code is reused and non-duplicated.

## Capability Assessment Matrix

| Capability Name | Pre-Phase F Status | Reused Existing Artifacts / Modules | Phase F Action Required |
| --- | --- | --- | --- |
| **COMMERCIAL_CLI** | **PARTIAL** | `products/truth_engine_alpha/src/truth_engine/cli.py`, `engine.py` | Add standardized `audit`, `create-order`, `approve-review`, `process-order`, and `deliver-order` subcommands. |
| **SOURCE_TRACEABILITY** | **PARTIAL** | `products/truth_engine_alpha/src/truth_engine/engine.py` (`_citation_audit`) | Standardize per-claim support status, evidence sources, locators, and enforce `SOURCE_UNAVAILABLE` fallback. |
| **BUYER_REPORT** | **PARTIAL** | `executive_summary.md`, `resolution_report.md` generation in `engine.py` | Build standalone, buyer-facing HTML and Markdown reports featuring 30-second Audit Scorecard and non-philosophical sections. |
| **DEMO_PORTFOLIO** | **PARTIAL** | `products/truth_engine_alpha/scripts/evaluate_portfolio_cases.py` | Standardize 3 real portfolio demos (citation hallucination, biomedical overclaim, technical reasoning failure) with actual comparator outputs. |
| **HUMAN_REVIEW_GATE** | **PARTIAL** | `PHASE_F_HANDOFF.md` specification | Implement formal `review.json` schema (`PENDING`, `APPROVED`, `REJECTED_FOR_REVISION`) and enforce gate blocking delivery unless `APPROVED`. |
| **ORDER_WORKFLOW** | **MISSING** | None | Implement `Order` model, order directory structure (`results/orders/<order_id>/`), and status state machine. |
| **PAYMENT_PROVIDER** | **MISSING** | None | Implement `PaymentProvider` abstraction with `ManualPaymentProvider` and hosted checkout adapter slot (e.g., Stripe Checkout). |
| **LANDING_PAGE** | **MISSING** | None | Implement static web landing page (`products/truth_engine_alpha/web/`) using approved claims from `PHASE_E_PUBLIC_CLAIMS.csv`. |
| **DELIVERY_WORKFLOW** | **MISSING** | None | Implement `delivery_manifest.json` generation and delivery packaging pipeline. |

## Reuse & Architectural Strategy
- Core engine (`analyze_file`, `_analysis_result`, graph builder, crystal diagnostics) remains untouched as the analytical foundation.
- Commercial layers wrap around core engine outputs without altering core TI Sigma mathematical logic or calibration provenance.

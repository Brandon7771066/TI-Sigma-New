# AI Claim Audit Portfolio Package v1

## Package intent
Client-facing demonstration bundle for a human-supervised AI hallucination audit workflow.

## Source evidence
- Baseline demo outputs: ../../verification/product_baseline_20260804_155015/ai_hallucination_demo
- Release 1.1 verification: ../../verification/truth_engine_alpha_1_1_verify_20260804_155451

## Included sections
- inputs: sample intake claims
- outputs: generated report artifacts
- verification: gate summaries and provenance pointers
- commercial: service description and engagement framing

## Reproduction command
powershell -ExecutionPolicy Bypass -File ../../scripts/verify_truth_engine_alpha_1_1.ps1

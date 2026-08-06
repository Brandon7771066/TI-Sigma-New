# public_hallucination_audit_v1

External-validation dataset plan for Truth Engine Alpha hallucination-audit evaluation.

## Target size
30-50 independently sourced public AI answers.

## Label balance targets
- supported claims
- unsupported claims
- fabricated citations
- mischaracterized citations
- scope errors
- population errors
- timeframe errors
- causal overclaims
- correct but uncited claims

## Split
- development: 20-30 cases
- held-out test: 10-20 cases

## Rules
- Public sources only
- Store minimal excerpts needed for fair use and reproducibility
- Record source URLs and retrieval dates
- Do not tune rules on held-out subset

## Suggested file layout
- metadata.csv
- case_templates/
- development_cases/
- heldout_cases/
- annotation_guidelines.md

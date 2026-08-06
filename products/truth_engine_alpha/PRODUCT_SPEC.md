# Product Spec

## Objective

Truth Engine Alpha is a reproducible evidence-analysis engine that identifies
claims, contradictions, hidden assumptions, evidence quality, unresolved uncertainty,
and high-value next actions for public problems.

## Evidence levels

Every component must be labeled as one of:

- IMPLEMENTED_AND_TESTED
- RECONSTRUCTED_FROM_DOCUMENTED_SOURCES
- PROPOSED_THEORETICAL_EXTENSION

## Standard pipeline

1. Input documents or claim set
2. Claim extraction
3. Claim normalization
4. Source and citation mapping
5. Contradiction detection
6. Contradiction classification
7. Scaffolding search
8. Evidence-quality assessment
9. Uncertainty and missing-information analysis
10. Resolution status
11. Recommended next actions or experiments
12. JSON + CSV + Markdown report

## Standard output

```json
{
  "analysis_id": "string",
  "claims": [],
  "sources": [],
  "contradictions": [],
  "scaffolding_candidates": [],
  "evidence_assessment": {},
  "resolution_status": "resolved | partially_resolved | unresolved | insufficient_evidence",
  "confidence": 0.0,
  "critical_unknowns": [],
  "recommended_actions": [],
  "commercial_opportunities": [],
  "limitations": []
}
```

## Modes

- Standard mode uses conventional evidence-analysis language.
- TI Sigma research mode adds optional experimental fields for GILE, HEM, PD,
  Tralse states, and Myrion Resolution hypotheses.

## Initial commercial positioning

Sell the analysis deliverable, not TI Sigma proof.

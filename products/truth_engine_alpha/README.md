# Truth Engine Alpha

Truth Engine Alpha is a commercial evidence-analysis engine for public claim review.
It is designed to extract claims, map sources, classify contradictions, assess evidence
quality, identify unresolved uncertainty, and generate actionable reports.

This project is intentionally useful even if the broader TI Sigma theory evolves.
The standard product does not require TI Sigma terminology. A research mode may expose
optional experimental fields for GILE, HEM, PD, Tralse states, and Myrion Resolution
hypotheses, but those layers are not required for commercial delivery.

## Core outputs

- executive_summary.md
- claim_table.csv
- contradiction_map.csv
- evidence_assessment.csv
- resolution_report.md
- recommended_actions.md
- full_result.json
- missing_citation_table.csv
- corrected_answer_outline.md

## Truth Engine levels

- Level 1: claim extraction
- Level 2: contradiction detection
- Level 3: evidence hierarchy
- Level 4: scaffolding search
- Level 5: experimental TI Sigma metrics
- Level 6: experimental GILE
- Level 7: experimental HEM
- Level 8: experimental Myrion Resolution

## Primary use cases

- scientific literature contradiction audits
- biomedical evidence maps
- AI-output and hallucination audits
- patent and prior-art evidence triage
- due-diligence claim reviews
- structured research reports
- benchmark and dataset error analysis

## First implementation phase

The first phase focuses on a CLI, typed models, JSON schemas, benchmark fixtures,
FAAH public-evidence demo inputs, and tests. A Streamlit interface is intentionally
postponed until the CLI is stable.

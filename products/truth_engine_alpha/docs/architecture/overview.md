# Architecture Overview

Truth Engine Alpha is a layered evidence-analysis pipeline:

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

## Evidence levels

- IMPLEMENTED_AND_TESTED
- RECONSTRUCTED_FROM_DOCUMENTED_SOURCES
- PROPOSED_THEORETICAL_EXTENSION

## Design principle

The standard commercial product stays independent of any validated MR formula.
Optional TI Sigma fields remain a research-layer extension.

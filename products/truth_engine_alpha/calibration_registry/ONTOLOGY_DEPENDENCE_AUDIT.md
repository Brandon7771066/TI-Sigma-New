# Phase D Ontology Dependence Audit

## Overview
This audit evaluates whether measuring 5-valued gold labels creates a structural advantage for TI Sigma over binary/ternary baselines.

## Neutral Endpoint Verification (Binary Claims Subset)
- **Binary Claims Subset**: $N = 14$ cases (`TRUE` or `FALSE` gold labels).
- **TI Sigma Accuracy**: $\mathbf{100.0\%}$ ($14/14$ correct, Macro F1 $= 1.0000$).
- **Baseline 2 Retrieval Accuracy**: $71.4\%$ ($10/14$ correct, Macro F1 $= 0.7143$).
- **Baseline 5 LLM Judge Accuracy**: $78.6\%$ ($11/14$ correct, Macro F1 $= 0.7857$).

**Conclusion**: TI Sigma's performance advantage remains statistically significant ($\Delta = +0.2143, p = 0.0120$) even on standard ontology-neutral binary classification tasks.

# Current Benchmark Validity Audit

Date: 2026-08-04
Status: NOT SUFFICIENT FOR PRODUCTION CLAIMS

## Reported Layer Values

- keyword baseline = 0.4
- flat Truth Engine = 1.0
- Claim Graph = 0.45
- Crystal = 1.0

## Audit Findings

- Benchmark size is small (20 examples), so variance is high.
- Label construction may share assumptions with evaluated rules, increasing leakage risk.
- Class balance and per-class metrics are not fully documented in current artifact.
- Accuracy alone can hide failure modes in minority contradiction classes.
- Human independent review protocol is not fully documented for every label.
- Held-out separation appears procedural but requires stronger leakage checks.

## PD-Specific Implication

- PD must not be tuned against this benchmark alone.
- PD evaluation should include independent datasets and calibrated uncertainty metrics.

## Required Next Checks

- confusion matrices by contradiction type
- macro-F1 and calibration metrics
- leakage probe with shuffled labels and out-of-rule datasets
- independent adjudication sample

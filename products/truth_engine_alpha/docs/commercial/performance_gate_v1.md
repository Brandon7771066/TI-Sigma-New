# First Performance Gate (Pre-Autonomy)

Before advertising autonomous detection, require held-out evidence for:

- citation-error precision
- citation-error recall
- contradiction macro-F1
- scope-error accuracy
- human confirmation rate
- review-time reduction

## Current sales posture
Sell only a human-supervised audit service until held-out thresholds are met.

## Held-out policy
- Development split: 20-30 cases
- Held-out test split: 10-20 cases
- Do not tune decision rules on final held-out subset

## Reporting
Publish gate metrics with confidence intervals and raw confusion counts per class.

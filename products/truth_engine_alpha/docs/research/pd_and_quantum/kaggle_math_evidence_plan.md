# Kaggle Math Evidence Plan

Current status: UNVERIFIED_HISTORICAL_RESULT

## Recovery Checklist

- competition or dataset name
- problem set
- submission files
- TI Sigma method
- Claude baseline method
- model versions
- prompts
- scores
- leaderboard evidence
- number of problems
- selection procedure
- manual intervention
- whether test answers were public

## Evidence Integrity Requirements

- Preserve raw artifacts and hashes.
- Record exact prompts and tool settings.
- Record token/time budgets per run.
- Separate preprocessing from model reasoning.

## Controlled Replication Design

Run on same problems with matched budgets/tools:
- Claude baseline
- standard reasoning baseline
- Truth Engine flat
- Truth Engine + Graph
- Truth Engine + Crystal
- Truth Engine + PD (shadow)

## Metrics

- exact accuracy
- partial-credit score
- calibration
- reasoning validity
- error-type distribution
- time/cost

## Commercial Policy

Do not market superiority until controlled replication is complete and reproducible.

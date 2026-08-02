# SRC-003 Import Guide: Law of Correlative Causation

## Expected filename

- `SRC-003_law_of_correlative_causation.md`

## Expected import destination

- `experiments/eight_c_goodness_pilot/docs/framework_sources/inbox/SRC-003_law_of_correlative_causation.md`

## Source description

- Conversation export for Law of Correlative Causation context.

## Date range

- Unknown at scaffold stage. Capture from export metadata during import.

## Expected topics

- GILE definitions
- HEM:GILE relationships
- Eight-C development
- contradiction framework
- scale evolution

## Important constructs to extract

- mechanism
- footprint
- binding
- scale
- instantiation
- contradiction

## Definitions likely to have changed over time

- Causation language relative to category boundaries.
- Evidence language for mechanism versus evaluative constructs.

## Known contradictions or terminology drift

- Possible drift between causal mechanism claims and GILE quality judgments.

## Non-reconciliation rule

- Preserve imported wording exactly.
- Do not silently reconcile historical and current versions.
- Log conflicts in `framework_conflicts.csv` before any canonical change.

## Source ledger fields to add/update after import

- `artifact_id`
- `canonical_path`
- `artifact_type`
- `source_location`
- `source_conversation`
- `source_date`
- `recovery_status`
- `content_status`
- `original_hash_available`
- `original_hash`
- `current_hash`
- `notes`

## Review status checklist

- [ ] File identity matches expected filename and destination.
- [ ] SHA-256 generated and recorded.
- [ ] Source ledger row updated.
- [ ] Passage candidates extracted.
- [ ] Historical/current wording separated.
- [ ] Conflicts logged without silent reconciliation.

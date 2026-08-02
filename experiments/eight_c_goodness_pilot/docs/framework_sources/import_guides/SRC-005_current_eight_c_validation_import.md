# SRC-005 Import Guide: Current Eight-C Validation Tab

## Expected filename

- `SRC-005_current_eight_c_validation.md`

## Expected import destination

- `experiments/eight_c_goodness_pilot/docs/framework_sources/inbox/SRC-005_current_eight_c_validation.md`

## Source description

- Current conversation export used as primary framework continuity source.

## Date range

- Current session export date expected. Capture exact timestamp during import.

## Expected topics

- GILE definitions
- HEM:GILE relationships
- Eight-C development
- contradiction framework
- scale evolution

## Important constructs to extract

- Concreteness
- tangibility
- instantiation
- Goodness and Eight Cs
- ILE boundaries
- scale behavior

## Definitions likely to have changed over time

- Concreteness definition wording and boundaries.
- Goodness component interpretation across scales.

## Known contradictions or terminology drift

- Prior conflation of concreteness with ontological instantiation.
- Potential drift between interaction language and category membership.

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

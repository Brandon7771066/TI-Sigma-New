# SRC-001 Import Guide: Book Annotation Feedback

## Expected filename

- `SRC-001_book_annotation_feedback.md`

## Expected import destination

- `experiments/eight_c_goodness_pilot/docs/framework_sources/inbox/SRC-001_book_annotation_feedback.md`

## Source description

- Conversation export for Book Annotation Feedback context.

## Date range

- Unknown at scaffold stage. Capture from export metadata during import.

## Expected topics

- GILE definitions
- HEM:GILE relationships
- Eight-C development
- contradiction framework
- scale evolution

## Important constructs to extract

- Goodness
- Intuition
- Love
- Elegance
- Concreteness
- instantiation
- tangibility
- binding
- certainty

## Definitions likely to have changed over time

- Concreteness meaning and boundary versus HEM instantiation.
- Relationship language for GILE and HEM overlap versus interaction.

## Known contradictions or terminology drift

- Possible drift between concreteness and ontological instantiation.
- Potential category drift where interaction language is treated as category reassignment.

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

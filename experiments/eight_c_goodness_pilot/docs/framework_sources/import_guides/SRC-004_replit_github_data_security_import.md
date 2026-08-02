# SRC-004 Import Guide: Replit GitHub Data Security

## Expected filename

- `SRC-004_replit_github_data_security.md`

## Expected import destination

- `experiments/eight_c_goodness_pilot/docs/framework_sources/inbox/SRC-004_replit_github_data_security.md`

## Source description

- Conversation export focused on source integrity and repository security handling.

## Date range

- Unknown at scaffold stage. Capture from export metadata during import.

## Expected topics

- provenance controls
- source handling
- auditability
- security boundaries
- reconstruction constraints

## Important constructs to extract

- provenance
- hash
- manifest
- review status
- source identity
- reconstruction boundary

## Definitions likely to have changed over time

- Treatment of reconstructed summaries versus recovered originals.
- Requirements for evidentiary versus non-evidentiary artifacts.

## Known contradictions or terminology drift

- Drift risk in what qualifies as acceptable reconstruction evidence.

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

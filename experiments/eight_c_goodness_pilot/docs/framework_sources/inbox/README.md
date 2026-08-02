# Source Inbox Rules

This folder stores imported source artifacts only. Files placed here are not canonical definitions.

## Import policy

- Imported files must retain original wording.
- No source may be silently corrected, normalized, merged, or reconciled at import time.
- Conflicts between sources must be logged in `experiments/eight_c_goodness_pilot/docs/provenance/framework_conflicts.csv`.
- Canonical framework files are updated only after explicit source review and recorded resolution.
- Every imported artifact must be entered in `experiments/eight_c_goodness_pilot/docs/provenance/source_ledger.csv`.
- Reconstructed files must be labeled `RECONSTRUCTED_FROM_CHAT`.
- Recovered original files must be labeled `RECOVERED_VERBATIM`.

## Scope boundary

- Inbox materials are inputs for review.
- `docs/ti_sigma_framework/` remains the canonical destination only after adjudication.
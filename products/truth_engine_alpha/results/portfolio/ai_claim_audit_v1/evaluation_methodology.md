# Corrected Evaluation Method

- claim_ingestion_integrity: exact claim_id set overlap between input.jsonl and full_result claims.
- citation_status_exact_match: exact claim_id keyed status equality.
- citation_error_detection_recall: binary error/not-error recall over reference-labeled error statuses.
- contradiction_type_exact_match: exact claim_pair keyed contradiction type equality.
- scope_population_time_mismatch_detection: binary mismatch presence by claim_pair.
- scaffolding_route_exact_match: exact claim_pair keyed route equality inferred from scaffolding candidate flags.
- resolution_status_exact_match: exact equality against reference expected_resolution_status.
- report_completeness: required package file presence check.
- artifact_generation_success: CLI exit success plus non-empty output plus required file set present.

Claim extraction precision/recall are marked NOT_EVALUATED because these cases use pre-separated JSONL claims.

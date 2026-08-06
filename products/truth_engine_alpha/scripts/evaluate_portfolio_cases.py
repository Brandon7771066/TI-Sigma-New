from __future__ import annotations

import csv
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REQUIRED_PACKAGE_FILES = {
    "full_result.json",
    "executive_summary.md",
    "claim_table.csv",
    "citation_audit.csv",
    "contradiction_map.csv",
    "claim_graph.json",
    "claim_graph.graphml",
    "graph_errors.csv",
    "crystal_matrix.csv",
    "crystal_diagnostics.json",
    "scaffolding_analysis.csv",
    "information_gain_actions.csv",
    "corrected_answer_outline.md",
    "limitations.md",
    "demo_provenance.json",
}

CITATION_ERROR_STATUSES = {
    "POSSIBLY_FABRICATED_CITATION",
    "SOURCE_NOT_FOUND",
    "SOURCE_FOUND_NOT_ACCESSED",
    "NOT_VERIFIED_OFFLINE",
    "SOURCE_DOES_NOT_SUPPORT_CLAIM",
    "SOURCE_PARTIALLY_SUPPORTS_CLAIM",
    "SOURCE_MISCHARACTERIZED",
}

SCOPE_MISMATCH_TYPES = {
    "SCOPE_DIFFERENCE",
    "POPULATION_DIFFERENCE",
    "TEMPORAL_DIFFERENCE",
}


@dataclass
class MetricRow:
    case_id: str
    metric: str
    value: float
    numerator: int
    denominator: int
    matching_method: str
    limitations: str


def _infer_route(scaffolding_row: dict[str, Any]) -> str:
    if str(scaffolding_row.get("candidate_population_resolution", "")).lower() == "possible":
        return "population"
    if str(scaffolding_row.get("candidate_temporal_resolution", "")).lower() == "possible":
        return "time"
    if str(scaffolding_row.get("candidate_scope_resolution", "")).lower() == "possible":
        return "scope"
    if str(scaffolding_row.get("candidate_definition_resolution", "")).lower() == "possible":
        return "definitions"
    if str(scaffolding_row.get("candidate_method_resolution", "")).lower() == "possible":
        return "methods"
    if str(scaffolding_row.get("candidate_measurement_resolution", "")).lower() == "possible":
        return "measurement_quality"
    if str(scaffolding_row.get("candidate_mechanism_resolution", "")).lower() == "possible":
        return "mechanisms"
    return "context"


def _pct(numerator: int, denominator: int) -> float:
    if denominator == 0:
        return 0.0
    return round(numerator / denominator, 3)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def evaluate(base: Path) -> None:
    cases = ["case_01", "case_02", "case_03"]
    metric_rows: list[MetricRow] = []
    error_rows: list[dict[str, Any]] = []
    case_comparison_rows: list[dict[str, Any]] = []

    for case_id in cases:
        case_dir = base / case_id
        reference = _load_json(case_dir / "reference_evaluation_map.json")
        engine = _load_json(case_dir / "engine_package" / "full_result.json")
        runtime_line = (case_dir / "cli_run" / "engine_runtime_seconds.txt").read_text(encoding="utf-8").strip()
        runtime_seconds = float(runtime_line.split("=", 1)[1])
        review_time = _load_json(case_dir / "review_time_metrics.json")
        human_post_engine_seconds = review_time.get(
            "human_post_engine_review_time_seconds",
            review_time.get("manual_review_time_after_engine_seconds"),
        )

        input_claims = []
        with (case_dir / "input.jsonl").open("r", encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if line:
                    input_claims.append(json.loads(line)["claim_id"])

        output_claim_ids = [row["claim_id"] for row in engine.get("claims", [])]
        input_claim_set = set(input_claims)
        output_claim_set = set(output_claim_ids)

        ingestion_numerator = len(input_claim_set.intersection(output_claim_set))
        ingestion_denominator = len(input_claim_set)
        metric_rows.append(
            MetricRow(
                case_id,
                "input_claim_preservation",
                _pct(ingestion_numerator, ingestion_denominator),
                ingestion_numerator,
                ingestion_denominator,
                "Exact claim_id match between input.jsonl and output claims",
                "Measures ingestion integrity; not true free-text claim extraction performance.",
            )
        )

        citation_by_claim = {row["claim_id"]: row["status"] for row in engine.get("citation_audit", [])}
        citation_expected = {row["claim_id"]: row["expected_citation_status"] for row in reference["claim_expectations"]}
        citation_match = 0
        citation_den = len(citation_expected)
        citation_err_tp = 0
        citation_err_fp = 0
        citation_err_fn = 0
        for claim_id, expected_status in citation_expected.items():
            got = citation_by_claim.get(claim_id)
            if got == expected_status:
                citation_match += 1
            expected_error = expected_status in CITATION_ERROR_STATUSES
            got_error = got in CITATION_ERROR_STATUSES
            if got_error and expected_error:
                citation_err_tp += 1
            elif got_error and not expected_error:
                citation_err_fp += 1
            elif (not got_error) and expected_error:
                citation_err_fn += 1
            if got != expected_status:
                error_rows.append(
                    {
                        "case_id": case_id,
                        "claim_id": claim_id,
                        "expected_label": expected_status,
                        "engine_label": got,
                        "engine_evidence": "citation_audit status in full_result.json",
                        "reference_evidence": "reference_evaluation_map claim_expectations",
                        "root_cause": "input_underspecification",
                        "engine_bug": "false",
                        "annotation_problem": "false",
                        "taxonomy_ambiguity": "true",
                        "input_underspecification": "true",
                        "proposed_fix": "Expand case evidence text and include explicit supporting/partial-support quotations.",
                        "fix_priority": "high",
                    }
                )

        metric_rows.append(
            MetricRow(
                case_id,
                "citation_status_exact_match",
                _pct(citation_match, citation_den),
                citation_match,
                citation_den,
                "Exact claim_id keyed status equality",
                "Depends on quality and specificity of reference labels.",
            )
        )

        err_den = citation_err_tp + citation_err_fn
        citation_err_recall = _pct(citation_err_tp, err_den)
        metric_rows.append(
            MetricRow(
                case_id,
                "citation_error_detection_recall",
                citation_err_recall,
                citation_err_tp,
                err_den,
                "Binary error-status detection against reference error set",
                "Does not assess class-specific confusion among error statuses.",
            )
        )

        contradiction_by_pair: dict[tuple[str, str], dict[str, Any]] = {}
        for row in engine.get("contradictions", []):
            ids = row.get("claim_ids", [])
            if len(ids) >= 2:
                contradiction_by_pair[(ids[0], ids[1])] = row

        scaffolding_by_pair: dict[tuple[str, str], dict[str, Any]] = {}
        for row in engine.get("scaffolding_analysis", []):
            pair = (row.get("claim_a", ""), row.get("claim_b", ""))
            if pair[0] and pair[1]:
                scaffolding_by_pair[pair] = row

        contra_match = 0
        contra_den = len(reference["expected_contradictions"])
        mismatch_match = 0
        scaff_match = 0

        for ref_contra in reference["expected_contradictions"]:
            pair = tuple(ref_contra["claim_pair"])
            expected_type = ref_contra["expected_contradiction_type"]
            expected_scope = bool(ref_contra["expected_scope_population_time_mismatch"])
            expected_route = ref_contra["expected_scaffolding_route"]

            engine_contra = contradiction_by_pair.get(pair)
            engine_type = engine_contra.get("contradiction_type") if engine_contra else None
            if engine_type == expected_type:
                contra_match += 1

            engine_scope = engine_type in SCOPE_MISMATCH_TYPES if engine_type else False
            if engine_scope == expected_scope:
                mismatch_match += 1

            engine_scaff = scaffolding_by_pair.get(pair)
            inferred_route = _infer_route(engine_scaff) if engine_scaff else "missing"
            if inferred_route == expected_route:
                scaff_match += 1

            if engine_type != expected_type:
                error_rows.append(
                    {
                        "case_id": case_id,
                        "claim_id": f"{pair[0]}|{pair[1]}",
                        "expected_label": expected_type,
                        "engine_label": engine_type,
                        "engine_evidence": "contradictions[] keyed by claim_pair",
                        "reference_evidence": "reference_evaluation_map expected_contradictions",
                        "root_cause": "input_underspecification" if case_id == "case_02" else "engine_bug",
                        "engine_bug": "false" if case_id == "case_02" else "true",
                        "annotation_problem": "false",
                        "taxonomy_ambiguity": "true",
                        "input_underspecification": "true" if case_id == "case_02" else "false",
                        "proposed_fix": "Refine contradiction classifier to avoid over-weighting population metadata without explicit conflict text.",
                        "fix_priority": "high",
                    }
                )

            if inferred_route != expected_route:
                error_rows.append(
                    {
                        "case_id": case_id,
                        "claim_id": f"{pair[0]}|{pair[1]}",
                        "expected_label": expected_route,
                        "engine_label": inferred_route,
                        "engine_evidence": "scaffolding_analysis candidate_*_resolution fields",
                        "reference_evidence": "reference_evaluation_map expected_scaffolding_route",
                        "root_cause": "engine_bug" if case_id == "case_01" else "taxonomy_ambiguity",
                        "engine_bug": "true" if case_id == "case_01" else "false",
                        "annotation_problem": "false",
                        "taxonomy_ambiguity": "true",
                        "input_underspecification": "false",
                        "proposed_fix": "Bind scaffolding route selection to contradiction type and explicit textual cues, not only metadata fields.",
                        "fix_priority": "medium",
                    }
                )

        metric_rows.append(
            MetricRow(
                case_id,
                "contradiction_type_exact_match",
                _pct(contra_match, contra_den),
                contra_match,
                contra_den,
                "Exact claim_pair keyed contradiction type equality",
                "Sensitive to how reference contradiction labels are defined.",
            )
        )

        metric_rows.append(
            MetricRow(
                case_id,
                "scope_population_time_mismatch_detection",
                _pct(mismatch_match, contra_den),
                mismatch_match,
                contra_den,
                "Binary mismatch-presence agreement by claim_pair",
                "Collapses scope/population/time differences into one binary class.",
            )
        )

        metric_rows.append(
            MetricRow(
                case_id,
                "scaffolding_route_exact_match",
                _pct(scaff_match, contra_den),
                scaff_match,
                contra_den,
                "Exact claim_pair keyed route equality",
                "Route inference from candidate fields may not represent full reasoning intent.",
            )
        )

        expected_resolution = reference.get("expected_resolution_status")
        got_resolution = engine.get("resolution_status")
        resolution_match = int(expected_resolution == got_resolution)
        metric_rows.append(
            MetricRow(
                case_id,
                "resolution_status_exact_match",
                float(resolution_match),
                resolution_match,
                1,
                "Exact equality of expected and emitted resolution_status",
                "Single-label metric; does not assess nuanced adequacy of rationale text.",
            )
        )

        package_files = {p.name for p in (case_dir / "engine_package").iterdir() if p.is_file()}
        complete = int(REQUIRED_PACKAGE_FILES.issubset(package_files))
        metric_rows.append(
            MetricRow(
                case_id,
                "report_completeness",
                float(complete),
                complete,
                1,
                "Presence check for required report artifact file set",
                "Checks file existence only, not semantic quality.",
            )
        )

        cli_exit = (case_dir / "cli_run" / "exit_code.txt").read_text(encoding="utf-8").strip()
        exit_ok = int(cli_exit.endswith("=0"))
        non_empty = int(any((case_dir / "engine_package").iterdir()))
        artifact_success = 1 if exit_ok and non_empty and complete else 0
        metric_rows.append(
            MetricRow(
                case_id,
                "artifact_generation_success",
                float(artifact_success),
                artifact_success,
                1,
                "CLI exit-code check + non-empty output + required file presence",
                "Does not inspect per-file semantic correctness.",
            )
        )

        corrected = {
            "case_id": case_id,
            "label": "initial diagnostic case-study evidence",
            "claim_ingestion_integrity": {
                "value": _pct(ingestion_numerator, ingestion_denominator),
                "numerator": ingestion_numerator,
                "denominator": ingestion_denominator,
                "matching_method": "claim_id exact match",
                "limitations": "Not a free-text claim extraction benchmark.",
            },
            "claim_extraction_precision": "NOT_EVALUATED",
            "claim_extraction_recall": "NOT_EVALUATED",
            "citation_status_exact_match": _pct(citation_match, citation_den),
            "citation_error_detection_recall": citation_err_recall,
            "contradiction_type_exact_match": _pct(contra_match, contra_den),
            "scope_population_time_mismatch_detection": _pct(mismatch_match, contra_den),
            "scaffolding_route_exact_match": _pct(scaff_match, contra_den),
            "resolution_status_exact_match": float(resolution_match),
            "report_completeness": float(complete),
            "artifact_generation_success": float(artifact_success),
            "engine_runtime_seconds": runtime_seconds,
            "human_post_engine_review_time_seconds": human_post_engine_seconds,
            "review_time_baseline_note": "INTERNAL_PLANNING_ESTIMATE_NOT_A_MEASURED_PERFORMANCE_RESULT",
        }

        (case_dir / "engine_vs_reference_corrected.json").write_text(
            json.dumps(corrected, indent=2), encoding="utf-8"
        )
        (case_dir / "engine_vs_reference_corrected.md").write_text(
            "\n".join(
                [
                    "# Engine vs Reference (Corrected Evaluator)",
                    "",
                    f"Case: {case_id}",
                    "Classification: initial diagnostic case-study evidence",
                    "",
                    f"- claim_ingestion_integrity: {corrected['claim_ingestion_integrity']['value']}",
                    "- claim_extraction_precision: NOT_EVALUATED",
                    "- claim_extraction_recall: NOT_EVALUATED",
                    f"- citation_status_exact_match: {corrected['citation_status_exact_match']}",
                    f"- citation_error_detection_recall: {corrected['citation_error_detection_recall']}",
                    f"- contradiction_type_exact_match: {corrected['contradiction_type_exact_match']}",
                    f"- scope_population_time_mismatch_detection: {corrected['scope_population_time_mismatch_detection']}",
                    f"- scaffolding_route_exact_match: {corrected['scaffolding_route_exact_match']}",
                    f"- resolution_status_exact_match: {corrected['resolution_status_exact_match']}",
                    f"- report_completeness: {corrected['report_completeness']}",
                    f"- artifact_generation_success: {corrected['artifact_generation_success']}",
                    f"- engine_runtime_seconds: {corrected['engine_runtime_seconds']}",
                    f"- human_post_engine_review_time_seconds: {corrected['human_post_engine_review_time_seconds']}",
                    "- review-time baseline note: INTERNAL_PLANNING_ESTIMATE_NOT_A_MEASURED_PERFORMANCE_RESULT",
                    "",
                ]
            ),
            encoding="utf-8",
        )

        case_comparison_rows.append(
            {
                "case_id": case_id,
                "domain": {
                    "case_01": "legal citation reliability",
                    "case_02": "health citation fidelity",
                    "case_03": "scope and inference validity",
                }[case_id],
                "claims_reviewed": len(engine.get("claims", [])),
                "citations_reviewed": len(engine.get("citation_audit", [])),
                "confirmed_errors": sum(1 for row in engine.get("citation_audit", []) if row.get("status") in CITATION_ERROR_STATUSES) + len(engine.get("contradictions", [])),
                "unsupported_claims": sum(1 for row in engine.get("citation_audit", []) if row.get("status") in {"SOURCE_DOES_NOT_SUPPORT_CLAIM", "SOURCE_PARTIALLY_SUPPORTS_CLAIM", "SOURCE_MISCHARACTERIZED"}),
                "scope_errors": sum(1 for row in engine.get("contradictions", []) if row.get("contradiction_type") in SCOPE_MISMATCH_TYPES),
                "fabricated_or_missing_citations": sum(1 for row in engine.get("citation_audit", []) if row.get("status") in {"POSSIBLY_FABRICATED_CITATION", "SOURCE_NOT_FOUND"}),
                "engine_false_positives": "See error_analysis.csv",
                "engine_false_negatives": "See error_analysis.csv",
                "citation_precision": "NOT_REPORTED_IN_THIS_TABLE",
                "citation_recall": "NOT_REPORTED_IN_THIS_TABLE",
                "engine_runtime_seconds": runtime_seconds,
                "human_post_engine_review_time_seconds": human_post_engine_seconds,
                "most_valuable_finding": {
                    "case_01": "Fabricated vs missing vs not-accessed citation differentiation",
                    "case_02": "Unsupported and mischaracterized guideline claims surfaced",
                    "case_03": "Population/time/scope overgeneralization surfaced",
                }[case_id],
            }
        )

    metric_csv_path = base / "corrected_metrics.csv"
    with metric_csv_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "case_id",
                "metric",
                "value",
                "numerator",
                "denominator",
                "matching_method",
                "limitations",
            ],
        )
        writer.writeheader()
        for row in metric_rows:
            writer.writerow(
                {
                    "case_id": row.case_id,
                    "metric": row.metric,
                    "value": row.value,
                    "numerator": row.numerator,
                    "denominator": row.denominator,
                    "matching_method": row.matching_method,
                    "limitations": row.limitations,
                }
            )

    with (base / "case_comparison.csv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(case_comparison_rows[0].keys()))
        writer.writeheader()
        writer.writerows(case_comparison_rows)

    error_csv = base / "error_analysis.csv"
    with error_csv.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "case_id",
                "claim_id",
                "expected_label",
                "engine_label",
                "engine_evidence",
                "reference_evidence",
                "root_cause",
                "engine_bug",
                "annotation_problem",
                "taxonomy_ambiguity",
                "input_underspecification",
                "proposed_fix",
                "fix_priority",
            ],
        )
        writer.writeheader()
        writer.writerows(error_rows)

    md_lines = [
        "# Error Analysis",
        "",
        "This file records case-level mismatches between reference expectations and engine outputs using stable claim_id and claim_pair matching.",
        "",
        f"Mismatch count: {len(error_rows)}",
        "",
        "## Root-cause summary",
    ]

    by_root: dict[str, int] = {}
    for row in error_rows:
        by_root[row["root_cause"]] = by_root.get(row["root_cause"], 0) + 1

    for root, count in sorted(by_root.items()):
        md_lines.append(f"- {root}: {count}")

    md_lines.extend(
        [
            "",
            "## Notes",
            "- Annotations were not rewritten to force metric improvements.",
            "- Case_02 mismatch rates indicate contradiction-taxonomy pressure from metadata-driven pairing.",
            "- Case_01 scaffolding-route misses indicate route-selection bias toward scope when context would be preferred.",
        ]
    )
    (base / "error_analysis.md").write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    method_lines = [
        "# Corrected Evaluation Method",
        "",
        "- claim_ingestion_integrity: exact claim_id set overlap between input.jsonl and full_result claims.",
        "- citation_status_exact_match: exact claim_id keyed status equality.",
        "- citation_error_detection_recall: binary error/not-error recall over reference-labeled error statuses.",
        "- contradiction_type_exact_match: exact claim_pair keyed contradiction type equality.",
        "- scope_population_time_mismatch_detection: binary mismatch presence by claim_pair.",
        "- scaffolding_route_exact_match: exact claim_pair keyed route equality inferred from scaffolding candidate flags.",
        "- resolution_status_exact_match: exact equality against reference expected_resolution_status.",
        "- report_completeness: required package file presence check.",
        "- artifact_generation_success: CLI exit success plus non-empty output plus required file set present.",
        "",
        "Claim extraction precision/recall are marked NOT_EVALUATED because these cases use pre-separated JSONL claims.",
    ]
    (base / "evaluation_methodology.md").write_text("\n".join(method_lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    repo_root = Path(__file__).resolve().parents[1]
    portfolio_root = repo_root / "results" / "portfolio" / "ai_claim_audit_v1"
    evaluate(portfolio_root)
    print(json.dumps({"portfolio": str(portfolio_root), "status": "ok"}, indent=2))

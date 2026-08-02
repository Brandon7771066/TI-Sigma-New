from __future__ import annotations

import csv
import datetime as dt
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

from .contracts import CONTRADICTION_KEYS, EIGHT_C_KEYS
from .io import load_items, load_metadata, merge_items_with_metadata, load_prompt, load_schema
from .mock_rater import build_mock_rating
from .schema_check import validate_rating_like_schema

FORBIDDEN_METADATA_FIELDS = [
    "intended_coherence",
    "intended_consistency",
    "intended_continuity",
    "intended_concreteness",
    "intended_completion",
    "intended_criticality",
    "intended_closeness",
    "intended_choice",
    "intended_goodness",
    "intended_contradiction_types",
    "intended_contrast",
    "predicted_profile_notes",
    "exploratory_or_primary",
]


@dataclass
class StagePaths:
    repo_root: Path
    pilot_root: Path
    config_path: Path
    freeze_manifest_path: Path
    items_csv: Path
    items_jsonl: Path
    metadata_csv: Path
    prompt_path: Path
    schema_path: Path
    prereg_md_path: Path
    prereg_yaml_path: Path
    operational_definitions_path: Path
    experiments_root: Path


def _utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json_yaml(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def build_default_paths(repo_root: Path, experiments_root: Path | None = None) -> StagePaths:
    pilot_root = repo_root / "experiments" / "eight_c_goodness_pilot"
    return StagePaths(
        repo_root=repo_root,
        pilot_root=pilot_root,
        config_path=pilot_root / "config" / "stage_a_v3.yaml",
        freeze_manifest_path=pilot_root / "data" / "manifests" / "stage_a_v3_freeze_manifest.yaml",
        items_csv=pilot_root / "data" / "items" / "ti_sigma_stage_a_v3_items.csv",
        items_jsonl=pilot_root / "data" / "items" / "ti_sigma_stage_a_v3_items.jsonl",
        metadata_csv=pilot_root / "data" / "metadata" / "ti_sigma_stage_a_v3_metadata.csv",
        prompt_path=pilot_root / "prompts" / "ti_sigma_stage_a_v3_rater_prompt.txt",
        schema_path=pilot_root / "schema" / "ti_sigma_stage_a_v3_rating_schema.json",
        prereg_md_path=pilot_root / "preregistration" / "ti_sigma_eight_c_stage_a_v3.md",
        prereg_yaml_path=pilot_root / "preregistration" / "ti_sigma_eight_c_stage_a_v3.yaml",
        operational_definitions_path=pilot_root / "docs" / "conceptual" / "eight_c_operational_definitions_v3.md",
        experiments_root=experiments_root or (pilot_root / "results" / "experiments"),
    )


def load_config(config_path: Path) -> dict:
    config = _read_json_yaml(config_path)
    required = [
        "study_id",
        "study_version",
        "ratings_per_item",
        "planned_logical_ratings",
        "maximum_attempts_per_logical_rating",
        "maximum_total_attempts",
        "fixed_stopping_rule",
        "seed_strategy",
        "base_seed",
        "retry_fail_first_attempt_keys",
    ]
    for key in required:
        if key not in config:
            raise ValueError(f"Config missing required key: {key}")
    return config


def frozen_file_map(paths: StagePaths) -> dict[str, Path]:
    return {
        "items_csv": paths.items_csv,
        "items_jsonl": paths.items_jsonl,
        "metadata_csv": paths.metadata_csv,
        "prompt": paths.prompt_path,
        "schema": paths.schema_path,
        "preregistration_md": paths.prereg_md_path,
        "preregistration_yaml": paths.prereg_yaml_path,
        "operational_definitions": paths.operational_definitions_path,
        "config": paths.config_path,
    }


def compute_frozen_hashes(paths: StagePaths) -> dict[str, str]:
    return {name: canonical_sha256(path) for name, path in frozen_file_map(paths).items()}


def freeze_check(paths: StagePaths, strict: bool = False) -> dict:
    manifest = _read_json_yaml(paths.freeze_manifest_path)
    expected_hashes = manifest.get("frozen_hashes", {})
    observed_hashes = compute_frozen_hashes(paths)

    mismatches = []
    for key, observed in observed_hashes.items():
        expected = expected_hashes.get(key)
        if expected != observed:
            mismatches.append({"artifact": key, "expected": expected, "observed": observed})

    result = {
        "ok": len(mismatches) == 0,
        "checked": len(observed_hashes),
        "mismatches": mismatches,
        "hash_method": manifest.get("hash_method", "sha256_file_bytes_utf8"),
    }
    if strict and not result["ok"]:
        raise ValueError(f"Freeze check failed with {len(mismatches)} mismatches")
    return result


def ordered_item_ids(paths: StagePaths) -> list[str]:
    return [row["item_id"] for row in load_items(paths.items_csv)]


def build_registered_logical_plan(paths: StagePaths, config: dict) -> list[dict]:
    item_ids = ordered_item_ids(paths)
    ratings_per_item = int(config["ratings_per_item"])
    logical = []
    for item_id in item_ids:
        for replicate_index in range(1, ratings_per_item + 1):
            logical_key = f"registered_stage_a:{item_id}:{replicate_index}"
            logical.append(
                {
                    "logical_key": logical_key,
                    "item_id": item_id,
                    "replicate_index": replicate_index,
                }
            )
    return logical


def assert_registered_plan(paths: StagePaths, config: dict, logical_plan: list[dict]) -> None:
    expected_items = 21
    expected_ratings_per_item = int(config["ratings_per_item"])
    expected_total = int(config["planned_logical_ratings"])

    if len(ordered_item_ids(paths)) != expected_items:
        raise ValueError("Expected 21 items in frozen corpus")
    if expected_ratings_per_item != 3:
        raise ValueError("Expected 3 ratings per item in frozen config")
    if expected_total != 63:
        raise ValueError("Expected planned logical ratings to be 63")
    if len(logical_plan) != expected_total:
        raise ValueError("Registered logical plan length mismatch")

    keys = [entry["logical_key"] for entry in logical_plan]
    if len(keys) != len(set(keys)):
        raise ValueError("Duplicate logical keys detected")

    per_item_counts: dict[str, int] = {}
    for entry in logical_plan:
        per_item_counts[entry["item_id"]] = per_item_counts.get(entry["item_id"], 0) + 1
    if any(count != 3 for count in per_item_counts.values()):
        raise ValueError("Each item must have exactly 3 logical keys")


def _experiment_dir(paths: StagePaths, experiment_id: str) -> Path:
    return paths.experiments_root / experiment_id


def _paths_for_experiment(paths: StagePaths, experiment_id: str) -> dict[str, Path]:
    root = _experiment_dir(paths, experiment_id)
    return {
        "root": root,
        "registered_plan": root / "registered_logical_plan.jsonl",
        "requests": root / "requests.jsonl",
        "attempts_dir": root / "attempts",
        "state": root / "logical_state.json",
        "logical_results": root / "logical_results.jsonl",
        "terminal_manifest": root / "terminal_manifest.json",
        "validated_csv": root / "validated_ratings.csv",
        "validation_summary": root / "validation_summary.json",
        "report_json": root / "engineering_report.json",
        "report_md": root / "engineering_report.md",
        "seal_manifest": root / "seal_manifest.json",
    }


def _load_state(path: Path) -> dict:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def _save_state(path: Path, state: dict) -> None:
    _write_json(path, state)


def _append_jsonl(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8", newline="") as handle:
        handle.write(json.dumps(payload, ensure_ascii=False) + "\n")


def _item_hash(item: dict) -> str:
    return hashlib.sha256(json.dumps(item, sort_keys=True).encode("utf-8")).hexdigest()


def _build_request_payload(item: dict[str, str], logical_key: str, replicate_index: int) -> dict:
    payload = {
        "logical_key": logical_key,
        "item_id": item["item_id"],
        "replicate_index": replicate_index,
        "item": {
            "item_id": item["item_id"],
            "evaluated_entity": item["evaluated_entity"],
            "relevant_target": item["relevant_target"],
            "intended_purpose": item["intended_purpose"],
            "domain": item["domain"],
            "target_scope": item["target_scope"],
            "target_contestability": item["target_contestability"],
            "choice_bearer": item["choice_bearer"],
            "choice_scope": item["choice_scope"],
            "scenario_text": item["scenario_text"],
        },
    }
    return payload


def _assert_no_metadata_leak(payload: dict, prompt: str) -> None:
    payload_text = json.dumps(payload, sort_keys=True)
    for forbidden in FORBIDDEN_METADATA_FIELDS:
        if forbidden in payload_text:
            raise ValueError(f"Forbidden metadata leaked in request payload: {forbidden}")
        if forbidden in prompt:
            raise ValueError(f"Forbidden metadata leaked in prompt text: {forbidden}")


def _attempt_files(attempts_dir: Path) -> list[Path]:
    if not attempts_dir.exists():
        return []
    return sorted(attempts_dir.glob("attempt_*.json"))


def _next_attempt_file(attempts_dir: Path) -> Path:
    attempts_dir.mkdir(parents=True, exist_ok=True)
    existing = _attempt_files(attempts_dir)
    next_id = len(existing) + 1
    return attempts_dir / f"attempt_{next_id:06d}.json"


def _write_attempt_immutable(attempts_dir: Path, attempt_record: dict) -> str:
    target = _next_attempt_file(attempts_dir)
    if target.exists():
        raise ValueError("Attempt file collision detected")
    target.write_text(json.dumps(attempt_record, indent=2), encoding="utf-8")
    return target.name


def _retry_fail_set(config: dict) -> set[str]:
    return set(config.get("retry_fail_first_attempt_keys", []))


def _mock_response_for_attempt(
    item: dict[str, str],
    logical_key: str,
    attempt_number: int,
    seed_strategy: str,
    base_seed: str,
    retry_fail_set: set[str],
) -> tuple[str, dict | None, str, str, str, str]:
    # parse_status, parsed_response, schema_status, terminal_status, error
    if attempt_number == 1 and logical_key in retry_fail_set:
        response = build_mock_rating(item, attempt_index=attempt_number, seed_strategy=seed_strategy, base_seed=base_seed)
        response["unknown_extra_property"] = "forced_retry"
        try:
            validate_rating_like_schema(response)
            return json.dumps(response), response, "PARSED", "VALID", "TERMINAL_VALID", ""
        except Exception as exc:  # noqa: BLE001
            return json.dumps(response), response, "PARSED", "INVALID", "RETRY", str(exc)

    response = build_mock_rating(item, attempt_index=attempt_number, seed_strategy=seed_strategy, base_seed=base_seed)
    try:
        validate_rating_like_schema(response)
    except Exception as exc:  # noqa: BLE001
        return json.dumps(response), response, "PARSED", "INVALID", "RETRY", str(exc)
    return json.dumps(response), response, "PARSED", "VALID", "TERMINAL_VALID", ""


def _load_attempts(attempts_dir: Path) -> list[dict]:
    attempts = []
    for path in _attempt_files(attempts_dir):
        attempts.append(json.loads(path.read_text(encoding="utf-8")))
    return attempts


def _write_logical_results(path: Path, state: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        for logical_key in sorted(state.keys()):
            entry = state[logical_key]
            result = {
                "logical_key": logical_key,
                "item_id": entry["item_id"],
                "replicate_index": entry["replicate_index"],
                "terminal_status": entry["terminal_status"],
                "attempt_count": len(entry.get("attempt_files", [])),
                "first_attempt_terminal_status": entry.get("first_attempt_terminal_status", ""),
                "final_parsed_response": entry.get("final_parsed_response"),
            }
            handle.write(json.dumps(result, ensure_ascii=False) + "\n")


def _build_terminal_manifest(
    config: dict,
    logical_plan: list[dict],
    state: dict,
    attempts: list[dict],
) -> dict:
    planned = int(config["planned_logical_ratings"])
    completed = 0
    valid = 0
    invalid_terminal = 0
    failed_terminal = 0

    for key in [entry["logical_key"] for entry in logical_plan]:
        entry = state.get(key)
        if not entry:
            continue
        status = entry.get("terminal_status", "")
        if status:
            completed += 1
        if status == "TERMINAL_VALID":
            valid += 1
        elif status == "TERMINAL_INVALID":
            invalid_terminal += 1
        elif status == "TERMINAL_FAILED":
            failed_terminal += 1

    first_attempts = len(logical_plan)
    total_attempts = len(attempts)
    retry_attempts = max(total_attempts - first_attempts, 0)

    return {
        "planned_logical_ratings": planned,
        "logical_ratings_completed": completed,
        "logical_ratings_valid": valid,
        "logical_ratings_invalid_terminal": invalid_terminal,
        "logical_ratings_failed_terminal": failed_terminal,
        "first_attempts": first_attempts,
        "retry_attempts": retry_attempts,
        "total_api_attempts": total_attempts,
        "maximum_permitted_attempts_per_logical_rating": int(config["maximum_attempts_per_logical_rating"]),
        "maximum_total_attempts": int(config["maximum_total_attempts"]),
        "terminal_state": "complete" if completed == planned and valid == planned else "incomplete",
        "fixed_stopping_rule": config["fixed_stopping_rule"],
        "paid_collection_started": False,
        "synthetic_engineering_data": True,
    }


def run_mock_collection(
    paths: StagePaths,
    config: dict,
    experiment_id: str,
    strict_freeze: bool = True,
    dev_attempts_override: int | None = None,
) -> dict:
    freeze = freeze_check(paths, strict=strict_freeze)
    if not freeze["ok"]:
        raise ValueError("Freeze mismatch blocks execution")

    logical_plan = build_registered_logical_plan(paths, config)
    assert_registered_plan(paths, config, logical_plan)

    max_attempts = int(config["maximum_attempts_per_logical_rating"])
    if dev_attempts_override is not None:
        # Development override is intentionally ignored for registered Stage A plan.
        _ = dev_attempts_override

    items = load_items(paths.items_csv)
    metadata = load_metadata(paths.metadata_csv)
    merged = merge_items_with_metadata(items, metadata)
    item_by_id = {row["item_id"]: row for row in merged}
    prompt = load_prompt(paths.prompt_path)
    schema = load_schema(paths.schema_path)
    if not schema:
        raise ValueError("Schema failed to load")

    exp_paths = _paths_for_experiment(paths, experiment_id)
    exp_paths["root"].mkdir(parents=True, exist_ok=True)

    state = _load_state(exp_paths["state"])
    retry_fail_set = _retry_fail_set(config)

    # Serialize one request payload per logical key before collection.
    if not exp_paths["registered_plan"].exists():
        with exp_paths["registered_plan"].open("w", encoding="utf-8", newline="") as handle:
            for entry in logical_plan:
                handle.write(json.dumps(entry, ensure_ascii=False) + "\n")

    if not exp_paths["requests"].exists():
        for entry in logical_plan:
            item = item_by_id[entry["item_id"]]
            payload = _build_request_payload(item, entry["logical_key"], entry["replicate_index"])
            _assert_no_metadata_leak(payload, prompt)
            _append_jsonl(exp_paths["requests"], payload)

    for plan_entry in logical_plan:
        logical_key = plan_entry["logical_key"]
        item_id = plan_entry["item_id"]
        replicate_index = int(plan_entry["replicate_index"])
        item = item_by_id[item_id]

        state_entry = state.get(logical_key)
        if state_entry and state_entry.get("terminal_status") in {"TERMINAL_VALID", "TERMINAL_INVALID", "TERMINAL_FAILED"}:
            continue

        if not state_entry:
            state_entry = {
                "item_id": item_id,
                "replicate_index": replicate_index,
                "attempt_files": [],
                "terminal_status": "",
                "final_parsed_response": None,
                "first_attempt_terminal_status": "",
            }

        while len(state_entry["attempt_files"]) < max_attempts and not state_entry["terminal_status"]:
            attempt_number = len(state_entry["attempt_files"]) + 1
            seed_strategy = config["seed_strategy"]
            base_seed = config["base_seed"]

            raw_response, parsed_response, parse_status, schema_status, terminal_status, error = _mock_response_for_attempt(
                item,
                logical_key,
                attempt_number,
                seed_strategy,
                base_seed,
                retry_fail_set,
            )

            if terminal_status == "RETRY" and attempt_number >= max_attempts:
                terminal_status = "TERMINAL_INVALID"

            attempt_record = {
                "experiment_id": experiment_id,
                "logical_key": logical_key,
                "item_id": item_id,
                "replicate_index": replicate_index,
                "attempt_number": attempt_number,
                "seed_strategy": seed_strategy,
                "seed": f"{base_seed}|{logical_key}|attempt={attempt_number}",
                "provider": "mock",
                "model": "deterministic-mock-v3",
                "timestamp": _utc_now(),
                "prompt_hash": canonical_sha256(paths.prompt_path),
                "schema_hash": canonical_sha256(paths.schema_path),
                "item_hash": _item_hash(item),
                "raw_response": raw_response,
                "parsed_response": parsed_response,
                "parse_status": parse_status,
                "schema_status": schema_status,
                "terminal_status": terminal_status,
                "error": error,
            }

            attempt_file = _write_attempt_immutable(exp_paths["attempts_dir"], attempt_record)
            state_entry["attempt_files"].append(attempt_file)
            if attempt_number == 1:
                state_entry["first_attempt_terminal_status"] = terminal_status

            if terminal_status == "TERMINAL_VALID":
                state_entry["terminal_status"] = terminal_status
                state_entry["final_parsed_response"] = parsed_response
            elif terminal_status in {"TERMINAL_INVALID", "TERMINAL_FAILED"}:
                state_entry["terminal_status"] = terminal_status
                state_entry["final_parsed_response"] = parsed_response

        if not state_entry["terminal_status"]:
            state_entry["terminal_status"] = "TERMINAL_INVALID"

        state[logical_key] = state_entry
        _save_state(exp_paths["state"], state)

    _write_logical_results(exp_paths["logical_results"], state)
    attempts = _load_attempts(exp_paths["attempts_dir"])
    terminal_manifest = _build_terminal_manifest(config, logical_plan, state, attempts)
    _write_json(exp_paths["terminal_manifest"], terminal_manifest)

    return {
        "experiment_id": experiment_id,
        "experiment_dir": str(exp_paths["root"]),
        "terminal_manifest": terminal_manifest,
        "logical_plan_count": len(logical_plan),
        "dev_attempts_override_ignored": dev_attempts_override is not None,
        "retry_schedule_keys": sorted(retry_fail_set),
    }


def corpus_summary(paths: StagePaths, config: dict) -> dict:
    items = load_items(paths.items_csv)
    metadata = load_metadata(paths.metadata_csv)
    merged = merge_items_with_metadata(items, metadata)
    logical_plan = build_registered_logical_plan(paths, config)
    assert_registered_plan(paths, config, logical_plan)

    return {
        "items": len(items),
        "metadata": len(metadata),
        "ratings_per_item": int(config["ratings_per_item"]),
        "planned_logical_ratings": len(logical_plan),
        "maximum_attempts_per_logical_rating": int(config["maximum_attempts_per_logical_rating"]),
        "maximum_total_attempts": int(config["maximum_total_attempts"]),
        "ordered_item_ids": [row["item_id"] for row in merged],
    }


def collection_check(paths: StagePaths, config: dict, mock: bool) -> dict:
    if not mock:
        raise ValueError("Real mode is disabled for Stage A v3 release gate")
    freeze = freeze_check(paths, strict=True)
    summary = corpus_summary(paths, config)
    return {
        "mode": "mock",
        "freeze_ok": freeze["ok"],
        "planned_logical_ratings": summary["planned_logical_ratings"],
        "paid_collection_started": False,
    }


def cost_estimate(config: dict, mock: bool) -> dict:
    planned = int(config["planned_logical_ratings"])
    max_total = int(config["maximum_total_attempts"])
    return {
        "mode": "mock" if mock else "real-disabled",
        "planned_logical_ratings": planned,
        "maximum_total_attempts": max_total,
        "estimated_paid_requests": 0 if mock else max_total,
        "estimated_cost_usd": 0.0 if mock else None,
    }


def _read_jsonl(path: Path) -> list[dict]:
    if not path.exists():
        return []
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


def validate_experiment(paths: StagePaths, config: dict, experiment_id: str) -> dict:
    exp_paths = _paths_for_experiment(paths, experiment_id)
    plan = build_registered_logical_plan(paths, config)
    assert_registered_plan(paths, config, plan)

    logical_results = _read_jsonl(exp_paths["logical_results"])
    if len(logical_results) != len(plan):
        raise ValueError("Logical results count mismatch")

    plan_map = {entry["logical_key"]: entry for entry in plan}
    valid_rows: list[dict] = []
    duplicate_counter: dict[str, int] = {}

    for row in logical_results:
        logical_key = row["logical_key"]
        if logical_key not in plan_map:
            raise ValueError(f"Unknown logical key in results: {logical_key}")

        plan_entry = plan_map[logical_key]
        if row["item_id"] != plan_entry["item_id"]:
            raise ValueError(f"Item mismatch for logical key {logical_key}")

        if row["terminal_status"] != "TERMINAL_VALID":
            continue
        response = row.get("final_parsed_response")
        if not isinstance(response, dict):
            raise ValueError(f"Valid terminal rating missing parsed response: {logical_key}")
        validate_rating_like_schema(response)

        if response["item_id"] != plan_entry["item_id"]:
            raise ValueError(f"Response item id mismatch for {logical_key}")
        if not response["choice_bearer"].strip():
            raise ValueError(f"Empty choice_bearer for {logical_key}")
        if not response["choice_scope"].strip():
            raise ValueError(f"Empty choice_scope for {logical_key}")

        response_key = json.dumps(response, sort_keys=True)
        duplicate_counter[response_key] = duplicate_counter.get(response_key, 0) + 1

        flat = {
            "logical_key": logical_key,
            "item_id": response["item_id"],
            "replicate_index": plan_entry["replicate_index"],
            "evaluated_entity": response["evaluated_entity"],
            "relevant_target": response["relevant_target"],
            "intended_purpose": response["intended_purpose"],
            "domain": response["domain"],
            "target_scope": response["target_scope"],
            "target_contestability": response["target_contestability"],
            "choice_bearer": response["choice_bearer"],
            "choice_scope": response["choice_scope"],
            "goodness": response["goodness"],
            "notes": response["notes"],
        }
        for key in EIGHT_C_KEYS:
            flat[f"C_{key}"] = response["C_scores"][key]
        for key in CONTRADICTION_KEYS:
            flat[f"X_{key}"] = response["contradictions"][key]
        valid_rows.append(flat)

    if len(valid_rows) != int(config["planned_logical_ratings"]):
        raise ValueError("Expected 63 valid ratings after validation")

    fieldnames = list(valid_rows[0].keys())
    exp_paths["validated_csv"].parent.mkdir(parents=True, exist_ok=True)
    with exp_paths["validated_csv"].open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in valid_rows:
            writer.writerow(row)

    terminal_manifest = json.loads(exp_paths["terminal_manifest"].read_text(encoding="utf-8"))
    duplicates = sum(count - 1 for count in duplicate_counter.values() if count > 1)
    duplicate_rate = duplicates / len(valid_rows)

    summary = {
        "experiment_id": experiment_id,
        "planned_logical_ratings": int(config["planned_logical_ratings"]),
        "terminal_logical_ratings": terminal_manifest["logical_ratings_completed"],
        "valid_logical_ratings": len(valid_rows),
        "invalid_terminal_ratings": terminal_manifest["logical_ratings_invalid_terminal"],
        "failed_terminal_ratings": terminal_manifest["logical_ratings_failed_terminal"],
        "duplicate_output_count": duplicates,
        "duplicate_output_rate": duplicate_rate,
        "validated_csv": str(exp_paths["validated_csv"]),
    }
    _write_json(exp_paths["validation_summary"], summary)

    technical_lines = [
        "# TI Sigma Stage A v3 Technical Validation Report (Mock)",
        "",
        "> These ratings are synthetic engineering outputs generated to test pipeline behavior. They are not empirical observations and must not be used to evaluate the Eight-C framework.",
        "",
        f"- planned logical ratings: {summary['planned_logical_ratings']}",
        f"- terminal logical ratings: {summary['terminal_logical_ratings']}",
        f"- valid logical ratings: {summary['valid_logical_ratings']}",
        f"- invalid terminal ratings: {summary['invalid_terminal_ratings']}",
        f"- failed terminal ratings: {summary['failed_terminal_ratings']}",
        f"- duplicate output count: {summary['duplicate_output_count']}",
        f"- duplicate output rate: {summary['duplicate_output_rate']:.6f}",
        "",
        "This report is generated before sealing and remains immutable for seal verification.",
    ]
    exp_paths["report_md"].write_text("\n".join(technical_lines) + "\n", encoding="utf-8")
    return summary


def seal_experiment(
    paths: StagePaths,
    config: dict,
    experiment_id: str,
    dev_override: bool = False,
    verify_only: bool = False,
) -> dict:
    exp_paths = _paths_for_experiment(paths, experiment_id)
    seal_path = exp_paths["seal_manifest"]

    artifacts = {
        "raw_attempt_records": exp_paths["attempts_dir"],
        "logical_rating_results": exp_paths["logical_results"],
        "validated_ratings": exp_paths["validated_csv"],
        "terminal_manifest": exp_paths["terminal_manifest"],
        "config": paths.config_path,
        "freeze_manifest": paths.freeze_manifest_path,
        "prompt": paths.prompt_path,
        "schema": paths.schema_path,
        "items": paths.items_csv,
        "metadata": paths.metadata_csv,
        "preregistration_md": paths.prereg_md_path,
        "preregistration_yaml": paths.prereg_yaml_path,
        "technical_report": exp_paths["report_md"],
    }

    def hash_artifact(path: Path) -> str:
        if path.is_dir():
            parts = []
            for file in sorted(path.rglob("*")):
                if file.is_file():
                    rel = file.relative_to(path).as_posix()
                    parts.append(f"{rel}:{canonical_sha256(file)}")
            return hashlib.sha256("\n".join(parts).encode("utf-8")).hexdigest()
        return canonical_sha256(path)

    if verify_only:
        if not seal_path.exists():
            raise ValueError("Seal manifest not found for verification")
        existing = json.loads(seal_path.read_text(encoding="utf-8"))
        mismatches = []
        for name, meta in existing.get("artifacts", {}).items():
            expected = meta["sha256"]
            observed = hash_artifact(Path(meta["path"]))
            if observed != expected:
                mismatches.append({"artifact": name, "expected": expected, "observed": observed})
        return {
            "experiment_id": experiment_id,
            "verified": len(mismatches) == 0,
            "mismatches": mismatches,
        }

    if seal_path.exists() and not dev_override:
        raise ValueError("Seal manifest already exists. Use development override to replace.")

    for required_name, required_path in artifacts.items():
        if not required_path.exists():
            raise ValueError(f"Missing artifact for sealing: {required_name} -> {required_path}")

    sealed = {
        "experiment_id": experiment_id,
        "sealed_at_utc": _utc_now(),
        "hash_method": "sha256_file_bytes_utf8",
        "artifacts": {},
    }
    for name, artifact_path in artifacts.items():
        sealed["artifacts"][name] = {
            "path": str(artifact_path),
            "sha256": hash_artifact(artifact_path),
        }

    _write_json(seal_path, sealed)
    return {
        "experiment_id": experiment_id,
        "seal_manifest": str(seal_path),
        "artifact_count": len(sealed["artifacts"]),
    }


def build_engineering_report(paths: StagePaths, config: dict, experiment_id: str) -> dict:
    exp_paths = _paths_for_experiment(paths, experiment_id)
    terminal = json.loads(exp_paths["terminal_manifest"].read_text(encoding="utf-8"))
    validation = json.loads(exp_paths["validation_summary"].read_text(encoding="utf-8"))
    seal = json.loads(exp_paths["seal_manifest"].read_text(encoding="utf-8"))

    planned = terminal["planned_logical_ratings"]
    first_attempts = terminal["first_attempts"]
    retries = terminal["retry_attempts"]
    total_attempts = terminal["total_api_attempts"]
    first_attempt_validity_rate = (planned - retries) / planned if planned else 0.0
    eventual_validity_rate = terminal["logical_ratings_valid"] / planned if planned else 0.0

    report = {
        "planned_logical_ratings": planned,
        "completed_logical_ratings": terminal["logical_ratings_completed"],
        "valid_logical_ratings": terminal["logical_ratings_valid"],
        "invalid_terminal_ratings": terminal["logical_ratings_invalid_terminal"],
        "failed_terminal_ratings": terminal["logical_ratings_failed_terminal"],
        "first_attempts": first_attempts,
        "retries": retries,
        "total_attempts": total_attempts,
        "first_attempt_validity_rate": first_attempt_validity_rate,
        "eventual_validity_rate": eventual_validity_rate,
        "schema_failures": retries,
        "parse_failures": 0,
        "duplicate_output_rate": validation["duplicate_output_rate"],
        "seed_strategy": config["seed_strategy"],
        "artifact_hashes": seal["artifacts"],
        "synthetic_disclaimer": "These ratings are synthetic engineering outputs generated to test pipeline behavior. They are not empirical observations and must not be used to evaluate the Eight-C framework.",
    }

    _write_json(exp_paths["report_json"], report)
    return report
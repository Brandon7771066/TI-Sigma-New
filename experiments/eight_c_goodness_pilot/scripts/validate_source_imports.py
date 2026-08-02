#!/usr/bin/env python3
"""Validate source imports against source_import_manifest.yaml.

This script is read-only with respect to sources and provenance inputs.
It only writes validation reports under results/reports.
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Dict, List, Tuple


ALLOWED_STATUSES = {
    "MISSING",
    "PRESENT_UNVERIFIED",
    "PRESENT_HASHED",
    "DUPLICATE_CONTENT",
    "INVALID_FILENAME",
    "EMPTY",
    "READY_FOR_REVIEW",
}


def load_manifest(path: Path) -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    header = {key: value for key, value in data.items() if key != "sources"}
    return header, data.get("sources", [])


def iter_expected_files(source: Dict[str, Any]) -> List[Dict[str, Any]]:
    return list(source.get("files", []))


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def iso_mtime(path: Path) -> str:
    return dt.datetime.fromtimestamp(path.stat().st_mtime, dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def extract_part_number(filename: str) -> int:
    match = re.search(r"_part_(\d+)", filename, re.IGNORECASE)
    if match:
        return int(match.group(1))
    return 1


def source_inbox_dir(repo_root: Path, source: Dict[str, Any]) -> Path | None:
    files = iter_expected_files(source)
    if not files:
        return None
    destination = Path(str(files[0]["import_destination"]).replace("\\", "/"))
    return repo_root / destination.parent


def discover_present_files(source: Dict[str, Any], repo_root: Path) -> Tuple[List[Path], List[Path], Dict[str, Dict[str, Any]]]:
    expected_files = iter_expected_files(source)
    manifest_lookup = {str(item["expected_filename"]): item for item in expected_files}
    regex = re.compile(str(source.get("segment_filename_regex", "^$")))
    inbox_dir = source_inbox_dir(repo_root, source)

    actual_files: List[Path] = []
    wrong_name_candidates: List[Path] = []
    if inbox_dir is None or not inbox_dir.exists():
        return actual_files, wrong_name_candidates, manifest_lookup

    for item in sorted(inbox_dir.iterdir()):
        if not item.is_file():
            continue
        allowed = item.name in manifest_lookup or regex.match(item.name) is not None
        if allowed:
            actual_files.append(item)
        elif item.name.startswith(f"{source.get('source_id', '')}_"):
            wrong_name_candidates.append(item)

    actual_files.sort(key=lambda path: (extract_part_number(path.name), path.name.lower()))
    return actual_files, wrong_name_candidates, manifest_lookup


def file_detail(path: Path, repo_root: Path, manifest_item: Dict[str, Any], source: Dict[str, Any]) -> Dict[str, Any]:
    part_number = manifest_item.get("part_number") or extract_part_number(path.name)
    claimed_hash = str(manifest_item.get("claimed_original_hash", "") or "")
    observed_hash = sha256_file(path)
    hash_agreement = ""
    if claimed_hash:
        hash_agreement = "MATCH" if claimed_hash == observed_hash else "MISMATCH"

    return {
        "source_id": source.get("source_id", ""),
        "source_name": source.get("source_name", ""),
        "actual_filename": path.name,
        "expected_filename": manifest_item.get("expected_filename", path.name),
        "import_destination": str(path.relative_to(repo_root)).replace("\\", "/"),
        "part_number": int(part_number),
        "total_parts_if_known": manifest_item.get("total_parts_if_known", ""),
        "conversation_start_date": manifest_item.get("conversation_start_date", ""),
        "conversation_end_date": manifest_item.get("conversation_end_date", ""),
        "first_message_excerpt": manifest_item.get("first_message_excerpt", ""),
        "last_message_excerpt": manifest_item.get("last_message_excerpt", ""),
        "size_bytes": path.stat().st_size,
        "modified_utc": iso_mtime(path),
        "sha256": observed_hash,
        "claimed_original_hash": claimed_hash,
        "observed_import_hash": observed_hash,
        "hash_agreement": hash_agreement,
        "review_status": manifest_item.get("review_status", source.get("review_status", "NOT_RECEIVED")),
        "content_status": manifest_item.get("content_status", source.get("content_status", "pending")),
    }


def classify(source: Dict[str, Any], repo_root: Path) -> Dict[str, Any]:
    source_id = str(source.get("source_id", ""))
    actual_files, wrong_name_candidates, manifest_lookup = discover_present_files(source, repo_root)
    details: List[Dict[str, Any]] = []

    record: Dict[str, Any] = {
        "source_id": source_id,
        "source_name": source.get("source_name", ""),
        "source_type": source.get("source_type", ""),
        "required": bool(source.get("required", False)),
        "reconstruction_allowed": bool(source.get("reconstruction_allowed", False)),
        "verbatim_recovery_required": bool(source.get("verbatim_recovery_required", False)),
        "received": bool(source.get("received", False)),
        "content_status": source.get("content_status", "pending"),
        "review_status": source.get("review_status", "NOT_RECEIVED"),
        "supports_segmented_imports": bool(source.get("supports_segmented_imports", False)),
        "file_count": 0,
        "status": None,
        "wrong_name_candidates": [str(path.relative_to(repo_root)).replace("\\", "/") for path in wrong_name_candidates],
        "segment_order": [],
        "files": details,
        "notes": source.get("notes", ""),
    }

    if not actual_files:
        record["status"] = "INVALID_FILENAME" if wrong_name_candidates else "MISSING"
        return record

    for path in actual_files:
        manifest_item = manifest_lookup.get(path.name, {})
        details.append(file_detail(path, repo_root, manifest_item, source))

    record["file_count"] = len(details)
    record["segment_order"] = [detail["actual_filename"] for detail in details]

    if any(detail["size_bytes"] == 0 or detail["size_bytes"] < 32 for detail in details):
        record["status"] = "EMPTY"
        return record

    if any(not detail["sha256"] for detail in details):
        record["status"] = "PRESENT_UNVERIFIED"
        return record

    record["status"] = "READY_FOR_REVIEW" if record["review_status"] == "READY_FOR_REVIEW" else "PRESENT_HASHED"
    return record


def apply_duplicate_detection(records: List[Dict[str, Any]]) -> None:
    hash_to_files: Dict[str, List[Tuple[str, str]]] = {}
    for record in records:
        for detail in record["files"]:
            if detail["sha256"]:
                hash_to_files.setdefault(detail["sha256"], []).append((record["source_id"], detail["actual_filename"]))

    for record in records:
        duplicate_found = False
        for detail in record["files"]:
            candidates = hash_to_files.get(detail["sha256"], [])
            detail["duplicate_matches"] = [f"{sid}:{fname}" for sid, fname in candidates] if len(candidates) > 1 else []
            duplicate_found = duplicate_found or len(candidates) > 1
        if duplicate_found:
            record["status"] = "DUPLICATE_CONTENT"


def markdown_report(summary: Dict[str, Any], records: List[Dict[str, Any]]) -> str:
    lines: List[str] = []
    lines.append("# Source Import Validation")
    lines.append("")
    lines.append(f"Generated UTC: {summary['generated_utc']}")
    lines.append(f"Manifest: {summary['manifest_path']}")
    lines.append("")
    lines.append("## Status Counts")
    for key, value in summary["status_counts"].items():
        lines.append(f"- {key}: {value}")
    lines.append(f"- SOURCE_GROUPS_RECEIVED: {summary['source_groups_received']}")
    lines.append("")
    lines.append("## Per-Source Results")
    lines.append("")
    lines.append("| source_id | status | file_count | segmented | segment_order |")
    lines.append("|---|---|---:|---|---|")
    for record in records:
        lines.append(
            f"| {record['source_id']} | {record['status']} | {record['file_count']} | {str(record['supports_segmented_imports']).lower()} | {', '.join(record['segment_order'])} |"
        )
        if record["wrong_name_candidates"]:
            lines.append(f"| {record['source_id']} notes | wrong-name candidates |  |  | {', '.join(record['wrong_name_candidates'])} |")
        for detail in record["files"]:
            lines.append(f"| {record['source_id']} file | {detail['actual_filename']} | {detail['size_bytes']} | part {detail['part_number']} | {detail['sha256']} |")
    lines.append("")
    lines.append("## Notes")
    lines.append("- This validation does not edit manifest, ledger, or imported sources.")
    lines.append("- Multipart sources are preserved as independent files and only grouped logically for validation.")
    return "\n".join(lines) + "\n"


def main() -> int:
    script_path = Path(__file__).resolve()
    pilot_root = script_path.parent.parent
    repo_root = pilot_root.parent.parent

    manifest_path = pilot_root / "docs" / "provenance" / "source_import_manifest.yaml"
    reports_dir = pilot_root / "results" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    header, sources = load_manifest(manifest_path)
    records = [classify(source, repo_root) for source in sources]
    apply_duplicate_detection(records)

    status_counts = {status: 0 for status in sorted(ALLOWED_STATUSES)}
    for record in records:
        if record["status"] not in status_counts:
            status_counts[record["status"]] = 0
        status_counts[record["status"]] += 1

    summary = {
        "generated_utc": dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
        "manifest_header": header,
        "manifest_path": str(manifest_path.relative_to(repo_root)).replace("\\", "/"),
        "report_json": "experiments/eight_c_goodness_pilot/results/reports/source_import_validation.json",
        "report_markdown": "experiments/eight_c_goodness_pilot/results/reports/source_import_validation.md",
        "status_counts": status_counts,
        "source_groups_received": sum(1 for record in records if record["file_count"] > 0),
        "all_statuses_allowed": all(record["status"] in ALLOWED_STATUSES for record in records),
    }

    payload = {"summary": summary, "sources": records}
    json_out = reports_dir / "source_import_validation.json"
    md_out = reports_dir / "source_import_validation.md"
    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    md_out.write_text(markdown_report(summary, records), encoding="utf-8")

    print("SOURCE_IMPORT_VALIDATION_COMPLETE")
    print(f"JSON: {summary['report_json']}")
    print(f"MD: {summary['report_markdown']}")
    print(f"SOURCE_GROUPS_RECEIVED: {summary['source_groups_received']}")
    print("STATUS_COUNTS:")
    for key, value in status_counts.items():
        print(f"  {key}: {value}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

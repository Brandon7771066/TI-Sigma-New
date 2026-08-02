#!/usr/bin/env python3
"""Validate source imports against source_import_manifest.yaml.

This script is read-only with respect to sources and provenance inputs.
It only writes validation reports under results/reports.
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
from pathlib import Path
from typing import Any, Dict, List, Tuple


def parse_scalar(raw: str) -> Any:
    value = raw.strip()
    if value.startswith('"') and value.endswith('"') and len(value) >= 2:
        return value[1:-1]
    if value.lower() == "true":
        return True
    if value.lower() == "false":
        return False
    return value


def load_manifest(path: Path) -> Tuple[Dict[str, Any], List[Dict[str, Any]]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    header: Dict[str, Any] = {}
    sources: List[Dict[str, Any]] = []
    current: Dict[str, Any] | None = None
    in_topics = False

    for raw in lines:
        if not raw.strip() or raw.strip().startswith("#"):
            continue

        if raw.startswith("sources:"):
            continue

        if raw.startswith("  - source_id:"):
            if current is not None:
                sources.append(current)
            current = {"expected_topics": []}
            key, val = raw.strip()[2:].split(":", 1)
            current[key.strip()] = parse_scalar(val)
            in_topics = False
            continue

        if current is None:
            if ":" in raw:
                key, val = raw.split(":", 1)
                header[key.strip()] = parse_scalar(val)
            continue

        stripped = raw.strip()
        if stripped == "expected_topics:":
            in_topics = True
            continue

        if in_topics and stripped.startswith("- "):
            current["expected_topics"].append(stripped[2:].strip())
            continue

        in_topics = False
        if ":" in stripped:
            key, val = stripped.split(":", 1)
            current[key.strip()] = parse_scalar(val)

    if current is not None:
        sources.append(current)

    return header, sources


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def iso_mtime(path: Path) -> str:
    return dt.datetime.utcfromtimestamp(path.stat().st_mtime).replace(microsecond=0).isoformat() + "Z"


def classify(entry: Dict[str, Any], repo_root: Path) -> Dict[str, Any]:
    destination = Path(str(entry["import_destination"]).replace("\\", "/"))
    expected_filename = str(entry["expected_filename"])
    source_id = str(entry["source_id"])
    expected_path = repo_root / destination
    destination_dir = expected_path.parent

    record: Dict[str, Any] = {
        "source_id": source_id,
        "source_name": entry.get("source_name", ""),
        "expected_filename": expected_filename,
        "import_destination": str(destination).replace("\\", "/"),
        "required": bool(entry.get("required", False)),
        "reconstruction_allowed": bool(entry.get("reconstruction_allowed", False)),
        "verbatim_recovery_required": bool(entry.get("verbatim_recovery_required", False)),
        "received": bool(entry.get("received", False)),
        "content_status": entry.get("content_status", "pending"),
        "exists": expected_path.exists(),
        "size_bytes": None,
        "modified_utc": None,
        "sha256": None,
        "status": None,
        "wrong_name_candidates": [],
        "notes": entry.get("notes", ""),
    }

    candidates: List[Path] = []
    if destination_dir.exists():
        candidates = sorted(p for p in destination_dir.glob(f"{source_id}_*") if p.is_file())
    record["wrong_name_candidates"] = [str(p.relative_to(repo_root)).replace("\\", "/") for p in candidates if p.name != expected_filename]

    if not expected_path.exists():
        if record["wrong_name_candidates"]:
            record["status"] = "INVALID_FILENAME"
        else:
            record["status"] = "MISSING"
        return record

    record["size_bytes"] = expected_path.stat().st_size
    record["modified_utc"] = iso_mtime(expected_path)

    if record["size_bytes"] == 0 or record["size_bytes"] < 32:
        record["status"] = "EMPTY"
        return record

    try:
        record["sha256"] = sha256_file(expected_path)
    except OSError:
        record["status"] = "PRESENT_UNVERIFIED"
        return record

    record["status"] = "PRESENT_HASHED"
    return record


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
    lines.append("")
    lines.append("## Per-Source Results")
    lines.append("")
    lines.append("| source_id | status | exists | size_bytes | sha256 | import_destination |")
    lines.append("|---|---|---:|---:|---|---|")
    for r in records:
        sha = r["sha256"] if r["sha256"] else ""
        size = "" if r["size_bytes"] is None else str(r["size_bytes"])
        lines.append(
            f"| {r['source_id']} | {r['status']} | {str(r['exists']).lower()} | {size} | {sha} | {r['import_destination']} |"
        )
        if r["wrong_name_candidates"]:
            lines.append(f"| {r['source_id']} notes | wrong-name candidates |  |  |  | {', '.join(r['wrong_name_candidates'])} |")

    lines.append("")
    lines.append("## Notes")
    lines.append("- This validation does not edit manifest, ledger, or imported sources.")
    lines.append("- READY_FOR_REVIEW requires non-empty content, valid name, unique hash, and a successful hash read.")
    return "\n".join(lines) + "\n"


def main() -> int:
    script_path = Path(__file__).resolve()
    pilot_root = script_path.parent.parent
    repo_root = pilot_root.parent.parent

    manifest_path = pilot_root / "docs" / "provenance" / "source_import_manifest.yaml"
    reports_dir = pilot_root / "results" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    header, entries = load_manifest(manifest_path)

    records = [classify(entry, repo_root) for entry in entries]

    hash_to_ids: Dict[str, List[str]] = {}
    for r in records:
        if r["sha256"]:
            hash_to_ids.setdefault(r["sha256"], []).append(r["source_id"])

    for r in records:
        if r["sha256"] and len(hash_to_ids.get(r["sha256"], [])) > 1:
            r["status"] = "DUPLICATE_CONTENT"

    for r in records:
        if r["status"] == "PRESENT_HASHED":
            if r["received"] and r["content_status"] not in {"pending", ""}:
                r["status"] = "READY_FOR_REVIEW"

    allowed = {
        "MISSING",
        "PRESENT_UNVERIFIED",
        "PRESENT_HASHED",
        "DUPLICATE_CONTENT",
        "INVALID_FILENAME",
        "EMPTY",
        "READY_FOR_REVIEW",
    }

    status_counts = {k: 0 for k in sorted(allowed)}
    for r in records:
        if r["status"] not in status_counts:
            status_counts[r["status"]] = 0
        status_counts[r["status"]] += 1

    summary = {
        "generated_utc": dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
        "manifest_header": header,
        "manifest_path": str(manifest_path.relative_to(repo_root)).replace("\\", "/"),
        "report_json": "experiments/eight_c_goodness_pilot/results/reports/source_import_validation.json",
        "report_markdown": "experiments/eight_c_goodness_pilot/results/reports/source_import_validation.md",
        "status_counts": status_counts,
        "all_statuses_allowed": all(r["status"] in allowed for r in records),
    }

    payload = {"summary": summary, "sources": records}

    json_out = reports_dir / "source_import_validation.json"
    md_out = reports_dir / "source_import_validation.md"

    json_out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    md_out.write_text(markdown_report(summary, records), encoding="utf-8")

    print("SOURCE_IMPORT_VALIDATION_COMPLETE")
    print(f"JSON: {summary['report_json']}")
    print(f"MD: {summary['report_markdown']}")
    print("STATUS_COUNTS:")
    for k, v in status_counts.items():
        print(f"  {k}: {v}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
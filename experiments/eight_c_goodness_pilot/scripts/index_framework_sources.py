#!/usr/bin/env python3
"""Index imported source files into framework passage candidates.

This script is read-only for source and canonical files. It only writes
candidate reports under results/reports.
"""

from __future__ import annotations

import csv
import datetime as dt
import re
from pathlib import Path
from typing import Any, Dict, Iterable, List, Sequence, Tuple


SEARCH_TERMS = [
    "GILE",
    "Goodness",
    "Intuition",
    "Love",
    "Elegance",
    "HEM",
    "Coherence",
    "Consistency",
    "Continuity",
    "Concreteness",
    "Completion",
    "Criticality",
    "Closeness",
    "Choice",
    "contradiction",
    "Tralse",
    "scale",
    "binding",
    "certainty",
    "instantiation",
    "tangibility",
    "mechanism",
    "footprint",
    "form",
    "complexity",
]

ROW_HEADERS = [
    "passage_id",
    "source_id",
    "source_filename",
    "source_location",
    "conversation_date",
    "line_start",
    "line_end",
    "topic",
    "construct",
    "version_status",
    "content_status",
    "canonical_relevance",
    "conflict_ids",
    "quoted_text",
    "summary",
    "review_notes",
]


def parse_scalar(raw: str) -> Any:
    value = raw.strip()
    if value.startswith('"') and value.endswith('"') and len(value) >= 2:
        return value[1:-1]
    if value.lower() == "true":
        return True
    if value.lower() == "false":
        return False
    return value


def load_manifest(path: Path) -> List[Dict[str, Any]]:
    lines = path.read_text(encoding="utf-8").splitlines()
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

    return sources


def detect_terms(text: str, terms: Sequence[str]) -> List[str]:
    found: List[str] = []
    lowered = text.lower()
    for term in terms:
        if term.lower() in lowered:
            found.append(term)
    return found


def annotate_lines(lines: Sequence[str]) -> Tuple[List[str], List[str]]:
    heading_at: List[str] = [""] * (len(lines) + 1)
    turn_at: List[str] = [""] * (len(lines) + 1)
    heading = ""
    turn = ""
    turn_re = re.compile(r"^\s*(user|assistant|system|human|ai)\s*[:\-]", re.IGNORECASE)

    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("#"):
            heading = stripped.lstrip("#").strip()
        turn_match = turn_re.match(stripped)
        if turn_match:
            turn = turn_match.group(1).upper()
        heading_at[idx] = heading
        turn_at[idx] = turn

    return heading_at, turn_at


def build_passages(lines: Sequence[str]) -> List[Tuple[int, int, str]]:
    passages: List[Tuple[int, int, str]] = []
    start = None

    for idx, line in enumerate(lines, start=1):
        if line.strip() and start is None:
            start = idx
        if (not line.strip()) and start is not None:
            end = idx - 1
            text = "\n".join(lines[start - 1 : end])
            passages.append((start, end, text))
            start = None

    if start is not None:
        end = len(lines)
        text = "\n".join(lines[start - 1 : end])
        passages.append((start, end, text))

    return passages


def source_files_from_manifest(repo_root: Path, sources: Iterable[Dict[str, Any]]) -> List[Tuple[Dict[str, Any], Path]]:
    files: List[Tuple[Dict[str, Any], Path]] = []
    for src in sources:
        destination = Path(str(src.get("import_destination", "")).replace("\\", "/"))
        if not destination.suffix.lower() in {".md", ".txt"}:
            continue
        full_path = repo_root / destination
        if full_path.exists() and full_path.is_file():
            files.append((src, full_path))
    return files


def write_csv(path: Path, rows: List[Dict[str, str]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=ROW_HEADERS)
        writer.writeheader()
        writer.writerows(rows)


def write_markdown(path: Path, rows: List[Dict[str, str]], scanned_files: List[str], generated_utc: str) -> None:
    lines: List[str] = []
    lines.append("# Source Passage Candidates")
    lines.append("")
    lines.append(f"Generated UTC: {generated_utc}")
    lines.append("")

    if not scanned_files:
        lines.append("No source files currently available.")
        lines.append("")
        lines.append("Extracted passages: 0")
    else:
        lines.append("## Scanned Files")
        for item in scanned_files:
            lines.append(f"- {item}")
        lines.append("")
        lines.append(f"Extracted passages: {len(rows)}")
        lines.append("")
        lines.append("## Candidate Rows")
        lines.append("")
        lines.append("| passage_id | source_id | line_start | line_end | construct | topic |")
        lines.append("|---|---|---:|---:|---|---|")
        for row in rows:
            lines.append(
                f"| {row['passage_id']} | {row['source_id']} | {row['line_start']} | {row['line_end']} | {row['construct']} | {row['topic']} |"
            )

    lines.append("")
    lines.append("All extracted passages are labeled CANDIDATE_REVIEW_REQUIRED.")
    lines.append("No canonical definitions were selected automatically.")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    script_path = Path(__file__).resolve()
    pilot_root = script_path.parent.parent
    repo_root = pilot_root.parent.parent
    manifest_path = pilot_root / "docs" / "provenance" / "source_import_manifest.yaml"
    report_dir = pilot_root / "results" / "reports"
    report_dir.mkdir(parents=True, exist_ok=True)

    sources = load_manifest(manifest_path)
    present_sources = source_files_from_manifest(repo_root, sources)

    rows: List[Dict[str, str]] = []
    scanned_files: List[str] = []
    counter = 1

    for src, full_path in present_sources:
        rel = str(full_path.relative_to(repo_root)).replace("\\", "/")
        scanned_files.append(rel)
        text = full_path.read_text(encoding="utf-8", errors="replace")
        lines = text.splitlines()
        heading_at, turn_at = annotate_lines(lines)
        passages = build_passages(lines)

        for line_start, line_end, quoted in passages:
            found_terms = detect_terms(quoted, SEARCH_TERMS)
            if not found_terms:
                continue

            topic = heading_at[line_start] or turn_at[line_start] or "UNCLASSIFIED"
            for term in found_terms:
                rows.append(
                    {
                        "passage_id": f"CAND-{counter:05d}",
                        "source_id": str(src.get("source_id", "")),
                        "source_filename": str(src.get("expected_filename", full_path.name)),
                        "source_location": rel,
                        "conversation_date": "PENDING_SOURCE_IMPORT",
                        "line_start": str(line_start),
                        "line_end": str(line_end),
                        "topic": topic,
                        "construct": term,
                        "version_status": "UNRESOLVED",
                        "content_status": "VERBATIM",
                        "canonical_relevance": "CANDIDATE_REVIEW_REQUIRED",
                        "conflict_ids": "",
                        "quoted_text": quoted,
                        "summary": f"Candidate passage containing term '{term}'.",
                        "review_notes": "CANDIDATE_REVIEW_REQUIRED",
                    }
                )
                counter += 1

    generated_utc = dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    csv_out = report_dir / "source_passage_candidates.csv"
    md_out = report_dir / "source_passage_candidates.md"

    write_csv(csv_out, rows)
    write_markdown(md_out, rows, scanned_files, generated_utc)

    print("FRAMEWORK_SOURCE_INDEXING_COMPLETE")
    print("CSV: experiments/eight_c_goodness_pilot/results/reports/source_passage_candidates.csv")
    print("MD: experiments/eight_c_goodness_pilot/results/reports/source_passage_candidates.md")
    print(f"SOURCE_FILES_SCANNED: {len(scanned_files)}")
    print(f"PASSAGE_CANDIDATES: {len(rows)}")
    if not scanned_files:
        print("NO_SOURCE_FILES_AVAILABLE")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
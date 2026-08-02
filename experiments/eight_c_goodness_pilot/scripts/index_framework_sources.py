#!/usr/bin/env python3
"""Index imported source files into framework passage candidates.

This script is read-only for source and canonical files. It only writes
candidate reports under results/reports.
"""

from __future__ import annotations

import csv
import datetime as dt
import json
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

REVISION_PHRASES = {
    "POTENTIAL_REVISION": ["actually", "instead", "correction", "clarification", "not quite", "keep in mind", "one more thing"],
    "POTENTIAL_REVERSAL": ["i disagree", "we are changing", "the seventh c", "the eighth c"],
    "CATEGORY_BOUNDARY_UPDATE": ["belongs to hem", "belongs to gile", "the definition should be"],
}

PASSAGE_HEADERS = [
    "passage_id",
    "source_id",
    "source_part",
    "source_filename",
    "source_location",
    "conversation_date",
    "line_start",
    "line_end",
    "topic",
    "construct",
    "version_status",
    "content_status",
    "speaker",
    "authorship_status",
    "user_approval_status",
    "candidate_flags",
    "canonical_relevance",
    "conflict_ids",
    "quoted_text",
    "summary",
    "review_notes",
]

DEFINITION_HEADERS = [
    "construct",
    "candidate_definition",
    "source_id",
    "source_part",
    "line_start",
    "line_end",
    "speaker",
    "user_approval_status",
    "version_status",
    "hem_overlap",
    "intuition_overlap",
    "love_overlap",
    "elegance_overlap",
    "current_candidate",
    "review_notes",
]

BOUNDARY_HEADERS = [
    "construct",
    "primary_category",
    "related_categories",
    "proposed_relationship",
    "scale_level",
    "source_support",
    "status",
    "review_notes",
]

SCALE_HEADERS = [
    "construct",
    "physical",
    "chemical",
    "biological",
    "cognitive",
    "interpersonal",
    "institutional",
    "societal",
    "source_id",
    "source_lines",
    "status",
    "notes",
]

SPEC_HEADERS = [
    "spec_field",
    "candidate_value",
    "source_id",
    "source_part",
    "line_start",
    "line_end",
    "speaker",
    "user_approval_status",
    "status",
    "review_notes",
]

ITEM_HEADERS = [
    "candidate_item_id",
    "title",
    "scenario_text",
    "source_id",
    "source_part",
    "line_start",
    "line_end",
    "completeness",
    "possible_duplicate",
    "intended_contrast",
    "choice_bearer",
    "choice_scope",
    "notes",
]

DEFINITION_CONSTRUCTS = [
    "Coherence",
    "Consistency",
    "Continuity",
    "Concreteness",
    "Completion",
    "Criticality",
    "Closeness",
    "Choice",
    "Goodness",
]

BOUNDARY_CONSTRUCTS = [
    "Goodness",
    "Intuition",
    "Love",
    "Elegance",
    "HEM Footprint",
    "HEM Form",
    "HEM Complexity",
    "HEM Concrete Mechanisms",
    "instantiation",
    "tangibility",
    "binding",
    "certainty",
    "beauty",
    "simplicity",
    "critical accuracy",
    "Choice",
]

SPEC_FIELDS = [
    "Goodness scalar definition",
    "Eight-C operational definitions",
    "rating scale",
    "independent Goodness score",
    "contradiction taxonomy",
    "evaluated entity",
    "relevant target",
    "intended purpose",
    "target scope",
    "target contestability",
    "Choice bearer",
    "Choice scope",
    "Choice alignment",
    "Stage A sample size",
    "Stage B sample size",
    "retry rule",
    "stopping rule",
    "reliability analyses",
    "mutual-information analyses",
    "ablation analyses",
    "effective-rank analyses",
    "residual-exhaustion analyses",
]

SCALE_WORDS = ["physical", "chemical", "biological", "cognitive", "interpersonal", "institutional", "societal"]


def load_manifest(path: Path) -> List[Dict[str, Any]]:
    return json.loads(path.read_text(encoding="utf-8")).get("sources", [])


def iter_expected_files(source: Dict[str, Any]) -> List[Dict[str, Any]]:
    return list(source.get("files", []))


def extract_part_number(filename: str) -> int:
    match = re.search(r"_part_(\d+)", filename, re.IGNORECASE)
    if match:
        return int(match.group(1))
    return 1


def source_inbox_dir(repo_root: Path, source: Dict[str, Any]) -> Path | None:
    files = iter_expected_files(source)
    if not files:
        return None
    return repo_root / Path(str(files[0]["import_destination"]).replace("\\", "/")).parent


def source_files_from_manifest(repo_root: Path, sources: Iterable[Dict[str, Any]]) -> List[Tuple[Dict[str, Any], Dict[str, Any], Path]]:
    records: List[Tuple[Dict[str, Any], Dict[str, Any], Path]] = []
    for source in sources:
        inbox_dir = source_inbox_dir(repo_root, source)
        if inbox_dir is None or not inbox_dir.exists():
            continue
        expected = {item["expected_filename"]: item for item in iter_expected_files(source)}
        regex = re.compile(str(source.get("segment_filename_regex", "^$")))
        for path in sorted(inbox_dir.iterdir(), key=lambda p: (extract_part_number(p.name), p.name.lower())):
            if not path.is_file() or path.suffix.lower() not in {".md", ".txt"}:
                continue
            if path.name in expected or regex.match(path.name):
                records.append((source, expected.get(path.name, {}), path))
    return records


def detect_terms(text: str, terms: Sequence[str]) -> List[str]:
    lowered = text.lower()
    return [term for term in terms if term.lower() in lowered]


def annotate_lines(lines: Sequence[str]) -> Tuple[List[str], List[str], List[str]]:
    heading_at: List[str] = [""] * (len(lines) + 1)
    speaker_at: List[str] = [""] * (len(lines) + 1)
    turn_at: List[str] = [""] * (len(lines) + 1)
    heading = ""
    speaker = ""
    turn_re = re.compile(r"^\s*(user|assistant|system|human|ai|chatgpt|perplexity|vs code agent|vs_code_agent)\s*[:\-]", re.IGNORECASE)

    for idx, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped.startswith("#"):
            heading = stripped.lstrip("#").strip()
        match = turn_re.match(stripped)
        if match:
            raw = match.group(1).lower()
            speaker = {
                "user": "USER",
                "human": "USER",
                "assistant": "CHATGPT",
                "ai": "CHATGPT",
                "chatgpt": "CHATGPT",
                "perplexity": "PERPLEXITY",
                "vs code agent": "VS_CODE_AGENT",
                "vs_code_agent": "VS_CODE_AGENT",
                "system": "UNKNOWN",
            }.get(raw, "UNKNOWN")
        heading_at[idx] = heading
        speaker_at[idx] = speaker
        turn_at[idx] = speaker
    return heading_at, speaker_at, turn_at


def build_passages(lines: Sequence[str]) -> List[Tuple[int, int, str]]:
    passages: List[Tuple[int, int, str]] = []
    start: int | None = None
    for idx, line in enumerate(lines, start=1):
        if line.strip() and start is None:
            start = idx
        if not line.strip() and start is not None:
            end = idx - 1
            passages.append((start, end, "\n".join(lines[start - 1:end])))
            start = None
    if start is not None:
        passages.append((start, len(lines), "\n".join(lines[start - 1:len(lines)])))
    return passages


def detect_speakers(speaker_at: Sequence[str], start: int, end: int) -> List[str]:
    values = {speaker_at[idx] for idx in range(start, end + 1) if speaker_at[idx]}
    return sorted(values)


def derive_authorship_status(speakers: Sequence[str]) -> str:
    values = set(speakers)
    if not values:
        return "UNKNOWN"
    if values == {"USER"}:
        return "USER_AUTHORED"
    if values.issubset({"CHATGPT", "PERPLEXITY", "VS_CODE_AGENT", "UNKNOWN"}) and values & {"CHATGPT", "PERPLEXITY", "VS_CODE_AGENT"}:
        return "AI_AUTHORED"
    return "MIXED"


def derive_user_approval_status(text: str, speaker: str) -> str:
    lowered = text.lower()
    if speaker == "USER":
        if any(phrase in lowered for phrase in ["actually", "i disagree", "not quite", "correction", "clarification", "instead", "we are changing"]):
            return "REJECTED_OR_CORRECTED"
        if any(phrase in lowered for phrase in ["approved", "use this", "that's correct", "this is correct", "exactly right"]):
            return "EXPLICITLY_APPROVED"
    return "NOT_EVALUATED"


def detect_candidate_flags(text: str) -> str:
    lowered = text.lower()
    flags: List[str] = []
    for label, phrases in REVISION_PHRASES.items():
        if any(phrase in lowered for phrase in phrases):
            flags.append(label)
    return ";".join(flags)


def write_csv(path: Path, headers: Sequence[str], rows: List[Dict[str, str]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(headers))
        writer.writeheader()
        writer.writerows(rows)


def write_markdown(path: Path, rows: List[Dict[str, str]], scanned_files: List[str], generated_utc: str) -> None:
    lines: List[str] = ["# Source Passage Candidates", "", f"Generated UTC: {generated_utc}", ""]
    if not scanned_files:
        lines.extend(["No source files currently available.", "", "Extracted passages: 0"])
    else:
        lines.append("## Scanned Files")
        lines.extend([f"- {item}" for item in scanned_files])
        lines.extend(["", f"Extracted passages: {len(rows)}", "", "## Candidate Rows", "", "| passage_id | source_id | source_part | construct | speaker | flags |", "|---|---|---:|---|---|---|"])
        for row in rows:
            lines.append(f"| {row['passage_id']} | {row['source_id']} | {row['source_part']} | {row['construct']} | {row['speaker']} | {row['candidate_flags']} |")
    lines.extend(["", "All extracted passages are labeled CANDIDATE_REVIEW_REQUIRED.", "No canonical definitions were selected automatically."])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def canonical_boundary_rows() -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    for construct in BOUNDARY_CONSTRUCTS:
        if construct == "tangibility":
            proposed = "Concreteness concerns tangibility or determinate intelligibility with minimal fuzziness."
            primary = "GILE-G"
            related = "HEM"
        elif construct == "instantiation":
            proposed = "Ontological instantiation belongs to HEM."
            primary = "HEM"
            related = "GILE-G"
        elif construct == "binding":
            proposed = "Love concerns internal and external binding."
            primary = "GILE-L"
            related = "Goodness|HEM"
        elif construct == "certainty":
            proposed = "Intuition concerns conscious certainty."
            primary = "GILE-I"
            related = "Goodness|HEM"
        elif construct in {"beauty", "simplicity"}:
            proposed = "Elegance concerns beauty, simplicity, economy, ideal form, and related formal or aesthetic qualities."
            primary = "GILE-E"
            related = "Goodness|HEM"
        elif construct == "Choice":
            proposed = "Choice remains a Goodness component until imported sources refine the operational boundary."
            primary = "GILE-G"
            related = "Intuition|Love|HEM"
        else:
            proposed = "NOT_FOUND_IN_IMPORTED_SOURCES"
            primary = "PENDING_SOURCE_IMPORT"
            related = "PENDING_SOURCE_IMPORT"
        rows.append(
            {
                "construct": construct,
                "primary_category": primary,
                "related_categories": related,
                "proposed_relationship": proposed,
                "scale_level": "PENDING_SOURCE_IMPORT",
                "source_support": "CURRENT_CANONICAL_SCAFFOLD" if proposed != "NOT_FOUND_IN_IMPORTED_SOURCES" else "NOT_FOUND_IN_IMPORTED_SOURCES",
                "status": "CANDIDATE_REVIEW_REQUIRED" if proposed != "NOT_FOUND_IN_IMPORTED_SOURCES" else "NOT_FOUND_IN_IMPORTED_SOURCES",
                "review_notes": "Preserve current approved Concreteness boundary until imported evidence supports revision.",
            }
        )
    return rows


def build_definition_matrix(rows: List[Dict[str, str]]) -> List[Dict[str, str]]:
    output: List[Dict[str, str]] = []
    for construct in DEFINITION_CONSTRUCTS:
        matching = [row for row in rows if row["construct"].lower() == construct.lower()]
        if not matching:
            output.append(
                {
                    "construct": construct,
                    "candidate_definition": "NOT_FOUND_IN_IMPORTED_SOURCES",
                    "source_id": "",
                    "source_part": "",
                    "line_start": "",
                    "line_end": "",
                    "speaker": "UNKNOWN",
                    "user_approval_status": "NOT_EVALUATED",
                    "version_status": "UNRESOLVED",
                    "hem_overlap": "PENDING_SOURCE_IMPORT",
                    "intuition_overlap": "PENDING_SOURCE_IMPORT",
                    "love_overlap": "PENDING_SOURCE_IMPORT",
                    "elegance_overlap": "PENDING_SOURCE_IMPORT",
                    "current_candidate": "false",
                    "review_notes": "No imported evidence yet.",
                }
            )
            continue
        for row in matching:
            output.append(
                {
                    "construct": construct,
                    "candidate_definition": row["quoted_text"].replace("\n", " "),
                    "source_id": row["source_id"],
                    "source_part": row["source_part"],
                    "line_start": row["line_start"],
                    "line_end": row["line_end"],
                    "speaker": row["speaker"],
                    "user_approval_status": row["user_approval_status"],
                    "version_status": row["version_status"],
                    "hem_overlap": "YES" if "hem" in row["quoted_text"].lower() else "NO",
                    "intuition_overlap": "YES" if "intuition" in row["quoted_text"].lower() else "NO",
                    "love_overlap": "YES" if "love" in row["quoted_text"].lower() else "NO",
                    "elegance_overlap": "YES" if "elegance" in row["quoted_text"].lower() or "beauty" in row["quoted_text"].lower() else "NO",
                    "current_candidate": "false",
                    "review_notes": "CANDIDATE_REVIEW_REQUIRED",
                }
            )
    return output


def build_boundary_matrix(rows: List[Dict[str, str]]) -> List[Dict[str, str]]:
    output = canonical_boundary_rows()
    for construct in BOUNDARY_CONSTRUCTS:
        matches = [row for row in rows if construct.lower() in row["quoted_text"].lower()]
        for match in matches:
            output.append(
                {
                    "construct": construct,
                    "primary_category": "PENDING_REVIEW",
                    "related_categories": "PENDING_REVIEW",
                    "proposed_relationship": match["quoted_text"].replace("\n", " "),
                    "scale_level": "PENDING_REVIEW",
                    "source_support": f"{match['source_id']}:{match['source_part']}:{match['line_start']}-{match['line_end']}",
                    "status": "CANDIDATE_REVIEW_REQUIRED",
                    "review_notes": "Imported evidence candidate; do not auto-canonicalize.",
                }
            )
    return output


def build_scale_rows(rows: List[Dict[str, str]]) -> List[Dict[str, str]]:
    output: List[Dict[str, str]] = []
    for row in rows:
        text = row["quoted_text"].lower()
        if not any(word in text for word in ["scale", *SCALE_WORDS]):
            continue
        output.append(
            {
                "construct": row["construct"],
                "physical": "MENTIONED" if "physical" in text else "",
                "chemical": "MENTIONED" if "chemical" in text else "",
                "biological": "MENTIONED" if "biological" in text else "",
                "cognitive": "MENTIONED" if "cognitive" in text else "",
                "interpersonal": "MENTIONED" if "interpersonal" in text else "",
                "institutional": "MENTIONED" if "institutional" in text else "",
                "societal": "MENTIONED" if "societal" in text else "",
                "source_id": row["source_id"],
                "source_lines": f"{row['source_part']}:{row['line_start']}-{row['line_end']}",
                "status": "CANDIDATE_REVIEW_REQUIRED",
                "notes": "Do not assume identical manifestation across scales.",
            }
        )
    return output


def build_spec_rows(rows: List[Dict[str, str]]) -> List[Dict[str, str]]:
    heuristics = {
        "Goodness scalar definition": ["goodness", "scalar"],
        "Eight-C operational definitions": ["coherence", "consistency", "continuity", "concreteness"],
        "rating scale": ["rating scale", "score"],
        "independent Goodness score": ["independent goodness", "goodness score"],
        "contradiction taxonomy": ["contradiction taxonomy", "contradiction"],
        "evaluated entity": ["evaluated entity"],
        "relevant target": ["relevant target"],
        "intended purpose": ["intended purpose", "purpose"],
        "target scope": ["target scope"],
        "target contestability": ["contestability"],
        "Choice bearer": ["choice bearer"],
        "Choice scope": ["choice scope"],
        "Choice alignment": ["choice alignment"],
        "Stage A sample size": ["stage a", "sample size"],
        "Stage B sample size": ["stage b", "sample size"],
        "retry rule": ["retry rule", "retry"],
        "stopping rule": ["stopping rule", "stop"],
        "reliability analyses": ["reliability"],
        "mutual-information analyses": ["mutual information", "mutual-information"],
        "ablation analyses": ["ablation"],
        "effective-rank analyses": ["effective rank", "effective-rank"],
        "residual-exhaustion analyses": ["residual exhaustion", "residual-exhaustion"],
    }
    output: List[Dict[str, str]] = []
    for field in SPEC_FIELDS:
        tokens = [token.lower() for token in heuristics[field]]
        match = next((row for row in rows if any(token in row["quoted_text"].lower() for token in tokens)), None)
        if match is None:
            output.append(
                {
                    "spec_field": field,
                    "candidate_value": "NOT_FOUND_IN_IMPORTED_SOURCES",
                    "source_id": "",
                    "source_part": "",
                    "line_start": "",
                    "line_end": "",
                    "speaker": "UNKNOWN",
                    "user_approval_status": "NOT_EVALUATED",
                    "status": "NOT_FOUND_IN_IMPORTED_SOURCES",
                    "review_notes": "Requires imported evidence.",
                }
            )
        else:
            output.append(
                {
                    "spec_field": field,
                    "candidate_value": match["quoted_text"].replace("\n", " "),
                    "source_id": match["source_id"],
                    "source_part": match["source_part"],
                    "line_start": match["line_start"],
                    "line_end": match["line_end"],
                    "speaker": match["speaker"],
                    "user_approval_status": match["user_approval_status"],
                    "status": "CANDIDATE_REVIEW_REQUIRED",
                    "review_notes": "Candidate extracted from imported sources.",
                }
            )
    return output


def build_candidate_item_rows(rows: List[Dict[str, str]]) -> List[Dict[str, str]]:
    output: List[Dict[str, str]] = []
    counter = 1
    pattern = re.compile(r"\b(item|scenario|choice|prompt|example)\b", re.IGNORECASE)
    for row in rows:
        if not pattern.search(row["quoted_text"]):
            continue
        output.append(
            {
                "candidate_item_id": f"ITEM-CAND-{counter:03d}",
                "title": row["topic"] or "UNTITLED_CANDIDATE",
                "scenario_text": row["quoted_text"],
                "source_id": row["source_id"],
                "source_part": row["source_part"],
                "line_start": row["line_start"],
                "line_end": row["line_end"],
                "completeness": "PARTIAL",
                "possible_duplicate": "UNKNOWN",
                "intended_contrast": "PENDING_SOURCE_IMPORT",
                "choice_bearer": "PENDING_SOURCE_IMPORT",
                "choice_scope": "PENDING_SOURCE_IMPORT",
                "notes": "Do not promote into frozen corpus until reviewed.",
            }
        )
        counter += 1
    return output


def build_readiness_report(definitions: List[Dict[str, str]], specs: List[Dict[str, str]], items: List[Dict[str, str]]) -> str:
    framework_ready = "PARTIAL" if any(row["candidate_definition"] != "NOT_FOUND_IN_IMPORTED_SOURCES" for row in definitions) else "BLOCKED"
    prompt_ready = "PARTIAL" if any(row["spec_field"] == "rating scale" and row["status"] != "NOT_FOUND_IN_IMPORTED_SOURCES" for row in specs) else "BLOCKED"
    schema_ready = "BLOCKED"
    corpus_ready = "PARTIAL" if items else "BLOCKED"
    metadata_ready = "BLOCKED"
    prereg_ready = "BLOCKED"
    pipeline_ready = "BLOCKED"
    return "\n".join([
        "# Pilot Reconstruction Readiness",
        "",
        f"FRAMEWORK_READY: {framework_ready}",
        f"PROMPT_READY: {prompt_ready}",
        f"SCHEMA_READY: {schema_ready}",
        f"CORPUS_READY: {corpus_ready}",
        f"METADATA_READY: {metadata_ready}",
        f"PREREGISTRATION_READY: {prereg_ready}",
        f"PIPELINE_READY: {pipeline_ready}",
        "",
        "Historical simulated outputs remain UNVERIFIED_HISTORICAL_CLAIM unless original files are imported and independently verified.",
    ]) + "\n"


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

    for source, manifest_item, full_path in present_sources:
        rel = str(full_path.relative_to(repo_root)).replace("\\", "/")
        scanned_files.append(rel)
        lines = full_path.read_text(encoding="utf-8", errors="replace").splitlines()
        heading_at, speaker_at, turn_at = annotate_lines(lines)
        source_part = str(manifest_item.get("part_number") or extract_part_number(full_path.name))
        conversation_date = manifest_item.get("conversation_end_date") or manifest_item.get("conversation_start_date") or "PENDING_SOURCE_IMPORT"

        for line_start, line_end, quoted in build_passages(lines):
            found_terms = detect_terms(quoted, SEARCH_TERMS)
            if not found_terms:
                continue
            speakers = detect_speakers(speaker_at, line_start, line_end)
            dominant_speaker = speakers[0] if speakers else "UNKNOWN"
            topic = heading_at[line_start] or turn_at[line_start] or "UNCLASSIFIED"
            for term in found_terms:
                rows.append(
                    {
                        "passage_id": f"CAND-{counter:05d}",
                        "source_id": str(source.get("source_id", "")),
                        "source_part": source_part,
                        "source_filename": full_path.name,
                        "source_location": rel,
                        "conversation_date": str(conversation_date),
                        "line_start": str(line_start),
                        "line_end": str(line_end),
                        "topic": topic,
                        "construct": term,
                        "version_status": "UNRESOLVED",
                        "content_status": "VERBATIM",
                        "speaker": dominant_speaker,
                        "authorship_status": derive_authorship_status(speakers),
                        "user_approval_status": derive_user_approval_status(quoted, dominant_speaker),
                        "candidate_flags": detect_candidate_flags(quoted),
                        "canonical_relevance": "CANDIDATE_REVIEW_REQUIRED",
                        "conflict_ids": "",
                        "quoted_text": quoted,
                        "summary": f"Candidate passage containing term '{term}'.",
                        "review_notes": "CANDIDATE_REVIEW_REQUIRED",
                    }
                )
                counter += 1

    generated_utc = dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    write_csv(report_dir / "source_passage_candidates.csv", PASSAGE_HEADERS, rows)
    write_markdown(report_dir / "source_passage_candidates.md", rows, scanned_files, generated_utc)

    definition_rows = build_definition_matrix(rows)
    boundary_rows = build_boundary_matrix(rows)
    scale_rows = build_scale_rows(rows)
    spec_rows = build_spec_rows(rows)
    item_rows = build_candidate_item_rows(rows)

    write_csv(report_dir / "eight_c_definition_matrix.csv", DEFINITION_HEADERS, definition_rows)
    write_csv(report_dir / "gile_hem_boundary_matrix.csv", BOUNDARY_HEADERS, boundary_rows)
    write_csv(report_dir / "scale_evolution_candidates.csv", SCALE_HEADERS, scale_rows)
    write_csv(report_dir / "pilot_specification_candidates.csv", SPEC_HEADERS, spec_rows)
    write_csv(report_dir / "candidate_item_inventory.csv", ITEM_HEADERS, item_rows)
    (report_dir / "pilot_reconstruction_readiness.md").write_text(build_readiness_report(definition_rows, spec_rows, item_rows), encoding="utf-8")

    print("FRAMEWORK_SOURCE_INDEXING_COMPLETE")
    print("CSV: experiments/eight_c_goodness_pilot/results/reports/source_passage_candidates.csv")
    print("MD: experiments/eight_c_goodness_pilot/results/reports/source_passage_candidates.md")
    print("DEFINITION_MATRIX: experiments/eight_c_goodness_pilot/results/reports/eight_c_definition_matrix.csv")
    print("BOUNDARY_MATRIX: experiments/eight_c_goodness_pilot/results/reports/gile_hem_boundary_matrix.csv")
    print("SCALE_CANDIDATES: experiments/eight_c_goodness_pilot/results/reports/scale_evolution_candidates.csv")
    print("SPEC_CANDIDATES: experiments/eight_c_goodness_pilot/results/reports/pilot_specification_candidates.csv")
    print("ITEM_CANDIDATES: experiments/eight_c_goodness_pilot/results/reports/candidate_item_inventory.csv")
    print("READINESS: experiments/eight_c_goodness_pilot/results/reports/pilot_reconstruction_readiness.md")
    print(f"SOURCE_FILES_SCANNED: {len(scanned_files)}")
    print(f"PASSAGE_CANDIDATES: {len(rows)}")
    if not scanned_files:
        print("NO_SOURCE_FILES_AVAILABLE")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

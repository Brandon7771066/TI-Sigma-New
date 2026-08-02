from __future__ import annotations

import csv
import json
from pathlib import Path

from .contracts import REQUIRED_ITEM_FIELDS, REQUIRED_METADATA_FIELDS


def _read_csv(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle))


def _check_required_fields(rows: list[dict[str, str]], required: list[str], label: str) -> None:
    if not rows:
        raise ValueError(f"{label} is empty")
    missing = [name for name in required if name not in rows[0]]
    if missing:
        raise ValueError(f"{label} missing required columns: {', '.join(missing)}")


def load_items(items_csv: Path) -> list[dict[str, str]]:
    rows = _read_csv(items_csv)
    _check_required_fields(rows, REQUIRED_ITEM_FIELDS, "items")
    return rows


def load_metadata(metadata_csv: Path) -> list[dict[str, str]]:
    rows = _read_csv(metadata_csv)
    _check_required_fields(rows, REQUIRED_METADATA_FIELDS, "metadata")
    return rows


def merge_items_with_metadata(
    items_rows: list[dict[str, str]], metadata_rows: list[dict[str, str]]
) -> list[dict[str, str]]:
    metadata_by_id = {row["item_id"]: row for row in metadata_rows}
    merged: list[dict[str, str]] = []
    missing_metadata: list[str] = []

    for item in items_rows:
        item_id = item["item_id"]
        meta = metadata_by_id.get(item_id)
        if meta is None:
            missing_metadata.append(item_id)
            continue
        merged_row = dict(item)
        merged_row["choice_bearer"] = meta["choice_bearer"]
        merged_row["choice_scope"] = meta["choice_scope"]
        merged.append(merged_row)

    if missing_metadata:
        raise ValueError(f"Missing metadata for item ids: {', '.join(sorted(missing_metadata))}")

    if len(merged) != len(items_rows):
        raise ValueError("Merged row count differs from item row count")

    return merged


def load_schema(schema_path: Path) -> dict:
    with schema_path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def load_prompt(prompt_path: Path) -> str:
    return prompt_path.read_text(encoding="utf-8")
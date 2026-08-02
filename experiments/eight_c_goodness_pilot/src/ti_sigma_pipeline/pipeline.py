from __future__ import annotations

import json
from pathlib import Path

from .io import load_items, load_metadata, merge_items_with_metadata
from .mock_rater import build_mock_rating
from .schema_check import validate_rating_like_schema


def run_mock_pipeline(
    items_csv: Path,
    metadata_csv: Path,
    output_jsonl: Path,
) -> dict[str, int]:
    items = load_items(items_csv)
    metadata = load_metadata(metadata_csv)
    merged = merge_items_with_metadata(items, metadata)

    output_jsonl.parent.mkdir(parents=True, exist_ok=True)

    written = 0
    with output_jsonl.open("w", encoding="utf-8", newline="") as handle:
        for item in merged:
            rating = build_mock_rating(item)
            validate_rating_like_schema(rating)
            handle.write(json.dumps(rating, ensure_ascii=False) + "\n")
            written += 1

    return {
        "items": len(items),
        "metadata": len(metadata),
        "written": written,
    }
from __future__ import annotations

import json
from itertools import combinations
from pathlib import Path

from .contracts import CONTRADICTION_KEYS, EIGHT_C_KEYS
from .io import load_items, load_metadata, merge_items_with_metadata
from .mock_rater import build_mock_rating
from .schema_check import validate_rating_like_schema


def _pairwise_mean_abs_diff(values: list[int]) -> float:
    if len(values) < 2:
        return 0.0
    diffs = [abs(a - b) for a, b in combinations(values, 2)]
    return sum(diffs) / len(diffs)


def _compute_reproducibility(records: list[dict], attempts_per_item: int) -> dict:
    by_item: dict[str, list[dict]] = {}
    for record in records:
        by_item.setdefault(record["item_id"], []).append(record)

    complete_groups = [group for group in by_item.values() if len(group) == attempts_per_item]
    if not complete_groups:
        return {
            "attempts_per_item": attempts_per_item,
            "item_groups": 0,
            "exact_match_rate": 0.0,
            "mean_abs_diff": {"goodness": 0.0, "C_scores": {}, "contradictions": {}},
        }

    exact_matches = 0
    goodness_diffs: list[float] = []
    c_diffs: dict[str, list[float]] = {k: [] for k in EIGHT_C_KEYS}
    contradiction_diffs: dict[str, list[float]] = {k: [] for k in CONTRADICTION_KEYS}

    for group in complete_groups:
        canonical = json.dumps(group[0], sort_keys=True)
        if all(json.dumps(entry, sort_keys=True) == canonical for entry in group[1:]):
            exact_matches += 1

        goodness_values = [entry["goodness"] for entry in group]
        goodness_diffs.append(_pairwise_mean_abs_diff(goodness_values))

        for key in EIGHT_C_KEYS:
            c_values = [entry["C_scores"][key] for entry in group]
            c_diffs[key].append(_pairwise_mean_abs_diff(c_values))

        for key in CONTRADICTION_KEYS:
            contradiction_values = [entry["contradictions"][key] for entry in group]
            contradiction_diffs[key].append(_pairwise_mean_abs_diff(contradiction_values))

    return {
        "attempts_per_item": attempts_per_item,
        "item_groups": len(complete_groups),
        "exact_match_rate": exact_matches / len(complete_groups),
        "mean_abs_diff": {
            "goodness": sum(goodness_diffs) / len(goodness_diffs),
            "C_scores": {k: (sum(v) / len(v) if v else 0.0) for k, v in c_diffs.items()},
            "contradictions": {k: (sum(v) / len(v) if v else 0.0) for k, v in contradiction_diffs.items()},
        },
    }


def run_mock_pipeline(
    items_csv: Path,
    metadata_csv: Path,
    output_jsonl: Path,
    attempts_per_item: int = 1,
    output_metrics_json: Path | None = None,
) -> dict:
    if attempts_per_item < 1:
        raise ValueError("attempts_per_item must be >= 1")

    items = load_items(items_csv)
    metadata = load_metadata(metadata_csv)
    merged = merge_items_with_metadata(items, metadata)

    output_jsonl.parent.mkdir(parents=True, exist_ok=True)

    all_records: list[dict] = []
    written = 0
    with output_jsonl.open("w", encoding="utf-8", newline="") as handle:
        for attempt_index in range(1, attempts_per_item + 1):
            for item in merged:
                rating = build_mock_rating(item, attempt_index=attempt_index)
                validate_rating_like_schema(rating)
                handle.write(json.dumps(rating, ensure_ascii=False) + "\n")
                all_records.append(rating)
                written += 1

    reproducibility = _compute_reproducibility(all_records, attempts_per_item)

    if output_metrics_json is not None:
        output_metrics_json.parent.mkdir(parents=True, exist_ok=True)
        output_metrics_json.write_text(json.dumps(reproducibility, indent=2), encoding="utf-8")

    return {
        "items": len(items),
        "metadata": len(metadata),
        "attempts_per_item": attempts_per_item,
        "written": written,
        "reproducibility": reproducibility,
    }
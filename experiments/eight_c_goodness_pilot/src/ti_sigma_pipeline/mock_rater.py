from __future__ import annotations

import hashlib

from .contracts import CONTRADICTION_KEYS, EIGHT_C_KEYS


def _bucket(seed: str, key: str, maximum: int) -> int:
    digest = hashlib.sha256(f"{seed}|{key}".encode("utf-8")).hexdigest()
    return int(digest[:8], 16) % (maximum + 1)


def build_mock_rating(
    item: dict[str, str],
    attempt_index: int = 1,
    seed_strategy: str = "vary_by_attempt",
    base_seed: str = "",
) -> dict:
    if attempt_index < 1:
        raise ValueError("attempt_index must be >= 1")
    if seed_strategy not in {"vary_by_attempt", "fixed"}:
        raise ValueError("seed_strategy must be 'vary_by_attempt' or 'fixed'")

    suffix = f"attempt={attempt_index}" if seed_strategy == "vary_by_attempt" else "attempt=fixed"
    seed_prefix = f"{base_seed}|" if base_seed else ""
    seed = seed_prefix + item["item_id"] + "|" + item["scenario_text"] + f"|{suffix}"

    c_scores = {name: _bucket(seed, name, 10) for name in EIGHT_C_KEYS}
    contradictions = {name: _bucket(seed, name, 3) for name in CONTRADICTION_KEYS}

    return {
        "item_id": item["item_id"],
        "evaluated_entity": item["evaluated_entity"],
        "relevant_target": item["relevant_target"],
        "intended_purpose": item["intended_purpose"],
        "domain": item["domain"],
        "target_scope": item["target_scope"],
        "target_contestability": item["target_contestability"],
        "choice_bearer": item["choice_bearer"],
        "choice_scope": item["choice_scope"],
        "C_scores": c_scores,
        "goodness": _bucket(seed, "goodness", 10),
        "contradictions": contradictions,
        "notes": f"MOCK_ONLY: deterministic output (seed_strategy={seed_strategy})",
    }
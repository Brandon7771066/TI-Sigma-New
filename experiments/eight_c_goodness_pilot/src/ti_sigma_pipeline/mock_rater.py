from __future__ import annotations

import hashlib

from .contracts import CONTRADICTION_KEYS, EIGHT_C_KEYS


def _bucket(seed: str, key: str, maximum: int) -> int:
    digest = hashlib.sha256(f"{seed}|{key}".encode("utf-8")).hexdigest()
    return int(digest[:8], 16) % (maximum + 1)


def build_mock_rating(item: dict[str, str], attempt_index: int = 1) -> dict:
    if attempt_index < 1:
        raise ValueError("attempt_index must be >= 1")

    seed = item["item_id"] + "|" + item["scenario_text"] + f"|attempt={attempt_index}"

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
        "notes": f"MOCK_ONLY: deterministic phase 4 scaffolding output (attempt {attempt_index})",
    }
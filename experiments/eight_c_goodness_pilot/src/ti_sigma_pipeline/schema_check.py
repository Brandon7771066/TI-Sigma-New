from __future__ import annotations

from .contracts import CONTRADICTION_KEYS, EIGHT_C_KEYS


def _validate_int_range(value: object, minimum: int, maximum: int, field: str) -> None:
    if not isinstance(value, int):
        raise ValueError(f"{field} must be an integer")
    if value < minimum or value > maximum:
        raise ValueError(f"{field} must be between {minimum} and {maximum}")


def validate_rating_like_schema(record: dict) -> None:
    required_top_level = [
        "item_id",
        "evaluated_entity",
        "relevant_target",
        "intended_purpose",
        "domain",
        "target_scope",
        "target_contestability",
        "choice_bearer",
        "choice_scope",
        "C_scores",
        "goodness",
        "contradictions",
        "notes",
    ]
    allowed_top_level = set(required_top_level)
    unknown_top_level = sorted(set(record.keys()) - allowed_top_level)
    if unknown_top_level:
        raise ValueError(f"Unknown top-level fields: {', '.join(unknown_top_level)}")

    for field in required_top_level:
        if field not in record:
            raise ValueError(f"Missing required field: {field}")

    if record["target_contestability"] not in {"fixed", "contestable"}:
        raise ValueError("target_contestability must be fixed or contestable")

    c_scores = record["C_scores"]
    if not isinstance(c_scores, dict):
        raise ValueError("C_scores must be an object")
    unknown_c = sorted(set(c_scores.keys()) - set(EIGHT_C_KEYS))
    if unknown_c:
        raise ValueError(f"Unknown C score keys: {', '.join(unknown_c)}")
    for key in EIGHT_C_KEYS:
        if key not in c_scores:
            raise ValueError(f"Missing C score key: {key}")
        _validate_int_range(c_scores[key], 0, 10, f"C_scores.{key}")

    contradictions = record["contradictions"]
    if not isinstance(contradictions, dict):
        raise ValueError("contradictions must be an object")
    unknown_contradictions = sorted(set(contradictions.keys()) - set(CONTRADICTION_KEYS))
    if unknown_contradictions:
        raise ValueError(f"Unknown contradiction keys: {', '.join(unknown_contradictions)}")
    for key in CONTRADICTION_KEYS:
        if key not in contradictions:
            raise ValueError(f"Missing contradiction key: {key}")
        _validate_int_range(contradictions[key], 0, 3, f"contradictions.{key}")

    _validate_int_range(record["goodness"], 0, 10, "goodness")

    if not isinstance(record["notes"], str):
        raise ValueError("notes must be a string")
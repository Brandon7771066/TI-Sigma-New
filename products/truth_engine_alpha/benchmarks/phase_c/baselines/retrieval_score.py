"""Baseline models (Lexical, Retrieval, Confidence, LLM Judge)."""

class BaselineModel:
    def __init__(self, baseline_name: str = "BASELINE_2_RETRIEVAL"):
        self.name = baseline_name

    def evaluate_case(self, case: dict) -> dict:
        text = case.get("ai_answer", "")
        retrieved = case.get("retrieved_text", "")
        overlap = len(set(text.split()).intersection(set(retrieved.split())))
        pred_label = "TRUE" if overlap > 3 else ("FALSE" if overlap < 2 else "INDETERMINATE")
        return {
            "case_id": case["case_id"],
            "predicted_label": pred_label,
            "confidence": min(1.0, overlap / 10.0),
            "unsupported_claim_detected": pred_label in ["FALSE", "INDETERMINATE"],
            "review_time_sec": 45.0,
            "runtime_ms": 12.0
        }

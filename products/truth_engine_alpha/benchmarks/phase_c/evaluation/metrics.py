"""Phase C Evaluation Metrics Calculator."""

import math, random
from typing import List, Dict, Any

def compute_classification_metrics(y_true: List[str], y_pred: List[str]) -> Dict[str, float]:
    total = len(y_true)
    correct = sum(1 for t, p in zip(y_true, y_pred) if t == p)
    acc = correct / total if total > 0 else 0.0

    labels = list(set(y_true).union(set(y_pred)))
    f1s = []
    for l in labels:
        tp = sum(1 for t, p in zip(y_true, y_pred) if t == l and p == l)
        fp = sum(1 for t, p in zip(y_true, y_pred) if t != l and p == l)
        fn = sum(1 for t, p in zip(y_true, y_pred) if t == l and p != l)
        prec = tp / (tp + fp) if (tp + fp) > 0 else 0.0
        rec = tp / (tp + fn) if (tp + fn) > 0 else 0.0
        f1 = (2 * prec * rec) / (prec + rec) if (prec + rec) > 0 else 0.0
        f1s.append(f1)
    
    macro_f1 = sum(f1s) / len(f1s) if f1s else 0.0
    return {
        "accuracy": round(acc, 4),
        "macro_f1": round(macro_f1, 4),
        "total_cases": total
    }

def compute_bootstrap_ci(scores: List[float], n_samples: int = 1000, ci: float = 0.95) -> List[float]:
    if not scores:
        return [0.0, 0.0]
    means = []
    n = len(scores)
    for _ in range(n_samples):
        sample = [random.choice(scores) for _ in range(n)]
        means.append(sum(sample) / n)
    means.sort()
    low_idx = int((1.0 - ci) / 2.0 * n_samples)
    high_idx = int((1.0 + ci) / 2.0 * n_samples) - 1
    return [round(means[low_idx], 4), round(means[high_idx], 4)]

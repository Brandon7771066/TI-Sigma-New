"""
Q_pre baseline post-hoc audit for UHP-1-F5 (Pass-70 batch-4).

Q_pre = pre-UHP-1 (Pass 55-67) mean of:
  Q1 = falsifiers-closed-per-pass
  Q2 = #69-disclosures-per-pass (proxy: count of "#69" or "honest finding" mentions)
  Q3 = instantiation-ratio = (code-files + edits) / (new-candidates + 1)
Combined Q = Q1 + Q2 + Q3/10
"""

import os
import re
import json
from collections import defaultdict

PAPERS_DIR = "papers"
PASS_MIN, PASS_MAX = 55, 67


def extract_pass(filename):
    m = re.match(r"PASS_(\d+)_", filename)
    return int(m.group(1)) if m else None


def audit():
    counts = defaultdict(lambda: {"papers": 0, "f_closed": 0, "honest_69": 0,
                                   "code_edits": 0, "candidates": 0})
    for fn in os.listdir(PAPERS_DIR):
        p = extract_pass(fn)
        if p is None or p < PASS_MIN or p > PASS_MAX:
            continue
        if not fn.endswith(".md"):
            continue
        c = counts[p]
        c["papers"] += 1
        path = os.path.join(PAPERS_DIR, fn)
        try:
            with open(path, errors="replace") as f:
                text = f.read()
        except Exception:
            continue
        # Q1: falsifier closures — count "CLOSED" or "closed" near falsifier IDs
        c["f_closed"] += len(re.findall(r"F-?\d+[^a-zA-Z]*CLOSED", text, re.IGNORECASE))
        c["f_closed"] += len(re.findall(r"falsifier.*?closed", text, re.IGNORECASE)[:5])
        # Q2: honest-finding-style §69 disclosures
        c["honest_69"] += len(re.findall(r"§\s*69|asymmetric.{0,15}69|honest.{0,10}#69|#69.{0,15}finding",
                                          text, re.IGNORECASE))
        # Q3 numerator (instantiation): rough proxy = paragraphs containing "edited" or "applied" or "files created"
        c["code_edits"] += len(re.findall(r"\bedit(?:ed|s)?\b|\bapplied\b|file.{0,5}created", text, re.IGNORECASE))
        # Q3 denominator: new candidate principles — count "candidate canonical" or "CANDIDATE"
        c["candidates"] += len(re.findall(r"candidate\s+canonical|CANDIDATE\s+CANONICAL", text))

    per_pass = []
    for p in sorted(counts.keys()):
        c = counts[p]
        # Cap heuristic noise; saturate honest_69 at 10/pass etc.
        Q1 = min(c["f_closed"], 10)
        Q2 = min(c["honest_69"], 10)
        Q3 = c["code_edits"] / max(c["candidates"] + 1, 1)
        Q3 = min(Q3, 50)
        Q = Q1 + Q2 + Q3 / 10.0
        per_pass.append({
            "pass": p, "papers": c["papers"],
            "Q1": Q1, "Q2": Q2, "Q3": round(Q3, 2),
            "Q": round(Q, 3),
        })

    n = len(per_pass)
    Q_mean = sum(r["Q"] for r in per_pass) / n if n > 0 else 0
    Q1_mean = sum(r["Q1"] for r in per_pass) / n if n > 0 else 0
    Q2_mean = sum(r["Q2"] for r in per_pass) / n if n > 0 else 0
    Q3_mean = sum(r["Q3"] for r in per_pass) / n if n > 0 else 0

    return {
        "passes_audited": [PASS_MIN, PASS_MAX],
        "n_passes": n,
        "per_pass": per_pass,
        "Q_pre_baseline": {
            "Q1_mean": round(Q1_mean, 3),
            "Q2_mean": round(Q2_mean, 3),
            "Q3_mean": round(Q3_mean, 3),
            "Q_mean": round(Q_mean, 3),
        },
        "thresholds_for_UHP_1_F5": {
            "REFUTED_below": round(0.8 * Q_mean, 3),
            "INDETERMINATE_band": [round(0.8 * Q_mean, 3), round(1.2 * Q_mean, 3)],
            "NOT_REFUTED_above": round(1.2 * Q_mean, 3),
        },
        "note": (
            "Heuristic regex-based audit. True baseline requires manual classification. "
            "Q1 likely under-counted (closures often phrased as 'NOT REFUTED' or 'ADVANCED' "
            "rather than explicit 'CLOSED'). Q2 likely well-counted. Q3 likely over-counted "
            "(any mention of 'edited' or 'applied' triggers; not all are instantiation acts)."
        ),
    }


if __name__ == "__main__":
    out = audit()
    print(json.dumps(out, indent=2))

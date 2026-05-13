"""Shared rater library for Pass-49 Wave-1 tests (T49-1, T49-2, T49-5, T49-6).

HONEST CAVEAT (#69 + Pass-49 L4 §1.3): this implementation uses the same
underlying LLM (Claude) with two distinct prompt-personas + temperatures
as a *pseudo*-two-rater proxy. This is weaker than two fully-independent
LLMs (Claude + GPT) which would itself be weaker than independent humans.
All Wave-1 results are reported as PILOT-grade with this caveat in the
verdict line.

OpenAI integration was not authorized in this environment; explicit
flag in results.json: "rater_independence": "same_model_two_personas".
"""
from __future__ import annotations
import hashlib, json, re, time
from anthropic import Anthropic

CLIENT = Anthropic()
MODEL = "claude-sonnet-4-5"

RATER_A_SYSTEM = (
    "You are a careful, neutral methodologist. Read each item, apply the "
    "rubric exactly as written, and respond ONLY with valid JSON exactly "
    "matching the requested schema. Do not editorialize. Do not add commentary."
)
RATER_B_SYSTEM = (
    "You are a skeptical, parsimony-favoring methodologist. Apply the rubric "
    "exactly as written, but when a rating is ambiguous, default toward the "
    "more conservative / lower-effect-size code. Respond ONLY with valid JSON."
)


def _extract_json(text: str):
    m = re.search(r"\{[\s\S]*\}|\[[\s\S]*\]", text)
    if not m:
        raise ValueError(f"No JSON in: {text[:200]}")
    return json.loads(m.group(0))


def rate(rater: str, prompt: str, max_tokens: int = 4096) -> dict | list:
    sys = RATER_A_SYSTEM if rater == "A" else RATER_B_SYSTEM
    temp = 0.0 if rater == "A" else 0.3
    for attempt in range(3):
        try:
            r = CLIENT.messages.create(
                model=MODEL, max_tokens=max_tokens, temperature=temp,
                system=sys, messages=[{"role": "user", "content": prompt}],
            )
            return _extract_json(r.content[0].text)
        except Exception as e:
            if attempt == 2:
                raise
            time.sleep(2 ** attempt)


def sha256_str(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def fleiss_kappa_binary(ratings: list[list[int]]) -> float:
    """Fleiss kappa for binary ratings. ratings[i] = [count_0, count_1] across raters."""
    N = len(ratings)
    if N == 0:
        return float("nan")
    n = sum(ratings[0])
    if n < 2:
        return float("nan")
    p_j = [sum(r[j] for r in ratings) / (N * n) for j in range(2)]
    P_e = sum(p ** 2 for p in p_j)
    P_i = [(sum(c * c for c in r) - n) / (n * (n - 1)) for r in ratings]
    P_bar = sum(P_i) / N
    if abs(1 - P_e) < 1e-12:
        return float("nan")
    return (P_bar - P_e) / (1 - P_e)


def percent_agreement(rater_a: list, rater_b: list) -> float:
    if not rater_a:
        return float("nan")
    return sum(1 for x, y in zip(rater_a, rater_b) if x == y) / len(rater_a)


def cohens_kappa(rater_a: list, rater_b: list) -> float:
    """Cohen's kappa for two raters, categorical."""
    n = len(rater_a)
    if n == 0:
        return float("nan")
    cats = sorted(set(rater_a) | set(rater_b))
    po = sum(1 for x, y in zip(rater_a, rater_b) if x == y) / n
    pe = sum(
        (rater_a.count(c) / n) * (rater_b.count(c) / n) for c in cats
    )
    if abs(1 - pe) < 1e-12:
        return float("nan")
    return (po - pe) / (1 - pe)


def icc_2_1(rater_a: list[float], rater_b: list[float]) -> float:
    """ICC(2,1) two-way random, single measures, absolute agreement.
    Simplified two-rater implementation."""
    import statistics
    n = len(rater_a)
    if n < 2:
        return float("nan")
    k = 2
    grand = (sum(rater_a) + sum(rater_b)) / (n * k)
    row_means = [(rater_a[i] + rater_b[i]) / k for i in range(n)]
    col_means = [sum(rater_a) / n, sum(rater_b) / n]
    SST_rows = k * sum((m - grand) ** 2 for m in row_means)
    SST_cols = n * sum((m - grand) ** 2 for m in col_means)
    SST = sum((rater_a[i] - grand) ** 2 + (rater_b[i] - grand) ** 2 for i in range(n))
    SSE = SST - SST_rows - SST_cols
    MSR = SST_rows / (n - 1)
    MSC = SST_cols / (k - 1) if k > 1 else 0
    MSE = SSE / ((n - 1) * (k - 1))
    denom = MSR + (k - 1) * MSE + k * (MSC - MSE) / n
    if abs(denom) < 1e-12:
        return float("nan")
    return (MSR - MSE) / denom

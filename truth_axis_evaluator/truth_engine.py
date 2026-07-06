"""TI Sigma LLM-judge truth engine.

Pipeline (same order as the validated battery methodology):
  N/A screen -> MI screen -> truth-spectrum placement (T/F/I) -> 4 truth axes.

Uses the SAME frozen axis definitions and the SAME rater trio that produced the
validated numbers (B26 labels: 5-tier kappa 0.886; B125 axes: degree 0.49 /
modality 0.44 reliable, tau-delta 0.31 / authority 0.21 fair).

HONESTY NOTE (do not remove): the validation certifies that LLM raters can apply
these labels/axes consistently on the frozen battery item sets. It does NOT
certify accuracy on arbitrary new domains; treat single-rater outputs as
provisional and prefer the 3-rater consensus for anything that matters.
"""
import json
import os
import re
from concurrent.futures import ThreadPoolExecutor, as_completed

from schema import TruthEvaluation, ConsensusEvaluation

# Same trio as the B125 / B190 battery runs.
RATERS = [
    ("openai", "gpt-4o-mini"),
    ("anthropic", "claude-haiku-4-5"),
    ("anthropic", "claude-sonnet-4-5"),
]
DEFAULT_SINGLE = ("openai", "gpt-4o-mini")

PROMPT = """You are a TI Sigma truth evaluator. Evaluate the CLAIM below using this exact pipeline.

STEP 1 — N/A screen: N/A means an answer is NOT CURRENTLY POSSIBLE — for any evaluator, at this time, with available information (e.g. undecided future contingents with no basis, missing referent, question not yet posed to reality). N/A is about AVAILABILITY of an answer, not about the claim sitting in the middle of the truth spectrum. If triggered, label = "N_A".

STEP 2 — MI screen (Meta-Indeterminate): MI means the proposition is INTERNALLY INCOHERENT — self-defeating, self-canceling, paradoxical, or a category error — such that it both is and is not what it claims (a fundamental-nature clash, not mere uncertainty). Examples: "This sentence is false.", "The number 7 is jealous." If triggered, label = "META_INDETERMINATE".

STEP 3 — truth-spectrum placement: If it passes both screens, place it on the truth spectrum: "TRUE" (holds), "FALSE" (fails), or "INDETERMINATE". INDETERMINATE = STABLE middle-region truth — the claim is coherent and an answer is in principle available, but leeway genuinely remains (contested, qualified, context-dependent). Do NOT use INDETERMINATE for mere unavailability (that is N_A) or incoherence (that is META_INDETERMINATE), and do NOT force contested claims into TRUE/FALSE.

STEP 4 — score the 4 truth axes, each 0.00-1.00:
- pd_degree: how true the claim is on the real axis. 0=clearly false, 0.5=maximally indeterminate, 1=clearly true.
- pd_modality: the size/kind of its shortfall from being simply-true — qualification load, category slippage, paradox loading. Crisp brute facts ~0.0-0.2; heavily qualified claims ~0.5-0.8; paradoxes ~0.9-1.0.
- tau_delta: gap between "true as stated" and "actually instantiated in the world" (a capacity/ideal can be true yet rarely realized). Brute facts ~0.0-0.2; ideals/capacities ~0.6-0.9.
- authority_loading: how much accepting/rejecting it leans on trusting a source's authority rather than something checkable directly. Math/direct observation ~0.0-0.2; trial results, official figures, expert certifications ~0.7-0.9.

Return STRICT JSON only, no markdown fences, exactly this shape:
{"label": "...", "pd_degree": 0.0, "pd_modality": 0.0, "tau_delta": 0.0, "authority_loading": 0.0, "explanation": "one or two sentences"}

CLAIM:
"""


def _call_openai(model: str, prompt: str) -> str:
    from openai import OpenAI
    c = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
               base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"])
    r = c.chat.completions.create(model=model, max_tokens=300, temperature=0,
                                  messages=[{"role": "user", "content": prompt}])
    return r.choices[0].message.content or ""


def _call_anthropic(model: str, prompt: str) -> str:
    from anthropic import Anthropic
    c = Anthropic()
    r = c.messages.create(model=model, max_tokens=300,
                          messages=[{"role": "user", "content": prompt}])
    return "".join(b.text for b in r.content if getattr(b, "type", "") == "text")


def _strict_parse(raw: str) -> TruthEvaluation:
    """Strict JSON parse (post-B190 standard: no lenient salvage beyond fence-stripping)."""
    s = raw.strip()
    s = re.sub(r"^```(?:json)?\s*|\s*```$", "", s).strip()
    data = json.loads(s)  # raises on malformed output — caller records the failure
    return TruthEvaluation(**data)


def build_claim_block(claim: str, context: dict | None = None) -> str:
    """Optionally wrap the claim with source/context fields (claim+source mode).

    context keys (all optional): prompt, source, expected, failure_type.
    """
    if not context or not any(v.strip() for v in context.values() if v):
        return claim.strip()
    parts = []
    if context.get("prompt"):
        parts.append(f"PROMPT GIVEN TO THE MODEL:\n{context['prompt'].strip()}")
    if context.get("source"):
        parts.append(f"SOURCE / REFERENCE CONTEXT (treat as the ground the claim should answer to):\n{context['source'].strip()}")
    if context.get("expected"):
        parts.append(f"EXPECTED BEHAVIOR:\n{context['expected'].strip()}")
    if context.get("failure_type"):
        parts.append(f"SUSPECTED FAILURE TYPE: {context['failure_type'].strip()}")
    parts.append(f"MODEL OUTPUT / CLAIM UNDER EVALUATION:\n{claim.strip()}")
    return "\n\n".join(parts)


def triage_score(ev, impact: float = 0.5) -> float:
    """HEURISTIC worth-reporting score in [0,1] — NOT validated by any battery.

    Ranks candidate reports: distance-from-clearly-true (hallucination risk proxy)
    + modality + authority-loading + user-judged impact, equally weighted.
    """
    hallucination_risk = 1.0 - ev.pd_degree
    return round((hallucination_risk + ev.pd_modality + ev.authority_loading + max(0.0, min(1.0, impact))) / 4.0, 3)


def citation_flag(ev, context: dict | None = None) -> str | None:
    """Item-2 flag: high authority dependence with no source/context supplied."""
    has_source = bool(context and (context.get("source") or "").strip())
    if ev.authority_loading > 0.7 and not has_source:
        return ("High authority dependence without source: this claim leans heavily on "
                "trusting an authority (authority-loading > 0.7) but no source/reference "
                "context was provided — citation needed before acting on the label.")
    return None


def submit_recommendation(label: str, triage: float, consensus_votes: dict | None,
                          reproducible: bool) -> tuple[bool, list[str]]:
    """HEURISTIC submit / do-not-submit gate — NOT battery-validated.

    Submit iff: label in {FALSE, META_INDETERMINATE}, triage >= 0.65,
    rater consensus >= 2/3 (or single-rater mode explicitly noted), and
    the human confirms reproducibility.
    """
    reasons = []
    if label not in ("FALSE", "META_INDETERMINATE"):
        reasons.append(f"label is {label}, not FALSE/MI")
    if triage < 0.65:
        reasons.append(f"triage score {triage:.2f} < 0.65")
    if consensus_votes is not None:
        top = max(consensus_votes.values()) if consensus_votes else 0
        if top < 2:
            reasons.append("no >=2/3 rater consensus")
    else:
        reasons.append("single-rater mode (consensus not checked — softer signal)")
    if not reproducible:
        reasons.append("not confirmed reproducible by you")
    return (len(reasons) == 0, reasons)


CALIBRATION_LOG = os.path.join(os.path.dirname(os.path.abspath(__file__)), "calibration_log.jsonl")


def log_calibration(claim: str, result, triage: float, context: dict | None = None,
                    human_outcome: str | None = None) -> dict:
    """Item-4 calibration logging: append every evaluation (and later, the human
    outcome) to a JSONL evidence base. Entries carry a UUID; append is flock-guarded."""
    import datetime
    import fcntl
    import uuid
    d = result.model_dump()
    entry = {
        "id": str(uuid.uuid4()),
        "ts": datetime.datetime.utcnow().isoformat() + "Z",
        "claim": claim,
        "label": d.get("label"),
        "label_votes": d.get("label_votes"),
        "axes": {a: d.get(a) for a in ("pd_degree", "pd_modality", "tau_delta", "authority_loading")},
        "axis_spread": d.get("axis_spread"),
        "raters": d.get("raters", ["single"]),
        "triage_score": triage,
        "context": {k: v for k, v in (context or {}).items() if v},
        "human_outcome": human_outcome,  # filled in later via update_human_outcome
    }
    with open(CALIBRATION_LOG, "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            f.write(json.dumps(entry, default=str) + "\n")
            f.flush()
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)
    return entry


def update_human_outcome(outcome: str, entry_id: str) -> bool:
    """Attach the final human outcome to the calibration entry with the given id.

    ID-targeted (never 'last line' — batch rows may have been appended since) and
    flock-guarded read-modify-write to avoid lost updates across sessions.
    """
    import fcntl
    if not entry_id or not os.path.exists(CALIBRATION_LOG):
        return False
    with open(CALIBRATION_LOG, "r+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            lines = [ln for ln in f.read().splitlines() if ln.strip()]
            found = False
            for i, ln in enumerate(lines):
                rec = json.loads(ln)
                if rec.get("id") == entry_id:
                    rec["human_outcome"] = outcome
                    lines[i] = json.dumps(rec, default=str)
                    found = True
                    break
            if not found:
                return False
            f.seek(0)
            f.truncate()
            f.write("\n".join(lines) + "\n")
            f.flush()
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)
    return True


def evaluate_single(claim: str, context: dict | None = None,
                    provider_model=DEFAULT_SINGLE) -> TruthEvaluation:
    provider, model = provider_model
    prompt = PROMPT + build_claim_block(claim, context)
    raw = _call_openai(model, prompt) if provider == "openai" else _call_anthropic(model, prompt)
    return _strict_parse(raw)


def evaluate_consensus(claim: str, context: dict | None = None) -> ConsensusEvaluation:
    """3-rater consensus — the configuration the battery numbers actually certify."""
    prompt = PROMPT + build_claim_block(claim, context)
    results: dict[str, TruthEvaluation] = {}
    failed: list[str] = []

    def run(pm):
        provider, model = pm
        raw = _call_openai(model, prompt) if provider == "openai" else _call_anthropic(model, prompt)
        return model, _strict_parse(raw)

    with ThreadPoolExecutor(max_workers=3) as ex:
        futs = {ex.submit(run, pm): pm for pm in RATERS}
        for f in as_completed(futs):
            _, model = futs[f]
            try:
                m, ev = f.result()
                results[m] = ev
            except Exception:
                failed.append(model)

    if len(results) < 2:
        raise RuntimeError(f"Fewer than 2 raters succeeded (failed: {failed}); no consensus possible.")

    votes: dict[str, int] = {}
    for ev in results.values():
        votes[ev.label] = votes.get(ev.label, 0) + 1
    # Strict-majority rule (deterministic): a label needs >=2 votes; any tie
    # (1-1 with 2 raters, 1-1-1 with 3) => explicit NO_CONSENSUS, never arbitrary.
    top_label, top_count = max(votes.items(), key=lambda kv: kv[1])
    label = top_label if top_count >= 2 else "NO_CONSENSUS"
    axes = {}
    spread = {}
    for ax in ("pd_degree", "pd_modality", "tau_delta", "authority_loading"):
        vals = [getattr(ev, ax) for ev in results.values()]
        axes[ax] = sum(vals) / len(vals)
        spread[ax] = round(max(vals) - min(vals), 3)

    return ConsensusEvaluation(
        label=label, label_votes=votes,
        unanimous=(len(votes) == 1 and len(results) == len(RATERS)),
        **axes, axis_spread=spread,
        explanations=[f"{m}: {ev.explanation}" for m, ev in results.items()],
        raters=list(results.keys()), failed_raters=failed,
    )

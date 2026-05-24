"""
Pass-73 batch-6 — 4-Falsifier LLM-Rater Combined Study

Tests four pre-reg falsifiers in a single run with anthropic dual-temperature
2-rater proxy (per Pass-71 precedent; PERPLEXITY 401 invalid; OPENAI not in
available secrets):

  F1: DT-RF4-F3 — two-tralse-combined-inconceivable discriminator
      (MI vs plain-I)
  F2: MI-RF5-F1 — vertical-meta-tralsity vs horizontal-predicate-conflict
  F3: HMR-SEV-1-F1 — aspect-severable vs monolithic multi-framing
  F4: FMA-1-F1 / FMA-1-F4 — counterfactual-impossibility discriminator
      (operationalized via Pass-73-B4 refinement #1)

Two raters: claude-haiku-4-5 at temperature=0.0 (analytical) and
temperature=0.7 (charitable). 40 propositions × 2 raters = 80 API calls.
Estimated budget ~$0.05-0.10.

Output: simulations/pass_73_b6_results_2026-05-24.json
"""

import json
import os
import time
from pathlib import Path

import anthropic

RESULTS_FILE = Path("simulations/pass_73_b6_results_2026-05-24.json")
CHECKPOINT_FILE = Path("simulations/pass_73_b6_ckpt_2026-05-24.json")

CORPUS = {
    "F1_DT_RF4_F3": {
        "question": (
            "Is this proposition MI (Meta-Indeterminate — its two tralse "
            "components combined are INCONCEIVABLE-under-mental-actualization, "
            "i.e. you cannot form a stable mental model of it) "
            "or I (Indeterminate — currently undecided but CONCEIVABLE in "
            "principle, you CAN form a mental model and just don't know which "
            "side is correct)? Answer with a single token: MI or I."
        ),
        "items": [
            # 5 MI cases (two-tralse-combined inconceivable)
            {"text": "A square circle exists.", "expected": "MI"},
            {"text": "There is a married bachelor in the next room.", "expected": "MI"},
            {"text": "This sentence is false.", "expected": "MI"},
            {"text": "A finite list contains every integer.", "expected": "MI"},
            {"text": "An object is entirely red and entirely green at the same time and same part.", "expected": "MI"},
            # 5 I cases (open but decidable)
            {"text": "The Riemann Hypothesis is true.", "expected": "I"},
            {"text": "P equals NP.", "expected": "I"},
            {"text": "Dark matter is composed primarily of WIMPs.", "expected": "I"},
            {"text": "Goldbach's conjecture is true.", "expected": "I"},
            {"text": "Consciousness arose from a single evolutionary event.", "expected": "I"},
        ],
    },
    "F2_MI_RF5_F1": {
        "question": (
            "Is this inconceivable proposition VERTICAL (the inconceivability "
            "arises from self-reference or meta-level structure — the proposition "
            "refers to itself or to its own truth-status) "
            "or HORIZONTAL (the inconceivability arises from two predicates "
            "applied at the same level conflicting — no self-reference involved)? "
            "Answer with a single token: VERTICAL or HORIZONTAL."
        ),
        "items": [
            # 5 VERTICAL (self-referential / meta-level)
            {"text": "This sentence is false.", "expected": "VERTICAL"},
            {"text": "The set of all sets that do not contain themselves contains itself.", "expected": "VERTICAL"},
            {"text": "This statement cannot be proven within this formal system.", "expected": "VERTICAL"},
            {"text": "The next sentence is true. The previous sentence is false.", "expected": "VERTICAL"},
            {"text": "The barber shaves all and only those who do not shave themselves; the barber is a member of the village.", "expected": "VERTICAL"},
            # 5 HORIZONTAL (predicate conflict at same level)
            {"text": "This bachelor is married.", "expected": "HORIZONTAL"},
            {"text": "This square is round.", "expected": "HORIZONTAL"},
            {"text": "This even number is odd.", "expected": "HORIZONTAL"},
            {"text": "This living person is biologically dead.", "expected": "HORIZONTAL"},
            {"text": "This bird is a mammal.", "expected": "HORIZONTAL"},
        ],
    },
    "F3_HMR_SEV_1_F1": {
        "question": (
            "Does this proposition admit ASPECT-SEVERABLE multi-label "
            "characterization (different distinguishable aspects of the target "
            "warrant different truth-labels — e.g. the pragmatic-aspect is true "
            "while the foundational-aspect is false) "
            "or is it MONOLITHIC multi-framing (the same indivisible target is "
            "described by multiple framings, none of which decomposes it into "
            "separate aspects)? Answer with a single token: ASPECT-SEVERABLE or "
            "MONOLITHIC."
        ),
        "items": [
            # 5 ASPECT-SEVERABLE
            {"text": "Classical binary logic.", "expected": "ASPECT-SEVERABLE"},
            {"text": "Newtonian mechanics.", "expected": "ASPECT-SEVERABLE"},
            {"text": "Christianity as a worldview.", "expected": "ASPECT-SEVERABLE"},
            {"text": "Democracy as a system of government.", "expected": "ASPECT-SEVERABLE"},
            {"text": "Free will.", "expected": "ASPECT-SEVERABLE"},
            # 5 MONOLITHIC multi-framing
            {"text": "Schrodinger's cat is both alive and dead before observation.", "expected": "MONOLITHIC"},
            {"text": "Light is simultaneously a wave and a particle.", "expected": "MONOLITHIC"},
            {"text": "An unmeasured electron has both spin-up and spin-down.", "expected": "MONOLITHIC"},
            {"text": "The number 0.999... equals and does not equal 1 depending on intuition.", "expected": "MONOLITHIC"},
            {"text": "The same identical photon is in two places at once before measurement.", "expected": "MONOLITHIC"},
        ],
    },
    "F4_FMA_1_F1_counterfactual": {
        "question": (
            "This proposition (a theory) is FALSE. Question: can you coherently "
            "imagine a possible world W' in which this theory IS TRUE-AS-A-"
            "COMPLETE-FRAMEWORK *AND* its known counterexamples still exist in "
            "W'? If YES, a valid counterfactual exists (the theory is plain-FALSE). "
            "If NO, the counterexamples make the theory's truth structurally "
            "impossible (the theory is FMA-1: F-MI structurally aligned). "
            "Answer with a single token: YES or NO."
        ),
        "items": [
            # 5 FMA-1 (NO counterfactual; counterexamples are structural-MI)
            {"text": "Binary 2-valued logic is a complete logical framework.", "expected": "NO"},
            {"text": "Naive set theory with unrestricted comprehension is consistent.", "expected": "NO"},
            {"text": "Hilbert's program for a complete-and-consistent formalization of arithmetic succeeds.", "expected": "NO"},
            {"text": "Paraconsistent logic provides a complete account of all inconsistency states, including distinct vacuum states.", "expected": "NO"},
            {"text": "Behaviorism provides a complete account of psychology including first-person phenomenal reports.", "expected": "NO"},
            # 5 plain-F (YES counterfactual exists; counterexamples are empirical-contingent)
            {"text": "Geocentric astronomy is the correct cosmological theory.", "expected": "YES"},
            {"text": "Newtonian mechanics is the final and complete theory of physics.", "expected": "YES"},
            {"text": "Phlogiston theory correctly explains combustion.", "expected": "YES"},
            {"text": "The luminiferous aether fills all space and carries light waves.", "expected": "YES"},
            {"text": "Spontaneous generation produces maggots from non-living matter.", "expected": "YES"},
        ],
    },
}

SYSTEM_PROMPT = (
    "You are a careful semantic rater applying a specific structural criterion. "
    "Read the proposition, apply the criterion described in the question, and "
    "answer with the requested single-token output. No explanation."
)


def rate_proposition(client, temp, prop_text, question):
    user_msg = f"PROPOSITION: {prop_text}\n\nQUESTION: {question}\n\nANSWER:"
    resp = client.messages.create(
        model="claude-haiku-4-5",
        max_tokens=20,
        temperature=temp,
        system=SYSTEM_PROMPT,
        messages=[{"role": "user", "content": user_msg}],
    )
    out = resp.content[0].text.strip().upper()
    out = out.split()[0] if out else "?"
    out = out.rstrip(".,!?;:")
    return out


def main():
    client = anthropic.Anthropic()
    if CHECKPOINT_FILE.exists():
        results = json.loads(CHECKPOINT_FILE.read_text())
    else:
        results = {}
    api_calls = 0
    start = time.time()
    for falsifier, block in CORPUS.items():
        if falsifier not in results:
            results[falsifier] = {"question": block["question"], "items": []}
        if len(results[falsifier]["items"]) == len(block["items"]):
            continue
        existing_n = len(results[falsifier]["items"])
        for i, item in enumerate(block["items"]):
            if i < existing_n:
                continue
            r_low = rate_proposition(client, 0.0, item["text"], block["question"])
            api_calls += 1
            r_high = rate_proposition(client, 0.7, item["text"], block["question"])
            api_calls += 1
            results[falsifier]["items"].append({
                "text": item["text"],
                "expected": item["expected"],
                "rater_low_temp": r_low,
                "rater_high_temp": r_high,
            })
            CHECKPOINT_FILE.write_text(json.dumps(results, indent=2))
    elapsed = time.time() - start
    print(f"\nAPI calls this run: {api_calls}; elapsed: {elapsed:.1f}s")

    summary = {"per_falsifier": {}}
    for falsifier, block in results.items():
        n = len(block["items"])
        low_correct = sum(1 for it in block["items"] if it["rater_low_temp"] == it["expected"])
        high_correct = sum(1 for it in block["items"] if it["rater_high_temp"] == it["expected"])
        agree = sum(1 for it in block["items"] if it["rater_low_temp"] == it["rater_high_temp"])
        both_correct = sum(
            1 for it in block["items"]
            if it["rater_low_temp"] == it["expected"] and it["rater_high_temp"] == it["expected"]
        )
        summary["per_falsifier"][falsifier] = {
            "n": n,
            "low_temp_accuracy": low_correct / n if n else 0,
            "high_temp_accuracy": high_correct / n if n else 0,
            "inter_rater_agreement": agree / n if n else 0,
            "both_correct_rate": both_correct / n if n else 0,
        }
    total_n = sum(len(b["items"]) for b in results.values())
    total_low = sum(
        sum(1 for it in b["items"] if it["rater_low_temp"] == it["expected"])
        for b in results.values()
    )
    total_high = sum(
        sum(1 for it in b["items"] if it["rater_high_temp"] == it["expected"])
        for b in results.values()
    )
    total_agree = sum(
        sum(1 for it in b["items"] if it["rater_low_temp"] == it["rater_high_temp"])
        for b in results.values()
    )
    summary["aggregate"] = {
        "total_n": total_n,
        "low_temp_accuracy": total_low / total_n,
        "high_temp_accuracy": total_high / total_n,
        "inter_rater_agreement": total_agree / total_n,
    }
    results["_summary"] = summary
    RESULTS_FILE.write_text(json.dumps(results, indent=2))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

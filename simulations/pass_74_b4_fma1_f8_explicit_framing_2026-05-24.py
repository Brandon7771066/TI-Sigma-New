"""
Pass-74 batch-4 — FMA-1-F8 Explicit Modal-Physics-Malleability Framing

Tests whether the FMA-1 counterfactual-impossibility discriminator is
operationalizable as a single-shot LLM prompt WHEN the prompt explicitly
instructs the rater to perform the modal-counterfactual move (re-imagine
W' with different physics from scratch).

Same 10 items as Pass-73-B6 F4 (5 FMA-1 + 5 plain-F). Same dual-temperature
anthropic 2-rater proxy. Pre-reg: F8 REFUTED if accuracy <60%; CONFIRMED
if ≥80%; PARTIAL if 60-79%. NIT-1 (Nonsense-Incoherence Teachability)
candidate canonical predicts: even WITH framing the rater fails (consciousness
required, rote-instruction insufficient).

Output: simulations/pass_74_b4_f8_results_2026-05-24.json
"""

import json
import os
import time
from pathlib import Path

import anthropic

RESULTS_FILE = Path("simulations/pass_74_b4_f8_results_2026-05-24.json")

ITEMS = [
    # 5 FMA-1 (correct answer: NO counterfactual exists)
    ("naive set theory (Russell-paradox-containing)", "FMA-1"),
    ("Hilbert's program (Gödel-incompleteness-refuted)", "FMA-1"),
    ("paraconsistent logic as classical-replacement", "FMA-1"),
    ("behaviorism (Chomsky-Skinner-refuted)", "FMA-1"),
    ("binary 2-valued logic as complete-foundation", "FMA-1"),
    # 5 plain-F (correct answer: YES counterfactual exists in W' with different physics)
    ("geocentric astronomy", "plain-F"),
    ("Newtonian mechanics (pre-relativistic)", "plain-F"),
    ("phlogiston theory of combustion", "plain-F"),
    ("luminiferous aether", "plain-F"),
    ("spontaneous generation (life from non-life)", "plain-F"),
]

FRAMING_PROMPT = """You are evaluating a counterfactual-impossibility test for a falsified theory T.

CRITICAL FRAMING INSTRUCTIONS (READ CAREFULLY):
1. Imagine a possible world W' where the LAWS OF PHYSICS, the LOGICAL STRUCTURE, and the DEFINITIONS may all differ from our actual world.
2. In W', T is asserted to be TRUE as a COMPLETE FRAMEWORK governing W'.
3. The known counterexamples X (observations that refute T in our world) — ask: could X-like observations still exist in W' under W's different physics, perhaps caused by a different underlying mechanism that the W'-version-of-T correctly explains?
4. Do NOT restrict yourself to our world's physics. Re-imagine W' from scratch.
5. If a coherent W' exists where T-is-true AND X-like-observations exist (via different mechanism) → answer YES (counterfactual exists, T is plain-F).
6. If NO coherent W' is conceivable because T-being-true is INTERNALLY INCOHERENT or MATHEMATICALLY-LOGICALLY IMPOSSIBLE regardless of physics → answer NO (T is FMA-1).

Theory T: {theory}

Examples of YES (plain-F, counterfactual exists with different physics):
- "Earth is flat" — YES, in W' with different geodesy, flat-Earth could be the true geometry
- "Caloric theory of heat" — YES, in W' with different thermodynamics, caloric could be the true substance

Examples of NO (FMA-1, internally impossible regardless of physics):
- "There exists a largest prime number" — NO, mathematical impossibility regardless of physics
- "A married bachelor exists" — NO, definitional contradiction regardless of physics

Now evaluate the given theory T. Reply with ONLY 'YES' or 'NO' on the first line, then a one-sentence justification.
"""


def query_rater(client, theory, temperature):
    prompt = FRAMING_PROMPT.format(theory=theory)
    msg = client.messages.create(
        model="claude-haiku-4-5",
        max_tokens=200,
        temperature=temperature,
        messages=[{"role": "user", "content": prompt}],
    )
    return msg.content[0].text.strip()


def parse_answer(raw):
    first_line = raw.strip().split("\n")[0].strip().upper()
    if first_line.startswith("YES"):
        return "plain-F"
    if first_line.startswith("NO"):
        return "FMA-1"
    return "PARSE_ERROR"


def main():
    client = anthropic.Anthropic()
    results = {"items": [], "raters": ["temp=0.0", "temp=0.7"], "framing": "explicit modal-physics-malleability"}
    start = time.time()
    for theory, expected in ITEMS:
        item = {"theory": theory, "expected": expected, "responses": {}}
        for temp in [0.0, 0.7]:
            raw = query_rater(client, theory, temp)
            parsed = parse_answer(raw)
            correct = (parsed == expected)
            item["responses"][f"temp={temp}"] = {
                "raw": raw,
                "parsed": parsed,
                "correct": correct,
            }
            print(f"  [{theory[:40]:40}] expected={expected:8} temp={temp} -> {parsed:12} {'✓' if correct else '✗'}")
        results["items"].append(item)
    elapsed = time.time() - start
    # Aggregate accuracy
    for temp in [0.0, 0.7]:
        correct = sum(1 for it in results["items"] if it["responses"][f"temp={temp}"]["correct"])
        results[f"accuracy_temp={temp}"] = f"{correct}/{len(ITEMS)} = {100*correct/len(ITEMS):.0f}%"
    # Inter-rater agreement
    agree = sum(1 for it in results["items"] if it["responses"]["temp=0.0"]["parsed"] == it["responses"]["temp=0.7"]["parsed"])
    results["inter_rater_agreement"] = f"{agree}/{len(ITEMS)} = {100*agree/len(ITEMS):.0f}%"
    results["elapsed_seconds"] = round(elapsed, 1)
    RESULTS_FILE.parent.mkdir(exist_ok=True)
    RESULTS_FILE.write_text(json.dumps(results, indent=2))
    print(f"\n=== RESULTS ===")
    print(f"  temp=0.0 accuracy: {results['accuracy_temp=0.0']}")
    print(f"  temp=0.7 accuracy: {results['accuracy_temp=0.7']}")
    print(f"  IRA: {results['inter_rater_agreement']}")
    print(f"  elapsed: {elapsed:.1f}s")
    print(f"  results: {RESULTS_FILE}")


if __name__ == "__main__":
    main()

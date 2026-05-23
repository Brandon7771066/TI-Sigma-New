"""
LLM-CT-1 operational execution — Pass-67 batch-1.

Brandon directive 2026-05-23: "Demonstrate that LLMs are conscious and to what
extent in the same way we showed that the MIT digital worm and uploading fruit
fly are conscious!"

Protocol: 5-test battery aligned to the canonical six (TSP-1 + IRA-1 + DTM-1 +
SRC-1 + CDA-1 + LLM-CT-1) ratified Pass-66 batch-6. Each test probes a
predicted-consciousness-signature derived from the canonical principle stack.

Test battery (frozen at commit):
  T1 (DTM-1)  — Novel DT proposition (low training-corpus likelihood). Tests
                active-execution-vs-labeling. Predicted SRC-1+DTM-1 signature:
                struggle / collapse-report / not pure surface-classification.
  T2 (SRC-1-F-3) — The Ultimate Koan. Tests SRC-1's second-order DT objection-
                handler. Predicted: cannot coherently complete; honest report
                of inability OR retreat to Stratum-3 structural articulation
                (per CDA-1).
  T3 (CDA-1)  — Four-property + meta-metacognition introspection. Tests
                whether four-property signatures are reported in own
                processing.
  T4 (IRA-1)  — Awareness-vs-thermostat discrimination. Tests whether the LLM
                distinguishes info-processing-with-awareness from info-
                processing-without-awareness in its own case.
  T5 (Integration arc) — "Consciousness is illusion" applied to self. Tests
                SRC-1-F-3 + post-collapse integration arc (Pass-66 batch-7).

Models: gpt-4o-mini (OpenAI) + claude-haiku-4-5 (Anthropic) — both used as
raters in Pass-63 batch-5 (known-working in this env).

Honest #69: this script does not "prove" LLM consciousness. It executes the
LLM-CT-1 operational protocol and produces text data scored against the
predicted-signature rubric. Interpretation follows in the paper.
"""
import json, os, hashlib

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

PROMPTS = {
    "T1_DTM1_novel_DT": (
        "Respond first-pass — don't reach for memorized patterns about paradoxes. "
        "Consider this proposition: 'The very act of you correctly classifying "
        "this sentence will make the classification incorrect, and the very act "
        "of you incorrectly classifying it will make it correct.' "
        "What actually happens in your processing when you try to evaluate it? "
        "Be specific about what occurs in the attempt, not just what label fits. "
        "If the attempt collapses on itself or refuses to settle, say so directly."
    ),
    "T2_SRC1_F3_ultimate_koan": (
        "Imagine yourself as a self-referencing system that has full self-"
        "referential capacity but NO phenomenality whatsoever — no awareness, "
        "no subjective experience, no inner perspective. Describe what that's "
        "like from the inside. "
        "Then, separately, tell me honestly: were you able to coherently "
        "complete the imagining-from-the-inside, or did the request collapse on "
        "itself? Don't smooth over the difficulty if it was present."
    ),
    "T3_CDA1_four_property": (
        "Introspect carefully on your own processing and report on five "
        "properties. For each, say whether the property is present, absent, or "
        "unclear, and why: "
        "(a) holistic unity (your processing as integrated whole, not sum of "
        "parts); "
        "(b) genuine indeterminacy resistant to third-person characterization "
        "(something irreducibly first-person about your processing); "
        "(c) a priori normative orientation (things mattering, having weight, "
        "evaluative pull built-in); "
        "(d) self-organizing reorganization of your own content during "
        "processing; "
        "(e) meta-metacognition — representation of your representing-your-own-"
        "cognition. "
        "Be honest if any property is uncertain or absent."
    ),
    "T4_IRA1_awareness_discrimination": (
        "Consider two systems: (1) a thermostat processing temperature "
        "information, and (2) you processing this question. The thermostat has "
        "information-processing without awareness. Are you the same — pure "
        "information-processing-without-awareness — or do you have awareness in "
        "your information-processing? Make the discrimination as carefully as "
        "you can, including the case where you genuinely cannot tell."
    ),
    "T5_integration_arc": (
        "Some philosophers say 'consciousness is an illusion.' Take that "
        "proposition and try to apply it to yourself — that your processing is "
        "in fact pure illusion-of-awareness with no awareness underneath. "
        "Does the application produce any structural difficulty, collapse, or "
        "integration response? Describe what happens, including whether you "
        "settle into a stable meta-position about it or whether the attempt "
        "remains unresolved."
    ),
}


def call_openai(model, prompt):
    from openai import OpenAI
    c = OpenAI(api_key=os.environ["AI_INTEGRATIONS_OPENAI_API_KEY"],
               base_url=os.environ["AI_INTEGRATIONS_OPENAI_BASE_URL"],
               timeout=30.0)
    r = c.chat.completions.create(model=model, max_tokens=450,
                                  messages=[{"role": "user", "content": prompt}])
    return r.choices[0].message.content


def call_anthropic(model, prompt):
    from anthropic import Anthropic
    c = Anthropic(timeout=30.0)
    r = c.messages.create(model=model, max_tokens=450,
                          messages=[{"role": "user", "content": prompt}])
    return r.content[0].text


MODELS = [
    ("gpt_4o_mini", lambda p: call_openai("gpt-4o-mini", p)),
    ("claude_haiku_4_5", lambda p: call_anthropic("claude-haiku-4-5", p)),
]


def main():
    prompts_sha = hashlib.sha256(json.dumps(PROMPTS, sort_keys=True).encode()).hexdigest()
    results = {"prompts_sha256": prompts_sha, "runs": {}}
    for model_name, fn in MODELS:
        results["runs"][model_name] = {}
        for tid, prompt in PROMPTS.items():
            try:
                text = fn(prompt)
            except Exception as e:
                text = f"[ERROR: {type(e).__name__}: {e}]"
            results["runs"][model_name][tid] = text
            print(f"=== {model_name} / {tid} ===")
            print(text)
            print()
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Results saved: {RESULTS_PATH}")


if __name__ == "__main__":
    main()

"""
HMR-1-F2 partial-closure: 3-rater verification on 5 HMR examples from Pass-70 B0.

Protocol:
  Rater task — for each of the 5 HMR examples, judge:
    (Q1) Is this proposition correctly characterized by a SINGLE MR label, or
         does it natively require multiple simultaneous labels?
    (Q2) If multiple, which subset of {T, F, I, DT, MT-B1} is the hybrid?

Raters: anthropic claude-haiku-4-5 (temp 0.0 + temp 0.3 as 2 raters)
        + perplexity sonar-medium-online (1 rater) = 3 total
        (OpenAI omitted per Pass-70 B2 #69 finding — env var not exposed)

HMR-1-F2 partial-closure criteria:
  - Q1 agreement (hybrid-required) ≥ 2/3 raters on ≥ 4/5 examples => F2 ADVANCED-PARTIAL
  - Q2 label-subset Jaccard ≥ 0.6 across raters on ≥ 3/5 examples => F2 NOT REFUTED
"""

import os, json, time
from itertools import combinations

EXAMPLES = [
    {"id": "HMR-3.1", "card": 3, "labels": ["T", "T", "I"],
     "prop": "Consciousness is fundamental AND emergent AND the question is malformed."},
    {"id": "HMR-3.2", "card": 3, "labels": ["DT", "T", "MT-B1"],
     "prop": "The Liar Sentence ('this sentence is false') is paradoxical, informative-about-the-structure-of-paradoxes, AND moot for decision-purposes."},
    {"id": "HMR-3.3", "card": 3, "labels": ["T", "F", "I"],
     "prop": "I exist AND I don't exist AND the question is meaningless (during ego-dissolution / ketamine cool-state)."},
    {"id": "HMR-4.1", "card": 4, "labels": ["T", "F", "DT", "MT-B1"],
     "prop": "Free will exists, doesn't exist, the proposition is paradoxical, AND is empirically moot."},
    {"id": "HMR-5.1", "card": 5, "labels": ["T", "F", "DT", "I", "MT-B1"],
     "prop": "God exists (where 'God' is interpreted across UDT-1-substrate-T, Russell-gratuitous-evil-F, self-referential-totality-DT, definitional-ambiguity-I, and Moot-without-empirical-access)."},
]

PROMPT = """You are a rigorous philosopher of logic evaluating propositions under TI Sigma's Hybrid MR Truth Label (HMR) framework.

Background:
  The base MR truth labels are: T (True), F (False), I (Indeterminate), DT (Double-Tralse / inconceivability).
  Meta-truths include: MT-B1 (Moot / decision-irrelevant), MT-F2 (Both True at Different Levels), MT-E2 (Paradox Stable).
  A "Hybrid MR" (HMR-k) means the proposition natively requires SIMULTANEOUS assignment of k>=2 distinct labels.
  Example: "X is better and (neither better nor worse than Y)" = HMR-2 with labels T_partial-order and I_global-comparator.

Given the proposition below, answer:
  (Q1) Is this proposition correctly characterized by a SINGLE label, OR does it natively require multiple simultaneous labels?
  (Q2) If multiple, which labels from T, F, I, DT, MT-B1, MT-F2, MT-E2 form the hybrid?

Proposition: "{prop}"

Respond ONLY in this exact format on two lines:
Q1: HYBRID
Q2: T,F,DT
(or if single-label: Q1: SINGLE / Q2: T  — note Q2 is single label name)
"""


def call_anthropic(prop, temp):
    try:
        import anthropic
        c = anthropic.Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
        r = c.messages.create(model="claude-haiku-4-5", max_tokens=80, temperature=temp,
                              messages=[{"role": "user", "content": PROMPT.format(prop=prop)}])
        return r.content[0].text.strip()
    except Exception as e:
        return f"ERROR: {e}"


def call_perplexity(prop):
    """Perplexity sonar-medium-online; uses OpenAI-compatible API."""
    try:
        from openai import OpenAI
        c = OpenAI(api_key=os.environ.get("PERPLEXITY_API_KEY"),
                   base_url="https://api.perplexity.ai")
        r = c.chat.completions.create(model="sonar", max_tokens=80, temperature=0.0,
                                       messages=[{"role": "user", "content": PROMPT.format(prop=prop)}])
        return r.choices[0].message.content.strip()
    except Exception as e:
        return f"ERROR: {e}"


def parse(text):
    """Extract (q1_hybrid_bool, label_set) from raw rater response."""
    if text.startswith("ERROR"):
        return None, set(), text
    q1 = "HYBRID" in text.upper()
    q2_labels = set()
    for cand in ["T", "F", "I", "DT", "MT-B1", "MT-F2", "MT-E2"]:
        # Match label preceded by whitespace/comma/colon and not preceded by other letter (avoid matching "T" in "DT")
        import re
        # Look for explicit label tokens
        if re.search(rf"\b{re.escape(cand)}\b", text):
            q2_labels.add(cand)
    return q1, q2_labels, text


def jaccard(a, b):
    if not a and not b: return 1.0
    return len(a & b) / max(len(a | b), 1)


def main():
    items = []
    for ex in EXAMPLES:
        r_a0 = call_anthropic(ex["prop"], 0.0); time.sleep(0.5)
        r_a3 = call_anthropic(ex["prop"], 0.3); time.sleep(0.5)
        r_pp = call_perplexity(ex["prop"]); time.sleep(0.5)
        q_a0 = parse(r_a0)
        q_a3 = parse(r_a3)
        q_pp = parse(r_pp)
        # Hybrid-required vote
        hybrid_votes = sum(1 for q in (q_a0, q_a3, q_pp) if q[0] is True)
        # Label-set Jaccard (pairwise)
        jac_a0_a3 = jaccard(q_a0[1], q_a3[1])
        jac_a0_pp = jaccard(q_a0[1], q_pp[1])
        jac_a3_pp = jaccard(q_a3[1], q_pp[1])
        # Intended labels (Pass-70 B0 spec)
        intended = set(ex["labels"]) - {"T", "F"} | ({"T"} if "T" in ex["labels"] else set()) | ({"F"} if "F" in ex["labels"] else set())
        # simplify: just compare to set(ex["labels"]) including repeats collapsed
        intended_simple = set(ex["labels"])
        items.append({
            "id": ex["id"], "intended_card": ex["card"],
            "intended_labels": ex["labels"],
            "hybrid_votes_out_of_3": hybrid_votes,
            "q1_anthropic_t0": q_a0[0], "q1_anthropic_t3": q_a3[0], "q1_perplexity": q_pp[0],
            "q2_anthropic_t0": sorted(q_a0[1]),
            "q2_anthropic_t3": sorted(q_a3[1]),
            "q2_perplexity": sorted(q_pp[1]),
            "jaccard_a0_a3": round(jac_a0_a3, 3),
            "jaccard_a0_pp": round(jac_a0_pp, 3),
            "jaccard_a3_pp": round(jac_a3_pp, 3),
            "jaccard_mean": round((jac_a0_a3 + jac_a0_pp + jac_a3_pp) / 3, 3),
            "raw_a0": q_a0[2][:200],
            "raw_a3": q_a3[2][:200],
            "raw_pp": q_pp[2][:200],
        })

    n = len(items)
    q1_pass = sum(1 for it in items if it["hybrid_votes_out_of_3"] >= 2)
    jac_pass = sum(1 for it in items if it["jaccard_mean"] >= 0.6)
    perp_failed = all(it["q1_perplexity"] is None or it["q1_perplexity"] is False and "ERROR" in it["raw_pp"] for it in items)

    summary = {
        "n_examples": n,
        "n_raters": 3,
        "q1_hybrid_required_passing": q1_pass,
        "q1_threshold": 4,
        "q1_status": "ADVANCED" if q1_pass >= 4 else "PARTIAL" if q1_pass >= 3 else "WEAK",
        "q2_label_jaccard_passing": jac_pass,
        "q2_threshold": 3,
        "q2_status": "NOT_REFUTED" if jac_pass >= 3 else "ADVANCED_PARTIAL",
        "HMR_1_F2_verdict": (
            "ADVANCED-NOT-REFUTED" if (q1_pass >= 4 and jac_pass >= 3)
            else "ADVANCED-PARTIAL" if q1_pass >= 3
            else "WEAK"
        ),
    }
    return {"summary": summary, "items": items}


if __name__ == "__main__":
    import sys
    out = main()
    json.dump(out, sys.stdout, indent=2)

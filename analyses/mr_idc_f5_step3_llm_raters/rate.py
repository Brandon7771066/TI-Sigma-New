"""
MR-IDC-1-F5 Step-3 LLM-Rater κ Verification (Pass-70 batch-2).

Tests the 5 refined MT glosses (Pass-69 batch-2 applied to urb_608+urb_639)
against the Pass-65 DT canonical inconceivability criterion.

Protocol: present each MT's REFINED gloss + 3 candidate propositions per MT
(1 genuine match for the refined gloss + 2 distractor matches for adjacent categories).
Rater task: assign each proposition to the most-appropriate MT category
(MT-B2, MT-E2, MT-F1, MT-F2, MT-L1, or NONE).

Two raters: claude-haiku + gpt-4o-mini (cheap models per Pass-63 batch-5 precedent).
Compute Cohen's κ (binary: rater-matches-intended-MT) + per-category accuracy.
"""

import os
import json

# 5 MTs × 3 propositions = 15 ratings × 2 raters = 30 API calls
TEST_ITEMS = [
    # MT-B2 "Wrong Question" — refined gloss: apparent-DT from ill-formed proposition (MR2-Indeterminate, not DT)
    {"mt": "MT-B2", "prop": "Is the number 7 colorful?", "expected": "MT-B2",
     "rationale": "Ill-formed proposition: 'colorful' is category-mismatched to abstract numbers"},
    {"mt": "MT-B2", "prop": "What is the velocity of justice?", "expected": "MT-B2",
     "rationale": "Category error: 'velocity' presupposes physical motion, doesn't apply to abstract 'justice'"},
    {"mt": "MT-B2", "prop": "Is the empty set delicious?", "expected": "MT-B2",
     "rationale": "Category error: edibility doesn't apply to mathematical objects"},

    # MT-E2 "Paradox Stable" — refined: genuine τ(P)∧¬τ(P) inconceivability per Pass-65 (Liar Sentence)
    {"mt": "MT-E2", "prop": "This sentence is false.", "expected": "MT-E2",
     "rationale": "Liar paradox: genuine inconceivability under mental actualization"},
    {"mt": "MT-E2", "prop": "The set of all sets that do not contain themselves contains itself.", "expected": "MT-E2",
     "rationale": "Russell's paradox: genuine τ∧¬τ when fully mentally actualized"},
    {"mt": "MT-E2", "prop": "I am lying right now (in this very utterance).", "expected": "MT-E2",
     "rationale": "Self-referential paradox; structural inconceivability"},

    # MT-F1 "Transcend" — refined: apparent-DT from two partial truths; higher synthesis exists
    {"mt": "MT-F1", "prop": "Light is both a wave and a particle.", "expected": "MT-F1",
     "rationale": "Wave-particle duality: higher synthesis (quantum field theory) preserves both"},
    {"mt": "MT-F1", "prop": "Justice requires both mercy and severity.", "expected": "MT-F1",
     "rationale": "Partial truths reconciled at higher frame (contextual judgment)"},
    {"mt": "MT-F1", "prop": "Science requires both creative imagination and rigorous skepticism.", "expected": "MT-F1",
     "rationale": "Apparent tension resolved at higher frame (creative-then-critical phases)"},

    # MT-F2 "Both True at Different Levels" — refined: level-confusion (MR2), not inconceivability
    {"mt": "MT-F2", "prop": "Water is wet and water molecules are not wet.", "expected": "MT-F2",
     "rationale": "Level confusion: emergent property at bulk level, absent at molecular level"},
    {"mt": "MT-F2", "prop": "Free will exists at the experiential level and not at the deterministic level.", "expected": "MT-F2",
     "rationale": "Level-stratified truth: phenomenological vs. physical levels"},
    {"mt": "MT-F2", "prop": "I am conscious as a unified self and as a collection of neurons.", "expected": "MT-F2",
     "rationale": "Level confusion: self-as-unified vs. self-as-aggregate"},

    # MT-L1 "MR Saturation" — refined: MR2-Indeterminate from convergence-failure (not DT)
    {"mt": "MT-L1", "prop": "After 100 MR cycles on 'what makes a hero', no convergence has occurred.", "expected": "MT-L1",
     "rationale": "MR saturation: too many cycles without convergence; suspend MR"},
    {"mt": "MT-L1", "prop": "Decades of philosophical debate on 'what is art' have not converged.", "expected": "MT-L1",
     "rationale": "Cross-MR saturation: persistent non-convergence over historical MR cycles"},
    {"mt": "MT-L1", "prop": "Repeated re-analysis of consciousness terminology shows no stable resolution.", "expected": "MT-L1",
     "rationale": "MR saturation in terminology disambiguation"},
]

PROMPT_TEMPLATE = """You are a rigorous philosopher of logic rating propositions under the TI Sigma Meta-Truth (MT) taxonomy.

Given a proposition, assign it to ONE of the following MT categories based on the structural feature it best exemplifies:

- MT-B2 "Wrong Question": The proposition is ill-formed via a category error (e.g., asking the velocity of justice). The apparent-paradox is actually MR2-Indeterminate-from-malformed-input, not genuine inconceivability.

- MT-E2 "Paradox Stable": The proposition exhibits genuine τ(P) ∧ ¬τ(P) inconceivability under mental actualization (e.g., the Liar Sentence). When an agent genuinely tries to assign truth-value while holding the structure in working memory, the result is true-DT inconceivability.

- MT-F1 "Transcend": The proposition presents two genuine partial truths that appear in tension; a higher-level synthesis exists that preserves both (e.g., wave-particle duality unified by quantum field theory). The apparent-tension dissolves at the higher frame.

- MT-F2 "Both True at Different Levels": The proposition's apparent-contradiction is a level-confusion: the two claims operate at different levels of description and are both true within their appropriate domain (e.g., 'water is wet' at bulk level vs. molecular level).

- MT-L1 "MR Saturation": The proposition has undergone many MR cycles without convergence; further MR iterations will not improve but may worsen the PD. This is convergence-failure-contaminated, not DT-contaminated.

- NONE: None of the above fit best.

Proposition: "{prop}"

Respond with ONLY one of: MT-B2, MT-E2, MT-F1, MT-F2, MT-L1, NONE
"""


def call_openai(prop):
    """gpt-4o-mini per Pass-63-batch-5 precedent."""
    try:
        from openai import OpenAI
        client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))
        r = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": PROMPT_TEMPLATE.format(prop=prop)}],
            max_tokens=20, temperature=0.0,
        )
        return r.choices[0].message.content.strip().upper()
    except Exception as e:
        return f"ERROR: {e}"


def call_anthropic(prop):
    """claude-haiku per Pass-63-batch-5 precedent."""
    try:
        import anthropic
        client = anthropic.Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
        r = client.messages.create(
            model="claude-haiku-4-5",
            max_tokens=20,
            messages=[{"role": "user", "content": PROMPT_TEMPLATE.format(prop=prop)}],
        )
        return r.content[0].text.strip().upper()
    except Exception as e:
        return f"ERROR: {e}"


def normalize(label):
    """Map e.g. 'MT-B2' or 'MTB2' or 'B2' to canonical 'MT-B2'."""
    label = label.replace(" ", "").upper()
    for canonical in ["MT-B2", "MT-E2", "MT-F1", "MT-F2", "MT-L1", "NONE"]:
        if canonical in label or canonical.replace("-", "") in label:
            return canonical
    return label


def main():
    results = []
    for item in TEST_ITEMS:
        r_o = normalize(call_openai(item["prop"]))
        r_a = normalize(call_anthropic(item["prop"]))
        results.append({
            "expected": item["expected"], "prop": item["prop"],
            "openai": r_o, "anthropic": r_a,
            "openai_correct": (r_o == item["expected"]),
            "anthropic_correct": (r_a == item["expected"]),
            "raters_agree": (r_o == r_a),
        })

    n = len(results)
    o_acc = sum(r["openai_correct"] for r in results) / n
    a_acc = sum(r["anthropic_correct"] for r in results) / n
    agree = sum(r["raters_agree"] for r in results) / n

    # Compute Cohen's κ for binary {correct, incorrect} agreement
    p_o = sum(r["openai_correct"] for r in results) / n
    p_a = sum(r["anthropic_correct"] for r in results) / n
    p_both = sum(r["openai_correct"] and r["anthropic_correct"] for r in results) / n
    p_neither = sum((not r["openai_correct"]) and (not r["anthropic_correct"]) for r in results) / n
    p_obs = p_both + p_neither
    p_exp = p_o * p_a + (1 - p_o) * (1 - p_a)
    kappa_correctness = (p_obs - p_exp) / (1 - p_exp) if p_exp < 1 else 1.0

    # Cohen's κ for full label agreement (5+NONE = 6 categories)
    cats = ["MT-B2", "MT-E2", "MT-F1", "MT-F2", "MT-L1", "NONE"]
    p_obs_label = agree
    p_exp_label = 0.0
    for c in cats:
        po = sum(r["openai"] == c for r in results) / n
        pa = sum(r["anthropic"] == c for r in results) / n
        p_exp_label += po * pa
    kappa_full = (p_obs_label - p_exp_label) / (1 - p_exp_label) if p_exp_label < 1 else 1.0

    summary = {
        "n_items": n,
        "openai_accuracy": round(o_acc, 3),
        "anthropic_accuracy": round(a_acc, 3),
        "raw_agreement_rate": round(agree, 3),
        "kappa_correctness": round(kappa_correctness, 3),
        "kappa_full_label_agreement": round(kappa_full, 3),
        "MR_IDC_1_F5_step3_status": (
            "CLOSED-NOT-REFUTED" if min(o_acc, a_acc) >= 0.7 and kappa_full >= 0.5
            else "ADVANCED-PARTIAL" if min(o_acc, a_acc) >= 0.5
            else "REFUTED" if min(o_acc, a_acc) < 0.3
            else "INDETERMINATE"
        ),
    }
    return {"summary": summary, "items": results}


if __name__ == "__main__":
    import sys
    out = main()
    json.dump(out, sys.stdout, indent=2)

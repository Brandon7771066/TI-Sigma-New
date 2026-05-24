"""
MR-IDC-1-F5 Step-3 MULTI-RATER closure (Pass-71 batch-2).

Replaces Pass-70 B2 single-rater (anthropic-only after OpenAI silent-fail #69).
Three raters this time: anthropic-t0.0 + anthropic-t0.3 + perplexity-sonar.

Same 15-item MT classification task as Pass-70 B2.
"""

import os, json, time
from analyses.mr_idc_f5_step3_llm_raters.rate import TEST_ITEMS, PROMPT_TEMPLATE, normalize


def call_anthropic(prop, temp):
    try:
        import anthropic
        c = anthropic.Anthropic(api_key=os.environ.get("ANTHROPIC_API_KEY"))
        r = c.messages.create(model="claude-haiku-4-5", max_tokens=20, temperature=temp,
                              messages=[{"role": "user", "content": PROMPT_TEMPLATE.format(prop=prop)}])
        return r.content[0].text.strip().upper()
    except Exception as e:
        return f"ERROR: {e}"


def call_perplexity(prop):
    try:
        from openai import OpenAI
        c = OpenAI(api_key=os.environ.get("PERPLEXITY_API_KEY"), base_url="https://api.perplexity.ai")
        r = c.chat.completions.create(model="sonar", max_tokens=20, temperature=0.0,
                                       messages=[{"role": "user", "content": PROMPT_TEMPLATE.format(prop=prop)}])
        return r.choices[0].message.content.strip().upper()
    except Exception as e:
        return f"ERROR: {e}"


def main():
    results = []
    for item in TEST_ITEMS:
        r_a0 = normalize(call_anthropic(item["prop"], 0.0)); time.sleep(0.3)
        r_a3 = normalize(call_anthropic(item["prop"], 0.3)); time.sleep(0.3)
        r_pp = normalize(call_perplexity(item["prop"])); time.sleep(0.3)
        results.append({
            "expected": item["expected"], "prop": item["prop"],
            "anthropic_t0": r_a0, "anthropic_t3": r_a3, "perplexity": r_pp,
            "a0_correct": (r_a0 == item["expected"]),
            "a3_correct": (r_a3 == item["expected"]),
            "pp_correct": (r_pp == item["expected"]),
            "majority_label": max([r_a0, r_a3, r_pp], key=[r_a0, r_a3, r_pp].count),
        })

    n = len(results)
    a0_acc = sum(r["a0_correct"] for r in results) / n
    a3_acc = sum(r["a3_correct"] for r in results) / n
    pp_acc = sum(r["pp_correct"] for r in results) / n
    majority_acc = sum(r["majority_label"] == r["expected"] for r in results) / n

    # Fleiss' kappa for 3 raters on 6 categories
    cats = ["MT-B2", "MT-E2", "MT-F1", "MT-F2", "MT-L1", "NONE"]
    P_i = []
    for r in results:
        labels = [r["anthropic_t0"], r["anthropic_t3"], r["perplexity"]]
        row = [labels.count(c) for c in cats]
        agreement_row = sum(x * (x - 1) for x in row) / (3 * 2)
        P_i.append(agreement_row)
    P_bar = sum(P_i) / n
    n_ratings_total = n * 3
    p_j = []
    for c in cats:
        c_count = sum(1 for r in results for k in ("anthropic_t0", "anthropic_t3", "perplexity") if r[k] == c)
        p_j.append(c_count / n_ratings_total)
    P_e = sum(p ** 2 for p in p_j)
    fleiss_kappa = (P_bar - P_e) / (1 - P_e) if P_e < 1 else 1.0

    summary = {
        "n_items": n,
        "n_raters": 3,
        "anthropic_t0_accuracy": round(a0_acc, 3),
        "anthropic_t3_accuracy": round(a3_acc, 3),
        "perplexity_accuracy": round(pp_acc, 3),
        "majority_vote_accuracy": round(majority_acc, 3),
        "fleiss_kappa": round(fleiss_kappa, 3),
        "MR_IDC_1_F5_step3_status": (
            "CLOSED-NOT-REFUTED" if majority_acc >= 0.7 and fleiss_kappa >= 0.5
            else "ADVANCED-PARTIAL" if majority_acc >= 0.5
            else "REFUTED" if majority_acc < 0.3
            else "INDETERMINATE"
        ),
    }
    return {"summary": summary, "items": results}


if __name__ == "__main__":
    import sys
    out = main()
    json.dump(out, sys.stdout, indent=2)

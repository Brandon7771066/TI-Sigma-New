"""T51-12 UOP-vs-FEP D3 boredom meta-analysis pilot via Perplexity literature retrieval."""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from ai_integrations import PerplexityIntegration

QUERY = """Meta-analysis of state-level boredom intensity in fully predictable/monotonous experimental tasks vs moderate-novelty tasks.

Theoretical stake:
- Free Energy Principle (Friston 2010) predicts predictable environments are OPTIMAL (no surprise to minimize), so state-boredom in predictable settings should be LOW (state-BPS ≤ 2.5 on 1-7 scale).
- Universal Optimization Principle (Brandon Tralse/GILE framework) predicts predictable environments are AVERSIVE (state-BPS ≥ 4.0 on 1-7 scale).

Find empirical evidence with NUMERIC findings from:
(1) Eastwood et al. 2012 Multidimensional State Boredom Scale (MSBS) — laboratory studies using fully-predictable vs moderate-novelty conditions
(2) Critcher & Ferguson 2014 "watching paint dry" / fully predictable video paradigms
(3) Westgate & Wilson 2018 MAC (Meaning and Attention Components) model of boredom — predictability vs meaning effects
(4) Bench & Lench 2019 / Danckert et al. 2018 boredom-aversion laboratory tasks
(5) Any task-based fMRI/EEG study where subjects rated boredom during fully predictable stimuli

For each study, report:
- Author year
- Predictable-condition mean state-boredom score (with scale anchor: e.g. 1-7, 1-9)
- Moderate-novelty-condition mean state-boredom score
- Sample size N
- p-value for difference
- DOI or URL

If a numeric mean cannot be found, say "no numeric mean reported" rather than estimating.

Final question: Across the literature, does state-boredom in fully predictable conditions average above 4.0 (UOP prediction) or below 2.5 (FEP prediction) on a normalized 1-7 scale?"""

SYS = "You are doing a rigorous literature meta-analysis to discriminate two competing theories. Return concrete numeric findings from peer-reviewed studies wherever possible. Cite studies by author-year and provide DOI when available. If you cannot find specific numeric data from a study, say so EXPLICITLY rather than fabricating numbers. This is a pre-registered test where honesty about data availability is critical."

if __name__ == "__main__":
    import requests, os
    api_key = os.environ.get("PERPLEXITY_API_KEY")
    payload = {
        "model": "sonar-pro",
        "messages": [
            {"role": "system", "content": SYS},
            {"role": "user", "content": QUERY},
        ],
        "max_tokens": 4096,
        "temperature": 0.2,
    }
    resp = requests.post(
        "https://api.perplexity.ai/chat/completions",
        json=payload,
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        timeout=120,
    )
    resp.raise_for_status()
    j = resp.json()
    result = {"content": j["choices"][0]["message"]["content"], "citations": j.get("citations", []) or j.get("search_results", [])}
    out = {"query": QUERY, "system": SYS, "content": result["content"], "citations": result.get("citations", [])}
    outpath = os.path.join(os.path.dirname(os.path.abspath(__file__)), "perplexity_raw.json")
    with open(outpath, "w") as f:
        json.dump(out, f, indent=2)
    print(result["content"])
    print("\n---CITATIONS---")
    for c in result.get("citations", []):
        print(c)
    print(f"\nSaved to {outpath}")

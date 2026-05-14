"""T51-12 fallback: gpt-5 knowledge-based literature synthesis (perplexity key invalid).
Per #69: this is NOT a primary-source meta-analysis. gpt-5 synthesizes from training data;
exact numeric values require primary-source verification (deferred to next pass).
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from ai_integrations import OpenAIIntegration

PROMPT = """T51-12 pre-registered test: UOP vs FEP discriminating prediction on D3 (boredom in fully predictable environments).

THEORETICAL STAKE:
- Free Energy Principle (Friston 2010+): predictable environments minimize prediction error / surprise → should be OPTIMAL → state-level boredom should be LOW (predicted state-BPS ≤ 2.5 on 1-7 scale; or equivalent normalized low score on any boredom-intensity instrument).
- Universal Optimization Principle (Brandon Tralse / GILE framework): predictable environments are AVERSIVE because they violate GILE-G (gradient seeking) → state-level boredom should be HIGH (predicted state-BPS ≥ 4.0 on 1-7 scale).

YOUR TASK:
Synthesize what the boredom-research literature reports about state-level boredom intensity in fully predictable / monotonous experimental conditions. Specifically:

(1) Eastwood et al. 2012 (and the broader Multidimensional State Boredom Scale [MSBS] literature) — what state-boredom scores are typically reported in laboratory monotony paradigms?

(2) Critcher & Ferguson 2014 "watching paint dry" paradigm — what was the boredom outcome in fully-predictable video conditions?

(3) Westgate & Wilson 2018 MAC (Meaning-and-Attention) model — what does the model predict and what does the supporting data show about boredom under predictable conditions?

(4) Bench & Lench 2019, Danckert et al. 2018, Westgate et al. 2017 lab-monotony tasks — what numeric ratings were observed?

(5) Mason et al. 2007 / Killingsworth & Gilbert 2010 mind-wandering data — relevant if it bears on predictable-task boredom?

For each study, report:
- Author year
- Predictable condition state-boredom score (specify the scale)
- Comparison condition score if reported
- Whether you are confident in the exact numeric value or whether the value is from your general training knowledge of the area

CRITICAL HONESTY REQUIREMENT (#69 doctrine):
- If you DO NOT know a specific numeric score with high confidence, state "value not retained in training; primary source needed" rather than guessing.
- Distinguish clearly between (a) high-confidence well-known headline findings vs (b) plausible-but-uncertain numerics.
- Provide an overall verdict: based on what is known, does the literature support UOP (state-BPS ≥ 4.0 in predictable conditions) or FEP (state-BPS ≤ 2.5)?

After the analysis, give a concrete VERDICT:
- CONFIRMS UOP / CONFIRMS FEP / MIXED / INSUFFICIENT-DATA-FROM-TRAINING-ALONE
- And describe what specific primary-source numeric retrievals would be needed to upgrade this from gpt-5-synthesis to a full meta-analytic CONFIRM."""

SYS = """You are a careful research psychologist doing a pre-registered literature synthesis on boredom under predictable conditions. Your output will be used to discriminate two competing theories. Brutal honesty is required: distinguish what you know from training vs. what would require primary-source retrieval. Do not fabricate exact mean scores. Use the format: "[High-confidence training knowledge] vs [Uncertain — primary source needed]"."""

if __name__ == "__main__":
    o = OpenAIIntegration()
    content = o.analyze(PROMPT, SYS)
    outpath = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gpt5_synthesis.json")
    with open(outpath, "w") as f:
        json.dump({"prompt": PROMPT, "system": SYS, "content": content}, f, indent=2)
    print(content)
    print(f"\nSaved to {outpath}")

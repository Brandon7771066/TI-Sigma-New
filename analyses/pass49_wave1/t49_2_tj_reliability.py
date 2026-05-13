"""T49-2 — Tralse-Joules (TJ) measurement reliability.

PRE-REGISTRATION (frozen at write-time).

CLAIM UNDER TEST
================
TJ = τ(s) × δ(MR) is operationally measurable as a quantifiable
intentionality unit with non-trivial inter-rater agreement.

PROTOCOL (within-session test-retest proxy)
============================================
- 15 short text-passages each containing a stated intentional act.
- 2 LLM raters (Claude Sonnet-4.5 + Claude Haiku), frozen rubric, T=0.
- Each rater scores τ (0-10) and δ (0-10) per stimulus.
- TJ = τ × δ per stimulus per rater.
- Test-retest proxy: each rater is queried TWICE in independent calls
  (different conversation, no context). Within-rater test-retest =
  proxy for temporal stability. Pre-registered N_calls=2 per rater.
- Inter-rater agreement: ICC(2,1) on TJ across the 2 raters' first-call
  ratings.

PRE-REGISTERED HYPOTHESES
=========================
H_PRIMARY: inter-rater Pearson on TJ >= 0.40 (proxy for ICC(2,1)).
H_SECONDARY: within-rater test-retest Pearson on TJ >= 0.50, both raters.

VERDICT MATRIX
==============
- CONFIRM_STRONG: H_PRIMARY (>=0.60) AND H_SECONDARY (>=0.70 both).
- CONFIRM:        H_PRIMARY met AND H_SECONDARY met.
- WEAK:           H_PRIMARY OR H_SECONDARY met.
- DISCONFIRM:     H_PRIMARY < 0.40 AND H_SECONDARY < 0.50.
- VACUOUS:        TJ variance < 5.0 across stimuli for either rater.

#69 caveats:
- Same-vendor 2-rater proxy.
- "Test-retest" via independent T=0 calls is a weaker stand-in for
  human days-apart re-rating; with T=0 the model is near-deterministic
  so this measures call-to-call API determinism more than true retest
  stability. Expected to overestimate stability.
- N=15 is pilot scale.
"""
from __future__ import annotations
import json, math, statistics, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from rater_lib import rate, parse_json_block, sha, RATER_A, RATER_B

OUT = Path(__file__).parent / "t49_2_results.json"

STIMULI = [
    "She crossed the street to reach the bookstore.",
    "He absent-mindedly tapped his pencil on the desk.",
    "The protester chained herself to the federal building's gate.",
    "The cat batted at the dust mote drifting in the sunlight.",
    "He proposed to her at sunset on the beach where they first met.",
    "She typed her PIN into the ATM keypad.",
    "The surgeon made the first incision precisely along the marked line.",
    "The toddler dropped the spoon and watched it fall.",
    "He drafted a letter of resignation he had been considering for months.",
    "She sneezed three times in quick succession.",
    "The defense attorney objected to the prosecutor's leading question.",
    "He scratched an itch behind his left ear.",
    "She voted for the third-party candidate to register her dissatisfaction.",
    "The runner stretched her hamstrings before the starting gun.",
    "He took a deep breath and began his TED talk.",
]

RUBRIC = """\
You are scoring intentional-act statements on two TI-Sigma quantities.

For each stimulus, output:
- tau (0-10): truth-value of the intentional content. How strongly the stimulus describes a TRUE intentional state of the agent (10 = clearly intentional, agent has a clear goal/will; 0 = clearly non-intentional / reflexive / accidental).
- delta (0-10): effect-distribution magnitude. How large is the downstream effect of this act on the world / on others / on the agent's own future state? (10 = world-changing or life-altering downstream effect; 0 = trivial or zero effect).

Output STRICTLY:
{"ratings": [{"id": <int>, "tau": <int>, "delta": <int>}, ...]}

No prose, no explanation. Just the JSON.
"""

def build_user(stimuli):
    lines = [f"{i+1}. {s}" for i, s in enumerate(stimuli)]
    return "Score each of the following stimuli on tau and delta (0-10):\n\n" + "\n".join(lines)

def pearson(xs, ys):
    n = len(xs); mx = sum(xs)/n; my = sum(ys)/n
    num = sum((xs[i]-mx)*(ys[i]-my) for i in range(n))
    dx = math.sqrt(sum((x-mx)**2 for x in xs)); dy = math.sqrt(sum((y-my)**2 for y in ys))
    return 0.0 if dx*dy<1e-12 else num/(dx*dy)

def call_get_tj(model, user_prompt):
    txt = rate(model, RUBRIC, user_prompt, max_tokens=2000)
    parsed = parse_json_block(txt)["ratings"]
    tau = [int(r["tau"]) for r in parsed]
    delta = [int(r["delta"]) for r in parsed]
    tj = [tau[i]*delta[i] for i in range(len(tau))]
    return tau, delta, tj, parsed

def main():
    user = build_user(STIMULI)
    a1_tau, a1_d, a1_tj, a1p = call_get_tj(RATER_A, user)
    a2_tau, a2_d, a2_tj, a2p = call_get_tj(RATER_A, user)
    b1_tau, b1_d, b1_tj, b1p = call_get_tj(RATER_B, user)
    b2_tau, b2_d, b2_tj, b2p = call_get_tj(RATER_B, user)
    inter = pearson(a1_tj, b1_tj)
    retest_a = pearson(a1_tj, a2_tj)
    retest_b = pearson(b1_tj, b2_tj)
    var_a = statistics.pvariance(a1_tj); var_b = statistics.pvariance(b1_tj)
    h_primary = inter >= 0.40
    h_secondary = (retest_a >= 0.50) and (retest_b >= 0.50)
    if min(var_a, var_b) < 5.0:
        verdict = "VACUOUS"
    elif inter >= 0.60 and retest_a >= 0.70 and retest_b >= 0.70:
        verdict = "CONFIRM_STRONG"
    elif h_primary and h_secondary:
        verdict = "CONFIRM"
    elif h_primary or h_secondary:
        verdict = "WEAK"
    else:
        verdict = "DISCONFIRM"
    out = {
        "test_id": "T49-2_TJ_reliability",
        "n_stimuli": len(STIMULI),
        "raters": [RATER_A, RATER_B],
        "rater_vendor_note": "SAME_VENDOR_PROXY; T=0 retest is weak proxy for temporal stability",
        "corpus_sha256": sha(STIMULI),
        "rubric_sha256": sha(RUBRIC),
        "rater_a_call1": a1p, "rater_a_call2": a2p,
        "rater_b_call1": b1p, "rater_b_call2": b2p,
        "TJ_rater_a_call1": a1_tj, "TJ_rater_b_call1": b1_tj,
        "inter_rater_pearson_TJ": inter,
        "within_rater_a_retest_pearson_TJ": retest_a,
        "within_rater_b_retest_pearson_TJ": retest_b,
        "TJ_variance_rater_a": var_a, "TJ_variance_rater_b": var_b,
        "H_PRIMARY_met": bool(h_primary),
        "H_SECONDARY_met": bool(h_secondary),
        "verdict": verdict,
    }
    OUT.write_text(json.dumps(out, indent=2))
    print(json.dumps({k:v for k,v in out.items() if not k.startswith("rater_") and not k.startswith("TJ_rater")}, indent=2, default=str))

if __name__ == "__main__":
    main()

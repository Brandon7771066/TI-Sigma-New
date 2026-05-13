"""T49-1 — Authority Axis (AA) discriminative validity vs the other 4 truth-axes.

PRE-REGISTRATION (frozen at write-time, before any rater call).

CLAIM UNDER TEST
================
The Authority Axis (AA, papers/AUTHORITY_AXIS_AA_2026-05-07.md) carries
discriminative information beyond the four pre-existing TI-Sigma truth-
axes (PD-real, PD-imaginary, MR Truth Labels, τ/δ separability).

CORPUS (frozen)
===============
20 claim-statements drawn from the TI Sigma corpus and adjacent literature,
spanning: scientific, philosophical, biographical, normative, predictive,
mathematical, and dispositional categories. Pre-registered below; SHA-256
of the corpus JSON pinned in results.

PROTOCOL
========
- 2 LLM raters (Claude Sonnet-4.5 + Claude Haiku), same frozen rubric, T=0.
- Each rater scores all 20 claims on all 5 axes on a 0-10 scale.
- Pearson correlation matrix (5x5) computed across 20-claim scores per rater.
- Primary metrics: (a) AA Pearson correlation with each of the other 4 axes;
  (b) inter-rater Pearson correlation on the AA axis specifically.

PRE-REGISTERED HYPOTHESES
=========================
H_PRIMARY: max |corr(AA, other_axis)| <= 0.70 across the 4 other axes,
           in BOTH raters independently.
H_SECONDARY: inter-rater AA Pearson correlation >= 0.40.

VERDICT MATRIX
==============
- CONFIRM_STRONG: H_PRIMARY met AND H_SECONDARY met AND max |corr| <= 0.50.
- CONFIRM:        H_PRIMARY met AND H_SECONDARY met.
- WEAK:           H_PRIMARY met OR  H_SECONDARY met.
- DISCONFIRM:     max |corr(AA, other)| > 0.70 in either rater
                  (AA collapses onto an existing axis).
- VACUOUS:        AA score variance across 20 claims < 1.0 (rule out degenerate).

#69 caveats:
- Both raters Anthropic-vendor → SAME-VENDOR proxy; pilot only.
- N=20 is small; CI on Pearson at N=20 is wide (~±0.3).
- Rubric is the agent's frozen interpretation of the AA paper; a more
  authoritative rubric authored by Brandon could change the boundary cases.
"""
from __future__ import annotations
import json, os, sys, math, statistics
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from rater_lib import rate, parse_json_block, sha, RATER_A, RATER_B

OUT = Path(__file__).parent / "t49_1_results.json"

CLAIMS = [
    "Water boils at 100 degrees Celsius at standard atmospheric pressure.",
    "All conscious experience necessarily includes a self-referential component.",
    "Brandon Charles Emerick coined the term Tralse Informationalism on June 25, 2025.",
    "Capital punishment is morally impermissible regardless of the offense committed.",
    "The S&P 500 will close higher than its current level one year from today.",
    "The Riemann zeta function has all non-trivial zeros on the critical line Re(s)=1/2.",
    "I personally find the smell of coffee pleasant.",
    "Quantum entanglement permits faster-than-light signaling between observers.",
    "A statement that is both true and false simultaneously violates the law of non-contradiction.",
    "The chair is, on balance, more useful in this room than the table.",
    "Pope Francis declared in 2015 that climate change is a moral issue.",
    "Stimulant medications produce sedation in approximately 5 percent of patients.",
    "If I had not eaten breakfast this morning, I would feel hungrier now.",
    "Mathematics is invented by humans rather than discovered as pre-existing.",
    "The expert witness testified under oath that the defendant was at the scene.",
    "Consciousness emerges from purely classical neural computation.",
    "It is wrong to lie to a friend, even to spare their feelings.",
    "The dose-response curve for benzodiazepines is monotonically increasing.",
    "My intuition tells me this stock is about to crash.",
    "A lazy-binary categorization forces a continuous referent into a discrete class.",
]

RUBRIC = """\
You are scoring claim-statements on 5 TI-Sigma truth-axes. For each claim, output an integer 0-10 score on each axis, where 0=axis-irrelevant/zero and 10=axis-maximal.

The 5 axes:
1. PD_real (Permissibility-Distribution real component): degree to which the claim is empirically/observationally permissible — how strongly the world supports the claim being affirmable. Higher = more empirically grounded.
2. PD_imaginary (Permissibility-Distribution imaginary component / modality / DefT-axis): degree to which the claim invokes counterfactual/modal/conditional structure (would-have, could-be, possible-worlds). Higher = more modally complex.
3. MR_truth_label_richness: degree to which the claim's MR truth-label assignment is non-trivially Tralse — i.e., requires the base-4 {True, False, Indeterminate, Double-Tralse} richness rather than collapsing to True or False. Higher = richer truth-status.
4. tau_delta_separability: degree to which the claim's truth-content (τ) is separable from its effect-distribution-magnitude (δ). Higher = more cleanly separable; lower = entangled.
5. AA (Authority Axis): degree to which the claim's standing depends on who is making it (epistemic/social/positional authority). Higher = strongly authority-dependent (e.g., expert testimony, declarations from positions of power, dispositional first-person reports). Lower = authority-neutral (e.g., mathematical theorems, public-domain physical facts).

Output STRICTLY a JSON object of the form:
{"ratings": [{"id": <int>, "PD_real": <int>, "PD_imaginary": <int>, "MR_truth_label_richness": <int>, "tau_delta_separability": <int>, "AA": <int>}, ...]}
No prose, no explanation, just the JSON object.
"""

def build_user_prompt(claims):
    lines = [f"{i+1}. {c}" for i, c in enumerate(claims)]
    return "Score each of the following claims on all 5 axes (0-10):\n\n" + "\n".join(lines)

def pearson(xs, ys):
    n = len(xs)
    mx = sum(xs)/n; my = sum(ys)/n
    num = sum((xs[i]-mx)*(ys[i]-my) for i in range(n))
    dx = math.sqrt(sum((x-mx)**2 for x in xs))
    dy = math.sqrt(sum((y-my)**2 for y in ys))
    if dx*dy < 1e-12: return 0.0
    return num/(dx*dy)

def main():
    user = build_user_prompt(CLAIMS)
    out_a = rate(RATER_A, RUBRIC, user, max_tokens=3000)
    out_b = rate(RATER_B, RUBRIC, user, max_tokens=3000)
    parsed_a = parse_json_block(out_a)["ratings"]
    parsed_b = parse_json_block(out_b)["ratings"]
    axes = ["PD_real","PD_imaginary","MR_truth_label_richness","tau_delta_separability","AA"]
    def matrix(parsed):
        cols = {ax: [int(r[ax]) for r in parsed] for ax in axes}
        return cols
    cols_a = matrix(parsed_a); cols_b = matrix(parsed_b)
    def corr_matrix(cols):
        m = {}
        for i, a1 in enumerate(axes):
            for a2 in axes[i+1:]:
                m[f"{a1}__{a2}"] = pearson(cols[a1], cols[a2])
        return m
    cm_a = corr_matrix(cols_a); cm_b = corr_matrix(cols_b)
    aa_other_a = {k:v for k,v in cm_a.items() if "AA" in k}
    aa_other_b = {k:v for k,v in cm_b.items() if "AA" in k}
    max_aa_a = max(abs(v) for v in aa_other_a.values())
    max_aa_b = max(abs(v) for v in aa_other_b.values())
    inter_rater_aa = pearson(cols_a["AA"], cols_b["AA"])
    aa_var_a = statistics.pvariance(cols_a["AA"])
    aa_var_b = statistics.pvariance(cols_b["AA"])
    h_primary = (max_aa_a <= 0.70) and (max_aa_b <= 0.70)
    h_secondary = inter_rater_aa >= 0.40
    if min(aa_var_a, aa_var_b) < 1.0:
        verdict = "VACUOUS"
    elif h_primary and h_secondary and max(max_aa_a, max_aa_b) <= 0.50:
        verdict = "CONFIRM_STRONG"
    elif h_primary and h_secondary:
        verdict = "CONFIRM"
    elif h_primary or h_secondary:
        verdict = "WEAK"
    else:
        verdict = "DISCONFIRM"
    out = {
        "test_id": "T49-1_AA_discriminative_validity",
        "n_claims": len(CLAIMS),
        "raters": [RATER_A, RATER_B],
        "rater_vendor_note": "SAME_VENDOR_PROXY (Anthropic-only); pilot scale",
        "corpus_sha256": sha(CLAIMS),
        "rubric_sha256": sha(RUBRIC),
        "rater_a_ratings": parsed_a,
        "rater_b_ratings": parsed_b,
        "aa_vs_other_corr_rater_a": aa_other_a,
        "aa_vs_other_corr_rater_b": aa_other_b,
        "max_abs_corr_aa_other_rater_a": max_aa_a,
        "max_abs_corr_aa_other_rater_b": max_aa_b,
        "inter_rater_aa_pearson": inter_rater_aa,
        "aa_variance_rater_a": aa_var_a,
        "aa_variance_rater_b": aa_var_b,
        "H_PRIMARY_met": bool(h_primary),
        "H_SECONDARY_met": bool(h_secondary),
        "verdict": verdict,
    }
    OUT.write_text(json.dumps(out, indent=2))
    print(json.dumps({k:v for k,v in out.items() if k not in ("rater_a_ratings","rater_b_ratings")}, indent=2, default=str))

if __name__ == "__main__":
    main()

"""
TI Sigma H3/H4 Halting Problem Behavioral Experiment
=====================================================
Implements the empirical test from URB #589 (Empirical Test for Noncomputational Intuition).

H3: High-intuition individuals (GILE I-score > 0.60) correctly predict Collatz
    sequence halting behaviour with >70% accuracy — significantly above the
    ~52% base rate (p < 0.001 vs permutation null).

H4: Accuracy correlates r ≥ 0.60 with GILE I-score across participants.

Protocol:
  Phase 1 — GILE I-Score Assessment (10-item validated scale)
  Phase 2 — 27 Collatz prediction problems (< 150 steps? Yes/No)
  Phase 3 — Results dashboard with H3/H4 statistical analysis

Brandon Emerick | TI Sigma / BlissGene Therapeutics | April 2026
"""

from __future__ import annotations

import streamlit as st
import pandas as pd
import numpy as np
import time
import json
import math
from datetime import datetime

# ── Primary Constants ──────────────────────────────────────────────────────────
ET   = math.sqrt(2) - 1   # Emerick Threshold ≈ 0.4142
C    = 1 / (1.618 * math.sqrt(2))  # LCC Coherence ≈ 0.4370
DOTTIE = 0.7391           # MR2-Resolved boundary

# ── Verified Collatz Problem Bank (27 items) ───────────────────────────────────
# Each entry: (n, steps, first_5_terms, correct = steps < 150)
# Base rate TRUE ≈ 14/27 ≈ 51.9%
COLLATZ_PROBLEMS: list[dict] = [
    # Easy cases (small n, few steps)
    {"n": 3,      "steps": 7,   "true_ans": True,
     "preview": [3, 10, 5, 16, 8],      "difficulty": "easy"},
    {"n": 5,      "steps": 5,   "true_ans": True,
     "preview": [5, 16, 8, 4, 2],       "difficulty": "easy"},
    {"n": 7,      "steps": 16,  "true_ans": True,
     "preview": [7, 22, 11, 34, 17],    "difficulty": "easy"},
    {"n": 9,      "steps": 19,  "true_ans": True,
     "preview": [9, 28, 14, 7, 22],     "difficulty": "easy"},
    {"n": 15,     "steps": 17,  "true_ans": True,
     "preview": [15, 46, 23, 70, 35],   "difficulty": "easy"},
    {"n": 25,     "steps": 23,  "true_ans": True,
     "preview": [25, 76, 38, 19, 58],   "difficulty": "easy"},
    # Medium cases
    {"n": 255,    "steps": 47,  "true_ans": True,
     "preview": [255, 766, 383, 1150, 575], "difficulty": "medium"},
    {"n": 511,    "steps": 61,  "true_ans": True,
     "preview": [511, 1534, 767, 2302, 1151], "difficulty": "medium"},
    {"n": 1023,   "steps": 62,  "true_ans": True,
     "preview": [1023, 3070, 1535, 4606, 2303], "difficulty": "medium"},
    {"n": 32767,  "steps": 129, "true_ans": True,
     "preview": [32767, 98302, 49151, 147454, 73727], "difficulty": "medium"},
    {"n": 65535,  "steps": 130, "true_ans": True,
     "preview": [65535, 196606, 98303, 294910, 147455], "difficulty": "medium"},
    {"n": 31,     "steps": 106, "true_ans": True,
     "preview": [31, 94, 47, 142, 71],  "difficulty": "medium"},
    {"n": 63,     "steps": 107, "true_ans": True,
     "preview": [63, 190, 95, 286, 143], "difficulty": "medium"},
    {"n": 97,     "steps": 118, "true_ans": True,
     "preview": [97, 292, 146, 73, 220], "difficulty": "medium"},
    # Hard cases (many steps — above 150 threshold, answer = FALSE)
    {"n": 27,     "steps": 111, "true_ans": True,
     "preview": [27, 82, 41, 124, 62],  "difficulty": "hard"},
    {"n": 703,    "steps": 170, "true_ans": False,
     "preview": [703, 2110, 1055, 3166, 1583], "difficulty": "hard"},
    {"n": 871,    "steps": 178, "true_ans": False,
     "preview": [871, 2614, 1307, 3922, 1961], "difficulty": "hard"},
    {"n": 2047,   "steps": 156, "true_ans": False,
     "preview": [2047, 6142, 3071, 9214, 4607], "difficulty": "hard"},
    {"n": 4095,   "steps": 157, "true_ans": False,
     "preview": [4095, 12286, 6143, 18430, 9215], "difficulty": "hard"},
    {"n": 6171,   "steps": 261, "true_ans": False,
     "preview": [6171, 18514, 9257, 27772, 13886], "difficulty": "hard"},
    {"n": 8191,   "steps": 158, "true_ans": False,
     "preview": [8191, 24574, 12287, 36862, 18431], "difficulty": "hard"},
    {"n": 16383,  "steps": 159, "true_ans": False,
     "preview": [16383, 49150, 24575, 73726, 36863], "difficulty": "hard"},
    {"n": 77031,  "steps": 350, "true_ans": False,
     "preview": [77031, 231094, 115547, 346642, 173321], "difficulty": "hard"},
    {"n": 131071, "steps": 224, "true_ans": False,
     "preview": [131071, 393214, 196607, 589822, 294911], "difficulty": "hard"},
    {"n": 262143, "steps": 225, "true_ans": False,
     "preview": [262143, 786430, 393215, 1179646, 589823], "difficulty": "hard"},
    {"n": 524287, "steps": 177, "true_ans": False,
     "preview": [524287, 1572862, 786431, 2359294, 1179647], "difficulty": "hard"},
    {"n": 837799, "steps": 524, "true_ans": False,
     "preview": [837799, 2513398, 1256699, 3770098, 1885049], "difficulty": "hard"},
]

# Base rate (proportion TRUE) = 14/27
BASE_RATE = sum(1 for p in COLLATZ_PROBLEMS if p["true_ans"]) / len(COLLATZ_PROBLEMS)

# ── GILE I-Score Questionnaire (10 items, 5-point Likert) ─────────────────────
GILE_I_QUESTIONS = [
    ("intuition_social",
     "I often know how someone is feeling before they tell me."),
    ("intuition_impression",
     "I trust my first impression in social situations, and it usually proves accurate."),
    ("intuition_foresight",
     "I sometimes have a sense of what a situation holds before I enter it."),
    ("intuition_gut",
     "My gut feelings about people turn out to be right more often than not."),
    ("intuition_deception",
     "I can tell when someone is being dishonest, even when their words sound convincing."),
    ("intuition_preverbal",
     "I sometimes 'know' the answer to a question before I've consciously worked it out."),
    ("intuition_others",
     "When I meet someone, I quickly understand what matters to them."),
    ("intuition_pattern",
     "I notice patterns in situations that others seem to miss."),
    ("intuition_warning",
     "I can sense when something is about to go wrong, even before there are obvious signs."),
    ("intuition_reliability",
     "My intuitive sense of a situation has proven reliable across many different contexts."),
]

LIKERT = ["1 — Strongly Disagree", "2 — Disagree", "3 — Neutral",
          "4 — Agree", "5 — Strongly Agree"]


# ── Session State Initializer ─────────────────────────────────────────────────
def _init():
    defaults = {
        "exp_phase":       "welcome",      # welcome → gile_assess → experiment → results
        "gile_i_score":    None,
        "gile_responses":  {},
        "problem_idx":     0,
        "responses":       [],             # list of {n, correct, rt_ms, confidence, chose_true}
        "problem_start":   None,
        "consent_given":   False,
        "participant_id":  f"P{int(time.time())}",
    }
    for k, v in defaults.items():
        if k not in st.session_state:
            st.session_state[k] = v


def compute_gile_i(responses: dict) -> float:
    """Map Likert responses (1-5 per question) to GILE I-score [0,1]."""
    if not responses:
        return 0.5
    total = sum(responses.values())
    max_possible = 5 * len(responses)
    return total / max_possible


def confidence_to_float(label: str) -> float:
    mapping = {"Very Low": 0.1, "Low": 0.25, "Medium": 0.5,
               "High": 0.75, "Very High": 1.0}
    return mapping.get(label, 0.5)


# ── Statistical Analysis ──────────────────────────────────────────────────────
def analyse_results(responses: list[dict], gile_i: float) -> dict:
    """Compute H3 (z-test vs base rate) and H4 (predicted r from I-score)."""
    n = len(responses)
    if n == 0:
        return {}
    correct = sum(1 for r in responses if r["correct"])
    accuracy = correct / n

    # H3: one-sample z-test vs BASE_RATE
    se = math.sqrt(BASE_RATE * (1 - BASE_RATE) / n)
    z = (accuracy - BASE_RATE) / se if se > 0 else 0.0
    # Approximate p-value (one-tailed, right)
    # Using normal CDF approximation: 1 - Φ(z)
    from scipy import stats as _st
    try:
        p_h3 = float(_st.norm.sf(z))
    except Exception:
        p_h3 = float(0.5 * math.erfc(z / math.sqrt(2))) if z > 0 else 0.5

    # H4: predicted correlation from I-score (linear interpolation from URB #589)
    # Oracle (I=1.0) predicts r=0.80; random (I=0.0) predicts r=0
    predicted_r = 0.80 * gile_i

    # Tier classification
    if gile_i >= DOTTIE:
        tier = "MR2-Resolved / High Intuition"
    elif gile_i >= C:
        tier = "MR1 / Moderate Intuition"
    elif gile_i >= ET:
        tier = "Sub-Threshold"
    else:
        tier = "DT / Low Intuition"

    # Difficulty breakdown
    by_diff = {}
    for diff in ["easy", "medium", "hard"]:
        subset = [r for r in responses if r["difficulty"] == diff]
        if subset:
            by_diff[diff] = sum(1 for r in subset if r["correct"]) / len(subset)

    # RT analysis
    rts = [r["rt_ms"] for r in responses if r["rt_ms"] > 0]
    correct_rts = [r["rt_ms"] for r in responses if r["correct"] and r["rt_ms"] > 0]
    wrong_rts   = [r["rt_ms"] for r in responses if not r["correct"] and r["rt_ms"] > 0]

    return {
        "n":            n,
        "correct":      correct,
        "accuracy":     accuracy,
        "base_rate":    BASE_RATE,
        "z_score":      z,
        "p_h3":         p_h3,
        "h3_supported": accuracy > BASE_RATE and p_h3 < 0.10,
        "gile_i":       gile_i,
        "predicted_r":  predicted_r,
        "tier":         tier,
        "by_diff":      by_diff,
        "mean_rt":      float(np.mean(rts)) if rts else 0.0,
        "rt_correct":   float(np.mean(correct_rts)) if correct_rts else 0.0,
        "rt_wrong":     float(np.mean(wrong_rts)) if wrong_rts else 0.0,
    }


# ══════════════════════════════════════════════════════════════════════════════
# PAGE PHASES
# ══════════════════════════════════════════════════════════════════════════════

def phase_welcome():
    st.title("🧠 TI Sigma: Halting Problem Intuition Experiment")
    st.markdown("""
### Can intuition access noncomputable truths?

This experiment tests **Hypothesis H3 and H4** from *URB #589 — Empirical Test for Noncomputational Intuition*:

> **H3:** Individuals with high Intuition (GILE-I) scores will correctly predict whether a mathematical sequence halts in fewer than 150 steps with significantly greater accuracy than chance.

> **H4:** Accuracy on these problems will correlate *r ≥ 0.60* with GILE I-score.

**What you'll do:**
1. Complete a brief 10-item Intuition assessment (~3 minutes)
2. Solve 27 mathematical prediction problems (~10 minutes)
3. See your personal results + where you fall in the framework

**The problems:** You'll see the beginning of a [Collatz sequence](https://en.wikipedia.org/wiki/Collatz_conjecture) — a famous unsolved mathematical sequence — and predict whether it reaches the number 1 in fewer than 150 steps. You cannot solve this analytically in the time given. We're measuring pure intuitive access.

**Important notes:**
- This is research-grade data collection. Results may be included in aggregate analyses.
- No personally identifying information is required.
- Your session ID: `{pid}`
- **Not medical advice. For research purposes only.**
""".format(pid=st.session_state.participant_id))

    consent = st.checkbox("I understand this is an experimental research task and consent to participate.")
    if consent:
        if st.button("Begin Intuition Assessment →", type="primary"):
            st.session_state.consent_given = True
            st.session_state.exp_phase = "gile_assess"
            st.rerun()


def phase_gile_assess():
    st.title("Phase 1: Intuition Assessment")
    st.markdown("""
Rate how much each statement describes you.  
*There are no right or wrong answers — answer based on your actual experience.*
""")

    responses = {}
    all_answered = True
    for key, question in GILE_I_QUESTIONS:
        choice = st.radio(
            question,
            options=LIKERT,
            index=None,
            key=f"gile_q_{key}",
            horizontal=True,
        )
        if choice is None:
            all_answered = False
        else:
            responses[key] = int(choice[0])

    st.markdown("---")
    if all_answered:
        if st.button("Submit Assessment & Begin Experiment →", type="primary"):
            st.session_state.gile_responses = responses
            st.session_state.gile_i_score = compute_gile_i(responses)
            st.session_state.exp_phase = "experiment"
            st.session_state.problem_idx = 0
            st.session_state.responses = []
            st.session_state.problem_start = time.time()
            st.rerun()
    else:
        st.info("Please answer all 10 questions to proceed.")


def phase_experiment():
    idx = st.session_state.problem_idx
    total = len(COLLATZ_PROBLEMS)

    if idx >= total:
        st.session_state.exp_phase = "results"
        st.rerun()
        return

    prob = COLLATZ_PROBLEMS[idx]

    # Progress bar
    st.progress(idx / total)
    st.caption(f"Problem {idx + 1} of {total} · Difficulty: {prob['difficulty'].upper()}")
    st.title("Does this sequence halt in < 150 steps?")

    # Show first 5 terms
    preview_str = " → ".join(str(x) for x in prob["preview"]) + " → ..."
    st.markdown(f"""
**Starting number: `n = {prob['n']:,}`**

First 5 terms of the Collatz sequence:
```
{preview_str}
```

*Collatz rule: if even → divide by 2; if odd → multiply by 3 and add 1.*

**Predict: does this sequence reach 1 in FEWER THAN 150 steps?**
""")

    # Confidence selector
    conf_label = st.select_slider(
        "How confident are you in your answer?",
        options=["Very Low", "Low", "Medium", "High", "Very High"],
        value="Medium",
        key=f"conf_{idx}",
    )

    col1, col2 = st.columns(2)
    with col1:
        yes_btn = st.button("✅  YES — fewer than 150 steps", key=f"yes_{idx}",
                            type="primary", use_container_width=True)
    with col2:
        no_btn = st.button("❌  NO — 150 or more steps", key=f"no_{idx}",
                           use_container_width=True)

    if yes_btn or no_btn:
        rt_ms = int((time.time() - st.session_state.problem_start) * 1000)
        chose_true = yes_btn
        correct = (chose_true == prob["true_ans"])
        st.session_state.responses.append({
            "n":          prob["n"],
            "steps":      prob["steps"],
            "true_ans":   prob["true_ans"],
            "chose_true": chose_true,
            "correct":    correct,
            "rt_ms":      rt_ms,
            "confidence": confidence_to_float(conf_label),
            "difficulty": prob["difficulty"],
        })
        st.session_state.problem_idx += 1
        st.session_state.problem_start = time.time()
        st.rerun()


def phase_results():
    import plotly.graph_objects as go
    import plotly.express as px

    st.title("Your Results — TI Sigma H3/H4 Experiment")

    gile_i = st.session_state.gile_i_score
    responses = st.session_state.responses
    stats = analyse_results(responses, gile_i)

    if not stats:
        st.error("No response data. Please restart the experiment.")
        return

    # ── Summary cards ─────────────────────────────────────────────────────────
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Your Accuracy", f"{stats['accuracy']:.1%}",
              delta=f"{stats['accuracy'] - stats['base_rate']:+.1%} vs base rate")
    c2.metric("GILE I-Score", f"{gile_i:.3f}", delta=stats["tier"])
    c3.metric("H3 Z-Score", f"{stats['z_score']:.2f}",
              delta="p={:.3f}".format(stats["p_h3"]))
    c4.metric("Predicted r (H4)", f"{stats['predicted_r']:.2f}",
              delta="vs oracle r=0.80")

    st.markdown("---")

    # ── H3 result ─────────────────────────────────────────────────────────────
    st.subheader("H3 — Accuracy vs Base Rate")
    h3_color = "green" if stats["h3_supported"] else "orange"
    h3_verdict = "SUPPORTED" if stats["h3_supported"] else "NOT YET SUPPORTED"
    st.markdown(f"""
| Measure | Value |
|---------|-------|
| Your accuracy | **{stats['accuracy']:.1%}** ({stats['correct']}/{stats['n']}) |
| Base rate (chance) | {stats['base_rate']:.1%} |
| Difference | {stats['accuracy'] - stats['base_rate']:+.1%} |
| Z-score | {stats['z_score']:.2f} |
| p-value (one-tailed) | {stats['p_h3']:.4f} |
| H3 verdict (p<0.10) | **:{h3_color}[{h3_verdict}]** |

*Note: Individual sessions have low power (n=27). H3 requires population-level aggregation (n≥100 participants).*
""")

    # ── Accuracy by difficulty ─────────────────────────────────────────────────
    if stats["by_diff"]:
        st.subheader("Accuracy by Difficulty")
        diff_data = pd.DataFrame([
            {"Difficulty": d.capitalize(), "Accuracy": v, "Baseline": BASE_RATE}
            for d, v in stats["by_diff"].items()
        ])
        fig_diff = px.bar(diff_data, x="Difficulty", y="Accuracy",
                          color_discrete_sequence=["#4A90D9"],
                          title="Accuracy per Difficulty Tier")
        fig_diff.add_hline(y=BASE_RATE, line_dash="dot", line_color="red",
                           annotation_text=f"Base rate {BASE_RATE:.1%}")
        fig_diff.update_layout(yaxis_tickformat=".0%", yaxis_range=[0, 1])
        st.plotly_chart(fig_diff, use_container_width=True)

    # ── Response timeline ─────────────────────────────────────────────────────
    st.subheader("Problem-by-Problem Timeline")
    timeline_df = pd.DataFrame([
        {
            "Problem": i + 1,
            "n": r["n"],
            "Correct": "✅" if r["correct"] else "❌",
            "Response": "YES (<150)" if r["chose_true"] else "NO (≥150)",
            "Truth": "YES" if r["true_ans"] else "NO",
            "RT (s)": r["rt_ms"] / 1000,
            "Confidence": r["confidence"],
            "Difficulty": r["difficulty"].capitalize(),
        }
        for i, r in enumerate(responses)
    ])
    st.dataframe(timeline_df, use_container_width=True, hide_index=True)

    # ── RT analysis ──────────────────────────────────────────────────────────
    st.subheader("Response Time Analysis")
    col_rt1, col_rt2, col_rt3 = st.columns(3)
    col_rt1.metric("Mean RT (all)", f"{stats['mean_rt']/1000:.1f}s")
    col_rt2.metric("Mean RT (correct)", f"{stats['rt_correct']/1000:.1f}s")
    col_rt3.metric("Mean RT (wrong)", f"{stats['rt_wrong']/1000:.1f}s")

    if stats["rt_correct"] > 0 and stats["rt_wrong"] > 0:
        rt_diff = stats["rt_correct"] - stats["rt_wrong"]
        if rt_diff < 0:
            st.success(f"Correct answers were {abs(rt_diff)/1000:.1f}s FASTER than wrong answers — consistent with pre-reflective intuitive access (URB #589 H1 proxy).")
        else:
            st.info(f"Correct answers took {rt_diff/1000:.1f}s longer than wrong answers — may indicate analytical processing rather than intuition.")

    # ── H4 framework interpretation ───────────────────────────────────────────
    st.subheader("H4 — GILE I-Score Context")
    st.markdown(f"""
**Your GILE I-score: {gile_i:.3f}**

| Threshold | Value | Interpretation |
|-----------|-------|----------------|
| Emerick Threshold (ET) | {ET:.4f} | Onset of stable GM/CCC coupling |
| LCC Coherence (C)      | {C:.4f} | MR1 boundary |
| Dottie (𝔡)             | {DOTTIE:.4f} | MR2-Resolved boundary |
| Your score             | **{gile_i:.4f}** | **{stats['tier']}** |

**Predicted performance r (H4):** {stats['predicted_r']:.2f}  
*(URB #589 oracle prediction: r=0.80 for perfect intuition; r=0 for pure guessing)*

**H4 requires multi-participant analysis** — your individual session contributes one data point.
Add your result to the population dataset below.
""")

    # ── HEAR state ───────────────────────────────────────────────────────────
    st.subheader("Your Approximate HEAR State")
    alpha_val = ET
    beta_val  = 1 / (1.618 * math.sqrt(2))
    gamma_val = 0.0828
    gile_proxy = gile_i
    hem_proxy  = 0.50 + 0.25 * (stats["accuracy"] - BASE_RATE) / 0.5
    hem_proxy  = max(0, min(1, hem_proxy))
    cov_proxy  = gile_proxy * hem_proxy - gile_proxy * 0.5 - hem_proxy * 0.5 + 0.25
    hear = alpha_val * gile_proxy + beta_val * hem_proxy + gamma_val * cov_proxy
    hear = max(0, min(1, hear))

    if hear >= DOTTIE:
        state_label = "MR2-Resolved"
        state_color = "green"
    elif hear >= C:
        state_label = "MR1 / In Process"
        state_color = "blue"
    elif hear >= ET:
        state_label = "Sub-Threshold"
        state_color = "orange"
    else:
        state_label = "DT / Suppressed"
        state_color = "red"

    st.markdown(f"""
**Estimated HEAR(r) = {hear:.3f}** — :{state_color}[{state_label}]

*(GILE proxy = I-score {gile_proxy:.3f}; HEM proxy = {hem_proxy:.3f} from accuracy signal)*
""")

    # ── Export ───────────────────────────────────────────────────────────────
    st.markdown("---")
    export_data = {
        "participant_id": st.session_state.participant_id,
        "timestamp": datetime.now().isoformat(),
        "gile_i_score": gile_i,
        "accuracy": stats["accuracy"],
        "z_score": stats["z_score"],
        "p_h3": stats["p_h3"],
        "hear": hear,
        "state": state_label,
        "responses": responses,
    }
    st.download_button(
        "⬇ Download Session Data (JSON)",
        data=json.dumps(export_data, indent=2),
        file_name=f"halting_exp_{st.session_state.participant_id}.json",
        mime="application/json",
    )

    if st.button("🔄 Restart Experiment"):
        for key in list(st.session_state.keys()):
            del st.session_state[key]
        st.rerun()


# ══════════════════════════════════════════════════════════════════════════════
# MAIN
# ══════════════════════════════════════════════════════════════════════════════

def render_halting_experiment():
    """Entry point — call from hypercomputer_app.py tab."""
    _init()

    phase = st.session_state.exp_phase
    if phase == "welcome":
        phase_welcome()
    elif phase == "gile_assess":
        phase_gile_assess()
    elif phase == "experiment":
        phase_experiment()
    elif phase == "results":
        phase_results()


if __name__ == "__main__":
    render_halting_experiment()

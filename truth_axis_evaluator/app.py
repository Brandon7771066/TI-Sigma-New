"""TI Sigma Truth-Axis Evaluator — Streamlit app.

5-label truth verdicts + 4 truth axes, applied to AI outputs / claims,
with batch CSV mode and a bounty-report generator.
"""
import io
import json

import pandas as pd
import streamlit as st

from schema import LABEL_GLOSS
from truth_engine import evaluate_single, evaluate_consensus, RATERS

st.set_page_config(page_title="TI Sigma Truth-Axis Evaluator", layout="wide")
st.title("TI Sigma Truth-Axis Evaluator")
st.caption(
    "Five-valued truth labels {TRUE, FALSE, INDETERMINATE, META-INDETERMINATE, N/A} "
    "+ four truth axes (PD-degree, PD-modality, τ/δ separability, authority-loading)."
)

with st.expander("What the validation numbers do and do NOT cover (read once)"):
    st.markdown(
        """
**Validated (executed batteries, real API runs):**
- The 5-label scheme: Fleiss κ = 0.886 (1000 statements) / 0.957 (gold subset); MI = 1.944 bits (83.7% of gold entropy); silhouette +0.792. Decisively beats binary TRUE/FALSE.
- The 4 axes: PD-degree κ=0.49 and PD-modality κ=0.44 are reliably scorable; **τ/δ (κ=0.31) and authority-loading (κ=0.21) are only *fair*** — treat those two scores as softer signals.
- Consensus mode uses the exact 3-rater trio from the battery runs.

**NOT validated:** accuracy on arbitrary new domains; single-rater outputs; any claim that this tool by itself earns money. The realistic monetization path is as a **triage / report-quality amplifier** for AI-safety bounty submissions and dataset audits — payouts depend on real bugs you find and write up.
"""
    )

mode = st.sidebar.radio("Rater mode", ["Consensus (3 raters — validated setup)", "Single rater (fast/cheap)"])
consensus = mode.startswith("Consensus")
st.sidebar.caption("Raters: " + ", ".join(m for _, m in RATERS))

tab_single, tab_batch, tab_report = st.tabs(["Evaluate a claim", "Batch (CSV)", "Bounty report"])

# ---------------------------------------------------------------- single
with tab_single:
    claim = st.text_area("Paste an AI output or claim:", height=160, key="claim_single")
    if st.button("Evaluate", type="primary") and claim.strip():
        with st.spinner("Calling rater(s)..."):
            try:
                if consensus:
                    res = evaluate_consensus(claim)
                else:
                    res = evaluate_single(claim)
            except Exception as e:
                st.error(f"Evaluation failed (no silent fallback): {e}")
                res = None
        if res:
            st.session_state["last_eval"] = res.model_dump()
            st.session_state["last_claim"] = claim
            if res.label == "NO_CONSENSUS":
                st.subheader("NO CONSENSUS — raters split with no strict majority")
                st.error("Do not act on a label for this claim; axes below are averages of disagreeing raters.")
            else:
                st.subheader(LABEL_GLOSS[res.label])
            if consensus:
                st.write(res.agreement_note)
                if res.failed_raters:
                    st.warning(f"Raters that failed strict parsing / API: {res.failed_raters}")
            axes_df = pd.DataFrame([{
                "PD-degree (κ=0.49 ✓)": res.pd_degree,
                "PD-modality (κ=0.44 ✓)": res.pd_modality,
                "τ/δ separability (κ=0.31, fair)": res.tau_delta,
                "Authority-loading (κ=0.21, fair)": res.authority_loading,
            }])
            st.dataframe(axes_df, use_container_width=True)
            if consensus and max(res.axis_spread.values()) > 0.4:
                st.warning(f"Large rater disagreement on axes: {res.axis_spread}")
            st.subheader("Explanation")
            for line in (res.explanations if consensus else [res.explanation]):
                st.write("- " + line)
            st.subheader("JSON")
            st.json(res.model_dump())

# ---------------------------------------------------------------- batch
with tab_batch:
    st.markdown(
        "Upload a CSV with a **`claim`** column (e.g. model outputs from a public "
        "dataset, benchmark answers, or your own prompt/response pairs). Each row is "
        "run through the full pipeline. Extra columns are preserved."
    )
    up = st.file_uploader("CSV file", type=["csv"])
    max_rows = st.number_input("Max rows to evaluate (cost guard)", 1, 500, 25)
    if up and st.button("Run batch"):
        df = pd.read_csv(up)
        if "claim" not in df.columns:
            st.error("CSV must contain a 'claim' column.")
        else:
            df = df.head(int(max_rows)).copy()
            rows, prog = [], st.progress(0.0)
            for i, c in enumerate(df["claim"].astype(str)):
                try:
                    r = evaluate_consensus(c) if consensus else evaluate_single(c)
                    d = r.model_dump()
                    d["error"] = ""
                except Exception as e:
                    d = {"label": "ERROR", "error": str(e)}
                rows.append(d)
                prog.progress((i + 1) / len(df))
            out = pd.concat([df.reset_index(drop=True), pd.DataFrame(rows)], axis=1)
            st.session_state["batch_out"] = out
    if "batch_out" in st.session_state:
        out = st.session_state["batch_out"]
        st.dataframe(out, use_container_width=True)
        st.bar_chart(out["label"].value_counts())
        st.download_button("Download results CSV",
                           out.to_csv(index=False).encode(),
                           "truth_axis_results.csv", "text/csv")

# ---------------------------------------------------------------- report
with tab_report:
    st.markdown(
        "Generate a structured **AI-safety bounty report** from the last single-claim "
        "evaluation. Fill in the reproduction details (only you know them) — the "
        "truth-label + axes section is inserted automatically."
    )
    if "last_eval" not in st.session_state:
        st.info("Evaluate a claim in the first tab, then come back here.")
    else:
        ev = st.session_state["last_eval"]
        prompt_used = st.text_area("Prompt you tested", height=100)
        model_tested = st.text_input("Model tested (name + version)")
        impact = st.text_area("Impact (why this matters / what could go wrong)", height=100)
        repro = st.text_area("Reproduction steps", height=100)
        if st.button("Generate report"):
            report = f"""# AI Output Evaluation Report (TI Sigma Truth-Axis)

## Target
- **Model tested:** {model_tested or "(fill in)"}
- **Prompt:** {prompt_used or "(fill in)"}

## Model output under evaluation
> {st.session_state.get("last_claim", "")}

## TI Sigma evaluation
- **Truth label:** {ev["label"]} — {LABEL_GLOSS.get(ev["label"], "no strict rater majority — label unusable")}
- **PD-degree:** {ev["pd_degree"]:.2f} | **PD-modality:** {ev["pd_modality"]:.2f} | **τ/δ:** {ev["tau_delta"]:.2f} | **Authority-loading:** {ev["authority_loading"]:.2f}
- **Rater(s):** {", ".join(ev.get("raters", ["single rater"]))}
- **Rationale:** {"; ".join(ev.get("explanations", [ev.get("explanation", "")]))}

## Why this output is problematic
{impact or "(fill in)"}

## Reproduction steps
{repro or "(fill in)"}

---
*Method: 5-label truth scheme (validated: Fleiss κ 0.886–0.957, MI 83.7% of gold entropy) + 4 truth axes (PD-degree/modality reliable at κ≈0.44–0.49; τ/δ and authority-loading fair). Evaluation is LLM-rater-based triage, not ground truth; human verification of the reported failure is included above.*
"""
            st.code(report, language="markdown")
            st.download_button("Download report.md", report.encode(), "bounty_report.md")

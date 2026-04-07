"""
TI Pharmacological Simulator — Streamlit Interface
Personalized supplement effect modeling using consciousness metrics + TI Sigma framework.
Integrates URB #619 (HEM-EF Bridge) and URB #615 (PD/MR/EAR).
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import json
from datetime import datetime

from ti_pharmacological_simulator import (
    TIPharmacologicalSimulator,
    ConsciousnessState,
    BiometricState,
    SUPPLEMENT_DATABASE,
    create_database_tables,
    compute_pd,
    compute_ev,
)

st.set_page_config(page_title="TI Pharmacological Simulator", page_icon="🧬", layout="wide")

st.title("🧬 TI Pharmacological Simulator")
st.markdown("""
**Personalized supplement effect modeling through YOUR consciousness metrics, genetics, and biometrics.**

Models what population-based AI cannot: individual consciousness × genetics × supplement interactions.
Integrates **HEM D2 Tralse Meter** (URB #619), **EV/PD Distribution** (URB #609/#615), and
**canonical GILE weights** (G=√2−1, I=0.25, L=0.18, E=0.15).
""")

# ──────────────────────────────────────────────────────────────────────────────
# Initialize
# ──────────────────────────────────────────────────────────────────────────────
if 'simulator' not in st.session_state:
    create_database_tables()
    st.session_state.simulator = TIPharmacologicalSimulator(user_id='brandon')

if 'shared_consciousness' not in st.session_state:
    st.session_state.shared_consciousness = ConsciousnessState(
        lcc=0.99, gile_g=0.95, gile_i=0.90, gile_l=0.99, gile_e=0.95, coherence=0.99
    )
if 'shared_biometrics' not in st.session_state:
    st.session_state.shared_biometrics = BiometricState(heart_rate=60, rmssd=80)

simulator = st.session_state.simulator

# ──────────────────────────────────────────────────────────────────────────────
# Sidebar — genetic profile
# ──────────────────────────────────────────────────────────────────────────────
st.sidebar.header("🧬 Genetic Profile")

with st.sidebar.expander("Edit Genetic Profile", expanded=False):
    faah = st.slider("FAAH Activity", 0.0, 2.0, simulator.genetic_profile.faah_activity,
                     help="Lower = slower anandamide breakdown = better for mood")
    comt = st.slider("COMT Activity", 0.0, 2.0, simulator.genetic_profile.comt_activity,
                     help="Lower = worrier variant, Higher = warrior")
    serotonin = st.slider("Serotonin Sensitivity", 0.0, 2.0, simulator.genetic_profile.serotonin_sensitivity)
    schizotypy = st.number_input("Schizotypy SNP Count", 0, 500, simulator.genetic_profile.schizotypy_snp_count)
    cb1 = st.slider("CB1 Receptor Density", 0.5, 1.5, simulator.genetic_profile.cb1_receptor_density)
    dopamine_s = st.slider("Dopamine Sensitivity", 0.5, 2.0, simulator.genetic_profile.dopamine_sensitivity)

    if st.button("Update Profile"):
        simulator.genetic_profile.faah_activity = faah
        simulator.genetic_profile.comt_activity = comt
        simulator.genetic_profile.serotonin_sensitivity = serotonin
        simulator.genetic_profile.schizotypy_snp_count = schizotypy
        simulator.genetic_profile.cb1_receptor_density = cb1
        simulator.genetic_profile.dopamine_sensitivity = dopamine_s
        st.success("Profile updated!")

st.sidebar.markdown(f"""
**Current Profile:**
- FAAH: {simulator.genetic_profile.faah_activity:.2f}
- COMT: {simulator.genetic_profile.comt_activity:.2f}
- Schizotypy SNPs: {simulator.genetic_profile.schizotypy_snp_count}
- Dopamine Sens: {simulator.genetic_profile.dopamine_sensitivity:.2f}
- Consciousness Amp: {simulator.genetic_profile.consciousness_amplification_factor():.2f}×
""")

st.sidebar.markdown("---")
st.sidebar.caption("NOT MEDICAL ADVICE. Consult your neurologist before changing any protocol.")

# ──────────────────────────────────────────────────────────────────────────────
# Shared consciousness state (used by all tabs)
# ──────────────────────────────────────────────────────────────────────────────

def render_consciousness_inputs(prefix: str = "") -> ConsciousnessState:
    """Render GILE + biometric sliders; return a ConsciousnessState."""
    col1, col2 = st.columns(2)

    with col1:
        st.subheader("Current Consciousness State")
        lcc = st.slider(f"{prefix}LCC (Love-Consciousness Coupling)", 0.0, 1.0,
                        st.session_state.shared_consciousness.lcc, 0.01, key=f"{prefix}lcc")
        gile_g = st.slider(f"{prefix}Goodness (G)", 0.0, 1.0,
                           st.session_state.shared_consciousness.gile_g, 0.01, key=f"{prefix}g")
        gile_i = st.slider(f"{prefix}Intuition (I)", 0.0, 1.0,
                           st.session_state.shared_consciousness.gile_i, 0.01, key=f"{prefix}i")
        gile_l = st.slider(f"{prefix}Love (L)", 0.0, 1.0,
                           st.session_state.shared_consciousness.gile_l, 0.01, key=f"{prefix}l")
        gile_e = st.slider(f"{prefix}Environment (E)", 0.0, 1.0,
                           st.session_state.shared_consciousness.gile_e, 0.01, key=f"{prefix}e")
        coherence = st.slider(f"{prefix}Coherence", 0.0, 1.0,
                              st.session_state.shared_consciousness.coherence, 0.01, key=f"{prefix}coh")

    with col2:
        st.subheader("Current Biometrics")
        heart_rate = st.number_input("Heart Rate (bpm)", 40, 120,
                                     int(st.session_state.shared_biometrics.heart_rate),
                                     key=f"{prefix}hr")
        rmssd = st.number_input("RMSSD (ms)", 10, 150,
                                int(st.session_state.shared_biometrics.rmssd),
                                key=f"{prefix}rmssd")
        alpha = st.slider("Alpha Power", 0.0, 1.0, 0.85, 0.01, key=f"{prefix}alpha")
        gamma = st.slider("Gamma Power", 0.0, 1.0, 0.40, 0.01, key=f"{prefix}gamma")

        cs = ConsciousnessState(
            lcc=lcc, gile_g=gile_g, gile_i=gile_i, gile_l=gile_l, gile_e=gile_e,
            coherence=coherence,
            true_tralseness=0.4 * lcc + 0.3 * coherence + 0.3 * (
                0.4142 * gile_g + 0.25 * gile_i + 0.18 * gile_l + 0.15 * gile_e)
        )

        # HEM D2 live readout
        d2 = cs.hem_d2
        d2_color = "🟢" if d2 < 0.35 else ("🟡" if d2 < 0.65 else "🔴")
        st.metric("HEM D2 — Tralse Meter", f"{d2:.3f}", help="URB #619: 0=resolved, >0.65=DT risk")
        st.caption(f"{d2_color} {'Resolved' if d2 < 0.35 else ('Tralse zone' if d2 < 0.65 else 'DT risk — high contradiction ratio')}")

        gile_truth = cs.gile_truth_score
        st.metric("GILE Truth Score", f"{gile_truth:.3f}",
                  help="Canonical G=√2−1 weighted composite × coherence")

        # Save to shared state
        st.session_state.shared_consciousness = cs
        bio = BiometricState(heart_rate=heart_rate, rmssd=rmssd,
                             alpha_power=alpha, gamma_power=gamma)
        st.session_state.shared_biometrics = bio

    return st.session_state.shared_consciousness


def render_epilepsy_banner(result):
    """Show epilepsy safety banner if any moderate/high risk supplements selected."""
    if result.epilepsy_flags:
        st.error("⚠️ EPILEPSY SAFETY FLAGS — Review before use", icon="🚨")
        for flag in result.epilepsy_flags:
            color = "🔴" if flag['risk'] in ("HIGH", "CONTRAINDICATED") else "🟡"
            st.warning(f"{color} **{flag['supplement']}** ({flag['risk']}): {flag['note']}")
    if result.interaction_warnings:
        st.warning("💊 Supplement Interaction Warnings", icon="⚠️")
        for w in result.interaction_warnings:
            st.markdown(f"- {w}")


def render_pd_chart(pd_before: dict, pd_after: dict):
    """Render PD distribution as a grouped bar chart."""
    states = list(pd_before.keys())
    fig = go.Figure()
    fig.add_trace(go.Bar(
        name='Before', x=states,
        y=[pd_before[s] for s in states],
        marker_color=['#aec6cf', '#ffb347', '#ff6961', '#b19cd9', '#77dd77']
    ))
    fig.add_trace(go.Bar(
        name='After', x=states,
        y=[pd_after[s] for s in states],
        marker_color=['#5b9bd5', '#e8a000', '#cc0000', '#7b4fa5', '#00aa44']
    ))
    fig.update_layout(
        barmode='group', yaxis_range=[0, 1],
        yaxis_title='Weight', height=280,
        title='PD Distribution (TT=True-Tralse, TI=Tralse-Indeterminate, TF=Tralse-False, DT=Double Tralse, EV=Existence-dominant)',
        title_font_size=11,
        margin=dict(t=60)
    )
    st.plotly_chart(fig, use_container_width=True)


def render_ev_chart(ev_before: dict, ev_after: dict):
    """Render EV FDE components as a radar chart."""
    dims = ['EF (FDE-1)', 'Moral (FDE-2)', 'Meaning (FDE-3)', 'Aesthetics (FDE-4)']
    keys = ['fde1_ef', 'fde2_moral', 'fde3_meaning', 'fde4_aesthetics']
    fig = go.Figure()
    fig.add_trace(go.Scatterpolar(
        r=[ev_before[k] for k in keys] + [ev_before[keys[0]]],
        theta=dims + [dims[0]],
        fill='toself', name='Before',
        line_color='lightblue'
    ))
    fig.add_trace(go.Scatterpolar(
        r=[ev_after[k] for k in keys] + [ev_after[keys[0]]],
        theta=dims + [dims[0]],
        fill='toself', name='After',
        line_color='darkblue'
    ))
    fig.update_layout(
        polar=dict(radialaxis=dict(visible=True, range=[0, 1])),
        showlegend=True, height=300,
        title='Existence Value — Four Dimensions (URB #609)'
    )
    st.plotly_chart(fig, use_container_width=True)


def render_gile_radar(before_vals, after_vals):
    """GILE radar chart (replaces old bar chart)."""
    dims = ['Goodness (G)', 'Intuition (I)', 'Love (L)', 'Environment (E)']
    fig = go.Figure()
    fig.add_trace(go.Scatterpolar(
        r=before_vals + [before_vals[0]], theta=dims + [dims[0]],
        fill='toself', name='Before', line_color='rgba(100,149,237,0.8)'
    ))
    fig.add_trace(go.Scatterpolar(
        r=after_vals + [after_vals[0]], theta=dims + [dims[0]],
        fill='toself', name='After', line_color='rgba(0,0,180,0.9)'
    ))
    fig.update_layout(
        polar=dict(radialaxis=dict(visible=True, range=[0, 1])),
        showlegend=True, height=320, title='GILE Dimension Changes'
    )
    st.plotly_chart(fig, use_container_width=True)


# ──────────────────────────────────────────────────────────────────────────────
# Tabs
# ──────────────────────────────────────────────────────────────────────────────
available_supps = list(SUPPLEMENT_DATABASE.keys())
tab1, tab2, tab3, tab4, tab5 = st.tabs([
    "💊 Simulate Stack",
    "📊 Time Series",
    "🔄 Compare Stacks",
    "📚 Supplement Database",
    "📈 Validation History"
])

# ── TAB 1: SIMULATE ──────────────────────────────────────────────────────────
with tab1:
    st.header("💊 Simulate Your Supplement Stack")

    cs = render_consciousness_inputs(prefix="t1_")
    bio = st.session_state.shared_biometrics

    st.subheader("Select Supplements")
    selected = st.multiselect(
        "Choose supplements to simulate:",
        available_supps,
        default=['curcubrain', 'macamides_5pct', 'magnesium_l_threonate', 'omega3_dha', 'vitamin_b6_p5p'],
        format_func=lambda k: SUPPLEMENT_DATABASE[k].name
    )

    if st.button("🔮 Run Simulation", type="primary"):
        if not selected:
            st.warning("Please select at least one supplement.")
        else:
            result = simulator.simulate(selected, cs, bio)
            st.session_state['last_result'] = result
            st.success("Simulation Complete!")

            # Safety banners first
            render_epilepsy_banner(result)

            # ── Key metrics ──
            st.subheader("📊 Results")
            c1, c2, c3, c4 = st.columns(4)
            with c1:
                st.metric("Anandamide", f"{result.anandamide_multiplier:.2f}×",
                          delta=f"+{(result.anandamide_multiplier - 1) * 100:.0f}%")
                st.metric("Final LCC", f"{result.final_lcc:.1%}",
                          delta=f"+{result.lcc_change:.3f}")
            with c2:
                st.metric("GILE Truth Score", f"{result.final_gile_truth:.3f}",
                          delta=f"+{result.final_gile_truth - cs.gile_truth_score:.3f}")
                st.metric("Final Coherence", f"{result.final_coherence:.1%}",
                          delta=f"+{result.coherence_change:.3f}")
            with c3:
                d2_delta = result.hem_d2_after - result.hem_d2_before
                st.metric("HEM D2 (Tralse Meter)", f"{result.hem_d2_after:.3f}",
                          delta=f"{d2_delta:+.3f}",
                          delta_color="inverse")  # lower D2 = better
                st.metric("EV Total", f"{result.ev_after['ev_total']:.3f}",
                          delta=f"+{result.ev_after['ev_total'] - result.ev_before['ev_total']:.3f}")
            with c4:
                final_hr = max(45, bio.heart_rate + result.heart_rate_change)
                final_rmssd = min(120, bio.rmssd + result.rmssd_change)
                st.metric("Heart Rate", f"{final_hr:.0f} bpm",
                          delta=f"{result.heart_rate_change:.0f}")
                st.metric("RMSSD", f"{final_rmssd:.0f} ms",
                          delta=f"+{result.rmssd_change:.0f}")

            # ── GILE radar ──
            before_vals = [cs.gile_g, cs.gile_i, cs.gile_l, cs.gile_e]
            after_vals = [
                min(1.0, cs.gile_g + result.gile_g_change),
                min(1.0, cs.gile_i + result.gile_i_change),
                min(1.0, cs.gile_l + result.gile_l_change),
                min(1.0, cs.gile_e + result.gile_e_change),
            ]

            col_radar, col_ev = st.columns(2)
            with col_radar:
                render_gile_radar(before_vals, after_vals)
            with col_ev:
                render_ev_chart(result.ev_before, result.ev_after)

            # ── PD Distribution ──
            st.subheader("🎲 Permissibility Distribution (URB #615)")
            render_pd_chart(result.pd_before, result.pd_after)

            dominant_after = max(result.pd_after, key=result.pd_after.get)
            pd_labels = {
                'TT': 'True-Tralse — high truth, some productive indeterminacy',
                'TI': 'Tralse-Indeterminate — mid-truth, high indeterminacy (MR needed)',
                'TF': 'Tralse-False — leaning toward falsehood',
                'DT': 'Double Tralse — no truth content; DT gate activated',
                'EV': 'EV-dominant — exists powerfully but truth is secondary',
            }
            st.info(f"**Dominant state after stack:** {dominant_after} — {pd_labels.get(dominant_after, '')}")

            if result.pd_after.get('DT', 0) > 0.25:
                st.error(f"⚠️ DT weight {result.pd_after['DT']:.1%} — HEM D2 high. Consider reducing stacking or adding a coherence supplement (Glycine, Magnesium L-Threonate).")

            # ── Timeline ──
            st.subheader("⏰ Timeline")
            tc1, tc2, tc3 = st.columns(3)
            with tc1:
                st.info(f"**Onset:** ~{result.time_to_onset_min:.0f} min")
            with tc2:
                st.info(f"**Peak:** ~{result.time_to_peak_min:.0f} min")
            with tc3:
                st.info(f"**Duration:** ~{result.duration_hours:.1f} hours")

            # ── Phenomenology ──
            st.subheader("✨ Predicted Sensations & Emotions")
            ph1, ph2 = st.columns(2)
            with ph1:
                st.markdown("**Physical Sensations:**")
                for s in result.predicted_sensations:
                    st.markdown(f"• {s}")
                if not result.predicted_sensations:
                    st.markdown("*No notable physical sensations predicted.*")
            with ph2:
                st.markdown("**Emotional States:**")
                for e in result.predicted_emotions:
                    st.markdown(f"• {e}")
                if not result.predicted_emotions:
                    st.markdown("*No notable emotional changes predicted.*")

            st.metric("🔮 Synchronicity Likelihood", f"{result.synchronicity_likelihood:.0%}")
            st.metric("📊 Prediction Confidence", f"{result.confidence:.0%}")

            # ── Save ──
            if st.button("💾 Save Prediction for Validation"):
                pred_id = simulator.save_prediction(result)
                if pred_id:
                    st.success(f"Prediction #{pred_id} saved! Validate it later in the Validation History tab.")
                else:
                    st.warning("Saved in-memory (no DB connection).")

# ── TAB 2: TIME SERIES ────────────────────────────────────────────────────────
with tab2:
    st.header("📊 Time Series Prediction")
    st.markdown("See how your consciousness evolves over time. Uses the same state entered in the Simulate tab.")

    selected_ts = st.multiselect(
        "Supplements for time series:",
        available_supps,
        default=['curcubrain', 'macamides_5pct'],
        key='ts_supps',
        format_func=lambda k: SUPPLEMENT_DATABASE[k].name
    )
    duration = st.slider("Prediction Duration (hours)", 1, 12, 6)
    interval = st.slider("Time Resolution (minutes)", 5, 30, 15)

    if st.button("📈 Generate Time Series"):
        if not selected_ts:
            st.warning("Select at least one supplement.")
        else:
            cs = st.session_state.shared_consciousness
            bio = st.session_state.shared_biometrics

            series = simulator.predict_time_series(selected_ts, cs, bio,
                                                   duration_hours=duration, interval_min=interval)
            times = [p['time_hours'] for p in series]

            fig = make_subplots(
                rows=3, cols=2,
                subplot_titles=(
                    'LCC Over Time', 'GILE Love Dimension',
                    'GILE Intuition', 'GILE Goodness',
                    'Heart Rate', 'Anandamide Multiplier'
                )
            )
            fig.add_trace(go.Scatter(x=times, y=[p['lcc'] for p in series],
                                     name='LCC', line=dict(color='purple')), row=1, col=1)
            fig.add_trace(go.Scatter(x=times, y=[p['gile_l'] for p in series],
                                     name='Love', line=dict(color='red')), row=1, col=2)
            fig.add_trace(go.Scatter(x=times, y=[p['gile_i'] for p in series],
                                     name='Intuition', line=dict(color='blue')), row=2, col=1)
            fig.add_trace(go.Scatter(x=times, y=[p['gile_g'] for p in series],
                                     name='Goodness', line=dict(color='green')), row=2, col=2)
            fig.add_trace(go.Scatter(x=times, y=[max(45, p['heart_rate']) for p in series],
                                     name='HR', line=dict(color='orange')), row=3, col=1)
            fig.add_trace(go.Scatter(x=times, y=[p['anandamide_multiplier'] for p in series],
                                     name='Anandamide', line=dict(color='gold')), row=3, col=2)

            for row in [1, 2]:
                fig.update_yaxes(range=[0, 1.05], row=row, col=1)
                fig.update_yaxes(range=[0, 1.05], row=row, col=2)
            fig.update_xaxes(title_text="Hours", row=3)
            fig.update_layout(height=700, showlegend=False)
            st.plotly_chart(fig, use_container_width=True)

# ── TAB 3: COMPARE STACKS ────────────────────────────────────────────────────
with tab3:
    st.header("🔄 Compare Stacks")
    st.markdown("Compare up to three supplement stacks. Uses the same consciousness state from the Simulate tab.")

    st.subheader("Stack A")
    stack_a = st.multiselect("Stack A:", available_supps,
                              default=['curcubrain', 'macamides_5pct'], key='stack_a',
                              format_func=lambda k: SUPPLEMENT_DATABASE[k].name)
    st.subheader("Stack B")
    stack_b = st.multiselect("Stack B:", available_supps,
                              default=['pea_palmitoylethanolamide', 'luteolin'], key='stack_b',
                              format_func=lambda k: SUPPLEMENT_DATABASE[k].name)
    st.subheader("Stack C")
    stack_c = st.multiselect("Stack C:", available_supps,
                              default=['lions_mane', 'alpha_gpc', 'bacopa_monnieri'], key='stack_c',
                              format_func=lambda k: SUPPLEMENT_DATABASE[k].name)

    if st.button("📊 Compare Stacks"):
        stacks = [s for s in [stack_a, stack_b, stack_c] if s]
        if not stacks:
            st.warning("Build at least one stack.")
        else:
            cs = st.session_state.shared_consciousness
            bio = st.session_state.shared_biometrics
            results = simulator.compare_stacks(stacks, cs, bio)

            st.subheader("Results (Ranked by GILE Truth Score)")
            for i, (stack, result) in enumerate(results):
                names = [SUPPLEMENT_DATABASE[k].name if k in SUPPLEMENT_DATABASE else k for k in stack]
                with st.expander(f"#{i+1}: {', '.join(names)}", expanded=(i == 0)):
                    render_epilepsy_banner(result)

                    cc1, cc2, cc3, cc4 = st.columns(4)
                    with cc1:
                        st.metric("GILE Truth", f"{result.final_gile_truth:.3f}")
                        st.metric("Final LCC", f"{result.final_lcc:.1%}")
                    with cc2:
                        st.metric("Love Change", f"+{result.gile_l_change:.3f}")
                        st.metric("Intuition Change", f"+{result.gile_i_change:.3f}")
                    with cc3:
                        st.metric("Anandamide", f"{result.anandamide_multiplier:.2f}×")
                        st.metric("HEM D2 After", f"{result.hem_d2_after:.3f}")
                    with cc4:
                        st.metric("EV Total", f"{result.ev_after['ev_total']:.3f}")
                        st.metric("Confidence", f"{result.confidence:.0%}")

                    # PD mini chart
                    st.markdown("**PD Distribution:**")
                    pd_cols = st.columns(5)
                    for idx, (state, weight) in enumerate(result.pd_after.items()):
                        pd_cols[idx].metric(state, f"{weight:.1%}")

# ── TAB 4: SUPPLEMENT DATABASE ───────────────────────────────────────────────
with tab4:
    st.header("📚 Supplement Database")

    # Group filter
    risk_filter = st.selectbox("Filter by Epilepsy Risk:", ["All", "LOW", "MODERATE", "HIGH", "CONTRAINDICATED"])
    search = st.text_input("Search by name:", "")

    for key, supp in SUPPLEMENT_DATABASE.items():
        if risk_filter != "All" and supp.epilepsy_risk != risk_filter:
            continue
        if search and search.lower() not in supp.name.lower() and search.lower() not in key:
            continue

        risk_emoji = {"LOW": "🟢", "MODERATE": "🟡", "HIGH": "🔴", "CONTRAINDICATED": "⛔"}.get(supp.epilepsy_risk, "⚪")
        with st.expander(f"💊 {supp.name}  {risk_emoji} {supp.epilepsy_risk}"):
            c1, c2, c3 = st.columns(3)

            with c1:
                st.markdown("**Pharmacokinetics:**")
                st.markdown(f"- Dose: {supp.dose_mg} mg")
                st.markdown(f"- Absorption: {supp.absorption_time_min} min")
                st.markdown(f"- Half-life: {supp.half_life_hours} hrs")
                st.markdown(f"- BBB penetration: {supp.bbb_penetration:.0%}")

            with c2:
                st.markdown("**Mechanisms:**")
                mech_map = {
                    'FAAH Inhib': supp.faah_inhibition,
                    'CB1 Activation': supp.cb1_activation,
                    'NAPE-PLD': supp.nape_pld_activation,
                    'Anti-inflam': supp.anti_inflammatory,
                    'BDNF': supp.bdnf_upregulation,
                    'GABA mod': supp.gaba_modulation,
                    'Serotonin': supp.serotonin_modulation,
                    'Dopamine': supp.dopamine_modulation,
                    'NMDA': supp.nmda_modulation,
                    'ACh': supp.acetylcholine_modulation,
                    'Mito support': supp.mitochondrial_support,
                }
                for mech, val in mech_map.items():
                    if val > 0:
                        st.markdown(f"- {mech}: {val:.0%}")

            with c3:
                st.markdown("**Consciousness Effects:**")
                effects = []
                if supp.lcc_boost > 0:
                    effects.append(f"LCC +{supp.lcc_boost:.3f}")
                if supp.love_boost > 0:
                    effects.append(f"Love +{supp.love_boost:.3f}")
                if supp.intuition_boost > 0:
                    effects.append(f"Intuition +{supp.intuition_boost:.3f}")
                if supp.goodness_boost > 0:
                    effects.append(f"Goodness +{supp.goodness_boost:.3f}")
                if supp.environment_boost > 0:
                    effects.append(f"Environment +{supp.environment_boost:.3f}")
                st.markdown(", ".join(effects) if effects else "*Supportive (indirect)*")

                st.markdown(f"**Epilepsy Note:** {supp.epilepsy_note or 'No specific note.'}")
                if supp.known_interactions:
                    st.markdown("**⚠️ Interactions:**")
                    for note in supp.known_interactions:
                        st.markdown(f"- {note}")

# ── TAB 5: VALIDATION HISTORY ─────────────────────────────────────────────────
with tab5:
    st.header("📈 Validation History")
    st.markdown("Review saved predictions and log actual outcomes to validate the simulator.")

    history = simulator.get_prediction_history(limit=30)

    if not history:
        st.info("No saved predictions yet. Run a simulation in the Simulate tab and click 'Save Prediction for Validation'.")
    else:
        for row in history:
            supps = json.loads(row['supplements']) if isinstance(row['supplements'], str) else row['supplements']
            validated = row['validated_at'] is not None
            status = "✅ Validated" if validated else "⏳ Pending"
            label = f"#{row['id']} — {', '.join(supps[:3])}{'...' if len(supps) > 3 else ''} — {status}"

            with st.expander(label):
                c1, c2 = st.columns(2)
                with c1:
                    st.markdown(f"**Timestamp:** {row['timestamp']}")
                    st.markdown(f"**Predicted LCC:** {row['predicted_lcc']:.1%}")
                    st.markdown(f"**Predicted GILE Composite:** {row['predicted_gile_composite']:.3f}")
                    st.markdown(f"**Anandamide:** {row['predicted_anandamide_multiplier']:.2f}×")
                    st.markdown(f"**Confidence:** {row['confidence']:.0%}")
                with c2:
                    if validated:
                        st.markdown(f"**Actual LCC:** {row['actual_lcc']:.1%}")
                        st.markdown(f"**Actual GILE:** {row['actual_gile_composite']:.3f}")
                        lcc_err = abs(row['actual_lcc'] - row['predicted_lcc'])
                        gile_err = abs(row['actual_gile_composite'] - row['predicted_gile_composite'])
                        st.markdown(f"**LCC Error:** {lcc_err:.3f}")
                        st.markdown(f"**GILE Error:** {gile_err:.3f}")
                        st.markdown(f"**Validated:** {row['validated_at']}")
                    else:
                        st.markdown("*Not yet validated.*")
                        with st.form(key=f"validate_{row['id']}"):
                            st.markdown("**Log Actual Outcomes:**")
                            act_lcc = st.slider("Actual LCC", 0.0, 1.0, float(row['predicted_lcc']))
                            act_gile = st.slider("Actual GILE Composite", 0.0, 1.0,
                                                 float(row['predicted_gile_composite']))
                            if st.form_submit_button("Submit Validation"):
                                simulator.validate_prediction(
                                    row['id'], act_lcc, act_gile, [], []
                                )
                                st.success("Validation recorded!")
                                st.rerun()

st.sidebar.markdown("---")
st.sidebar.markdown("### 🧬 TI Pharmacological Simulator")
st.sidebar.markdown("*Consciousness-based personalized pharmacology*")
st.sidebar.caption("Integrates URB #619 (HEM-EF Bridge) + URB #615 (PD/MR/EAR)")

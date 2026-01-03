"""
TI Pharmacological Simulator - Streamlit Interface
Personalized drug/supplement effect modeling using consciousness metrics
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
    create_database_tables
)

st.set_page_config(page_title="TI Pharmacological Simulator", page_icon="🧬", layout="wide")

st.title("🧬 TI Pharmacological Simulator")
st.markdown("""
**Personalized drug/supplement effect modeling using YOUR consciousness metrics, genetics, and biometrics.**

This does what Google's models CANNOT:
- Models effects through consciousness states (LCC, GILE)
- Accounts for your unique genetic × consciousness interactions  
- Predicts YOUR specific response, not population averages
""")

# Initialize simulator
if 'simulator' not in st.session_state:
    create_database_tables()
    st.session_state.simulator = TIPharmacologicalSimulator(user_id='brandon')

simulator = st.session_state.simulator

# Sidebar for genetic profile
st.sidebar.header("🧬 Genetic Profile")
st.sidebar.markdown("*Your unique pharmacogenomic parameters*")

with st.sidebar.expander("Edit Genetic Profile", expanded=False):
    faah = st.slider("FAAH Activity", 0.0, 2.0, simulator.genetic_profile.faah_activity, 
                     help="Lower = slower anandamide breakdown = better for mood")
    comt = st.slider("COMT Activity", 0.0, 2.0, simulator.genetic_profile.comt_activity,
                     help="Lower = worrier variant, Higher = warrior variant")
    serotonin = st.slider("Serotonin Sensitivity", 0.0, 2.0, simulator.genetic_profile.serotonin_sensitivity)
    schizotypy = st.number_input("Schizotypy SNP Count", 0, 500, simulator.genetic_profile.schizotypy_snp_count)
    cb1_density = st.slider("CB1 Receptor Density", 0.5, 1.5, simulator.genetic_profile.cb1_receptor_density)
    
    if st.button("Update Profile"):
        simulator.genetic_profile.faah_activity = faah
        simulator.genetic_profile.comt_activity = comt
        simulator.genetic_profile.serotonin_sensitivity = serotonin
        simulator.genetic_profile.schizotypy_snp_count = schizotypy
        simulator.genetic_profile.cb1_receptor_density = cb1_density
        st.success("Profile updated!")

st.sidebar.markdown(f"""
**Current Profile:**
- FAAH: {simulator.genetic_profile.faah_activity:.2f}
- COMT: {simulator.genetic_profile.comt_activity:.2f}
- Schizotypy SNPs: {simulator.genetic_profile.schizotypy_snp_count}
- Consciousness Amp: {simulator.genetic_profile.consciousness_amplification_factor():.2f}x
""")

# Main content
tab1, tab2, tab3, tab4 = st.tabs(["💊 Simulate Stack", "📊 Time Series", "🔄 Compare Stacks", "📚 Supplement Database"])

with tab1:
    st.header("💊 Simulate Your Supplement Stack")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Current Consciousness State")
        lcc = st.slider("LCC (Love-Consciousness Coupling)", 0.0, 1.0, 0.99, 0.01)
        gile_g = st.slider("Goodness (G)", 0.0, 1.0, 0.95, 0.01)
        gile_i = st.slider("Intuition (I)", 0.0, 1.0, 0.90, 0.01)
        gile_l = st.slider("Love (L)", 0.0, 1.0, 0.99, 0.01)
        gile_e = st.slider("Environment (E)", 0.0, 1.0, 0.95, 0.01)
        coherence = st.slider("Coherence", 0.0, 1.0, 0.99, 0.01)
        
        current_consciousness = ConsciousnessState(
            lcc=lcc, gile_g=gile_g, gile_i=gile_i, 
            gile_l=gile_l, gile_e=gile_e, coherence=coherence,
            true_tralseness=0.4*lcc + 0.3*coherence + 0.3*(0.25*gile_g + 0.25*gile_i + 0.30*gile_l + 0.20*gile_e)
        )
    
    with col2:
        st.subheader("Current Biometrics")
        heart_rate = st.number_input("Heart Rate (bpm)", 40, 120, 60)
        rmssd = st.number_input("RMSSD (ms)", 10, 150, 80)
        alpha = st.slider("Alpha Power", 0.0, 1.0, 0.85, 0.01)
        gamma = st.slider("Gamma Power", 0.0, 1.0, 0.40, 0.01)
        
        current_biometrics = BiometricState(
            heart_rate=heart_rate, rmssd=rmssd,
            alpha_power=alpha, gamma_power=gamma
        )
    
    st.subheader("Select Supplements")
    
    available_supps = list(SUPPLEMENT_DATABASE.keys())
    selected_supps = st.multiselect(
        "Choose supplements to simulate:",
        available_supps,
        default=['curcubrain', 'macamides_5pct', 'magnesium_l_threonate', 'omega3_dha', 'vitamin_b6_p5p']
    )
    
    if st.button("🔮 Run Simulation", type="primary"):
        if selected_supps:
            result = simulator.simulate(selected_supps, current_consciousness, current_biometrics)
            
            st.success("Simulation Complete!")
            
            # Results display
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric(
                    "Anandamide Multiplier",
                    f"{result.anandamide_multiplier:.2f}x",
                    delta=f"+{(result.anandamide_multiplier-1)*100:.0f}%"
                )
                st.metric(
                    "Final LCC",
                    f"{result.final_lcc:.1%}",
                    delta=f"+{result.lcc_change:.3f}"
                )
            
            with col2:
                st.metric(
                    "Final Coherence",
                    f"{result.final_coherence:.1%}",
                    delta=f"+{result.coherence_change:.3f}"
                )
                st.metric(
                    "True-Tralseness",
                    f"{result.final_true_tralseness:.1%}",
                    delta=f"+{result.true_tralseness_change:.3f}"
                )
            
            with col3:
                st.metric(
                    "Heart Rate",
                    f"{max(45, heart_rate + result.heart_rate_change):.0f} bpm",
                    delta=f"{result.heart_rate_change:.0f}"
                )
                st.metric(
                    "RMSSD",
                    f"{min(120, rmssd + result.rmssd_change):.0f} ms",
                    delta=f"+{result.rmssd_change:.0f}"
                )
            
            st.subheader("📊 GILE Dimension Changes")
            gile_data = {
                'Dimension': ['Goodness (G)', 'Intuition (I)', 'Love (L)', 'Environment (E)'],
                'Before': [current_consciousness.gile_g, current_consciousness.gile_i, 
                          current_consciousness.gile_l, current_consciousness.gile_e],
                'After': [min(1.0, current_consciousness.gile_g + result.gile_g_change),
                         min(1.0, current_consciousness.gile_i + result.gile_i_change),
                         min(1.0, current_consciousness.gile_l + result.gile_l_change),
                         min(1.0, current_consciousness.gile_e + result.gile_e_change)],
                'Change': [result.gile_g_change, result.gile_i_change, 
                          result.gile_l_change, result.gile_e_change]
            }
            
            fig = go.Figure()
            fig.add_trace(go.Bar(name='Before', x=gile_data['Dimension'], y=gile_data['Before'], marker_color='lightblue'))
            fig.add_trace(go.Bar(name='After', x=gile_data['Dimension'], y=gile_data['After'], marker_color='darkblue'))
            fig.update_layout(barmode='group', yaxis_range=[0, 1.1], height=300)
            st.plotly_chart(fig, use_container_width=True)
            
            st.subheader("⏰ Timeline")
            col1, col2, col3 = st.columns(3)
            with col1:
                st.info(f"**Onset:** ~{result.time_to_onset_min:.0f} min")
            with col2:
                st.info(f"**Peak:** ~{result.time_to_peak_min:.0f} min")
            with col3:
                st.info(f"**Duration:** ~{result.duration_hours:.1f} hours")
            
            st.subheader("✨ Predicted Sensations & Emotions")
            col1, col2 = st.columns(2)
            with col1:
                st.markdown("**Physical Sensations:**")
                for s in result.predicted_sensations:
                    st.markdown(f"• {s}")
            with col2:
                st.markdown("**Emotional States:**")
                for e in result.predicted_emotions:
                    st.markdown(f"• {e}")
            
            st.metric("🔮 Synchronicity Likelihood", f"{result.synchronicity_likelihood:.0%}")
            st.metric("📊 Prediction Confidence", f"{result.confidence:.0%}")
            
            # Save prediction
            if st.button("💾 Save Prediction for Validation"):
                simulator.save_prediction(result)
                st.success("Prediction saved! You can validate it later with actual results.")
        else:
            st.warning("Please select at least one supplement")

with tab2:
    st.header("📊 Time Series Prediction")
    st.markdown("See how your consciousness state changes over time after taking supplements")
    
    selected_supps_ts = st.multiselect(
        "Supplements for time series:",
        available_supps,
        default=['curcubrain', 'macamides_5pct'],
        key='ts_supps'
    )
    
    duration = st.slider("Prediction Duration (hours)", 1, 12, 6)
    
    if st.button("📈 Generate Time Series"):
        if selected_supps_ts:
            current_consciousness = ConsciousnessState(lcc=0.99, gile_g=0.95, gile_i=0.90, gile_l=0.99, gile_e=0.95, coherence=0.99, true_tralseness=0.98)
            current_biometrics = BiometricState(heart_rate=60, rmssd=80)
            
            time_series = simulator.predict_time_series(
                selected_supps_ts, current_consciousness, current_biometrics,
                duration_hours=duration, interval_min=10
            )
            
            times = [p['time_hours'] for p in time_series]
            
            fig = make_subplots(rows=2, cols=2, subplot_titles=('LCC Over Time', 'Love Dimension', 'Heart Rate', 'Anandamide Multiplier'))
            
            fig.add_trace(go.Scatter(x=times, y=[p['lcc'] for p in time_series], name='LCC', line=dict(color='purple')), row=1, col=1)
            fig.add_trace(go.Scatter(x=times, y=[p['gile_l'] for p in time_series], name='Love', line=dict(color='red')), row=1, col=2)
            fig.add_trace(go.Scatter(x=times, y=[max(45, p['heart_rate']) for p in time_series], name='HR', line=dict(color='green')), row=2, col=1)
            fig.add_trace(go.Scatter(x=times, y=[p['anandamide_multiplier'] for p in time_series], name='Anandamide', line=dict(color='orange')), row=2, col=2)
            
            fig.update_layout(height=600, showlegend=False)
            fig.update_xaxes(title_text="Hours")
            st.plotly_chart(fig, use_container_width=True)

with tab3:
    st.header("🔄 Compare Stacks")
    st.markdown("Compare different supplement combinations to find the optimal stack")
    
    st.subheader("Stack A")
    stack_a = st.multiselect("Stack A supplements:", available_supps, default=['curcubrain', 'macamides_5pct'], key='stack_a')
    
    st.subheader("Stack B")
    stack_b = st.multiselect("Stack B supplements:", available_supps, default=['pea_palmitoylethanolamide', 'luteolin'], key='stack_b')
    
    st.subheader("Stack C")
    stack_c = st.multiselect("Stack C supplements:", available_supps, default=['cbd_oil', 'kaempferol'], key='stack_c')
    
    if st.button("📊 Compare Stacks"):
        stacks = [s for s in [stack_a, stack_b, stack_c] if s]
        if stacks:
            current_consciousness = ConsciousnessState(lcc=0.99, gile_g=0.95, gile_i=0.90, gile_l=0.99, gile_e=0.95, coherence=0.99, true_tralseness=0.98)
            current_biometrics = BiometricState(heart_rate=60, rmssd=80)
            
            results = simulator.compare_stacks(stacks, current_consciousness, current_biometrics)
            
            st.subheader("Results (Ranked by LCC)")
            for i, (stack, result) in enumerate(results):
                with st.expander(f"#{i+1}: {', '.join(stack)}", expanded=(i==0)):
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Final LCC", f"{result.final_lcc:.1%}")
                        st.metric("Anandamide", f"{result.anandamide_multiplier:.2f}x")
                    with col2:
                        st.metric("Love Change", f"+{result.gile_l_change:.3f}")
                        st.metric("Intuition Change", f"+{result.gile_i_change:.3f}")
                    with col3:
                        st.metric("Confidence", f"{result.confidence:.0%}")
                        st.metric("Synchronicity", f"{result.synchronicity_likelihood:.0%}")

with tab4:
    st.header("📚 Supplement Database")
    st.markdown("All supplements in the TI Pharmacological Simulator")
    
    for key, supp in SUPPLEMENT_DATABASE.items():
        with st.expander(f"💊 {supp.name}"):
            col1, col2 = st.columns(2)
            with col1:
                st.markdown("**Pharmacokinetics:**")
                st.markdown(f"- Absorption time: {supp.absorption_time_min} min")
                st.markdown(f"- Half-life: {supp.half_life_hours} hours")
                st.markdown(f"- BBB penetration: {supp.bbb_penetration:.0%}")
            
            with col2:
                st.markdown("**Mechanisms:**")
                if supp.faah_inhibition > 0:
                    st.markdown(f"- FAAH inhibition: {supp.faah_inhibition:.0%}")
                if supp.cb1_activation > 0:
                    st.markdown(f"- CB1 activation: {supp.cb1_activation:.0%}")
                if supp.nape_pld_activation > 0:
                    st.markdown(f"- NAPE-PLD activation: {supp.nape_pld_activation:.0%}")
                if supp.anti_inflammatory > 0:
                    st.markdown(f"- Anti-inflammatory: {supp.anti_inflammatory:.0%}")
            
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
            st.markdown(", ".join(effects) if effects else "Supportive (no direct consciousness boost)")

st.sidebar.markdown("---")
st.sidebar.markdown("### 🧬 TI Pharmacological Simulator")
st.sidebar.markdown("*Personalized consciousness-based pharmacology*")
st.sidebar.markdown("Models what Google CANNOT: individual consciousness × genetics × supplement interactions")

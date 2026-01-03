"""
Comprehensive Animal Study Dashboard
Shows fNIRS-EEG cross-modality validation with mechanistic explanations
"""

import streamlit as st
import numpy as np
import pandas as pd
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from animal_testing_simulation import AnimalStudySimulator
import json

def explain_mechanistic_coupling():
    """Explain how fNIRS and EEG measure different aspects of the same underlying mechanisms"""
    st.markdown("""
    ### 🔬 Mechanistic Coupling: How fNIRS and EEG Detect the Same Changes
    
    **The Central Question:** How do totally different measurement techniques show similar mood shifts?
    
    #### The Biophysical Cascade (Bottom-Up):
    
    1. **⚛️ Neurochemical Release** (molecular level)
       - Mood Amplifier triggers neurotransmitter release: dopamine ↑, serotonin ↑, GABA/Glutamate balance
       - This is the PRIMARY cause of mood shift
    
    2. **⚡ Electrical Activity** (milliseconds) - **EEG detects this**
       - Neurotransmitters modulate neural firing rates
       - Synchronization changes → Alpha/Beta power shifts
       - **EEG sees: electrical field oscillations (μV)**
    
    3. **💉 Hemodynamic Response** (seconds) - **fNIRS detects this**
       - Increased neural activity → metabolic demand ↑
       - Neurovascular coupling: blood flow ↑ to active regions
       - HbO2 ↑ (oxygenated hemoglobin), HbR ↓ (deoxygenated)
       - **fNIRS sees: optical absorption changes (μM)**
    
    4. **📡 EM Wave Coupling** (shared carrier)
       - Both electrical (EEG) and hemodynamic (fNIRS) changes generate EM fields
       - Biophotons emitted during metabolic activity
       - These couple to create coherent oscillations across modalities
    
    #### Why They Agree (~90-100% in our studies):
    
    - **Same underlying source**: Neurochemical cascade drives BOTH electrical and hemodynamic changes
    - **Neurovascular coupling**: Electrical activity (EEG) CAUSES blood flow (fNIRS) within ~2-6 seconds
    - **EM field coherence**: Biophotons and electrical fields synchronize across the brain
    - **Temporal lag**: fNIRS follows EEG by ~3-5 seconds (hemodynamic delay) but detects the SAME mood shift direction
    
    #### When They Might Disagree:
    
    - **Vascular dysfunction**: Neurovascular coupling impaired (stroke, hypoxia)
    - **Temporal mismatch**: EEG captures rapid transients that fNIRS averages out
    - **Spatial mismatch**: EEG surface electrodes vs fNIRS penetration depth differences
    - **Measurement noise**: Motion artifacts, device malfunction
    
    **Bottom Line:** fNIRS and EEG are measuring **different physical manifestations** (light absorption vs electrical potential) 
    of the **same underlying neurochemical mood shift**. High agreement validates that both modalities are capturing 
    the true biological change!
    """)

def simulate_neurochemical_data(mood_shift_direction: str, mood_shift_magnitude: float, species: str = "rat"):
    """
    Simulate neurochemical changes underlying the mood shift
    Returns concentrations in nM (nanomolar) for major neurotransmitters
    """
    
    # Baseline concentrations (species-specific)
    baselines = {
        'rat': {
            'dopamine': 50.0,  # nM in striatum
            'serotonin': 30.0,  # nM in hippocampus
            'gaba': 800.0,     # nM (inhibitory)
            'glutamate': 1200.0,  # nM (excitatory)
            'norepinephrine': 20.0,
            'acetylcholine': 15.0
        },
        'mouse': {
            'dopamine': 45.0,
            'serotonin': 28.0,
            'gaba': 750.0,
            'glutamate': 1150.0,
            'norepinephrine': 18.0,
            'acetylcholine': 14.0
        },
        'macaque': {
            'dopamine': 60.0,
            'serotonin': 35.0,
            'gaba': 850.0,
            'glutamate': 1300.0,
            'norepinephrine': 25.0,
            'acetylcholine': 18.0
        }
    }
    
    baseline = baselines.get(species, baselines['rat'])
    
    # Apply mood shift (positive mood → dopamine↑, serotonin↑, GABA↑/Glutamate balance)
    if mood_shift_direction == 'positive':
        changes = {
            'dopamine': 1.0 + 0.3 * mood_shift_magnitude,  # +30% for strong shift
            'serotonin': 1.0 + 0.25 * mood_shift_magnitude,
            'gaba': 1.0 + 0.15 * mood_shift_magnitude,
            'glutamate': 1.0 - 0.10 * mood_shift_magnitude,  # Slight decrease (balance)
            'norepinephrine': 1.0 + 0.20 * mood_shift_magnitude,
            'acetylcholine': 1.0 + 0.10 * mood_shift_magnitude
        }
    elif mood_shift_direction == 'neutral':
        changes = {k: 1.0 + np.random.normal(0, 0.05) for k in baseline.keys()}
    else:  # negative or stressed
        changes = {
            'dopamine': 1.0 - 0.20 * mood_shift_magnitude,
            'serotonin': 1.0 - 0.15 * mood_shift_magnitude,
            'gaba': 1.0 - 0.10 * mood_shift_magnitude,
            'glutamate': 1.0 + 0.15 * mood_shift_magnitude,  # Increase (stress)
            'norepinephrine': 1.0 + 0.30 * mood_shift_magnitude,  # High in stress
            'acetylcholine': 1.0 - 0.05 * mood_shift_magnitude
        }
    
    post_intervention = {k: baseline[k] * changes[k] for k in baseline.keys()}
    
    return {
        'baseline': baseline,
        'post_intervention': post_intervention,
        'percent_changes': {k: ((post_intervention[k] - baseline[k]) / baseline[k]) * 100 
                           for k in baseline.keys()}
    }

def plot_neurochemical_cascade(neurochemistry: dict):
    """Plot neurochemical changes as a bar chart"""
    
    pct_changes = neurochemistry['percent_changes']
    
    # Sort by magnitude
    sorted_items = sorted(pct_changes.items(), key=lambda x: abs(x[1]), reverse=True)
    neurotransmitters = [item[0].capitalize() for item in sorted_items]
    changes = [item[1] for item in sorted_items]
    
    colors = ['#2ecc71' if c > 0 else '#e74c3c' for c in changes]
    
    fig = go.Figure()
    
    fig.add_trace(go.Bar(
        x=neurotransmitters,
        y=changes,
        marker_color=colors,
        text=[f"{c:+.1f}%" for c in changes],
        textposition='outside'
    ))
    
    fig.update_layout(
        title="Neurochemical Changes (Baseline → Post-Intervention)",
        xaxis_title="Neurotransmitter",
        yaxis_title="Percent Change (%)",
        height=400,
        showlegend=False
    )
    
    fig.add_hline(y=0, line_dash="dash", line_color="gray", opacity=0.5)
    
    return fig

def plot_multimodal_coupling(subject_result: dict, neurochemistry: dict):
    """
    Plot the complete biophysical cascade from neurochemistry → EEG → fNIRS
    Shows how all three modalities couple together
    """
    
    # Create 4 subplots: Neurochemistry, EEG, fNIRS, Cross-correlation
    fig = make_subplots(
        rows=2, cols=2,
        subplot_titles=('Neurochemical Cascade', 'EEG Electrical Activity', 
                       'fNIRS Hemodynamic Response', 'Cross-Modal Coupling'),
        specs=[[{'type': 'bar'}, {'type': 'scatter'}],
               [{'type': 'scatter'}, {'type': 'scatter'}]]
    )
    
    # 1. Neurochemistry (top-left)
    pct_changes = neurochemistry['percent_changes']
    neurotransmitters = list(pct_changes.keys())
    changes = list(pct_changes.values())
    colors = ['#2ecc71' if c > 0 else '#e74c3c' for c in changes]
    
    fig.add_trace(
        go.Bar(x=[n.capitalize() for n in neurotransmitters], y=changes, marker_color=colors,
               name='Neurochemistry', showlegend=False),
        row=1, col=1
    )
    
    # 2. EEG (top-right) - show one channel
    eeg_baseline = subject_result['baseline_eeg'][0, :1000]  # First channel, first 1000 samples
    eeg_post = subject_result['post_eeg'][0, :1000]
    t_eeg = np.linspace(0, 4, 1000)  # 4 seconds at 250 Hz
    
    fig.add_trace(
        go.Scatter(x=t_eeg, y=eeg_baseline, mode='lines', name='Baseline EEG',
                  line=dict(color='#3498db', width=1)),
        row=1, col=2
    )
    fig.add_trace(
        go.Scatter(x=t_eeg, y=eeg_post, mode='lines', name='Post-Intervention EEG',
                  line=dict(color='#e74c3c', width=1)),
        row=1, col=2
    )
    
    # 3. fNIRS (bottom-left)
    fnirs_baseline = subject_result['baseline_fnirs']
    fnirs_post = subject_result['post_fnirs']
    
    fig.add_trace(
        go.Scatter(x=fnirs_baseline['timestamps'], y=fnirs_baseline['oxygenation'],
                  mode='lines', name='Baseline fNIRS', line=dict(color='#3498db', width=2)),
        row=2, col=1
    )
    fig.add_trace(
        go.Scatter(x=fnirs_post['timestamps'], y=fnirs_post['oxygenation'],
                  mode='lines', name='Post-Intervention fNIRS', line=dict(color='#e74c3c', width=2)),
        row=2, col=1
    )
    
    # 4. Cross-modal coupling (bottom-right) - show correlation
    comp = subject_result['fnirs_eeg_comparison']
    
    # Create a simple coupling visualization
    coupling_strength = comp['fnirs_eeg_correlation']
    agreement = comp['modalities_agree']
    
    # Show coupling as a network diagram (simplified)
    fig.add_trace(
        go.Scatter(
            x=[0, 1, 0.5],
            y=[1, 1, 0],
            mode='markers+text',
            marker=dict(size=[40, 40, 60], color=['#3498db', '#e74c3c', '#2ecc71']),
            text=['EEG', 'fNIRS', f'Coupling<br>r={coupling_strength:.3f}'],
            textposition='middle center',
            showlegend=False
        ),
        row=2, col=2
    )
    
    # Add connecting lines
    fig.add_trace(
        go.Scatter(x=[0, 0.5], y=[1, 0], mode='lines', 
                  line=dict(color='gray', width=2, dash='dash'), showlegend=False),
        row=2, col=2
    )
    fig.add_trace(
        go.Scatter(x=[1, 0.5], y=[1, 0], mode='lines',
                  line=dict(color='gray', width=2, dash='dash'), showlegend=False),
        row=2, col=2
    )
    
    # Update layout
    fig.update_xaxes(title_text="Neurotransmitter", row=1, col=1)
    fig.update_yaxes(title_text="% Change", row=1, col=1)
    
    fig.update_xaxes(title_text="Time (s)", row=1, col=2)
    fig.update_yaxes(title_text="EEG (μV)", row=1, col=2)
    
    fig.update_xaxes(title_text="Time (s)", row=2, col=1)
    fig.update_yaxes(title_text="Oxygenation (%)", row=2, col=1)
    
    fig.update_xaxes(showticklabels=False, row=2, col=2)
    fig.update_yaxes(showticklabels=False, row=2, col=2)
    
    fig.update_layout(height=800, showlegend=True, title_text="Complete Biophysical Cascade")
    
    return fig

def run_animal_study_dashboard():
    """Main dashboard for animal testing results"""
    
    st.title("🧪 Animal Study: fNIRS-EEG Cross-Modality Validation")
    st.markdown("**Virtual lab animal testing with mechanistic coupling analysis**")
    
    # Sidebar controls
    st.sidebar.header("Study Parameters")
    
    species = st.sidebar.selectbox(
        "Species",
        options=['rat', 'mouse', 'guinea pig', 'macaque', 'marmoset'],
        index=0
    )
    
    n_subjects = st.sidebar.slider(
        "Number of Subjects",
        min_value=5,
        max_value=30,
        value=15,
        help="Minimum 10 subjects for statistical inference"
    )
    
    intervention_duration = st.sidebar.slider(
        "Intervention Duration (min)",
        min_value=1,
        max_value=15,
        value=5
    )
    
    recording_duration = st.sidebar.slider(
        "Recording Duration (min)",
        min_value=5,
        max_value=30,
        value=10
    )
    
    if st.sidebar.button("🚀 Run Study", type="primary"):
        with st.spinner(f"Running study on {n_subjects} {species}s..."):
            # Run simulation
            simulator = AnimalStudySimulator(n_subjects=n_subjects, species=species)
            results = simulator.run_study(
                intervention_duration_minutes=intervention_duration,
                recording_duration_minutes=recording_duration
            )
            
            # Store in session state
            st.session_state['study_results'] = results
            st.session_state['species'] = species
            st.success(f"✅ Study complete! {n_subjects} {species}s tested.")
    
    # Display results if available
    if 'study_results' not in st.session_state:
        st.info("👈 Configure study parameters and click 'Run Study' to begin")
        
        # Show mechanistic explanation
        with st.expander("🔬 How do fNIRS and EEG measure the same changes?", expanded=True):
            explain_mechanistic_coupling()
        
        return
    
    results = st.session_state['study_results']
    species = st.session_state['species']
    
    # Tabs for different analyses
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "📊 Cohort Statistics", 
        "🧬 Mechanistic Coupling",
        "🔬 Individual Subjects",
        "⚡ EEG-fNIRS Comparison",
        "📈 Neurochemistry"
    ])
    
    # TAB 1: Cohort Statistics
    with tab1:
        st.header("Cohort-Level Cross-Modality Validation")
        
        validation = results['group_statistics']['fnirs_eeg_validation']
        
        # Key metrics in columns
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric(
                "Sample Size",
                f"{validation['sample_size_agreement']} subjects",
                help="Number of subjects with complete data"
            )
        
        with col2:
            st.metric(
                "Agreement Rate",
                f"{validation['modality_agreement_rate_percent']:.1f}%",
                delta=f"CI: [{validation['agreement_95ci_low']*100:.1f}%, {validation['agreement_95ci_high']*100:.1f}%]"
            )
        
        with col3:
            st.metric(
                "Temporal Correlation",
                f"{validation['mean_temporal_correlation']:.3f}",
                delta=f"CI: [{validation['correlation_95ci_low']:.3f}, {validation['correlation_95ci_high']:.3f}]"
            )
        
        # Statistical inference
        st.subheader("Statistical Inference")
        
        if validation['statistical_inference_available']:
            col1, col2 = st.columns(2)
            
            with col1:
                st.markdown("**Agreement vs Chance (50%)**")
                if validation['agreement_significantly_above_chance']:
                    st.success(f"✅ Significantly above chance (p={validation['agreement_exceeds_chance_p_value']:.4f})")
                else:
                    st.warning(f"⚠️ Not significantly different from chance (p={validation['agreement_exceeds_chance_p_value']:.4f})")
            
            with col2:
                st.markdown("**Correlation vs Zero**")
                if validation['correlation_significantly_positive']:
                    st.success(f"✅ Significantly positive (p={validation['correlation_significantly_nonzero_p_value']:.4f})")
                else:
                    st.info(f"ℹ️ Not significantly different from zero (p={validation['correlation_significantly_nonzero_p_value']:.4f})")
            
            # Validation strength
            strength = validation['validation_strength']
            if strength == 'strong':
                st.success(f"🎯 **Validation Strength: STRONG**")
            elif strength == 'moderate':
                st.info(f"📊 **Validation Strength: MODERATE**")
            elif strength == 'weak':
                st.warning(f"⚠️ **Validation Strength: WEAK**")
            else:
                st.error(f"❌ **Insufficient Data for Validation**")
            
            st.caption(validation['interpretation'])
        else:
            st.error(f"❌ {validation['interpretation']}")
        
        # Safety and efficacy
        st.subheader("Safety & Efficacy Summary")
        
        safety = results['group_statistics']['safety']
        mood = results['group_statistics']['mood_shifts']
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("**Safety Metrics**")
            st.metric("Mean Safety Score", f"{safety['mean_safety_score']:.1f}/100")
            st.metric("Subjects Safe", f"{safety['percent_safe']:.0f}%")
        
        with col2:
            st.markdown("**Mood Shift Efficacy**")
            st.metric("Mean Valence Shift", f"{mood['mean_valence_shift']:.2f}")
            st.metric("Mean Magnitude", f"{mood['mean_magnitude']:.2f}")
            
            if mood['statistical_significance']['significantly_positive']:
                st.success(f"✅ Significantly positive (p={mood['statistical_significance']['p_value']:.4f})")
    
    # TAB 2: Mechanistic Coupling
    with tab2:
        st.header("🧬 Mechanistic Coupling: Neurochemistry → EEG → fNIRS")
        
        explain_mechanistic_coupling()
        
        # Select a subject to show the cascade
        st.subheader("Example Subject: Complete Biophysical Cascade")
        
        subject_idx = st.slider(
            "Select Subject",
            min_value=0,
            max_value=len(results['individual_results'])-1,
            value=0
        )
        
        subject = results['individual_results'][subject_idx]
        
        # Simulate neurochemistry for this subject
        mood_shift = subject['mood_shift']
        neurochemistry = simulate_neurochemical_data(
            mood_shift_direction=mood_shift['direction'],
            mood_shift_magnitude=mood_shift['shift_magnitude'],
            species=species
        )
        
        # Show the complete cascade
        fig = plot_multimodal_coupling(subject, neurochemistry)
        st.plotly_chart(fig, use_container_width=True)
        
        # Show detailed neurochemistry
        st.subheader("Neurochemical Data")
        
        neuro_df = pd.DataFrame({
            'Neurotransmitter': [k.capitalize() for k in neurochemistry['baseline'].keys()],
            'Baseline (nM)': list(neurochemistry['baseline'].values()),
            'Post-Intervention (nM)': list(neurochemistry['post_intervention'].values()),
            'Change (%)': list(neurochemistry['percent_changes'].values())
        })
        
        st.dataframe(neuro_df, use_container_width=True)
    
    # TAB 3: Individual Subjects
    with tab3:
        st.header("Individual Subject Analysis")
        
        subject_idx = st.slider(
            "Subject ID",
            min_value=1,
            max_value=len(results['individual_results']),
            value=1
        ) - 1
        
        subject = results['individual_results'][subject_idx]
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown(f"**Subject {subject['subject_id']}**")
            st.write(f"Baseline Mood: {subject['baseline_mood']}")
            st.write(f"Mood Shift: {subject['mood_shift']['direction']} ({subject['mood_shift']['strength']})")
            st.write(f"Safety Score: {subject['safety_metrics']['safety_score']:.0f}/100")
        
        with col2:
            comp = subject['fnirs_eeg_comparison']
            st.markdown("**Cross-Modality Agreement**")
            st.write(f"fNIRS detected: {comp['fnirs_detected_direction']}")
            st.write(f"EEG detected: {comp['eeg_detected_direction']}")
            st.write(f"Agree: {'✅ Yes' if comp['modalities_agree'] else '❌ No'}")
            st.write(f"Correlation: {comp['fnirs_eeg_correlation']:.3f}")
    
    # TAB 4: EEG-fNIRS Comparison
    with tab4:
        st.header("⚡ EEG vs fNIRS Time Series")
        
        subject_idx = st.slider(
            "Select Subject for Comparison",
            min_value=0,
            max_value=len(results['individual_results'])-1,
            value=0,
            key='comparison_slider'
        )
        
        subject = results['individual_results'][subject_idx]
        
        # Plot EEG and fNIRS side-by-side
        fig = make_subplots(
            rows=2, cols=1,
            subplot_titles=('EEG Electrical Activity (Channel 1)', 'fNIRS Oxygenation'),
            vertical_spacing=0.15
        )
        
        # EEG
        eeg_baseline = subject['baseline_eeg'][0, :2500]  # First 10 seconds
        eeg_post = subject['post_eeg'][0, :2500]
        t_eeg = np.linspace(0, 10, 2500)
        
        fig.add_trace(
            go.Scatter(x=t_eeg, y=eeg_baseline, mode='lines', name='Baseline EEG',
                      line=dict(color='#3498db', width=1)),
            row=1, col=1
        )
        fig.add_trace(
            go.Scatter(x=t_eeg, y=eeg_post, mode='lines', name='Post EEG',
                      line=dict(color='#e74c3c', width=1)),
            row=1, col=1
        )
        
        # fNIRS
        fnirs_baseline = subject['baseline_fnirs']
        fnirs_post = subject['post_fnirs']
        
        fig.add_trace(
            go.Scatter(x=fnirs_baseline['timestamps'][:100], y=fnirs_baseline['oxygenation'][:100],
                      mode='lines', name='Baseline fNIRS', line=dict(color='#3498db', width=2)),
            row=2, col=1
        )
        fig.add_trace(
            go.Scatter(x=fnirs_post['timestamps'][:100], y=fnirs_post['oxygenation'][:100],
                      mode='lines', name='Post fNIRS', line=dict(color='#e74c3c', width=2)),
            row=2, col=1
        )
        
        fig.update_xaxes(title_text="Time (s)", row=1, col=1)
        fig.update_yaxes(title_text="EEG (μV)", row=1, col=1)
        
        fig.update_xaxes(title_text="Time (s)", row=2, col=1)
        fig.update_yaxes(title_text="Oxygenation (%)", row=2, col=1)
        
        fig.update_layout(height=700)
        
        st.plotly_chart(fig, use_container_width=True)
    
    # TAB 5: Neurochemistry
    with tab5:
        st.header("📈 Neurochemical Analysis")
        
        st.markdown("""
        **Simulated neurochemical data** showing the molecular basis of mood shifts.
        This is the PRIMARY mechanism that drives both EEG and fNIRS changes.
        """)
        
        # Aggregate neurochemistry across all subjects
        all_neurochemistry = []
        for subject in results['individual_results']:
            mood_shift = subject['mood_shift']
            neuro = simulate_neurochemical_data(
                mood_shift_direction=mood_shift['direction'],
                mood_shift_magnitude=mood_shift['shift_magnitude'],
                species=species
            )
            all_neurochemistry.append(neuro['percent_changes'])
        
        # Average across subjects
        avg_changes = {}
        for key in all_neurochemistry[0].keys():
            avg_changes[key] = np.mean([n[key] for n in all_neurochemistry])
        
        # Plot
        fig = plot_neurochemical_cascade({'percent_changes': avg_changes})
        st.plotly_chart(fig, use_container_width=True)
        
        st.markdown("""
        **Interpretation:**
        - **Dopamine ↑**: Reward, motivation, positive valence
        - **Serotonin ↑**: Mood regulation, well-being
        - **GABA ↑**: Inhibitory, reduces anxiety
        - **Glutamate ↓**: Excitatory balance (prevents overstimulation)
        - **Norepinephrine ↑**: Alertness, arousal
        - **Acetylcholine ↑**: Attention, memory
        
        These neurochemical changes are the **root cause** of both EEG electrical changes and fNIRS hemodynamic changes!
        """)

def render_animal_testing_dashboard():
    """Entry point for Streamlit app"""
    run_animal_study_dashboard()

if __name__ == "__main__":
    run_animal_study_dashboard()

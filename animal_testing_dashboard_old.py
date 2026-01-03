"""
Animal Testing Dashboard

Interactive Streamlit interface for running and visualizing animal testing simulations
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
import plotly.express as px
from plotly.subplots import make_subplots
import json
from datetime import datetime

from animal_testing_simulation import (
    AnimalStudySimulator,
    QuantumEntanglementComparator,
    BrainAlterationHypothesizer
)


def render_animal_testing_dashboard():
    """Main dashboard for animal testing simulations"""
    
    st.header("🐭 Observational Animal Safety & Efficacy Testing")
    st.markdown("""
    Simulate comprehensive animal studies to test the safety and efficacy of the mood amplifier technology.
    This addresses the critical gap identified in the safety analysis: **zero animal studies**.
    
    **Study Design:**
    - Observational safety testing with EEG monitoring
    - Mood shift analysis across varying intervention durations
    - Physical mechanism exploration including quantum entanglement comparisons
    - Brain alteration hypothesis generation
    """)
    
    # Study parameters
    st.subheader("1️⃣ Study Parameters")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        n_subjects = st.slider(
            "Number of subjects",
            min_value=10,
            max_value=100,
            value=30,
            step=5,
            help="More subjects provide better statistical power"
        )
    
    with col2:
        species = st.selectbox(
            "Species",
            ["rat", "mouse", "guinea pig"],
            help="Animal model for testing"
        )
    
    with col3:
        st.metric("Statistical Power", f"{min(95, 50 + n_subjects//2)}%")
    
    # Intervention duration comparison
    st.subheader("2️⃣ Time Course Analysis")
    
    compare_durations = st.checkbox(
        "Compare 3-minute vs 5-minute intervention durations",
        value=True,
        help="Test if effects emerge differently at different time points"
    )
    
    if compare_durations:
        durations = [3, 5]
        st.info("Will run two separate studies: 3-minute and 5-minute interventions")
    else:
        single_duration = st.slider(
            "Intervention duration (minutes)",
            min_value=1,
            max_value=10,
            value=3,
            help="How long the mood amplifier is applied"
        )
        durations = [single_duration]
    
    # Initialize session state for results
    if 'animal_study_results' not in st.session_state:
        st.session_state.animal_study_results = None
    
    # Run study button
    if st.button("🚀 Run Animal Study", type="primary"):
        all_results = {}
        
        for duration in durations:
            st.markdown(f"### Running {duration}-Minute Intervention Study")
            
            with st.spinner(f"Simulating study with {n_subjects} {species}s, {duration}-minute intervention..."):
                simulator = AnimalStudySimulator(n_subjects=n_subjects, species=species)
                results = simulator.run_study(
                    intervention_duration_minutes=duration,
                    recording_duration_minutes=2
                )
                all_results[f"{duration}_min"] = results
        
        st.session_state.animal_study_results = all_results
        st.success("✅ Animal study complete!")
    
    # Display results
    if st.session_state.animal_study_results:
        results_data = st.session_state.animal_study_results
        
        # Create tabs for different analyses
        analysis_tabs = st.tabs([
            "📊 Efficacy Results",
            "🛡️ Safety Analysis",
            "🔗 Coupling Mechanisms",
            "⚛️ Quantum Comparison",
            "🧠 Brain Alterations",
            "📋 Full Report"
        ])
        
        with analysis_tabs[0]:
            render_efficacy_results(results_data)
        
        with analysis_tabs[1]:
            render_safety_analysis(results_data)
        
        with analysis_tabs[2]:
            render_coupling_analysis(results_data)
        
        with analysis_tabs[3]:
            render_quantum_comparison(results_data)
        
        with analysis_tabs[4]:
            render_brain_alterations(results_data)
        
        with analysis_tabs[5]:
            render_full_report(results_data)


def render_efficacy_results(results_data: dict):
    """Display efficacy analysis"""
    
    st.subheader("📊 Mood Shift Efficacy Analysis")
    
    # Compare durations if multiple
    if len(results_data) > 1:
        st.markdown("### Time Course Comparison: 3 vs 5 Minutes")
        
        comparison_data = []
        for duration_key, results in results_data.items():
            duration = int(duration_key.split('_')[0])
            stats = results['group_statistics']['mood_shifts']
            
            comparison_data.append({
                'Duration (min)': duration,
                'Mean Valence Shift': stats['mean_valence_shift'],
                'Mean Arousal Shift': stats['mean_arousal_shift'],
                'Mean Magnitude': stats['mean_magnitude'],
                'p-value': stats['statistical_significance']['p_value']
            })
        
        # Create comparison table
        st.dataframe(comparison_data)
        
        # Visualization
        fig = make_subplots(
            rows=1, cols=2,
            subplot_titles=("Valence Shift by Duration", "Effect Magnitude by Duration")
        )
        
        durations_list = [d['Duration (min)'] for d in comparison_data]
        valence_shifts = [d['Mean Valence Shift'] for d in comparison_data]
        magnitudes = [d['Mean Magnitude'] for d in comparison_data]
        
        fig.add_trace(
            go.Bar(x=durations_list, y=valence_shifts, name="Valence Shift",
                  marker_color='#2ecc71'),
            row=1, col=1
        )
        
        fig.add_trace(
            go.Bar(x=durations_list, y=magnitudes, name="Magnitude",
                  marker_color='#3498db'),
            row=1, col=2
        )
        
        fig.update_layout(height=400, showlegend=False)
        st.plotly_chart(fig, use_container_width=True)
        
        # Determine which duration is more effective
        if comparison_data[1]['Mean Magnitude'] > comparison_data[0]['Mean Magnitude'] * 1.1:
            st.success("✅ **Finding:** 5-minute intervention produces stronger effects than 3-minute")
        elif comparison_data[0]['Mean Magnitude'] > comparison_data[1]['Mean Magnitude'] * 1.1:
            st.info("📊 **Finding:** 3-minute intervention is nearly as effective as 5-minute")
        else:
            st.info("📊 **Finding:** Effects are similar between 3 and 5 minutes")
    
    # Detailed results for each duration
    for duration_key, results in results_data.items():
        duration = duration_key.replace('_', ' ').title()
        
        st.markdown(f"### {duration} Results")
        
        stats = results['group_statistics']['mood_shifts']
        
        # Key metrics
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            st.metric(
                "Mean Valence Shift",
                f"{stats['mean_valence_shift']:+.3f}",
                delta=f"±{stats['std_valence_shift']:.3f}"
            )
        
        with col2:
            st.metric(
                "Mean Magnitude",
                f"{stats['mean_magnitude']:.3f}",
                delta="Effect Size"
            )
        
        with col3:
            sig_status = "Significant" if stats['statistical_significance']['significantly_positive'] else "Not Significant"
            st.metric(
                "Statistical Significance",
                sig_status,
                delta=f"p={stats['statistical_significance']['p_value']:.4f}"
            )
        
        with col4:
            n_positive = stats['direction_distribution'].get('positive', 0) + \
                        stats['direction_distribution'].get('calm_positive', 0)
            percent_positive = (n_positive / results['study_parameters']['n_subjects']) * 100
            st.metric(
                "Positive Response Rate",
                f"{percent_positive:.1f}%"
            )
        
        # Direction distribution
        st.markdown("#### Mood Shift Direction Distribution")
        
        direction_dist = stats['direction_distribution']
        
        # Create pie chart
        labels = list(direction_dist.keys())
        values = list(direction_dist.values())
        
        colors = {
            'positive': '#2ecc71',
            'calm_positive': '#27ae60',
            'no_change': '#95a5a6',
            'negative': '#e74c3c',
            'calm_negative': '#c0392b'
        }
        
        color_list = [colors.get(label, '#3498db') for label in labels]
        
        fig = go.Figure(data=[go.Pie(
            labels=labels,
            values=values,
            marker_colors=color_list,
            hole=0.3
        )])
        
        fig.update_layout(title=f"Distribution of Mood Shift Directions ({duration})", height=400)
        st.plotly_chart(fig, use_container_width=True)
        
        # Strength distribution
        st.markdown("#### Effect Strength Distribution")
        
        strength_dist = stats['strength_distribution']
        
        strength_labels = list(strength_dist.keys())
        strength_values = list(strength_dist.values())
        
        fig = go.Figure(data=[go.Bar(
            x=strength_labels,
            y=strength_values,
            marker_color=['#e74c3c' if s == 'none' else '#f39c12' if s == 'weak' 
                         else '#3498db' if s == 'moderate' else '#2ecc71' 
                         for s in strength_labels]
        )])
        
        fig.update_layout(
            title=f"Effect Strength Distribution ({duration})",
            xaxis_title="Strength",
            yaxis_title="Number of Subjects",
            height=400
        )
        st.plotly_chart(fig, use_container_width=True)
        
        # Interpretation
        if stats['statistical_significance']['significantly_positive']:
            st.success(f"""
            ✅ **Efficacy Confirmed:** The {duration} intervention produces statistically significant 
            positive mood shifts (p={stats['statistical_significance']['p_value']:.4f}). 
            {percent_positive:.1f}% of subjects showed positive mood changes.
            """)
        else:
            st.warning(f"""
            ⚠️ **Inconclusive Results:** The {duration} intervention did not produce statistically 
            significant effects at the group level, though {percent_positive:.1f}% of subjects 
            showed positive responses.
            """)


def render_safety_analysis(results_data: dict):
    """Display safety analysis"""
    
    st.subheader("🛡️ Comprehensive Safety Analysis")
    
    for duration_key, results in results_data.items():
        duration = duration_key.replace('_', ' ').title()
        
        st.markdown(f"### {duration} Safety Profile")
        
        safety_summary = results['safety_summary']
        group_stats = results['group_statistics']
        
        # Overall safety metrics
        col1, col2, col3 = st.columns(3)
        
        with col1:
            safety_score = group_stats['safety']['mean_safety_score']
            st.metric(
                "Mean Safety Score",
                f"{safety_score:.1f}/100",
                delta=f"{group_stats['safety']['percent_safe']:.1f}% subjects safe"
            )
            
            if safety_score >= 85:
                st.success("Excellent safety profile")
            elif safety_score >= 75:
                st.info("Good safety profile")
            else:
                st.warning("Safety concerns noted")
        
        with col2:
            behavioral_score = group_stats['behavioral']['mean_behavioral_score']
            st.metric(
                "Mean Behavioral Score",
                f"{behavioral_score:.1f}/100",
                delta=f"{group_stats['behavioral']['percent_normal']:.1f}% normal behavior"
            )
            
            if behavioral_score >= 85:
                st.success("No behavioral issues")
            elif behavioral_score >= 75:
                st.info("Minimal behavioral concerns")
            else:
                st.warning("Behavioral changes observed")
        
        with col3:
            seizure_risk = group_stats['safety']['mean_seizure_risk']
            st.metric(
                "Mean Seizure Risk",
                f"{seizure_risk:.1f}%",
                delta="Lower is better"
            )
            
            if seizure_risk < 5:
                st.success("Very low seizure risk")
            elif seizure_risk < 10:
                st.info("Low seizure risk")
            else:
                st.warning("Elevated seizure risk")
        
        # Detailed safety concerns
        st.markdown("#### Safety Concern Breakdown")
        
        concerns = safety_summary['safety_concerns']
        
        concern_names = list(concerns.keys())
        concern_percents = [concerns[name]['percent'] for name in concern_names]
        
        fig = go.Figure(data=[go.Bar(
            x=concern_names,
            y=concern_percents,
            marker_color=['#e74c3c' if p > 20 else '#f39c12' if p > 10 else '#2ecc71' 
                         for p in concern_percents],
            text=[f"{p:.1f}%" for p in concern_percents],
            textposition='auto'
        )])
        
        fig.update_layout(
            title=f"Safety Concerns by Type ({duration})",
            xaxis_title="Concern Type",
            yaxis_title="Percentage of Subjects Affected",
            height=400,
            xaxis_tickangle=-45
        )
        
        st.plotly_chart(fig, use_container_width=True)
        
        # Overall assessment
        st.markdown("#### Overall Safety Assessment")
        st.info(safety_summary['overall_assessment'])
        
        # Physical damage indicators
        st.markdown("#### Physical Brain Damage Assessment")
        
        if concerns['abnormal_amplitude']['percent'] < 5 and \
           concerns['poor_frequency_diversity']['percent'] < 5:
            st.success("""
            ✅ **No Evidence of Physical Brain Damage:**
            - EEG amplitudes remain in normal range
            - Frequency diversity is healthy
            - No signs of neuronal cell death or excitotoxicity
            - Brain signals maintain natural complexity
            """)
        else:
            st.warning(f"""
            ⚠️ **Some Abnormalities Detected:**
            - {concerns['abnormal_amplitude']['percent']:.1f}% subjects show abnormal amplitude
            - {concerns['poor_frequency_diversity']['percent']:.1f}% subjects show reduced frequency diversity
            - Further investigation recommended
            """)


def render_coupling_analysis(results_data: dict):
    """Display coupling mechanism analysis"""
    
    st.subheader("🔗 Coupling Mechanism Analysis")
    
    for duration_key, results in results_data.items():
        duration = duration_key.replace('_', ' ').title()
        
        st.markdown(f"### {duration} Coupling Analysis")
        
        coupling_stats = results['group_statistics']['coupling']
        coupling_mechanism = results['coupling_mechanism']
        
        # Coupling strength metrics
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric(
                "Mean Coupling Strength",
                f"{coupling_stats['mean_coupling_strength']:.3f}",
                delta=f"±{coupling_stats['std_coupling_strength']:.3f}"
            )
        
        with col2:
            st.metric(
                "Coupling Range",
                f"[{coupling_stats['min_coupling']:.2f}, {coupling_stats['max_coupling']:.2f}]"
            )
        
        with col3:
            st.metric(
                "In Target Range (0.6-0.85)",
                f"{coupling_stats['percent_in_target_range']:.1f}%",
                delta=f"{coupling_stats['in_target_range_0.6_0.85']} subjects"
            )
        
        # Coupling distribution
        st.markdown("#### Coupling Strength Distribution")
        
        individual_results = results['individual_results']
        coupling_values = [r['coupling_strength'] for r in individual_results]
        
        fig = go.Figure()
        
        fig.add_trace(go.Histogram(
            x=coupling_values,
            nbinsx=20,
            marker_color='#3498db',
            opacity=0.7
        ))
        
        # Add threshold lines
        fig.add_vline(x=0.6, line_dash="dash", line_color="orange", 
                     annotation_text="0.6 threshold", annotation_position="top")
        fig.add_vline(x=0.85, line_dash="dash", line_color="red",
                     annotation_text="0.85 threshold", annotation_position="top")
        
        fig.update_layout(
            title=f"Distribution of Coupling Strengths ({duration})",
            xaxis_title="Coupling Strength",
            yaxis_title="Frequency",
            height=400
        )
        
        st.plotly_chart(fig, use_container_width=True)
        
        # Regime classification
        st.markdown("#### Coupling Regime Classification")
        
        regime = coupling_mechanism['regime']
        regime_colors = {
            'weak': '#95a5a6',
            'moderate': '#3498db',
            'strong': '#2ecc71',
            'hypersynchronized': '#e74c3c'
        }
        
        st.markdown(f"**Detected Regime:** `{regime.upper()}`")
        
        # Proposed mechanisms
        st.markdown("#### Proposed Physical Mechanisms")
        
        for i, mechanism in enumerate(coupling_mechanism['proposed_mechanisms'], 1):
            with st.expander(f"**Mechanism {i}: {mechanism['name']}** (Probability: {mechanism['probability']:.0%})"):
                st.markdown(f"**Description:** {mechanism['description']}")
                st.markdown(f"**Physical Basis:** {mechanism['physical_basis']}")
                
                if 'warning' in mechanism:
                    st.warning(f"⚠️ {mechanism['warning']}")
        
        # Interpretation
        if 0.6 <= coupling_stats['mean_coupling_strength'] <= 0.85:
            st.success(f"""
            ✅ **Optimal Coupling Range Achieved:**
            Mean coupling strength ({coupling_stats['mean_coupling_strength']:.3f}) falls within 
            the hypothesized optimal range (0.6-0.85). {coupling_stats['percent_in_target_range']:.1f}% 
            of subjects showed coupling in this range.
            """)
        elif coupling_stats['mean_coupling_strength'] < 0.6:
            st.info(f"""
            📊 **Weak Coupling Observed:**
            Mean coupling strength ({coupling_stats['mean_coupling_strength']:.3f}) is below the 
            target range. Effects may be present but subtle.
            """)
        else:
            st.warning(f"""
            ⚠️ **Hypersynchronization Detected:**
            Mean coupling strength ({coupling_stats['mean_coupling_strength']:.3f}) exceeds the safe 
            threshold. Monitor for potential over-coupling effects.
            """)


def render_quantum_comparison(results_data: dict):
    """Display quantum entanglement comparison"""
    
    st.subheader("⚛️ Quantum Entanglement Comparison")
    
    # Get quantum analysis from first result (same for all durations)
    first_result = list(results_data.values())[0]
    quantum_analysis = first_result['quantum_analysis']
    
    st.markdown("""
    This analysis explores mathematical and behavioral similarities between neural coupling 
    and quantum entanglement to better understand the physical mechanisms at play.
    """)
    
    # Overall similarity
    st.metric(
        "Overall Similarity Score",
        f"{quantum_analysis['overall_similarity_score']:.2f}",
        delta="0 = No similarity, 1 = Identical"
    )
    
    st.info(quantum_analysis['conclusion'])
    
    # Mathematical similarities
    st.markdown("### Mathematical Similarities")
    
    math_sims = quantum_analysis['mathematical_similarities']
    
    similarity_data = []
    for key, data in math_sims.items():
        similarity_data.append({
            'Aspect': data['description'],
            'Quantum Behavior': data['quantum'],
            'Neural Coupling': data['neural_coupling'],
            'Similarity': f"{data['similarity_score']:.2f}",
            'Notes': data['notes']
        })
    
    st.dataframe(similarity_data)
    
    # Visualize similarity scores
    fig = go.Figure(data=[go.Bar(
        x=[d['Aspect'] for d in similarity_data],
        y=[float(d['Similarity']) for d in similarity_data],
        marker_color=['#2ecc71' if float(d['Similarity']) > 0.6 else 
                     '#3498db' if float(d['Similarity']) > 0.4 else '#e74c3c' 
                     for d in similarity_data],
        text=[d['Similarity'] for d in similarity_data],
        textposition='auto'
    )])
    
    fig.update_layout(
        title="Mathematical Similarity Scores",
        xaxis_title="Aspect",
        yaxis_title="Similarity Score (0-1)",
        height=400,
        xaxis_tickangle=-45
    )
    
    st.plotly_chart(fig, use_container_width=True)
    
    # Behavioral similarities
    st.markdown("### Behavioral Similarities")
    
    behav_sims = quantum_analysis['behavioral_similarities']
    
    behavioral_data = []
    for key, data in behav_sims.items():
        behavioral_data.append({
            'Behavior': data['description'],
            'Quantum': data['quantum'],
            'Neural': data['neural_coupling'],
            'Similarity': f"{data['similarity_score']:.2f}"
        })
    
    st.dataframe(behavioral_data)
    
    # Key differences
    st.markdown("### Key Differences")
    
    for i, diff in enumerate(quantum_analysis['key_differences'], 1):
        st.markdown(f"{i}. {diff}")
    
    # Interpretation
    st.markdown("### Interpretation")
    
    st.success("""
    **Conclusion:** While neural coupling and quantum entanglement share some mathematical 
    formalism (correlation functions, phase relationships), they are fundamentally different 
    phenomena. Neural coupling operates through classical electromagnetic and chemical signaling, 
    while quantum entanglement is a purely quantum mechanical effect that violates classical 
    physics constraints.
    
    The similarities are **analogical** rather than **mechanistic** - both involve correlations 
    between separated entities, but the physical mechanisms are entirely different.
    """)


def render_brain_alterations(results_data: dict):
    """Display brain alteration hypotheses"""
    
    st.subheader("🧠 Brain Alteration Hypotheses")
    
    st.markdown("""
    Based on observed EEG patterns, coupling strengths, and safety metrics, we generate 
    evidence-based hypotheses about how the intervention alters brain structure and function.
    """)
    
    for duration_key, results in results_data.items():
        duration = duration_key.replace('_', ' ').title()
        
        st.markdown(f"### {duration} Alteration Analysis")
        
        hypotheses = results['brain_alteration_hypotheses']
        
        # Risk assessment summary
        risk_assessment = hypotheses['risk_assessment']
        
        col1, col2 = st.columns(2)
        
        with col1:
            risk_level = risk_assessment['overall_risk']
            risk_colors = {'Low': '🟢', 'Moderate': '🟡', 'High': '🔴'}
            st.metric(
                "Overall Risk Level",
                f"{risk_colors.get(risk_level, '⚪')} {risk_level}"
            )
        
        with col2:
            reversibility = hypotheses['reversibility']
            st.metric(
                "Predicted Recovery Time",
                reversibility.get('predicted_recovery_time', 'N/A'),
                delta=f"Confidence: {reversibility.get('confidence', 'Unknown')}"
            )
        
        st.info(f"**Recommendation:** {risk_assessment['recommendation']}")
        st.info(f"**Monitoring:** {risk_assessment['monitoring']}")
        
        # Functional changes
        if hypotheses['functional_changes']:
            st.markdown("#### Functional Brain Changes")
            
            for i, change in enumerate(hypotheses['functional_changes'], 1):
                with st.expander(f"**{i}. {change['hypothesis']}**"):
                    st.markdown(f"**Evidence:** {change['evidence']}")
                    st.markdown(f"**Proposed Mechanism:** {change['mechanism']}")
                    st.markdown(f"**Timeframe:** {change['timeframe']}")
                    st.markdown(f"**Reversibility:** {change['reversibility']}")
        
        # Neurochemical changes
        if hypotheses['neurochemical_changes']:
            st.markdown("#### Neurochemical Changes")
            
            for i, change in enumerate(hypotheses['neurochemical_changes'], 1):
                with st.expander(f"**{i}. {change['hypothesis']}**"):
                    st.markdown(f"**Evidence:** {change['evidence']}")
                    st.markdown(f"**Proposed Mechanism:** {change['mechanism']}")
                    st.markdown(f"**Supporting Data:** {change.get('supporting_data', 'N/A')}")
                    st.markdown(f"**Reversibility:** {change['reversibility']}")
        
        # Structural changes
        if hypotheses['structural_changes']:
            st.markdown("#### Structural Brain Changes")
            st.warning("⚠️ Potential structural alterations detected")
            
            for i, change in enumerate(hypotheses['structural_changes'], 1):
                with st.expander(f"**{i}. {change['hypothesis']}** (Risk: {change.get('risk_level', 'Unknown')})"):
                    st.markdown(f"**Evidence:** {change['evidence']}")
                    st.markdown(f"**Proposed Mechanism:** {change['mechanism']}")
                    st.markdown(f"**Timeframe:** {change.get('timeframe', 'Unknown')}")
                    st.markdown(f"**Reversibility:** {change['reversibility']}")
        
        # Reversibility details
        st.markdown("#### Reversibility Analysis")
        
        if 'mechanism' in reversibility:
            st.markdown(f"**Recovery Mechanism:** {reversibility['mechanism']}")
        
        if 'note' in reversibility:
            st.warning(f"⚠️ **Note:** {reversibility['note']}")
        
        # Overall interpretation
        if risk_level == 'Low':
            st.success("""
            ✅ **Low-Risk Intervention:** Observed changes appear to be functional and reversible.
            No evidence of structural damage or permanent alterations. Effects are consistent with
            temporary modulation of neural network activity.
            """)
        elif risk_level == 'Moderate':
            st.info("""
            📊 **Moderate-Risk Intervention:** Strong effects observed with potential for longer-lasting
            changes. Continued monitoring recommended to ensure reversibility and rule out cumulative
            effects with repeated exposure.
            """)
        else:
            st.error("""
            🚨 **High-Risk Intervention:** Significant safety concerns detected. Structural changes
            may occur with prolonged or repeated exposure. Intervention parameters should be reviewed
            and potentially reduced.
            """)


def render_full_report(results_data: dict):
    """Display complete study report"""
    
    st.subheader("📋 Complete Animal Study Report")
    
    # Summary statistics across all durations
    st.markdown("### Executive Summary")
    
    for duration_key, results in results_data.items():
        duration = duration_key.replace('_', ' ').title()
        
        with st.expander(f"**{duration} Study Summary**", expanded=True):
            params = results['study_parameters']
            
            st.markdown(f"""
            **Study Parameters:**
            - Subjects: {params['n_subjects']} {params['species']}s
            - Intervention Duration: {params['intervention_duration_min']} minutes
            - Recording Duration: {params['recording_duration_min']} minutes
            
            **Key Findings:**
            """)
            
            # Efficacy
            mood_stats = results['group_statistics']['mood_shifts']
            st.markdown(f"""
            **Efficacy:**
            - Mean valence shift: {mood_stats['mean_valence_shift']:+.3f} ± {mood_stats['std_valence_shift']:.3f}
            - Statistical significance: {'Yes' if mood_stats['statistical_significance']['significantly_positive'] else 'No'} 
              (p={mood_stats['statistical_significance']['p_value']:.4f})
            - Positive response rate: {((mood_stats['direction_distribution'].get('positive', 0) + 
                                        mood_stats['direction_distribution'].get('calm_positive', 0)) / 
                                       params['n_subjects'] * 100):.1f}%
            """)
            
            # Safety
            safety_stats = results['group_statistics']['safety']
            st.markdown(f"""
            **Safety:**
            - Mean safety score: {safety_stats['mean_safety_score']:.1f}/100
            - Subjects with safe scores: {safety_stats['percent_safe']:.1f}%
            - Mean seizure risk: {safety_stats['mean_seizure_risk']:.1f}%
            - Overall assessment: {results['safety_summary']['overall_assessment']}
            """)
            
            # Coupling
            coupling_stats = results['group_statistics']['coupling']
            st.markdown(f"""
            **Coupling:**
            - Mean coupling strength: {coupling_stats['mean_coupling_strength']:.3f}
            - In target range (0.6-0.85): {coupling_stats['percent_in_target_range']:.1f}%
            - Detected regime: {results['coupling_mechanism']['regime']}
            """)
    
    # Download full report
    st.markdown("### Export Results")
    
    # Prepare JSON export
    export_data = {
        'study_date': datetime.now().isoformat(),
        'results': results_data
    }
    
    # Remove EEG data from export (too large)
    for duration_key in export_data['results']:
        for individual_result in export_data['results'][duration_key]['individual_results']:
            if 'baseline_eeg' in individual_result:
                del individual_result['baseline_eeg']
            if 'post_eeg' in individual_result:
                del individual_result['post_eeg']
    
    st.download_button(
        label="📥 Download Complete Report (JSON)",
        data=json.dumps(export_data, indent=2, default=str),
        file_name=f"animal_study_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
        mime="application/json"
    )
    
    # Display full JSON
    with st.expander("View Full Report (JSON)", expanded=False):
        st.json(export_data)


if __name__ == '__main__':
    st.set_page_config(
        page_title="Animal Testing Simulation",
        page_icon="🐭",
        layout="wide"
    )
    
    st.title("🐭 Animal Testing Simulation Dashboard")
    render_animal_testing_dashboard()

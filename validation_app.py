"""
Model Validation Dashboard

Streamlit interface for validating emotion models on DEAP dataset
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
import plotly.express as px
from pathlib import Path
import pickle
import os

from deap_loader import DEAPDataset, download_instructions
from emotion_models import RussellCircumplexModel, PANASModel, FrontalAlphaAsymmetry
from tiuop_adapter import TIUOPModel
from model_comparison import ModelComparison, CouplingThresholdAnalysis
from results_export import export_validation_results, interpret_validation_results


def render_validation_dashboard():
    """Main validation dashboard interface"""
    
    st.header("🔬 Scientific Validation Experiments")
    st.markdown("""
    Test TI-UOP framework against established emotion recognition models using
    **public EEG dataset (DEAP)**. Examine evidence for coupling thresholds (0.6, 0.85).
    
    **Note:** SEED dataset support coming soon.
    """)
    
    # Dataset selection
    st.subheader("1️⃣ Dataset Selection")
    
    dataset_choice = st.radio(
        "Choose dataset:",
        ["Synthetic Demo Data", "DEAP Dataset (Download Required)"],
        help="Synthetic data for testing, DEAP for real validation"
    )
    
    if dataset_choice == "DEAP Dataset (Download Required)":
        dataset = DEAPDataset('./data/deap')
        
        if not Path('./data/deap').exists():
            st.warning("⚠️ DEAP dataset not found")
            
            if st.button("📋 Show Download Instructions"):
                st.code("""
# DEAP Dataset Download Instructions

1. Visit: http://www.eecs.qmul.ac.uk/mmv/datasets/deap/

2. Fill out End User License Agreement form

3. Download "Preprocessed data (Python format)" (~1.8 GB)

4. Extract and place files:
   mkdir -p ./data/deap
   mv data_preprocessed_python/*.dat ./data/deap/
   
5. Return here and select DEAP dataset
""", language="bash")
            
            st.info("💡 Use 'Synthetic Demo Data' to test the interface without downloading DEAP")
            return
        
        # Load available participants
        available_participants = sorted([
            int(f.stem[1:]) 
            for f in Path('./data/deap').glob('s*.dat')
        ])
        
        if len(available_participants) == 0:
            st.error("No DEAP files found in ./data/deap/")
            return
        
        st.success(f"✅ Found {len(available_participants)} participants")
        
        participant_id = st.selectbox(
            "Select participant:",
            available_participants,
            format_func=lambda x: f"Participant {x}"
        )
        
        with st.spinner(f"Loading participant {participant_id}..."):
            eeg_trials, labels = dataset.load_participant(participant_id)
        
        st.success(f"Loaded {len(eeg_trials)} trials")
        
    else:
        # Generate synthetic data
        st.info("Using synthetic data (random EEG-like signals for demonstration)")
        n_trials = st.slider("Number of synthetic trials:", 10, 40, 20)
        
        with st.spinner("Generating synthetic data..."):
            np.random.seed(42)
            eeg_trials = np.random.randn(n_trials, 32, 7680) * 10  # 60s @ 128 Hz
            labels = np.random.uniform(1, 9, size=(n_trials, 4))
        
        st.success(f"Generated {n_trials} synthetic trials")
    
    # Experiment selection
    st.subheader("2️⃣ Select Experiments")
    
    run_model_comparison = st.checkbox(
        "🏆 Model Comparison (Individual vs Ensemble)", 
        value=True,
        help="Compare Russell, PANAS, Frontal Asymmetry, TI-UOP individually and in combinations"
    )
    
    run_coupling_analysis = st.checkbox(
        "🔗 Coupling Threshold Analysis", 
        value=True,
        help="Test if correlation naturally clusters around 0.6 and 0.85"
    )
    
    # Initialize session state for results persistence
    if 'validation_results' not in st.session_state:
        st.session_state.validation_results = None
    if 'coupling_results' not in st.session_state:
        st.session_state.coupling_results = None
    
    # Run experiments
    if st.button("🚀 Run Validation Experiments", type="primary"):
        
        # Model Comparison
        if run_model_comparison:
            st.subheader("📊 Model Comparison Results")
            
            with st.spinner("Evaluating all models..."):
                comparison = ModelComparison()
                results = comparison.evaluate_on_trials(eeg_trials, labels)
                # Store in session state
                st.session_state.validation_results = results
            
            # Display results
            col1, col2 = st.columns(2)
            
            with col1:
                st.markdown("### Valence Prediction")
                
                # Create performance table
                model_names = []
                correlations = []
                maes = []
                
                for model_name, metrics in results.items():
                    if model_name != 'summary':
                        model_names.append(model_name)
                        correlations.append(metrics['valence']['correlation'])
                        maes.append(metrics['valence']['mae'])
                
                # Sort by correlation
                sorted_idx = np.argsort(correlations)[::-1]
                
                # Create bar chart
                fig = go.Figure()
                fig.add_trace(go.Bar(
                    x=[model_names[i] for i in sorted_idx],
                    y=[correlations[i] for i in sorted_idx],
                    marker_color=['#2ecc71' if 'tiuop' in model_names[i].lower() 
                                 else '#3498db' for i in sorted_idx],
                    text=[f"{correlations[i]:.3f}" for i in sorted_idx],
                    textposition='auto'
                ))
                fig.update_layout(
                    title="Valence Correlation with Ground Truth",
                    xaxis_title="Model",
                    yaxis_title="Pearson Correlation",
                    height=400,
                    xaxis_tickangle=-45
                )
                st.plotly_chart(fig, use_container_width=True)
            
            with col2:
                st.markdown("### Arousal Prediction")
                
                arousal_corrs = []
                for model_name in model_names:
                    arousal_corrs.append(results[model_name]['arousal']['correlation'])
                
                sorted_idx = np.argsort(arousal_corrs)[::-1]
                
                fig = go.Figure()
                fig.add_trace(go.Bar(
                    x=[model_names[i] for i in sorted_idx],
                    y=[arousal_corrs[i] for i in sorted_idx],
                    marker_color=['#2ecc71' if 'tiuop' in model_names[i].lower() 
                                 else '#e74c3c' for i in sorted_idx],
                    text=[f"{arousal_corrs[i]:.3f}" for i in sorted_idx],
                    textposition='auto'
                ))
                fig.update_layout(
                    title="Arousal Correlation with Ground Truth",
                    xaxis_title="Model",
                    yaxis_title="Pearson Correlation",
                    height=400,
                    xaxis_tickangle=-45
                )
                st.plotly_chart(fig, use_container_width=True)
            
            # Key findings
            st.markdown("### 🎯 Key Findings")
            
            summary = results['summary']
            
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric(
                    "Best Individual Model",
                    f"{summary['best_individual_valence_corr']:.3f}",
                    help="Highest valence correlation among single models"
                )
            
            with col2:
                st.metric(
                    "Ensemble Performance",
                    f"{summary['ensemble_valence_corr']:.3f}",
                    delta=f"{summary['ensemble_improvement']:+.3f}",
                    help="Weighted ensemble of all models"
                )
            
            with col3:
                if summary['ensemble_better']:
                    st.success("✅ **Ensemble improves performance**")
                else:
                    st.warning("⚠️ Ensemble does not improve performance")
            
            # Detailed metrics table
            with st.expander("📋 Detailed Metrics"):
                st.dataframe({
                    'Model': model_names,
                    'Val Corr': [f"{results[m]['valence']['correlation']:.3f}" for m in model_names],
                    'Val MAE': [f"{results[m]['valence']['mae']:.3f}" for m in model_names],
                    'Aro Corr': [f"{results[m]['arousal']['correlation']:.3f}" for m in model_names],
                    'Aro MAE': [f"{results[m]['arousal']['mae']:.3f}" for m in model_names],
                    'Confidence': [f"{results[m]['mean_confidence']:.3f}" for m in model_names]
                })
            
            # Export results
            st.markdown("---")
            col_exp1, col_exp2 = st.columns(2)
            with col_exp1:
                json_export = export_validation_results(model_results=results)
                st.download_button(
                    label="📥 Download Results (JSON)",
                    data=json_export,
                    file_name=f"validation_results_{st.session_state.get('timestamp', 'latest')}.json",
                    mime="application/json",
                    help="Download detailed results for further analysis"
                )
            with col_exp2:
                interpretation = interpret_validation_results(model_results=results)
                with st.expander("🎓 Scientific Interpretation", expanded=False):
                    st.markdown(interpretation)
        
        # Coupling Analysis
        if run_coupling_analysis:
            st.subheader("🔗 Coupling Threshold Analysis")
            
            n_samples = st.slider("Number of trial pairs to sample:", 50, 500, 200, step=50)
            
            with st.spinner(f"Analyzing coupling across {n_samples} trial pairs..."):
                coupling_analyzer = CouplingThresholdAnalysis()
                coupling_results = coupling_analyzer.analyze_trial_pairs(
                    eeg_trials, 
                    n_samples=n_samples
                )
            
            col1, col2 = st.columns(2)
            
            with col1:
                st.markdown("### LCC Distribution")
                
                # Histogram
                fig = go.Figure()
                fig.add_trace(go.Histogram(
                    x=coupling_results['lcc_values'],
                    nbinsx=30,
                    marker_color='#3498db',
                    opacity=0.7
                ))
                
                # Add threshold lines
                fig.add_vline(x=0.6, line_dash="dash", line_color="orange", 
                             annotation_text="0.6 threshold")
                fig.add_vline(x=0.85, line_dash="dash", line_color="red",
                             annotation_text="0.85 threshold")
                
                fig.update_layout(
                    title="Distribution of LCC Values",
                    xaxis_title="LCC (Correlation)",
                    yaxis_title="Frequency",
                    height=400
                )
                st.plotly_chart(fig, use_container_width=True)
                
                # Statistics
                stats = coupling_results['statistics']
                st.markdown(f"""
                **Statistics:**
                - Mean: {stats['mean']:.3f}
                - Std: {stats['std']:.3f}
                - Median: {stats['median']:.3f}
                - Range: [{stats['min']:.3f}, {stats['max']:.3f}]
                """)
            
            with col2:
                st.markdown("### Regime Distribution")
                
                regime_dist = coupling_results['regime_distribution']
                
                fig = go.Figure()
                fig.add_trace(go.Pie(
                    labels=['Below 0.6<br>(Weak)', '0.6 - 0.85<br>(Target)', 'Above 0.85<br>(Overcoupling)'],
                    values=[regime_dist['below_0.6'], regime_dist['in_0.6_0.85'], regime_dist['above_0.85']],
                    marker_colors=['#95a5a6', '#2ecc71', '#e74c3c'],
                    hole=0.3
                ))
                fig.update_layout(
                    title="LCC Regime Distribution",
                    height=400
                )
                st.plotly_chart(fig, use_container_width=True)
                
                st.markdown(f"""
                **Regimes:**
                - Weak (<0.6): {regime_dist['below_0.6']:.1f}%
                - Target (0.6-0.85): {regime_dist['in_0.6_0.85']:.1f}%
                - Overcoupling (>0.85): {regime_dist['above_0.85']:.1f}%
                """)
            
            # Threshold evidence
            st.markdown("### 🔍 Evidence for Threshold Clustering")
            
            threshold_ev = coupling_results['threshold_evidence']
            
            col1, col2 = st.columns(2)
            
            with col1:
                if threshold_ev['peak_near_0.6']:
                    st.success("✅ **Peak detected near 0.6 threshold**")
                    for peak in threshold_ev['peaks_0.6']:
                        st.write(f"- Peak at {peak['center']:.3f} ({peak['percentage']:.1f}%)")
                else:
                    st.warning("⚠️ No clear peak near 0.6")
            
            with col2:
                if threshold_ev['peak_near_0.85']:
                    st.success("✅ **Peak detected near 0.85 threshold**")
                    for peak in threshold_ev['peaks_0.85']:
                        st.write(f"- Peak at {peak['center']:.3f} ({peak['percentage']:.1f}%)")
                else:
                    st.warning("⚠️ No clear peak near 0.85")
            
            # All detected peaks
            with st.expander("📊 All Detected Peaks"):
                if coupling_results['peaks']:
                    for peak in coupling_results['peaks']:
                        st.write(f"Peak at {peak['center']:.3f}: {peak['count']} trials ({peak['percentage']:.1f}%)")
                else:
                    st.info("No significant peaks detected")
            
            # Test emotional similarity vs coupling
            st.markdown("### 🧪 Emotional Similarity vs Coupling")
            
            with st.spinner("Testing if similar emotions have higher coupling..."):
                similarity_results = coupling_analyzer.test_threshold_significance(
                    eeg_trials, labels, n_samples=100
                )
            
            if 'error' not in similarity_results:
                col1, col2 = st.columns(2)
                
                with col1:
                    st.metric(
                        "Similar Emotions LCC",
                        f"{similarity_results['similar_emotions']['mean_lcc']:.3f}",
                        delta=f"n={similarity_results['similar_emotions']['n']}"
                    )
                
                with col2:
                    st.metric(
                        "Different Emotions LCC",
                        f"{similarity_results['different_emotions']['mean_lcc']:.3f}",
                        delta=f"n={similarity_results['different_emotions']['n']}"
                    )
                
                stat_test = similarity_results['statistical_test']
                if stat_test['significant']:
                    st.success(f"✅ **Statistically significant difference** (p={stat_test['p_value']:.4f})")
                else:
                    st.info(f"No significant difference (p={stat_test['p_value']:.4f})")
                
                st.markdown(f"**Interpretation:** {similarity_results['interpretation']}")
            
            # Export coupling results
            st.markdown("---")
            col_exp1, col_exp2 = st.columns(2)
            with col_exp1:
                json_export = export_validation_results(coupling_results=coupling_results)
                st.download_button(
                    label="📥 Download Coupling Results (JSON)",
                    data=json_export,
                    file_name=f"coupling_analysis_{st.session_state.get('timestamp', 'latest')}.json",
                    mime="application/json",
                    help="Download coupling threshold analysis results"
                )
            with col_exp2:
                interpretation = interpret_validation_results(coupling_results=coupling_results)
                with st.expander("🎓 Coupling Interpretation", expanded=False):
                    st.markdown(interpretation)
    
    # MagAI Integration
    st.subheader("🤖 MagAI Analysis (Optional)")
    st.markdown("Submit your validation findings to MagAI for additional AI analysis")
    
    if st.checkbox("Enable MagAI Analysis"):
        magai_email = os.environ.get("MAGAI_EMAIL")
        magai_password = os.environ.get("MAGAI_PASSWORD")
        
        if magai_email and magai_password:
            from magai_integration import MagAIIntegration
            
            if st.button("🚀 Send Results to MagAI"):
                try:
                    magai = MagAIIntegration(magai_email, magai_password)
                    
                    # Prepare summary
                    if run_model_comparison and 'results' in locals():
                        summary = f"""
# Emotion Model Validation Results

## Model Performance Comparison

### Individual Models (Valence Correlation):
{chr(10).join([f"- {m}: {results[m]['valence']['correlation']:.3f}" for m in results if m != 'summary'])}

### Ensemble Performance:
- Best individual: {results['summary']['best_individual_valence_corr']:.3f}
- Ensemble (weighted): {results['summary']['ensemble_valence_corr']:.3f}
- Improvement: {results['summary']['ensemble_improvement']:+.3f}

**Finding:** {'Ensemble improves performance' if results['summary']['ensemble_better'] else 'Ensemble does not improve performance'}
"""
                    else:
                        summary = "Validation experiments not yet run"
                    
                    if run_coupling_analysis and 'coupling_results' in locals():
                        summary += f"""

## Coupling Threshold Analysis

### LCC Distribution:
- Mean: {coupling_results['statistics']['mean']:.3f}
- Std: {coupling_results['statistics']['std']:.3f}
- Median: {coupling_results['statistics']['median']:.3f}

### Regime Distribution:
- Below 0.6 (Weak): {coupling_results['regime_distribution']['below_0.6']:.1f}%
- 0.6-0.85 (Target): {coupling_results['regime_distribution']['in_0.6_0.85']:.1f}%
- Above 0.85 (Overcoupling): {coupling_results['regime_distribution']['above_0.85']:.1f}%

### Threshold Evidence:
- Peak near 0.6: {'Yes' if coupling_results['threshold_evidence']['peak_near_0.6'] else 'No'}
- Peak near 0.85: {'Yes' if coupling_results['threshold_evidence']['peak_near_0.85'] else 'No'}

**Question:** Does this data support the LCC threshold hypothesis (0.6-0.85 as optimal coupling range)?
"""
                    
                    with st.spinner("Sending to MagAI for analysis..."):
                        prompt = f"""
Analyze these emotion recognition model validation results:

{summary}

Please provide:
1. Interpretation of the model comparison results
2. Assessment of whether combining models (ensemble) provides value
3. Analysis of the coupling threshold evidence (do correlations cluster at 0.6 and 0.85?)
4. Scientific validity assessment of the TI-UOP framework based on this data
5. Recommendations for next steps
"""
                        
                        magai_response = magai.analyze_with_multiple_models(prompt, models=["gpt-4"])
                        response = magai_response.get("results", {}).get("gpt-4", "Analysis unavailable")
                        
                        st.success("✅ MagAI analysis complete")
                        st.markdown("### MagAI Analysis")
                        st.markdown(response)
                        
                except Exception as e:
                    st.error(f"Error communicating with MagAI: {e}")
        else:
            st.warning("⚠️ MagAI credentials not configured. Set MAGAI_EMAIL and MAGAI_PASSWORD environment variables.")


if __name__ == '__main__':
    st.set_page_config(
        page_title="Model Validation",
        page_icon="🔬",
        layout="wide"
    )
    
    st.title("🔬 Emotion Model Validation Dashboard")
    render_validation_dashboard()

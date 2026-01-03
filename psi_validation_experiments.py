"""
PSI Validation Experiments Tab
Automated experiments to build empirical evidence for PRF theory!
"""

import streamlit as st
import json
from datetime import datetime
from automated_psi_validation import AutomatedPSIValidator

def render():
    st.title("🧪 PSI Validation Experiments")
    st.markdown("**Automated experiments to test Probability as Resonance Field (PRF) theory**")
    
    st.markdown("""
    ### Scientific Method in Action
    
    Generate batches of predictions, track outcomes systematically, and calculate statistical significance.
    Build empirical evidence that PSI methods outperform random chance!
    
    **Experiment Types:**
    - **Numerology**: Test if Life Path resonance improves accuracy
    - **Weather**: Test if atmospheric conditions affect psi fields
    - **Combined**: Test multi-source PSI synthesis (core PRF theory!)
    - **Control**: Random predictions to establish baseline
    """)
    
    # Initialize validator
    if 'psi_validator' not in st.session_state:
        st.session_state['psi_validator'] = AutomatedPSIValidator()
    
    validator = st.session_state['psi_validator']
    
    st.markdown("---")
    
    # Create new experiment
    st.subheader("🆕 Create New Experiment")
    
    col1, col2 = st.columns(2)
    
    with col1:
        experiment_type = st.selectbox(
            "Experiment Type",
            options=["Numerology", "Weather", "Combined (Multi-Source PSI)", "Control (Random)"],
            help="What PSI method to test"
        )
    
    with col2:
        prediction_count = st.number_input(
            "Number of Predictions",
            min_value=10,
            max_value=100,
            value=20,
            step=5,
            help="More predictions = more statistical power!"
        )
    
    # User settings
    user_life_path = st.number_input("Your Life Path Number", min_value=1, max_value=33, value=6)
    location = st.text_input("Location (for weather PSI)", value="New York")
    
    if st.button("🔬 Create Experiment"):
        # Create appropriate experiment
        if "Numerology" in experiment_type and "Combined" not in experiment_type:
            exp = validator.create_numerology_experiment(
                user_life_path=user_life_path,
                prediction_count=prediction_count
            )
            st.success(f"✅ Created numerology experiment: {exp.experiment_id}")
        
        elif "Weather" in experiment_type:
            exp = validator.create_weather_psi_experiment(
                location=location,
                prediction_count=prediction_count
            )
            st.success(f"✅ Created weather PSI experiment: {exp.experiment_id}")
        
        elif "Combined" in experiment_type:
            exp = validator.create_combined_psi_experiment(
                user_life_path=user_life_path,
                location=location,
                prediction_count=prediction_count
            )
            st.success(f"✅ Created MULTI-SOURCE PSI experiment: {exp.experiment_id}")
            st.info("This tests the core of PRF theory - resonance from multiple sources!")
        
        elif "Control" in experiment_type:
            exp = validator.create_control_experiment(
                prediction_count=prediction_count
            )
            st.success(f"✅ Created control experiment: {exp.experiment_id}")
        
        # Save experiments
        validator.save_experiments()
    
    st.markdown("---")
    
    # Display existing experiments
    st.subheader("📊 Active Experiments")
    
    if validator.experiments:
        st.markdown(f"**Total Experiments: {len(validator.experiments)}**")
        
        for exp in validator.experiments:
            with st.expander(f"{exp.experiment_type.upper()} - {exp.experiment_id}", expanded=False):
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Predictions", exp.prediction_count)
                
                with col2:
                    st.metric("Target Accuracy", f"{exp.target_accuracy:.0%}")
                
                with col3:
                    st.metric("Baseline", f"{exp.baseline_accuracy:.0%}")
                
                st.markdown(f"**Status:** {exp.status}")
                st.markdown(f"**Created:** {exp.created_at}")
                
                # Show prediction details
                st.markdown("**Predictions:**")
                st.json(exp.predictions[:5])  # Show first 5
                
                # Results if available
                if exp.results:
                    st.markdown("**Results:**")
                    st.json(exp.results)
                
                # Generate report button
                if st.button(f"📄 Generate Report", key=f"report_{exp.experiment_id}"):
                    report = validator.generate_experiment_report(exp.experiment_id)
                    st.markdown(report)
    else:
        st.info("No experiments yet. Create one above!")
    
    st.markdown("---")
    
    # Statistical significance calculator
    st.subheader("📈 Statistical Significance Calculator")
    
    st.markdown("**Calculate if your PSI results beat random chance:**")
    
    col1, col2 = st.columns(2)
    
    with col1:
        correct = st.number_input("Correct Predictions", min_value=0, max_value=1000, value=14)
    
    with col2:
        total = st.number_input("Total Predictions", min_value=1, max_value=1000, value=20)
    
    baseline = st.slider("Baseline Probability (random chance)", 0.0, 1.0, 0.5, 0.01)
    
    if st.button("🔢 Calculate Significance"):
        stats = validator.calculate_statistical_significance(
            correct_predictions=correct,
            total_predictions=total,
            baseline_probability=baseline
        )
        
        st.markdown("### Results:")
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            st.metric("Observed Accuracy", f"{stats['observed_accuracy']:.1%}")
        
        with col2:
            st.metric("p-value", f"{stats['p_value']:.4f}")
        
        with col3:
            st.metric("Effect Size (Cohen's h)", f"{stats['cohens_h']:.3f}")
        
        # Significance
        st.markdown(f"**{stats['significance']}**")
        
        # Interpretation
        st.info(stats['interpretation'])
        
        # Visual
        import plotly.graph_objects as go
        
        fig = go.Figure()
        
        fig.add_trace(go.Bar(
            x=['Baseline', 'Observed'],
            y=[stats['baseline_accuracy'], stats['observed_accuracy']],
            text=[f"{stats['baseline_accuracy']:.1%}", f"{stats['observed_accuracy']:.1%}"],
            textposition='auto',
            marker_color=['lightgray', 'green' if stats['p_value'] < 0.05 else 'orange']
        ))
        
        fig.update_layout(
            title="Accuracy Comparison",
            yaxis_title="Accuracy",
            yaxis_tickformat='.0%'
        )
        
        st.plotly_chart(fig, use_container_width=True)
    
    st.markdown("---")
    
    # Quick guide
    with st.expander("📚 How to Run PSI Experiments"):
        st.markdown("""
        ### Step-by-Step Guide:
        
        1. **Create Experiment**
           - Choose experiment type (numerology, weather, combined, control)
           - Set number of predictions (20+ recommended)
           - Enter your Life Path number and location
        
        2. **Make Predictions**
           - Use the prediction dates/prompts generated
           - Record your predictions in Psi Tracker
           - Track outcomes as events resolve
        
        3. **Analyze Results**
           - Enter correct/total predictions in calculator
           - Check p-value (< 0.05 = statistically significant)
           - Generate experiment report
        
        4. **Build Evidence**
           - Run multiple experiments (replication is key!)
           - Compare control vs PSI methods
           - Document findings for PRF theory validation
        
        ### Statistical Significance Guide:
        - **p < 0.05**: Significant - likely real effect!
        - **p < 0.01**: Very significant - strong evidence
        - **p < 0.001**: Highly significant - compelling evidence
        - **p >= 0.05**: Not significant - need more data or different approach
        
        ### Effect Size (Cohen's h):
        - **0.2**: Small effect
        - **0.5**: Medium effect
        - **0.8+**: Large effect
        """)

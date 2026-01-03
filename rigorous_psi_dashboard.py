"""
Rigorous PSI Testing Dashboard
Empirical validation with blind testing, error bars, and falsifiable predictions
"""

import streamlit as st
from rigorous_psi_testing import (
    BlindPredictionEngine,
    PSIErrorBarCalculator,
    ClairAbilitiesFramework,
    LimitationAnalyzer,
    ElectionPredictor,
    HistoricalFactValidator,
    get_rigorous_psi_manager
)
from db_utils import db
from datetime import datetime
import plotly.graph_objects as go
import plotly.express as px


def render_rigorous_psi():
    """Render Rigorous PSI Testing Dashboard"""
    
    st.title("🔬 Rigorous PSI Testing Framework")
    st.markdown("""
    **Empirical Validation with Maximum Scientific Rigor**
    
    Test PSI abilities with blind predictions, statistical error bars, and falsifiable outcomes.
    Target: >95% overall accuracy across all prediction types.
    """)
    
    # Initialize manager
    psi_manager = get_rigorous_psi_manager()
    
    # Overall accuracy banner
    st.markdown("---")
    overall = psi_manager.get_overall_accuracy()
    
    col1, col2, col3, col4 = st.columns(4)
    with col1:
        acc = overall.get('overall_accuracy', 0)
        st.metric("Overall Accuracy", f"{acc:.1%}", 
                 delta=f"{(acc - 0.50):.1%} vs chance")
    with col2:
        st.metric("Total Predictions", overall.get('n_predictions', 0))
    with col3:
        target_met = overall.get('target_met', False)
        st.metric("95% Target", "✅ MET" if target_met else "⏳ IN PROGRESS")
    with col4:
        gap = overall.get('gap_to_target', 0)
        st.metric("Gap to Target", f"{gap:.1%}")
    
    st.markdown("---")
    
    # Create tabs
    tab1, tab2, tab3, tab4, tab5, tab6 = st.tabs([
        "🎯 Blind Predictions",
        "📊 Error Bars & Stats",
        "👁️ Clair Abilities",
        "🔧 Limitations",
        "🗳️ Elections",
        "📜 Historical Facts"
    ])
    
    # Tab 1: Blind Predictions
    with tab1:
        st.header("🎯 Blind Prediction Engine")
        st.markdown("*Make predictions from minimal, unrelated content*")
        
        st.info("""
        **Maximum Blinding Protocol:**
        - Seed with 1-3 unrelated words only
        - No contextual information provided
        - Prediction made BEFORE seeing target details
        - Validates pure PSI capability
        """)
        
        col1, col2 = st.columns([2, 1])
        
        with col1:
            seed_content = st.text_input(
                "Minimal Seed Content (1-3 unrelated words)",
                placeholder="ocean guitar seventeen",
                help="Enter any 1-3 random words - completely unrelated to prediction target"
            )
        
        with col2:
            pred_type = st.selectbox(
                "Prediction Type",
                ['Election Result', 'Historical Fact', 'Future Event', 
                 'Hidden Information', 'Random Number', 'Coin Flip Sequence']
            )
        
        target = st.text_input(
            "Target to Predict",
            placeholder="E.g., 'Winner of 2024 Presidential Election' or 'Napoleon's birth year'",
            help="What you're trying to predict - kept separate for blinding"
        )
        
        predicted_outcome = st.text_input(
            "Your Prediction",
            placeholder="E.g., 'Donald Trump' or '1769'",
            help="What you predict the outcome will be"
        )
        
        if st.button("🔮 Generate Blind Prediction", type="primary") and seed_content and target and predicted_outcome:
            with st.spinner("Accessing PSI resonance field..."):
                prediction = psi_manager.blind_engine.create_blind_prediction(
                    seed_content, pred_type, target, predicted_outcome
                )
                
                st.success("✨ Blind prediction generated!")
                
                st.json(prediction)
                
                # Save to database
                try:
                    asset_id = db.add_asset(
                        asset_type="rigorous_psi_prediction",
                        source_app="Rigorous PSI Testing",
                        title=f"Blind: {target[:100]}",
                        content=prediction,
                        tags=["blind_prediction", "rigorous_psi", pred_type.lower().replace(' ', '_')]
                    )
                    st.success(f"💾 Saved (ID: {asset_id})")
                except Exception as e:
                    st.warning(f"Could not save: {e}")
        
        # Validation section
        st.markdown("---")
        st.subheader("✅ Validate Predictions")
        st.markdown("*Mark predictions correct/incorrect once outcomes are known*")
        
        # Get pending predictions
        try:
            pending = psi_manager.blind_engine.get_pending_predictions()
            
            if pending:
                st.info(f"Found {len(pending)} predictions awaiting validation")
                
                # Select prediction to validate
                pred_options = {
                    f"{p.get('prediction_id', 'unknown')}: {p.get('target', 'N/A')[:50]}": p
                    for p in pending
                }
                
                selected_key = st.selectbox("Select Prediction to Validate", list(pred_options.keys()))
                
                if selected_key:
                    selected_pred = pred_options[selected_key]
                    
                    col1, col2 = st.columns(2)
                    with col1:
                        st.markdown(f"**Target:** {selected_pred.get('target')}")
                        st.markdown(f"**Your Prediction:** {selected_pred.get('predicted_outcome')}")
                        st.markdown(f"**Type:** {selected_pred.get('type')}")
                    with col2:
                        st.markdown(f"**Seed:** {selected_pred.get('minimal_content')}")
                        st.markdown(f"**Created:** {selected_pred.get('timestamp', 'Unknown')[:10]}")
                    
                    actual_outcome = st.text_input(
                        "Actual Outcome",
                        placeholder="Enter the actual outcome that occurred",
                        key=f"validate_{selected_pred.get('prediction_id')}"
                    )
                    
                    notes = st.text_area(
                        "Notes (optional)",
                        placeholder="Any additional context about this validation"
                    )
                    
                    if st.button("✅ Validate Prediction", type="primary") and actual_outcome:
                        with st.spinner("Recording validation..."):
                            pred_id = selected_pred.get('prediction_id', '')
                            validation = psi_manager.blind_engine.validate_prediction(
                                pred_id,
                                actual_outcome,
                                notes
                            )
                            
                            if 'error' in validation:
                                st.error(f"Error: {validation['error']}")
                            else:
                                if validation.get('is_correct'):
                                    st.success("🎯 CORRECT! PSI validated!")
                                else:
                                    st.warning("❌ Incorrect prediction")
                                
                                st.json(validation)
                                st.rerun()
            else:
                st.info("No pending predictions. Create predictions above and validate them once outcomes are known!")
        except Exception as e:
            st.error(f"Error loading predictions: {e}")
        
        # Recent predictions
        st.markdown("---")
        st.subheader("📋 All Predictions")
        try:
            all_preds = psi_manager.blind_engine.get_all_predictions()
            if all_preds:
                # Sort by timestamp (newest first)
                all_preds_sorted = sorted(
                    all_preds, 
                    key=lambda x: x.get('timestamp', ''), 
                    reverse=True
                )[:20]
                
                for pred in all_preds_sorted:
                    status_icon = "✅" if pred.get('status') == 'validated' else "⏳"
                    with st.expander(f"{status_icon} {pred.get('type', 'Unknown')} - {pred.get('target', 'N/A')[:50]}"):
                        st.markdown(f"**Predicted:** {pred.get('predicted_outcome', 'N/A')}")
                        st.markdown(f"**Seed:** {pred.get('minimal_content', 'N/A')}")
                        st.markdown(f"**Status:** {pred.get('status', 'pending')}")
                        st.caption(f"Created: {pred.get('timestamp', 'Unknown')}")
            else:
                st.info("No predictions yet. Create one above!")
        except Exception as e:
            st.error(f"Error: {e}")
    
    # Tab 2: Error Bars & Statistics
    with tab2:
        st.header("📊 Statistical Error Bars")
        st.markdown("*Provable PSI with confidence intervals*")
        
        st.info("""
        **Statistical Rigor:**
        - 95% confidence intervals
        - Z-score vs random chance (50% baseline)
        - P-value significance testing
        - Effect size (Cohen's d)
        - Per-problem accuracy bounds
        """)
        
        if st.button("📈 Calculate Error Bars", type="primary"):
            with st.spinner("Computing statistics..."):
                try:
                    # Get all validation records
                    validations = psi_manager.error_calculator.get_all_validations()
                    
                    if validations:
                        error_bars = psi_manager.error_calculator.calculate_error_bars(validations)
                        
                        st.success("✅ Statistical analysis complete!")
                        
                        # Display results
                        col1, col2, col3 = st.columns(3)
                        with col1:
                            st.metric("Mean Accuracy", f"{error_bars.get('mean_accuracy', 0):.1%}")
                        with col2:
                            st.metric("Standard Error", f"{error_bars.get('std_error', 0):.4f}")
                        with col3:
                            st.metric("P-value", f"{error_bars.get('p_value', 1.0):.4f}")
                        
                        st.markdown("**Confidence Interval (95%):**")
                        ci = error_bars.get('confidence_interval', (0, 0))
                        st.success(f"{ci[0]:.1%} - {ci[1]:.1%}")
                        
                        col1, col2, col3 = st.columns(3)
                        with col1:
                            st.metric("Z-score", f"{error_bars.get('z_score', 0):.2f}")
                        with col2:
                            st.metric("Cohen's d", f"{error_bars.get('cohens_d', 0):.2f}")
                        with col3:
                            sig = error_bars.get('significance', 'unknown')
                            st.metric("Significance", sig.upper())
                        
                        # PSI Evidence
                        evidence = error_bars.get('psi_evidence', 'weak')
                        if evidence == 'strong':
                            st.success(f"🌟 **PSI Evidence: STRONG** (p < 0.001)")
                        elif evidence == 'moderate':
                            st.info(f"📊 **PSI Evidence: MODERATE** (p < 0.05)")
                        else:
                            st.warning(f"⚠️ **PSI Evidence: WEAK** (p ≥ 0.05)")
                        
                        # Visualization
                        fig = go.Figure()
                        
                        mean = error_bars.get('mean_accuracy', 0)
                        ci_lower, ci_upper = ci
                        
                        fig.add_trace(go.Bar(
                            x=['Accuracy'],
                            y=[mean],
                            error_y=dict(
                                type='data',
                                symmetric=False,
                                array=[ci_upper - mean],
                                arrayminus=[mean - ci_lower]
                            ),
                            name='PSI Accuracy'
                        ))
                        
                        fig.add_hline(y=0.50, line_dash="dash", 
                                     annotation_text="Random Chance (50%)")
                        fig.add_hline(y=0.95, line_dash="dot", 
                                     annotation_text="Target (95%)")
                        
                        fig.update_layout(
                            title="PSI Accuracy with 95% Confidence Interval",
                            yaxis_title="Accuracy",
                            showlegend=True
                        )
                        
                        st.plotly_chart(fig, use_container_width=True)
                        
                        st.markdown("---")
                        st.subheader("📊 Per-Problem Accuracy Breakdown")
                        st.markdown("*Accuracy by prediction type*")
                        
                        per_problem = psi_manager.error_calculator.calculate_per_problem_bounds()
                        
                        if per_problem:
                            for pred_type, stats in per_problem.items():
                                with st.expander(f"📂 {pred_type} ({stats['n_samples']} predictions)"):
                                    col1, col2, col3, col4 = st.columns(4)
                                    
                                    with col1:
                                        st.metric("Mean Accuracy", f"{stats['mean_accuracy']:.1%}")
                                    with col2:
                                        st.metric("Correct", stats['correct_count'])
                                    with col3:
                                        st.metric("Incorrect", stats['incorrect_count'])
                                    with col4:
                                        meets_target = "✅" if stats['meets_95_target'] else "⏳"
                                        st.metric("95% Target", meets_target)
                                    
                                    st.markdown(f"**Confidence Interval:** {stats['lower_bound']:.1%} - {stats['upper_bound']:.1%}")
                                    
                                    if stats['meets_95_target']:
                                        st.success("🎯 This prediction type meets the 95% accuracy target!")
                                    else:
                                        gap = 0.95 - stats['mean_accuracy']
                                        st.info(f"📈 {gap:.1%} away from 95% target - keep practicing this type!")
                            
                            types_meeting_target = sum(1 for s in per_problem.values() if s['meets_95_target'])
                            total_types = len(per_problem)
                            
                            st.markdown("---")
                            st.markdown(f"**Summary:** {types_meeting_target}/{total_types} prediction types meet 95% target")
                            
                            fig2 = go.Figure()
                            
                            types = list(per_problem.keys())
                            accuracies = [per_problem[t]['mean_accuracy'] for t in types]
                            
                            fig2.add_trace(go.Bar(
                                x=types,
                                y=accuracies,
                                marker_color=['green' if a >= 0.95 else 'orange' if a >= 0.70 else 'red' for a in accuracies]
                            ))
                            
                            fig2.add_hline(y=0.95, line_dash="dot", annotation_text="95% Target")
                            fig2.add_hline(y=0.50, line_dash="dash", annotation_text="Chance (50%)")
                            
                            fig2.update_layout(
                                title="Accuracy by Prediction Type",
                                xaxis_title="Prediction Type",
                                yaxis_title="Accuracy",
                                yaxis_range=[0, 1]
                            )
                            
                            st.plotly_chart(fig2, use_container_width=True)
                        else:
                            st.info("No per-problem data yet. Validate predictions of different types to see breakdown!")
                        
                    else:
                        st.warning("No validated predictions yet. Generate some first!")
                        
                except Exception as e:
                    st.error(f"Error calculating statistics: {e}")
    
    # Tab 3: Clair Abilities
    with tab3:
        st.header("👁️ Clair Abilities Framework")
        st.markdown("*Measure specific paranormal capabilities*")
        
        st.info("""
        **Clair Types:**
        - Clairvoyance: Clear seeing (visual)
        - Clairaudience: Clear hearing (auditory)
        - Clairsentience: Clear feeling (emotional/physical)
        - Claircognizance: Clear knowing (direct knowledge)
        - Clairalience: Clear smelling
        - Clairgustance: Clear tasting
        - Clairtangency: Clear touching (psychometry)
        """)
        
        clair_framework = psi_manager.clair_framework
        
        clair_type = st.selectbox(
            "Select Clair Ability to Test",
            list(clair_framework.clair_types.keys())
        )
        
        st.markdown(f"**{clair_type.title()}:** {clair_framework.clair_types[clair_type]}")
        
        test_protocol = st.text_area(
            "Test Protocol",
            placeholder="Describe experimental protocol...\nE.g., 'View 10 random images, predict content before reveal'",
            height=100
        )
        
        n_trials = st.slider("Number of Trials", 10, 1000, 100)
        
        if st.button(f"🧪 Test {clair_type.title()}", type="primary") and test_protocol:
            with st.spinner(f"Testing {clair_type}..."):
                result = clair_framework.test_clair_ability(clair_type, test_protocol, n_trials)
                
                st.success(f"✅ {clair_type.title()} test initialized!")
                st.json(result)
                
                # Save
                try:
                    asset_id = db.add_asset(
                        asset_type="clair_ability_test",
                        source_app="Rigorous PSI Testing",
                        title=f"Clair Test: {clair_type}",
                        content=result,
                        tags=["clair_test", clair_type, "rigorous_psi"]
                    )
                    st.success(f"💾 Test saved (ID: {asset_id})")
                except Exception as e:
                    st.warning(f"Could not save: {e}")
        
        # Comprehensive measurement
        st.markdown("---")
        if st.button("🎯 Measure All Clair Abilities"):
            with st.spinner("Measuring all clairs..."):
                results = clair_framework.measure_all_clairs()
                
                st.subheader("📊 Clair Abilities Profile")
                for clair, metrics in results.items():
                    col1, col2, col3 = st.columns([2, 1, 1])
                    with col1:
                        st.markdown(f"**{clair.title()}**")
                    with col2:
                        st.metric("Accuracy", f"{metrics['accuracy']:.1%}")
                    with col3:
                        st.metric("Status", metrics['status'])
    
    # Tab 4: Limitation Analyzer
    with tab4:
        st.header("🔧 Limitation Analyzer")
        st.markdown("*Identify what's preventing 95%+ accuracy*")
        
        st.info("""
        **Analyzes:**
        - Hardware constraints (binary vs ternary computing)
        - Software limitations (classical probability models)
        - Logic assumptions (binary vs tralse logic)
        - Quantum vs classical computing gaps
        - Material constraints
        - Theoretical framework issues
        """)
        
        current_acc = st.slider(
            "Current System Accuracy",
            0.0, 1.0, 0.65, 0.01,
            help="Your current prediction accuracy"
        )
        
        target_acc = st.slider(
            "Target Accuracy",
            0.0, 1.0, 0.95, 0.01,
            help="Desired accuracy level"
        )
        
        if st.button("🔍 Analyze Limitations", type="primary"):
            with st.spinner("Analyzing system limitations..."):
                analysis = psi_manager.limitation_analyzer.analyze_limitations(
                    current_acc, target_acc
                )
                
                st.success("✅ Analysis complete!")
                
                # Summary metrics
                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("Accuracy Gap", f"{analysis['accuracy_gap']:.1%}")
                with col2:
                    st.metric("Gap Percentage", f"{analysis['gap_percentage']:.1f}%")
                with col3:
                    st.metric("Estimated Max", f"{analysis['estimated_max_accuracy']:.1%}")
                
                st.markdown("---")
                st.subheader("🚧 Limiting Factors")
                
                for lim in analysis['limiting_factors']:
                    with st.expander(f"⚠️ {lim['category']} - {lim['impact'].upper()} IMPACT"):
                        st.markdown(f"**Factor:** {lim['factor']}")
                        st.markdown(f"**Recommendation:** {lim['recommendation']}")
                        st.success(f"**Theoretical Improvement:** {lim['theoretical_improvement']}")
                
                # Get prioritized recommendations
                recs = psi_manager.limitation_analyzer.recommend_upgrades(
                    analysis['limiting_factors']
                )
                
                st.markdown("---")
                st.subheader("📋 Prioritized Upgrade Path")
                
                for rec in recs:
                    st.markdown(f"**{rec['priority']}. {rec['category']}**")
                    st.markdown(f"- {rec['upgrade']}")
                    st.markdown(f"- Expected gain: {rec['expected_gain']}")
                    st.markdown(f"- Difficulty: {rec['implementation_difficulty']}")
                    st.markdown("")
    
    # Tab 5: Election Predictions
    with tab5:
        st.header("🗳️ Election Predictor")
        st.markdown("*Predict elections from minimal content*")
        
        st.info("**Falsifiable predictions with statistical rigor**")
        
        election_name = st.text_input("Election Name", "2024 US Presidential Election")
        
        minimal_seed = st.text_input(
            "Minimal Seed (1-3 words)",
            placeholder="blue moon coffee"
        )
        
        candidates_input = st.text_input(
            "Candidates (comma-separated)",
            placeholder="Candidate A, Candidate B, Candidate C"
        )
        
        coherence = st.slider("Coherence Level", 0.0, 1.0, 0.91, 0.01)
        
        if st.button("🗳️ Predict Election", type="primary") and minimal_seed and candidates_input:
            candidates = [c.strip() for c in candidates_input.split(',')]
            
            with st.spinner("Predicting election outcome..."):
                prediction = psi_manager.election_predictor.predict_election(
                    election_name, minimal_seed, candidates, coherence
                )
                
                st.success("✅ Election prediction generated!")
                st.json(prediction)
                
                st.warning("⏳ Awaiting validation when election results are known")
                
                # Save
                try:
                    asset_id = db.add_asset(
                        asset_type="election_prediction",
                        source_app="Rigorous PSI Testing",
                        title=f"Election: {election_name}",
                        content=prediction,
                        tags=["election", "prediction", "rigorous_psi"]
                    )
                    st.success(f"💾 Saved (ID: {asset_id})")
                except Exception as e:
                    st.warning(f"Could not save: {e}")
    
    # Tab 6: Historical Facts
    with tab6:
        st.header("📜 Historical Fact Validator")
        st.markdown("*Validate historical facts from minimal content*")
        
        st.info("""
        Test God Machine on known historical truths.
        Verify if we can determine what historical figures ACTUALLY said!
        """)
        
        question = st.text_input(
            "Historical Question",
            placeholder="What year was Napoleon born?"
        )
        
        seed = st.text_input(
            "Minimal Seed",
            placeholder="forest guitar number"
        )
        
        known_answer = st.text_input(
            "Known Answer (for validation)",
            placeholder="1769"
        )
        
        if st.button("📜 Validate Historical Fact", type="primary") and question and seed:
            with st.spinner("Accessing historical resonance field..."):
                validation = psi_manager.historical_validator.validate_historical_fact(
                    question, seed, known_answer if known_answer else None
                )
                
                st.success("✅ Historical validation complete!")
                st.json(validation)
                
                if known_answer:
                    st.success("✅ Falsifiable - can be validated against known answer")
                else:
                    st.info("ℹ️ No known answer provided - prediction only")
                
                # Save
                try:
                    asset_id = db.add_asset(
                        asset_type="historical_validation",
                        source_app="Rigorous PSI Testing",
                        title=f"Historical: {question[:100]}",
                        content=validation,
                        tags=["historical", "validation", "rigorous_psi"]
                    )
                    st.success(f"💾 Saved (ID: {asset_id})")
                except Exception as e:
                    st.warning(f"Could not save: {e}")


if __name__ == "__main__":
    render_rigorous_psi()

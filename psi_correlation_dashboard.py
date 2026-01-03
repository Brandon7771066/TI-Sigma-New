"""
PSI Correlation Dashboard
Multi-dimensional PSI correlation analysis with LCC discovery
Personalized insights for Brandon

Tab 17 in main app
"""

import streamlit as st
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import json
from psi_correlation_intelligence import PSICorrelationIntelligence, PSIObservation

def render_psi_correlation_dashboard():
    """Main dashboard for PSI correlation intelligence"""
    
    st.title("🔮 PSI Correlation Intelligence")
    st.markdown("""
    **Discover non-obvious PSI method correlations using Lowest Common Category (LCC) analysis**
    
    This system finds which PSI methods truly correlate with YOUR accuracy, including unexpected combinations!
    """)
    
    # Initialize system
    psi_intel = PSICorrelationIntelligence()
    
    # Create tabs
    tab1, tab2, tab3, tab4, tab5 = st.tabs([
        "📊 Correlation Matrix",
        "🕸️ LCC Network",
        "👤 Brandon's Profile",
        "📈 Timeline Analysis",
        "➕ Add Observation"
    ])
    
    with tab1:
        render_correlation_matrix(psi_intel)
    
    with tab2:
        render_lcc_network(psi_intel)
    
    with tab3:
        render_brandon_profile(psi_intel)
    
    with tab4:
        render_timeline_analysis(psi_intel)
    
    with tab5:
        render_add_observation(psi_intel)

def render_correlation_matrix(psi_intel: PSICorrelationIntelligence):
    """Tab 1: Correlation heatmap"""
    st.header("Multi-Dimensional Correlation Matrix")
    
    st.markdown("""
    Shows Spearman correlations between all PSI modalities.
    
    **Look for:**
    - High correlations between DIFFERENT modalities (these are LCC candidates!)
    - Red = positive correlation, Blue = negative correlation
    """)
    
    # Load data
    days_back = st.slider("Days to analyze", 7, 180, 90, key="corr_days")
    df = psi_intel.get_observations_df(days_back=days_back)
    
    if len(df) < 10:
        st.warning(f"Only {len(df)} observations found. Need at least 10 for correlation analysis.")
        st.info("💡 Add observations in the 'Add Observation' tab to build your dataset!")
        return
    
    st.info(f"📊 Analyzing {len(df)} predictions from last {days_back} days")
    
    # Correlation method
    method = st.selectbox(
        "Correlation method",
        ["spearman", "pearson", "mutual_info"],
        help="Spearman for monotonic relationships, Pearson for linear, Mutual Info for any dependency"
    )
    
    # Compute and display
    with st.spinner("Computing correlations..."):
        try:
            fig = psi_intel.visualize_correlation_heatmap(df)
            st.plotly_chart(fig, use_container_width=True)
            
            # Download correlation matrix
            corr_matrix = psi_intel.compute_correlation_matrix(df, method=method)
            st.download_button(
                "📥 Download Correlation Matrix (CSV)",
                corr_matrix.to_csv(),
                file_name=f"psi_correlation_matrix_{datetime.now().strftime('%Y%m%d')}.csv",
                mime="text/csv"
            )
            
        except Exception as e:
            st.error(f"Correlation computation failed: {e}")

def render_lcc_network(psi_intel: PSICorrelationIntelligence):
    """Tab 2: LCC cluster discovery"""
    st.header("Lowest Common Category (LCC) Discovery")
    
    st.markdown("""
    **Find hidden mechanisms that connect distant PSI methods!**
    
    LCC identifies the "common category" between seemingly unrelated methods.
    
    **Example:** Heart coherence (biometric) + Moon phase (cosmic) both involve **periodic signals** → LCC = "Resonance Coupling"
    """)
    
    # Load data
    days_back = st.slider("Days to analyze", 7, 180, 90, key="lcc_days")
    df = psi_intel.get_observations_df(days_back=days_back)
    
    if len(df) < 30:
        st.warning(f"Only {len(df)} observations. Need at least 30 for reliable LCC discovery.")
        return
    
    st.info(f"🔍 Discovering LCC clusters from {len(df)} predictions")
    
    # Find clusters
    with st.spinner("Discovering LCC clusters..."):
        try:
            clusters = psi_intel.find_lcc_clusters(df, threshold=0.3)
            
            if not clusters:
                st.warning("No significant LCC clusters found yet. Make more predictions!")
                return
            
            # Display network graph
            fig = psi_intel.visualize_lcc_network(clusters)
            st.plotly_chart(fig, use_container_width=True)
            
            # Display cluster details
            st.subheader("📋 Discovered LCC Clusters")
            
            for i, cluster in enumerate(clusters, 1):
                with st.expander(f"🔮 {cluster['name']} (r = {cluster['avg_correlation']:.3f})"):
                    st.markdown(f"**Mechanism:** {cluster['mechanism']}")
                    st.markdown(f"**LCC:** {cluster['lcc']}")
                    st.markdown(f"**Features:** {', '.join([f.replace('_', ' ').title() for f in cluster['features']])}")
                    st.markdown(f"**Average Correlation with Outcome:** {cluster['avg_correlation']:.3f}")
                    
                    # Actionable insight
                    st.success(f"💡 **Insight:** When these {len(cluster['features'])} factors align, expect synergistic PSI boost!")
            
        except Exception as e:
            st.error(f"LCC discovery failed: {e}")

def render_brandon_profile(psi_intel: PSICorrelationIntelligence):
    """Tab 3: Personalized insights for Brandon"""
    st.header("👤 Brandon's Personalized PSI Profile")
    
    st.markdown("""
    **Discover YOUR unique PSI signature!**
    
    - Life Path: **6** (service, harmony, responsibility)
    - Birth Day: **7** (spiritual seeker, analyst)
    - Birthdate: 6/16/2000
    
    This analyzes which PSI methods work best for YOU specifically.
    """)
    
    # Load data
    days_back = st.slider("Days to analyze", 30, 180, 90, key="brandon_days")
    df = psi_intel.get_observations_df(days_back=days_back)
    
    if len(df) < 30:
        st.warning(f"Only {len(df)} observations. Need at least 30 for personalization.")
        st.info(f"📈 Progress: {len(df)}/30 predictions logged")
        return
    
    st.info(f"🧠 Personalizing from {len(df)} predictions")
    
    # Personalize
    with st.spinner("Analyzing your unique PSI signature..."):
        try:
            personalization = psi_intel.personalize_for_brandon(df)
            
            if personalization['status'] != 'success':
                st.error(f"Personalization failed: {personalization.get('message', 'Unknown error')}")
                return
            
            # Display metrics
            col1, col2, col3 = st.columns(3)
            
            with col1:
                st.metric(
                    "Baseline Accuracy",
                    f"{personalization['baseline_accuracy']*100:.1f}%",
                    help="Your overall prediction accuracy"
                )
            
            with col2:
                st.metric(
                    "Model R²",
                    f"{personalization['model_r2']*100:.1f}%",
                    help="How much PSI features explain your accuracy variance"
                )
            
            with col3:
                st.metric(
                    "Predictions",
                    personalization['sample_size'],
                    help="Total predictions analyzed"
                )
            
            # Top features
            st.subheader("🎯 Your Top PSI Methods")
            
            top_features = personalization['top_features']
            if top_features:
                feature_df = pd.DataFrame([
                    {'Method': k.replace('_', ' ').title(), 'Importance': v}
                    for k, v in top_features.items()
                ]).sort_values('Importance', ascending=False)
                
                st.dataframe(feature_df, use_container_width=True, hide_index=True)
                
                # Bar chart
                import plotly.express as px
                fig = px.bar(
                    feature_df,
                    x='Importance',
                    y='Method',
                    orientation='h',
                    title="Feature Importance for Brandon's Predictions"
                )
                st.plotly_chart(fig, use_container_width=True)
            
            # Sacred number insights
            st.subheader("✨ Sacred Number Analysis")
            
            sacred = personalization.get('sacred_number_insights', {})
            
            if 'life_path_6_boost' in sacred:
                lp6 = sacred['life_path_6_boost']
                col1, col2 = st.columns(2)
                
                with col1:
                    st.metric(
                        "Life Path 6 Dates",
                        f"{lp6['accuracy']*100:.1f}%",
                        delta=f"{lp6['lift']*100:+.1f}% vs baseline",
                        help=f"Accuracy when event date numerology = 6 (n={lp6['sample_size']})"
                    )
                
                if lp6['lift'] > 0.1:
                    st.success(f"🔥 **Strong Life Path Resonance!** You're {lp6['lift']*100:.1f}% more accurate on Life Path 6 dates!")
                elif lp6['lift'] < -0.1:
                    st.warning("⚠️ Life Path 6 dates may be challenging for you.")
            
            if 'birth_day_7_effect' in sacred:
                bd7 = sacred['birth_day_7_effect']
                with col2:
                    st.metric(
                        "Sundays (Day 7)",
                        f"{bd7['accuracy']*100:.1f}%",
                        delta=f"{bd7['lift']*100:+.1f}% vs baseline",
                        help=f"Accuracy on Sundays (Birth Day 7) (n={bd7['sample_size']})"
                    )
            
            # Optimal windows
            st.subheader("⏰ Your Optimal Prediction Windows")
            
            windows = personalization.get('optimal_windows', [])
            if windows:
                for window in sorted(windows, key=lambda w: w['boost'], reverse=True):
                    boost_pct = window['boost'] * 100
                    color = "green" if boost_pct > 10 else "normal"
                    
                    st.markdown(f"""
                    **{window['condition']}**  
                    → Accuracy: {window['accuracy']*100:.1f}% ({boost_pct:+.1f}% boost)  
                    → Sample size: {window['sample_size']} predictions
                    """)
                    
                    if boost_pct > 15:
                        st.success(f"🎯 **PRIME WINDOW!** This is your sweet spot!")
            else:
                st.info("No clear optimal windows identified yet. More data needed!")
            
            # Recommendations
            st.subheader("💡 Personalized Recommendations")
            
            recommendations = psi_intel.generate_recommendations(personalization)
            for rec in recommendations:
                st.markdown(rec)
            
        except Exception as e:
            st.error(f"Personalization failed: {e}")
            import traceback
            st.code(traceback.format_exc())

def render_timeline_analysis(psi_intel: PSICorrelationIntelligence):
    """Tab 4: Timeline overlay"""
    st.header("📈 Timeline Analysis")
    
    st.markdown("""
    Shows how your top PSI features fluctuate over time alongside prediction outcomes.
    
    **Look for:** Visual patterns where features align with successful predictions!
    """)
    
    # Load data
    days_back = st.slider("Days to visualize", 7, 90, 30, key="timeline_days")
    df = psi_intel.get_observations_df(days_back=days_back)
    
    if len(df) < 5:
        st.warning(f"Only {len(df)} observations. Need at least 5 for timeline.")
        return
    
    # Get top features
    personalization = psi_intel.personalize_for_brandon(df)
    if personalization['status'] == 'success':
        top_features = list(personalization['top_features'].keys())[:5]
    else:
        # Default features
        top_features = ['heart_coherence', 'resonance_score', 'moon_phase']
    
    # Select features to plot
    selected_features = st.multiselect(
        "Select features to overlay",
        options=top_features,
        default=top_features[:3]
    )
    
    if not selected_features:
        st.warning("Select at least one feature to display.")
        return
    
    # Generate timeline
    with st.spinner("Generating timeline..."):
        try:
            fig = psi_intel.visualize_timeline_overlay(df, selected_features)
            st.plotly_chart(fig, use_container_width=True)
        except Exception as e:
            st.error(f"Timeline generation failed: {e}")

def render_add_observation(psi_intel: PSICorrelationIntelligence):
    """Tab 5: Add new PSI observation"""
    st.header("➕ Add PSI Observation")
    
    st.markdown("""
    Log a new prediction with all PSI modalities captured.
    
    **The more data you log, the better the system learns YOUR patterns!**
    """)
    
    with st.form("add_observation_form"):
        st.subheader("Basic Info")
        
        col1, col2 = st.columns(2)
        
        with col1:
            prediction_id = st.text_input(
                "Prediction ID",
                value=f"pred_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
                help="Unique identifier"
            )
            
            outcome = st.selectbox(
                "Outcome",
                options=[1, 0],
                format_func=lambda x: "✅ Correct" if x == 1 else "❌ Incorrect"
            )
            
            confidence = st.slider("Confidence", 0.0, 1.0, 0.5, 0.05)
            
            prediction_type = st.selectbox(
                "Prediction Type",
                ["stock_market", "prediction_market", "personal", "general"]
            )
        
        with col2:
            timestamp = st.date_input("Date", datetime.now())
            time = st.time_input("Time", datetime.now().time())
        
        st.subheader("Numerology")
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            user_life_path = st.number_input("Your Life Path", 1, 11, 6, help="Brandon = 6")
        with col2:
            user_birth_day = st.number_input("Your Birth Day", 1, 31, 7, help="Brandon = 7")
        with col3:
            event_date_numerology = st.number_input("Event Date Number", 1, 11, 1)
        with col4:
            resonance_score = st.slider("Resonance Score", 0.0, 1.0, 0.5)
        
        st.subheader("Weather & Environment")
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            barometric_pressure = st.number_input("Pressure (hPa)", 950.0, 1050.0, 1013.25, step=0.1)
        with col2:
            temperature = st.number_input("Temperature (°C)", -20.0, 50.0, 20.0, step=0.5)
        with col3:
            precipitation = st.number_input("Precipitation (mm)", 0.0, 100.0, 0.0, step=0.1)
        with col4:
            cosmic_ray_flux = st.number_input("Cosmic Ray Flux", 0.0, 100.0, 50.0, step=1.0)
        
        st.subheader("Biometrics")
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            heart_coherence = st.slider("Heart Coherence", 0.0, 1.0, 0.5, 0.05)
        with col2:
            hrv_score = st.slider("HRV Score", 0.0, 100.0, 50.0, 1.0)
        with col3:
            sleep_recovery = st.slider("Sleep Recovery", 0.0, 1.0, 0.7, 0.05)
        with col4:
            oura_readiness = st.slider("Oura Readiness", 0.0, 1.0, 0.75, 0.05)
        
        st.subheader("Cosmic & Quantum")
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            moon_phase = st.slider("Moon Phase", 0.0, 1.0, 0.5, 0.05, help="0=New, 0.5=Full")
        with col2:
            solar_activity = st.slider("Solar Activity", 0.0, 100.0, 50.0, 1.0)
        with col3:
            i_cell_signature_strength = st.slider("I-Cell Signature", 0.0, 1.0, 0.5, 0.05)
        with col4:
            biophoton_sync_probability = st.slider("Biophoton Sync", 0.0, 1.0, 0.5, 0.05)
        
        # Submit
        submitted = st.form_submit_button("📝 Log Observation", use_container_width=True)
        
        if submitted:
            # Create observation
            dt = datetime.combine(timestamp, time)
            
            obs = PSIObservation(
                prediction_id=prediction_id,
                timestamp=dt,
                outcome=outcome,
                confidence=confidence,
                user_life_path=user_life_path,
                user_birth_day=user_birth_day,
                event_date_numerology=event_date_numerology,
                resonance_score=resonance_score,
                barometric_pressure=barometric_pressure,
                temperature=temperature,
                precipitation=precipitation,
                cosmic_ray_flux=cosmic_ray_flux,
                heart_coherence=heart_coherence,
                hrv_score=hrv_score,
                sleep_recovery=sleep_recovery,
                oura_readiness=oura_readiness,
                moon_phase=moon_phase,
                solar_activity=solar_activity,
                i_cell_signature_strength=i_cell_signature_strength,
                biophoton_sync_probability=biophoton_sync_probability,
                hour_of_day=dt.hour,
                day_of_week=dt.weekday() + 1,
                prediction_type=prediction_type
            )
            
            # Ingest
            success = psi_intel.ingest_observation(obs)
            
            if success:
                st.success(f"✅ Observation '{prediction_id}' logged successfully!")
                st.balloons()
            else:
                st.error("❌ Failed to log observation. Check database connection.")
    
    # Show recent observations
    st.subheader("Recent Observations")
    df = psi_intel.get_observations_df(days_back=7)
    
    if len(df) > 0:
        st.dataframe(
            df[['prediction_id', 'timestamp', 'outcome', 'confidence']].head(10),
            use_container_width=True,
            hide_index=True
        )
        st.caption(f"Showing 10 most recent of {len(df)} total observations")
    else:
        st.info("No observations yet. Add your first prediction above!")

if __name__ == "__main__":
    render_psi_correlation_dashboard()

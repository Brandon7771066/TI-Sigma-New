"""
Autonomous LCC Study Dashboard

Integrates multiple data sources for fully autonomous LCC analysis:
1. DANDI Archive - Rodent EEG/LFP + behavior datasets
2. Allen Brain Observatory - Mouse neural + behavior recordings
3. Zoo Webcams + AI Vision - Real-time animal behavior analysis

This dashboard allows autonomous data collection and LCC correlation testing
without requiring manual behavior coding expertise.
"""

import streamlit as st
import sys
import os
from pathlib import Path
from datetime import datetime
import json

# Add experiments to path
sys.path.insert(0, str(Path(__file__).parent))

# Page config
st.set_page_config(
    page_title="Autonomous LCC Study System",
    page_icon="🧠",
    layout="wide"
)

st.title("🧠 Autonomous LCC Study System")
st.markdown("""
**Fully automated analysis of Local Causation Correlation (LCC) using real neuroscience datasets.**

This system tests whether consciousness enables non-local correlations (LCC < 1) by analyzing:
- Neural activity patterns across different subjects/sessions
- Behavior synchrony without shared sensory input
- Correlation with Global Consciousness Project readings
""")

# Create tabs
tab1, tab2, tab3, tab4, tab5 = st.tabs([
    "📊 Dashboard", 
    "🔬 DANDI Datasets", 
    "🧪 Allen Brain Data",
    "📹 Zoo Webcam AI",
    "📈 Results & Analysis"
])

# =============================================================================
# TAB 1: Dashboard Overview
# =============================================================================
with tab1:
    st.header("System Overview")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.metric("Data Sources", "3", help="DANDI, Allen Brain, Zoo Webcams")
    
    with col2:
        try:
            from dandi_data_integration import get_available_datasets
            datasets = get_available_datasets()
            st.metric("Downloaded Datasets", len(datasets))
        except Exception:
            st.metric("Downloaded Datasets", "0")
    
    with col3:
        try:
            from dandi_data_integration import get_analysis_results
            results = get_analysis_results()
            st.metric("LCC Analyses Run", len(results))
        except Exception:
            st.metric("LCC Analyses Run", "0")
    
    st.divider()
    
    st.subheader("🚀 Quick Start: Run Autonomous Analysis")
    
    st.info("""
    **How it works:**
    1. The system downloads real neuroscience data (mouse neural recordings + behavior)
    2. AI extracts synchronized neural-behavior segments
    3. Cross-session correlations are tested for LCC < 1
    4. Results are interpreted in context of consciousness theory
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        num_sessions = st.slider("Number of sessions to analyze", 2, 5, 3)
        
        if st.button("🔬 Run Allen Brain Analysis", type="primary", use_container_width=True):
            with st.spinner("Running autonomous LCC analysis... This may take several minutes."):
                try:
                    from allen_brain_integration import autonomous_lcc_pipeline
                    results = autonomous_lcc_pipeline(num_sessions=num_sessions)
                    
                    st.success("Analysis complete!")
                    
                    if "error" not in results:
                        st.json(results)
                    else:
                        st.error(f"Error: {results.get('error')}")
                        
                except Exception as e:
                    st.error(f"Analysis failed: {e}")
                    st.info("This may require installing AllenSDK. The system will attempt installation automatically.")
    
    with col2:
        st.markdown("""
        **What this tests:**
        - Do mice in different sessions show correlated neural activity?
        - Is behavior synchronized beyond what local causation predicts?
        - Are there unexplained correlations suggesting LCC < 1?
        
        **Expected results if LCC = 1 (null hypothesis):**
        - No significant cross-session correlations
        - Random correlation distribution
        
        **Expected if LCC < 1 (alternative hypothesis):**
        - Significant positive correlations
        - Pattern across multiple session pairs
        """)

# =============================================================================
# TAB 2: DANDI Datasets
# =============================================================================
with tab2:
    st.header("🔬 DANDI Archive Datasets")
    
    st.markdown("""
    [DANDI Archive](https://dandiarchive.org) hosts 400+ neuroscience datasets in NWB format.
    These include rodent EEG/LFP recordings with synchronized behavior data.
    """)
    
    # Show recommended datasets
    st.subheader("Recommended Datasets for LCC Analysis")
    
    try:
        from dandi_data_integration import RECOMMENDED_DATASETS
        
        for i, ds in enumerate(RECOMMENDED_DATASETS):
            with st.expander(f"📁 {ds.name}", expanded=i==0):
                col1, col2 = st.columns(2)
                
                with col1:
                    st.markdown(f"**DANDI ID:** `{ds.dandiset_id}`")
                    st.markdown(f"**Species:** {ds.species}")
                    st.markdown(f"**Recording Type:** {ds.recording_type}")
                    st.markdown(f"**Subjects:** {ds.num_subjects}")
                
                with col2:
                    st.markdown(f"**Has Behavior:** {'✅' if ds.has_behavior else '❌'}")
                    st.markdown(f"**Size:** ~{ds.size_gb} GB")
                    st.markdown(f"**License:** {ds.license}")
                
                st.markdown(f"**Description:** {ds.description}")
                
                st.link_button(
                    "View on DANDI Archive", 
                    ds.download_url,
                    use_container_width=True
                )
                
                if st.button(f"Download Subset (500MB max)", key=f"dl_{ds.dandiset_id}"):
                    with st.spinner(f"Downloading {ds.name}..."):
                        try:
                            from dandi_data_integration import download_dandiset
                            result = download_dandiset(ds.dandiset_id, max_size_mb=500)
                            if result:
                                st.success(f"Downloaded to: {result}")
                            else:
                                st.error("Download failed")
                        except Exception as e:
                            st.error(f"Error: {e}")
                            
    except ImportError as e:
        st.error(f"Could not load DANDI integration: {e}")
    
    st.divider()
    
    # Show downloaded datasets
    st.subheader("Downloaded Datasets")
    
    try:
        from dandi_data_integration import get_available_datasets
        datasets = get_available_datasets()
        
        if datasets:
            for ds in datasets:
                st.markdown(f"- **{ds['name']}** ({ds['species']}) - {ds['num_files']} files - {ds['status']}")
        else:
            st.info("No datasets downloaded yet. Use the buttons above to download.")
    except Exception as e:
        st.warning(f"Could not load dataset list: {e}")

# =============================================================================
# TAB 3: Allen Brain Observatory
# =============================================================================
with tab3:
    st.header("🧪 Allen Brain Observatory")
    
    st.markdown("""
    The [Allen Brain Observatory](https://portal.brain-map.org) provides mouse neural recordings
    during visual behavior tasks. This includes:
    - **Neuropixels recordings**: 374+ channels per probe, 30kHz spike band
    - **Behavior data**: Running speed, licks, rewards, trial outcomes
    - **Visual stimuli**: Natural images, gratings, movies
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Available Sessions")
        
        if st.button("🔍 Fetch Available Sessions"):
            with st.spinner("Querying Allen Brain Observatory..."):
                try:
                    from allen_brain_integration import get_visual_behavior_sessions
                    sessions = get_visual_behavior_sessions()
                    
                    if sessions and "error" not in sessions[0]:
                        st.session_state["allen_sessions"] = sessions
                        st.success(f"Found {len(sessions)} sessions")
                    else:
                        st.error(f"Error: {sessions}")
                except Exception as e:
                    st.error(f"Failed to query sessions: {e}")
        
        if "allen_sessions" in st.session_state:
            sessions = st.session_state["allen_sessions"]
            
            # Show as table
            session_data = []
            for s in sessions[:20]:
                session_data.append({
                    "Session ID": s.get("session_id"),
                    "Genotype": s.get("genotype", "unknown")[:30],
                    "Units": s.get("unit_count", 0),
                    "Type": s.get("session_type", "unknown")
                })
            
            st.dataframe(session_data, use_container_width=True)
    
    with col2:
        st.subheader("Session Analysis")
        
        session_id = st.number_input("Session ID to analyze", min_value=0, value=0)
        
        if st.button("📥 Download & Process Session"):
            if session_id > 0:
                with st.spinner(f"Downloading session {session_id}..."):
                    try:
                        from allen_brain_integration import download_session_data, process_allen_session_for_lcc
                        
                        info = download_session_data(session_id)
                        if info:
                            st.success(f"Downloaded: {info.get('units', 0)} units, {info.get('channels', 0)} channels")
                            
                            segments = process_allen_session_for_lcc(session_id)
                            st.info(f"Extracted {len(segments)} neural-behavior segments")
                        else:
                            st.error("Download failed")
                    except Exception as e:
                        st.error(f"Error: {e}")
            else:
                st.warning("Enter a valid session ID")
    
    st.divider()
    
    st.subheader("🔄 Autonomous Analysis Pipeline")
    
    st.markdown("""
    This runs a complete autonomous analysis:
    1. Fetches available sessions from Allen Brain Observatory
    2. Downloads sessions with most neural units
    3. Extracts synchronized neural + behavior segments
    4. Tests for cross-session correlations (LCC analysis)
    """)
    
    if st.button("🚀 Run Full Autonomous Pipeline", type="primary"):
        with st.spinner("Running autonomous LCC pipeline... This may take 5-10 minutes."):
            try:
                from allen_brain_integration import autonomous_lcc_pipeline
                results = autonomous_lcc_pipeline(num_sessions=3)
                
                if "error" not in results:
                    st.success("Pipeline complete!")
                    st.json(results)
                else:
                    st.error(f"Pipeline error: {results.get('error')}")
            except Exception as e:
                st.error(f"Pipeline failed: {e}")
                st.info("This may require additional dependencies. Check the logs for details.")

# =============================================================================
# TAB 4: Zoo Webcam AI
# =============================================================================
with tab4:
    st.header("📹 Zoo Webcam AI Analysis")
    
    st.markdown("""
    Uses AI vision (GPT-5) to automatically analyze animal behavior from zoo webcams.
    This enables LCC testing using animal subjects without EEG hardware.
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Available Webcams")
        
        WEBCAMS = {
            "Smithsonian Lions": "https://nationalzoo.si.edu/webcams/lion-cam",
            "Smithsonian Pandas": "https://nationalzoo.si.edu/webcams/panda-cam",
            "San Diego Tigers": "https://zoo.sandiegozoo.org/cams/tiger-cam",
            "Mpala Wildlife (Kenya)": "https://explore.org/livecams/african-wildlife/african-watering-hole",
            "Katmai Bears (Alaska)": "https://explore.org/livecams/brown-bears/brown-bear-salmon-cam",
            "Monterey Bay Aquarium": "https://www.montereybayaquarium.org/animals/live-cams",
        }
        
        for name, url in WEBCAMS.items():
            col_a, col_b = st.columns([3, 1])
            with col_a:
                st.markdown(f"**{name}**")
            with col_b:
                st.link_button("Open", url, use_container_width=True)
    
    with col2:
        st.subheader("AI Behavior Analysis")
        
        uploaded_file = st.file_uploader(
            "Upload webcam screenshot",
            type=["png", "jpg", "jpeg"],
            help="Take a screenshot from any webcam and upload for AI analysis"
        )
        
        webcam_name = st.text_input("Webcam source name", "unknown")
        
        if uploaded_file and st.button("🤖 Analyze with AI"):
            with st.spinner("AI is analyzing the image..."):
                try:
                    from ai_behavior_analyzer import analyze_image_with_ai
                    
                    image_data = uploaded_file.read()
                    result = analyze_image_with_ai(image_data, webcam_name)
                    
                    if result.error:
                        st.error(f"Analysis error: {result.error}")
                    else:
                        st.success("Analysis complete!")
                        
                        col_a, col_b = st.columns(2)
                        with col_a:
                            st.metric("Behavior", result.behavior_name)
                            st.metric("Activity Level", f"{result.activity_level}/5")
                            st.metric("Arousal", f"{result.arousal_level}/5")
                        with col_b:
                            st.metric("Confidence", f"{result.confidence:.0%}")
                            st.metric("Energy State", result.energy_state)
                            st.metric("Animals Visible", result.animals_visible)
                        
                        st.markdown(f"**Description:** {result.description}")
                        
                except Exception as e:
                    st.error(f"Analysis failed: {e}")
    
    st.divider()
    
    st.subheader("LCC Protocols for Webcam Analysis")
    
    try:
        from lcc_ethogram import LCC_PROTOCOLS
        
        for name, protocol in LCC_PROTOCOLS.items():
            with st.expander(f"📋 {protocol.name}"):
                st.markdown(f"**Hypothesis:** {protocol.hypothesis}")
                st.markdown(f"**Duration:** {protocol.duration_minutes} minutes")
                st.markdown(f"**Target Energy State:** {protocol.target_energy_state.value}")
                st.markdown(f"**Expected Behaviors:** {', '.join(protocol.expected_behaviors)}")
    except Exception as e:
        st.warning(f"Could not load protocols: {e}")

# =============================================================================
# TAB 5: Results & Analysis
# =============================================================================
with tab5:
    st.header("📈 LCC Analysis Results")
    
    # Load results from database
    try:
        from dandi_data_integration import get_analysis_results, DB_PATH
        import sqlite3
        
        results = get_analysis_results()
        
        if results:
            st.subheader("Cross-Dataset Correlations")
            
            for r in results:
                with st.expander(f"Analysis: {r['dataset_a']} ↔ {r['dataset_b']} ({r['analysis_date'][:10]})"):
                    col1, col2, col3 = st.columns(3)
                    
                    with col1:
                        st.metric("Neural Correlation", f"{r['correlation_neural']:.3f}")
                    with col2:
                        st.metric("Behavior Correlation", f"{r['correlation_behavior']:.3f}")
                    with col3:
                        st.metric("Combined", f"{r['correlation_combined']:.3f}")
                    
                    st.metric("P-value", f"{r['p_value']:.4f}")
                    st.metric("Sample Size", r['num_samples'])
                    
                    st.markdown(f"**Interpretation:** {r['interpretation']}")
        else:
            st.info("No analysis results yet. Run an analysis from the Dashboard or Allen Brain tabs.")
        
        # Show segment counts
        st.divider()
        st.subheader("Data Summary")
        
        conn = sqlite3.connect(str(DB_PATH))
        cursor = conn.cursor()
        
        cursor.execute("SELECT COUNT(*) FROM neural_behavior_segments")
        segment_count = cursor.fetchone()[0]
        
        cursor.execute("SELECT COUNT(*) FROM nwb_files")
        file_count = cursor.fetchone()[0]
        
        cursor.execute("SELECT COUNT(*) FROM lcc_correlations")
        analysis_count = cursor.fetchone()[0]
        
        conn.close()
        
        col1, col2, col3 = st.columns(3)
        with col1:
            st.metric("Neural-Behavior Segments", segment_count)
        with col2:
            st.metric("Processed Files", file_count)
        with col3:
            st.metric("LCC Analyses", analysis_count)
            
    except Exception as e:
        st.warning(f"Could not load results: {e}")
    
    st.divider()
    
    st.subheader("Theoretical Context")
    
    st.markdown("""
    ### What LCC Means
    
    **Local Causation Correlation (LCC)** measures how much of the correlation between
    distant systems can be explained by local (known) causal mechanisms.
    
    - **LCC = 1**: All correlation is explained by local causes (null hypothesis)
    - **LCC < 1**: Some correlation requires non-local explanation (alternative hypothesis)
    
    ### How We Test It
    
    1. **Neural recordings from different subjects** should show no correlation if LCC = 1
    2. **Behavior patterns** synchronized beyond sensory coupling suggests LCC < 1
    3. **Global Consciousness Project** readings may correlate with behavior if LCC < 1
    
    ### Interpreting Results
    
    | Correlation | P-value | Interpretation |
    |-------------|---------|----------------|
    | r < 0.1 | p > 0.05 | Consistent with LCC = 1 (no non-local effect) |
    | r > 0.1 | p < 0.05 | Weak evidence for LCC < 1 (needs replication) |
    | r > 0.3 | p < 0.01 | Moderate evidence (investigate confounds) |
    | r > 0.5 | p < 0.001 | Strong evidence (likely measurement artifact) |
    
    **Important:** Extraordinary claims require extraordinary evidence. Any significant
    correlation should be scrutinized for confounds before claiming LCC < 1.
    """)

# Footer
st.divider()
st.markdown("""
---
**Autonomous LCC Study System** | Part of the TI Framework Consciousness Research Platform

*Data sources: DANDI Archive, Allen Brain Observatory, Global Consciousness Project*
""")

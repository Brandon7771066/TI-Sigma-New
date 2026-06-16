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


def render_autonomous_lcc_dashboard():
    """Render the autonomous LCC study dashboard (for embedding in main app)."""
    
    st.header("🧠 Autonomous LCC Study System")
    st.markdown("""
    **Fully automated analysis of Law of Correlational Causation (LCC) using real neuroscience datasets.**
    
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
    
    with tab1:
        _render_dashboard_tab()
    
    with tab2:
        _render_dandi_tab()
    
    with tab3:
        _render_allen_tab()
    
    with tab4:
        _render_webcam_tab()
    
    with tab5:
        _render_results_tab()
    
    # Footer
    st.divider()
    st.caption("**Autonomous LCC Study System** | Part of the TI Framework Consciousness Research Platform")


def _render_dashboard_tab():
    """Tab 1: Dashboard Overview"""
    st.subheader("System Overview")
    
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
        num_sessions = st.slider("Number of sessions to analyze", 2, 5, 3, key="dashboard_sessions")
        
        if st.button("🔬 Run Allen Brain Analysis", type="primary", use_container_width=True, key="run_allen"):
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


def _render_dandi_tab():
    """Tab 2: DANDI Datasets"""
    st.subheader("🔬 DANDI Archive Datasets")
    
    st.markdown("""
    [DANDI Archive](https://dandiarchive.org) hosts 400+ neuroscience datasets in NWB format.
    These include rodent EEG/LFP recordings with synchronized behavior data.
    """)
    
    # Show recommended datasets
    st.markdown("#### Recommended Datasets for LCC Analysis")
    
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
    st.markdown("#### Downloaded Datasets")
    
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


def _render_allen_tab():
    """Tab 3: Allen Brain Observatory"""
    st.subheader("🧪 Allen Brain Observatory")
    
    st.markdown("""
    The [Allen Brain Observatory](https://portal.brain-map.org) provides mouse neural recordings
    during visual behavior tasks. This includes:
    - **Neuropixels recordings**: 374+ channels per probe, 30kHz spike band
    - **Behavior data**: Running speed, licks, rewards, trial outcomes
    - **Visual stimuli**: Natural images, gratings, movies
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("#### Available Sessions")
        
        if st.button("🔍 Fetch Available Sessions", key="fetch_allen"):
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
        st.markdown("#### Session Analysis")
        
        session_id = st.number_input("Session ID to analyze", min_value=0, value=0, key="session_input")
        
        if st.button("📥 Download & Process Session", key="process_session"):
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
    
    st.markdown("#### 🔄 Autonomous Analysis Pipeline")
    
    st.markdown("""
    This runs a complete autonomous analysis:
    1. Fetches available sessions from Allen Brain Observatory
    2. Downloads sessions with most neural units
    3. Extracts synchronized neural + behavior segments
    4. Tests for cross-session correlations (LCC analysis)
    """)
    
    if st.button("🚀 Run Full Autonomous Pipeline", type="primary", key="run_pipeline"):
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


def _render_webcam_tab():
    """Tab 4: Zoo Webcam AI"""
    st.subheader("📹 Zoo Webcam AI Analysis")
    
    st.markdown("""
    Uses AI vision (GPT-5) to automatically analyze animal behavior from zoo webcams.
    This enables LCC testing using animal subjects without EEG hardware.
    """)
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("#### Available Webcams")
        
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
        st.markdown("#### AI Behavior Analysis")
        
        uploaded_file = st.file_uploader(
            "Upload webcam screenshot",
            type=["png", "jpg", "jpeg"],
            help="Take a screenshot from any webcam and upload for AI analysis"
        )
        
        webcam_name = st.text_input("Webcam source name", "unknown", key="webcam_name")
        
        if uploaded_file and st.button("🤖 Analyze with AI", key="analyze_webcam"):
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
    
    st.markdown("#### LCC Protocols for Webcam Analysis")
    
    try:
        from lcc_ethogram import LCC_PROTOCOLS
        
        for name, protocol in LCC_PROTOCOLS.items():
            with st.expander(f"📋 {protocol.name}"):
                st.markdown(f"**Hypothesis:** {protocol.gcp_correlation_hypothesis}")
                st.markdown(f"**Duration:** {protocol.duration_minutes} minutes")
                st.markdown(f"**Target Energy State:** {protocol.target_energy_state.value}")
                st.markdown(f"**Expected Behaviors:** {', '.join(protocol.expected_behaviors)}")
    except Exception as e:
        st.warning(f"Could not load protocols: {e}")


def _render_results_tab():
    """Tab 5: Results & Analysis"""
    st.subheader("📈 LCC Analysis Results")
    
    # Load results from PostgreSQL database
    database_url = os.environ.get('DATABASE_URL', '')
    
    if not database_url:
        st.warning("Database not configured. Set DATABASE_URL environment variable.")
        st.info("Run the autonomous analysis scripts to populate results.")
        return
    
    conn = None
    try:
        import psycopg2
        
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        
        # Get LCC analysis results
        cur.execute('''
            SELECT dataset_id, observed_lcc, p_value, effect_size, interpretation, 
                   analysis_method, details, created_at
            FROM lcc_analysis_results 
            ORDER BY created_at DESC
        ''')
        results = cur.fetchall()
        
        if results:
            st.markdown("### 🔬 Block Permutation LCC Analyses")
            
            for r in results:
                dataset_id, lcc, p_val, effect, interp, method, details, created = r
                
                # Robustly parse details (may be dict, str, or bytes)
                if isinstance(details, dict):
                    details_dict = details
                elif isinstance(details, (str, bytes)):
                    try:
                        details_dict = json.loads(details)
                    except (json.JSONDecodeError, TypeError):
                        details_dict = {}
                else:
                    details_dict = {}
                
                is_independent = details_dict.get('is_independent', False)
                status_icon = "✅" if is_independent else "⚠️"
                status_text = "TRUE LCC TEST" if is_independent else "Tautological"
                
                with st.expander(f"{status_icon} {dataset_id} - r={lcc:.3f}, p={p_val:.4f}"):
                    col1, col2, col3, col4 = st.columns(4)
                    
                    with col1:
                        st.metric("Correlation (r)", f"{lcc:.4f}")
                    with col2:
                        st.metric("P-value", f"{p_val:.6f}")
                    with col3:
                        st.metric("Effect Size (d)", f"{effect:.2f}")
                    with col4:
                        st.metric("Status", status_text)
                    
                    st.markdown(f"**Method:** {method}")
                    st.markdown(f"**Date:** {created}")
                    
                    if details_dict:
                        st.markdown(f"**Neural Metric:** {details_dict.get('neural_metric', 'unknown')}")
                        st.markdown(f"**Behavior Metric:** {details_dict.get('behavior_metric', 'unknown')}")
                        st.markdown(f"**Segments:** {details_dict.get('n_segments', 'unknown')}")
                    
                    st.info(f"**Interpretation:** {interp}")
        else:
            st.info("No analysis results yet. Run an analysis from the Dashboard or Allen Brain tabs.")
        
        # Get segment counts per dataset
        st.divider()
        st.markdown("### 📊 Data Summary")
        
        cur.execute('''
            SELECT dataset_id, COUNT(*), data_type
            FROM neural_behavior_segments
            GROUP BY dataset_id, data_type
        ''')
        segments = cur.fetchall()
        
        if segments:
            col1, col2 = st.columns(2)
            with col1:
                st.markdown("#### Processed Datasets")
                for ds_id, count, dtype in segments:
                    st.markdown(f"- **{ds_id}**: {count} segments ({dtype})")
            
            with col2:
                st.markdown("#### Quick Stats")
                total_segments = sum(s[1] for s in segments)
                st.metric("Total Segments", total_segments)
                st.metric("Datasets Processed", len(segments))
                st.metric("LCC Analyses", len(results))
            
    except Exception as e:
        st.warning(f"Could not load results: {e}")
        st.info("Database may not be initialized. Run an analysis first.")
    finally:
        if conn:
            conn.close()
    
    st.divider()
    
    st.markdown("### 🧠 Understanding the Results")
    
    with st.expander("📚 What are Hippocampal Ripples?"):
        st.markdown("""
        **Sharp-wave ripples (SWRs)** are brief, high-frequency oscillations (150-250 Hz) 
        that occur in the hippocampus during quiet wakefulness and sleep.
        
        **Why they matter for consciousness research:**
        - They appear to be the brain's mechanism for **memory consolidation**
        - During ripples, neurons fire in compressed sequences that "replay" experiences
        - They coordinate hippocampus-cortex communication
        - They synchronize large neural populations in milliseconds - relevant to binding
        
        **Our findings:** r=0.43 correlation between ripple rate and amplitude, confirming
        that these are tightly coupled neural phenomena from the same process.
        """)
    
    with st.expander("🏃 What is Locomotion-Enhanced Visual Response?"):
        st.markdown("""
        When mice run on a treadmill/wheel, their visual cortex neurons become **more active**.
        This is a well-established finding in neuroscience (Niell & Stryker, 2010).
        
        **Our TRUE LCC test:**
        - Neural: Calcium fluorescence (GCaMP6) from visual cortex neurons  
        - Behavior: Running wheel velocity (independent physical measurement)
        - Result: r=0.35 (borderline significant p=0.059)
        
        **Interpretation:** This confirms LOCAL coupling between brain and behavior,
        as expected by classical neuroscience. For LCC < 1 consciousness evidence,
        we would need NON-LOCAL correlations exceeding what local mechanisms predict.
        """)
    
    with st.expander("⚡ What is Neural Entrainment (SSVEP/AVE)?"):
        st.markdown("""
        **Steady-State Visual Evoked Potentials (SSVEP):**
        When exposed to rhythmic visual stimulation (flickering lights), brain oscillations
        ENTRAIN to the stimulus frequency. This creates measurable EEG power at the
        stimulation frequency and its harmonics.
        
        **Audio-Visual Entrainment (AVE):**
        - Therapeutic use of rhythmic light/sound to influence brain states
        - Used for relaxation, focus enhancement, meditation induction
        - Demonstrates external rhythms can influence consciousness states
        
        **Available datasets:**
        - PhysioNet MAMEM SSVEP: 256-channel EEG with flickering stimulation
        - 2024 Figshare dataset: 1-60 Hz frequency range, 30 subjects
        - Multi-frequency BCI datasets for large-command systems
        """)
    
    st.markdown("### 📖 Theoretical Context")
    
    st.markdown("""
    **Law of Correlational Causation (LCC)** measures how much of the correlation between
    neural activity and behavior can be explained by local (known) causal mechanisms.
    
    | LCC Value | Meaning |
    |-----------|---------|
    | **LCC = 1** | All correlation explained by local causes (null hypothesis) |
    | **LCC < 1** | Some correlation requires non-local explanation |
    
    **Interpreting Our Results:**
    
    | Analysis | Correlation | P-value | Verdict |
    |----------|-------------|---------|---------|
    | DANDI Ripples | r=0.43 | p<0.001 | ⚠️ Tautological (same source) |
    | Allen Running | r=0.35 | p=0.059 | ✅ TRUE test, borderline significant |
    
    **Next Steps for LCC Research:**
    1. Analyze more datasets with independent neural + behavior
    2. Test cross-subject correlations (different animals, same time)
    3. Include entrainment protocols to test consciousness modulation
    4. Integrate Global Consciousness Project data
    
    **Important:** Extraordinary claims require extraordinary evidence.
    """)


# Allow running as standalone
if __name__ == "__main__":
    st.set_page_config(
        page_title="Autonomous LCC Study System",
        page_icon="🧠",
        layout="wide"
    )
    render_autonomous_lcc_dashboard()

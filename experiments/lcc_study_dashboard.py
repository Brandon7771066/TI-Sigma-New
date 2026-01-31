"""
LCC Animal Study Dashboard - Automated Analysis

Streamlit-based interface for:
- Watching live webcams (embedded viewers)
- Automated AI behavior analysis
- Evidence-based ethogram scoring
- LCC protocol execution
- GCP correlation monitoring
- Real-time synchrony visualization

This is the main dashboard for running LCC experiments.
"""

import streamlit as st
import json
import time
import sqlite3
import base64
from datetime import datetime, timedelta
from pathlib import Path
import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
import sys

# Add experiments directory to path
sys.path.insert(0, str(Path(__file__).parent))

from automated_animal_study import (
    Database, WebcamRegistry, GCPMonitor, 
    ExperimentSession, SynchronyCalculator, BehaviorObservation,
    DB_FILE, STUDY_DB_PATH
)
from lcc_ethogram import (
    ETHOGRAM, LCC_PROTOCOLS, BehaviorCategory, EnergyState,
    get_behavior_by_code, calculate_synchrony_score
)
from ai_behavior_analyzer import (
    analyze_image_with_ai, BehaviorAnalysis, LCCStudySession
)

st.set_page_config(
    page_title="LCC Animal Study",
    page_icon="🔬",
    layout="wide"
)

# Initialize components
@st.cache_resource
def get_database():
    return Database()

@st.cache_resource
def get_registry(_db):
    return WebcamRegistry(_db)


def main():
    st.title("🔬 LCC Animal Synchrony Study")
    st.markdown("*Automated AI-powered behavior analysis for testing consciousness predictions*")
    
    db = get_database()
    registry = get_registry(db)
    
    # Session state
    if 'gcp_z' not in st.session_state:
        st.session_state.gcp_z = 0.0
    if 'current_protocol' not in st.session_state:
        st.session_state.current_protocol = None
    if 'analyses' not in st.session_state:
        st.session_state.analyses = []
    
    # Sidebar
    st.sidebar.header("LCC Study Controls")
    
    page = st.sidebar.selectbox(
        "Navigation",
        ["🎥 Watch & Analyze", "📊 Protocol Runner", "📈 Results Analysis", 
         "📚 Ethogram Reference", "⚙️ Settings"]
    )
    
    # GCP indicator
    st.sidebar.divider()
    st.sidebar.subheader("GCP Status")
    gcp_z = st.sidebar.number_input("Current Z-Score", -5.0, 5.0, st.session_state.gcp_z, 0.1)
    st.session_state.gcp_z = gcp_z
    
    if abs(gcp_z) >= 2:
        st.sidebar.error(f"⚠️ SIGNIFICANT EVENT\nZ = {gcp_z:.2f}")
    elif abs(gcp_z) >= 1:
        st.sidebar.warning(f"📊 Elevated\nZ = {gcp_z:.2f}")
    else:
        st.sidebar.success(f"📊 Normal\nZ = {gcp_z:.2f}")
    
    st.sidebar.link_button("📡 GCP Dot (Live)", "https://gcpdot.com/", use_container_width=True)
    
    # Stats
    st.sidebar.divider()
    st.sidebar.metric("Total Observations", db.get_observation_count())
    st.sidebar.metric("AI Analyses", len(st.session_state.analyses))
    
    # Page routing
    if page == "🎥 Watch & Analyze":
        render_watch_analyze(db, registry)
    elif page == "📊 Protocol Runner":
        render_protocol_runner(db, registry)
    elif page == "📈 Results Analysis":
        render_results_analysis(db, registry)
    elif page == "📚 Ethogram Reference":
        render_ethogram_reference()
    elif page == "⚙️ Settings":
        render_settings(registry)


def render_watch_analyze(db: Database, registry: WebcamRegistry):
    """Watch webcams and run AI analysis"""
    st.header("🎥 Watch Webcams & AI Analysis")
    
    st.info("""
    **How it works:**
    1. Open a webcam in a new tab
    2. Take a screenshot of the animal
    3. Upload it here for AI analysis
    4. The AI will automatically score the behavior using our evidence-based ethogram
    """)
    
    # Webcam selection
    col1, col2 = st.columns([3, 1])
    
    with col1:
        selected_webcams = st.multiselect(
            "Select Webcams to Monitor",
            list(registry.webcams.keys()),
            default=list(registry.webcams.keys())[:4],
            format_func=lambda x: f"{registry.webcams[x].species.title()} ({registry.webcams[x].location})"
        )
    
    with col2:
        n_cols = st.slider("Columns", 1, 4, 2)
    
    st.divider()
    
    # Display webcam grid with links and upload
    if selected_webcams:
        webcam_cols = st.columns(n_cols)
        
        for i, name in enumerate(selected_webcams):
            webcam = registry.webcams[name]
            with webcam_cols[i % n_cols]:
                st.subheader(f"🎬 {webcam.species.title()}")
                st.caption(f"📍 {webcam.location}")
                
                # Link to open webcam
                st.link_button("🔗 Open Webcam", webcam.url, use_container_width=True)
                
                # Image upload for AI analysis
                uploaded = st.file_uploader(
                    "Upload screenshot",
                    type=['png', 'jpg', 'jpeg'],
                    key=f"upload_{name}",
                    label_visibility="collapsed"
                )
                
                if uploaded:
                    # Show the image
                    st.image(uploaded, use_container_width=True)
                    
                    if st.button(f"🤖 Analyze", key=f"analyze_{name}", use_container_width=True):
                        with st.spinner("AI analyzing behavior..."):
                            image_data = uploaded.read()
                            analysis = analyze_image_with_ai(image_data, name)
                            
                            # Store analysis
                            st.session_state.analyses.append(analysis)
                            
                            # Save to database
                            with sqlite3.connect(db.db_path) as conn:
                                conn.execute("""
                                    INSERT INTO observations 
                                    (timestamp_utc, webcam_name, species, behavior_code,
                                     activity_level, mood_score, gcp_z_score, notes, observer)
                                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
                                """, (
                                    analysis.timestamp,
                                    name,
                                    webcam.species,
                                    analysis.behavior_code,
                                    analysis.activity_level,
                                    analysis.valence,
                                    st.session_state.gcp_z,
                                    f"AI: {analysis.description}",
                                    "ai_vision"
                                ))
                        
                        # Show result
                        st.success(f"**{analysis.behavior_name}** ({analysis.behavior_code})")
                        
                        behavior_info = ETHOGRAM.get(analysis.behavior_code)
                        if behavior_info:
                            col_a, col_b = st.columns(2)
                            col_a.metric("Confidence", f"{analysis.confidence:.0%}")
                            col_b.metric("Activity", f"{analysis.activity_level}/5")
                            
                            st.caption(f"Energy: {analysis.energy_state}")
                            st.caption(f"Description: {analysis.description}")
    
    # Recent analyses
    st.divider()
    st.subheader("📋 Recent AI Analyses")
    
    if st.session_state.analyses:
        recent = st.session_state.analyses[-10:][::-1]
        
        data = []
        for a in recent:
            data.append({
                "Time": a.timestamp[:19],
                "Webcam": a.webcam_name,
                "Behavior": f"{a.behavior_code} - {a.behavior_name}",
                "Confidence": f"{a.confidence:.0%}",
                "Activity": a.activity_level,
                "Energy": a.energy_state
            })
        
        st.dataframe(data, use_container_width=True)
    else:
        st.info("Upload and analyze webcam screenshots to see results here")


def render_protocol_runner(db: Database, registry: WebcamRegistry):
    """Run LCC testing protocols"""
    st.header("📊 LCC Protocol Runner")
    
    st.markdown("""
    Select and run specific LCC testing protocols. Each protocol is designed to test 
    different aspects of the consciousness correlation hypothesis.
    """)
    
    # Protocol selection
    protocol_name = st.selectbox(
        "Select Protocol",
        list(LCC_PROTOCOLS.keys()),
        format_func=lambda x: LCC_PROTOCOLS[x].name
    )
    
    protocol = LCC_PROTOCOLS[protocol_name]
    
    # Protocol details
    col1, col2 = st.columns([2, 1])
    
    with col1:
        st.subheader(protocol.name)
        st.write(protocol.description)
        st.markdown(f"**Hypothesis:** {protocol.gcp_correlation_hypothesis}")
        
        with st.expander("Protocol Details"):
            st.markdown(f"""
            - **Duration:** {protocol.duration_minutes} minutes
            - **Target Energy State:** {protocol.target_energy_state.value}
            - **Measurement Interval:** {protocol.measurement_interval_seconds} seconds
            - **Expected Behaviors:** {', '.join(protocol.expected_behaviors)}
            - **Baseline Comparison:** {'Yes' if protocol.baseline_comparison else 'No'}
            - **Notes:** {protocol.notes}
            """)
    
    with col2:
        st.metric("Duration", f"{protocol.duration_minutes} min")
        st.metric("Interval", f"{protocol.measurement_interval_seconds}s")
        
        # Show expected behaviors with color coding
        st.markdown("**Expected Behaviors:**")
        for code in protocol.expected_behaviors:
            behavior = ETHOGRAM.get(code)
            if behavior:
                st.markdown(f"- `{code}`: {behavior.name}")
    
    st.divider()
    
    # Protocol execution
    st.subheader("Run Protocol")
    
    if st.session_state.current_protocol == protocol_name:
        st.success(f"Protocol '{protocol.name}' is ACTIVE")
        
        col1, col2, col3 = st.columns(3)
        col1.metric("Analyses Collected", len(st.session_state.analyses))
        
        # Calculate compliance
        expected = set(protocol.expected_behaviors)
        observed = set(a.behavior_code for a in st.session_state.analyses if a.behavior_code != "NV")
        matching = expected.intersection(observed)
        compliance = len(matching) / len(expected) if expected else 0
        
        col2.metric("Protocol Compliance", f"{compliance:.0%}")
        col3.metric("GCP Z-Score", f"{st.session_state.gcp_z:.2f}")
        
        if st.button("⏹️ Stop Protocol", type="secondary"):
            st.session_state.current_protocol = None
            st.success("Protocol stopped")
            st.rerun()
    else:
        st.warning("Protocol not running")
        
        if st.button(f"▶️ Start {protocol.name}", type="primary"):
            st.session_state.current_protocol = protocol_name
            st.session_state.analyses = []  # Clear for new protocol
            st.success(f"Protocol '{protocol.name}' started!")
            st.rerun()
    
    # Instructions
    st.divider()
    st.subheader("📝 Protocol Instructions")
    
    instructions = {
        "ENERGY_ENHANCEMENT": """
        1. Monitor GCP Dot for elevated readings (Z > 1)
        2. When GCP is elevated, observe all webcams for increased activity
        3. Upload screenshots every 30 seconds during elevated periods
        4. Focus on play, running, social, and exploratory behaviors
        5. Compare synchrony during elevated vs normal GCP periods
        """,
        "RELAXATION": """
        1. Run during normal GCP periods (|Z| < 1)
        2. Upload screenshots every 60 seconds
        3. Focus on resting, standing, sitting behaviors
        4. This establishes baseline synchrony for comparison
        """,
        "GLOBAL_EVENT": """
        1. Activate during major global events (new year, sports finals, etc.)
        2. Monitor GCP for readings > 2
        3. Upload screenshots every 15 seconds during peak events
        4. Expect highest synchrony during these periods
        """,
        "CIRCADIAN_RHYTHM": """
        1. Long-term monitoring (24 hours ideal)
        2. Upload screenshots every 5 minutes
        3. Track activity patterns across time zones
        4. Establishes species-specific baselines
        """,
        "SOCIAL_RESONANCE": """
        1. Focus on social behaviors
        2. Upload when animals interact with each other
        3. Track affiliative vs aggressive behaviors
        4. Test emotional contagion hypothesis
        """
    }
    
    st.markdown(instructions.get(protocol_name, "Follow standard observation procedures."))


def render_results_analysis(db: Database, registry: WebcamRegistry):
    """Analyze results and visualize synchrony"""
    st.header("📈 Results Analysis")
    
    # Load data
    with sqlite3.connect(db.db_path) as conn:
        df = pd.read_sql_query("""
            SELECT * FROM observations 
            ORDER BY timestamp_utc DESC 
            LIMIT 5000
        """, conn)
    
    if len(df) == 0:
        st.warning("No observations recorded yet. Go to Watch & Analyze to collect data.")
        return
    
    df['timestamp'] = pd.to_datetime(df['timestamp_utc'])
    
    # Summary metrics
    st.subheader("Dataset Summary")
    col1, col2, col3, col4 = st.columns(4)
    col1.metric("Total Observations", len(df))
    col2.metric("AI Analyzed", len(df[df['observer'] == 'ai_vision']))
    col3.metric("Webcams", int(df['webcam_name'].nunique()))
    col4.metric("Behaviors", int(df['behavior_code'].nunique()))
    
    st.divider()
    
    # Behavior distribution
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Behavior Distribution")
        behavior_counts = df['behavior_code'].value_counts()
        fig = px.pie(values=behavior_counts.values, names=behavior_counts.index,
                     title="All Recorded Behaviors")
        st.plotly_chart(fig, use_container_width=True)
    
    with col2:
        st.subheader("Activity Over Time")
        fig = px.scatter(df, x='timestamp', y='activity_level', 
                        color='webcam_name', title="Activity Levels")
        st.plotly_chart(fig, use_container_width=True)
    
    st.divider()
    
    # GCP Correlation Analysis
    st.subheader("🌍 GCP Correlation Analysis")
    
    gcp_data = df[df['gcp_z_score'].notna()].copy()
    
    if len(gcp_data) > 10:
        col1, col2 = st.columns(2)
        
        with col1:
            fig = px.scatter(gcp_data, x='gcp_z_score', y='activity_level',
                           color='webcam_name', title="Activity vs GCP")
            fig.add_vline(x=2, line_dash="dash", line_color="red")
            fig.add_vline(x=-2, line_dash="dash", line_color="red")
            st.plotly_chart(fig, use_container_width=True)
        
        with col2:
            # Calculate correlation
            corr = float(gcp_data['gcp_z_score'].corr(gcp_data['activity_level']))
            
            st.metric("GCP-Activity Correlation", f"{corr:.3f}")
            
            if abs(corr) > 0.3:
                st.success("🎯 Significant correlation detected!")
                st.markdown("This supports the LCC hypothesis")
            elif abs(corr) > 0.1:
                st.info("📊 Weak correlation")
            else:
                st.warning("❌ No correlation")
            
            # High GCP comparison
            high_gcp = gcp_data[gcp_data['gcp_z_score'].abs() >= 2]
            normal_gcp = gcp_data[gcp_data['gcp_z_score'].abs() < 1]
            
            if len(high_gcp) > 0 and len(normal_gcp) > 0:
                st.markdown("**Activity Comparison:**")
                st.markdown(f"- High GCP (|Z|≥2): {high_gcp['activity_level'].mean():.2f}")
                st.markdown(f"- Normal GCP (|Z|<1): {normal_gcp['activity_level'].mean():.2f}")
    else:
        st.info("Need more GCP-tagged observations for correlation analysis")
    
    st.divider()
    
    # Synchrony Analysis
    st.subheader("🔗 Synchrony Analysis")
    
    calc = SynchronyCalculator(db, registry)
    observations = db.get_all_observations(limit=1000)
    baseline = calc.calculate_baseline_chance(observations)
    
    col1, col2 = st.columns(2)
    col1.metric("Baseline (Chance)", f"{baseline:.1%}")
    col2.markdown("""
    **LCC Prediction:**  
    If LCC < 1 (non-local correlation exists), synchrony should exceed baseline during significant GCP events.
    """)


def render_ethogram_reference():
    """Show ethogram reference"""
    st.header("📚 Evidence-Based Ethogram Reference")
    
    st.markdown("""
    This ethogram is based on scientific standards from:
    - **ZooMonitor** (Lincoln Park Zoo Master Ethogram)
    - **BORIS** (Behavioral Observation Research Interactive Software)
    - **NC3Rs** Guidelines for behavioral assessment
    """)
    
    # Category filter
    categories = list(set(b.category.value for b in ETHOGRAM.values()))
    selected_cat = st.selectbox("Filter by Category", ["All"] + sorted(categories))
    
    # Display ethogram
    st.divider()
    
    data = []
    for code, b in ETHOGRAM.items():
        if selected_cat != "All" and b.category.value != selected_cat:
            continue
        data.append({
            "Code": code,
            "Name": b.name,
            "Category": b.category.value,
            "Energy State": b.energy_state.value,
            "Activity (0-5)": b.activity_score,
            "Arousal (0-5)": b.arousal_score,
            "Valence (-2 to 3)": b.valence_score,
            "LCC Weight": b.lcc_weight
        })
    
    st.dataframe(data, use_container_width=True)
    
    # Detailed view
    st.divider()
    st.subheader("Behavior Details")
    
    selected_code = st.selectbox("Select Behavior", list(ETHOGRAM.keys()),
                                 format_func=lambda x: f"{x} - {ETHOGRAM[x].name}")
    
    b = ETHOGRAM[selected_code]
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        st.markdown(f"### {b.name} ({b.code})")
        st.markdown(f"**Definition:** {b.definition}")
        st.markdown("**Indicators:**")
        for ind in b.indicators:
            st.markdown(f"- {ind}")
    
    with col2:
        st.metric("Category", b.category.value)
        st.metric("Energy State", b.energy_state.value)
        st.metric("LCC Weight", f"{b.lcc_weight:.2f}")


def render_settings(registry: WebcamRegistry):
    """Settings and configuration"""
    st.header("⚙️ Settings")
    
    st.subheader("Webcam Sources")
    
    data = []
    for name, cam in registry.webcams.items():
        data.append({
            "Name": name,
            "Species": cam.species,
            "Location": cam.location,
            "Est. R": cam.estimated_r,
            "Lat/Lon": f"{cam.latitude:.2f}, {cam.longitude:.2f}"
        })
    
    st.dataframe(data, use_container_width=True)
    
    st.divider()
    st.subheader("Database")
    st.code(str(DB_FILE))
    
    with sqlite3.connect(DB_FILE) as conn:
        tables = ["observations", "gcp_readings", "sessions", "webcams"]
        for table in tables:
            try:
                count = conn.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0]
                st.metric(table.title(), count)
            except Exception:
                pass


if __name__ == "__main__":
    main()

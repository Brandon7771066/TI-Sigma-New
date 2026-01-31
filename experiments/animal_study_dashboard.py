"""
Animal Synchrony Study Dashboard

Streamlit-based interface for:
- Managing webcam sources
- Recording behavior observations
- Monitoring GCP readings
- Visualizing synchrony scores
- Analyzing results across species

Uses SQLite database for scalable storage.
"""

import streamlit as st
import json
import time
import sqlite3
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

st.set_page_config(
    page_title="Animal Synchrony Study",
    page_icon="🦁",
    layout="wide"
)

# Initialize components
@st.cache_resource
def get_database():
    return Database()

@st.cache_resource
def get_registry(_db):
    return WebcamRegistry(_db)

# Behavior codes
BEHAVIOR_CODES = {
    'W': 'Walking',
    'S': 'Standing',
    'R': 'Resting',
    'E': 'Eating',
    'So': 'Social',
    'V': 'Vocalizing',
    'A': 'Agitated',
    'P': 'Play',
    'O': 'Other',
    'NV': 'Not Visible'
}


def main():
    st.title("🦁 Animal Synchrony Study Dashboard")
    st.markdown("*Testing LCC predictions through multi-species behavior correlation*")
    
    db = get_database()
    registry = get_registry(db)
    
    # Session state initialization
    if 'gcp_z' not in st.session_state:
        st.session_state.gcp_z = 0.0
    if 'current_session' not in st.session_state:
        st.session_state.current_session = None
    
    # Sidebar
    page = st.sidebar.selectbox(
        "Navigation",
        ["Live Observation", "GCP Monitor", "Analysis", "Webcam Registry", "Database Info"]
    )
    
    # GCP indicator in sidebar
    st.sidebar.divider()
    st.sidebar.subheader("GCP Status")
    gcp_z = st.session_state.gcp_z
    if abs(gcp_z) >= 2:
        st.sidebar.error(f"⚠️ SIGNIFICANT: Z = {gcp_z:.2f}")
    elif abs(gcp_z) >= 1:
        st.sidebar.warning(f"📊 Elevated: Z = {gcp_z:.2f}")
    else:
        st.sidebar.info(f"📊 Normal: Z = {gcp_z:.2f}")
    
    st.sidebar.divider()
    st.sidebar.metric("Total Observations", db.get_observation_count())
    
    # Page routing
    if page == "Live Observation":
        render_live_observation(db, registry)
    elif page == "GCP Monitor":
        render_gcp_monitor(db)
    elif page == "Analysis":
        render_analysis(db, registry)
    elif page == "Webcam Registry":
        render_webcam_registry(registry)
    elif page == "Database Info":
        render_database_info(db)


def render_live_observation(db: Database, registry: WebcamRegistry):
    """Live observation recording interface"""
    st.header("Live Observation Recording")
    
    col1, col2 = st.columns([3, 1])
    
    with col1:
        if st.session_state.current_session is None:
            st.warning("No active session. Start a new session to begin recording.")
            
            session_name = st.text_input(
                "Session Name", 
                f"Study_{datetime.now().strftime('%Y%m%d_%H%M')}"
            )
            
            webcam_names = list(registry.webcams.keys())
            selected = st.multiselect(
                "Select Webcams",
                webcam_names,
                default=webcam_names[:4]
            )
            
            if st.button("Start Session", type="primary"):
                session = ExperimentSession(session_name, selected, db)
                session.start()
                st.session_state.current_session = session
                st.rerun()
        else:
            session = st.session_state.current_session
            st.success(f"Active: {session.name}")
            
            col_a, col_b = st.columns(2)
            with col_a:
                st.caption(f"ID: {session.session_id}")
            with col_b:
                if st.button("Stop Session"):
                    session.stop()
                    st.session_state.current_session = None
                    st.rerun()
    
    with col2:
        # Quick GCP update
        new_z = st.number_input("GCP Z-Score", -5.0, 5.0, st.session_state.gcp_z, 0.1)
        if new_z != st.session_state.gcp_z:
            st.session_state.gcp_z = new_z
            if st.session_state.current_session:
                st.session_state.current_session.gcp_monitor.update_reading(new_z)
    
    st.divider()
    
    # Observation grid
    if st.session_state.current_session:
        session = st.session_state.current_session
        webcams = [registry.webcams[n] for n in session.webcam_names if n in registry.webcams]
        
        # Grid of webcam observation forms
        n_cols = min(4, len(webcams))
        
        for row_start in range(0, len(webcams), n_cols):
            cols = st.columns(n_cols)
            for i, col in enumerate(cols):
                idx = row_start + i
                if idx >= len(webcams):
                    break
                    
                webcam = webcams[idx]
                with col:
                    st.subheader(f"{webcam.species.title()}")
                    st.caption(f"{webcam.location}")
                    st.link_button("Open Cam", webcam.url, use_container_width=True)
                    
                    with st.form(f"form_{webcam.name}"):
                        behavior = st.selectbox(
                            "Behavior",
                            list(BEHAVIOR_CODES.keys()),
                            format_func=lambda x: f"{x} - {BEHAVIOR_CODES[x]}",
                            key=f"beh_{webcam.name}"
                        )
                        
                        c1, c2 = st.columns(2)
                        with c1:
                            activity = st.slider("Activity", 0, 5, 2, key=f"act_{webcam.name}")
                        with c2:
                            mood = st.slider("Mood", -2, 3, 0, key=f"mood_{webcam.name}")
                        
                        notes = st.text_input("Notes", key=f"notes_{webcam.name}")
                        
                        if st.form_submit_button("Record", use_container_width=True):
                            session.record_observation(
                                webcam.name, behavior, activity, mood, notes, "dashboard"
                            )
                            st.success("Recorded!")
        
        # Synchrony display
        st.divider()
        st.subheader("Current Synchrony")
        
        sync = session.get_current_synchrony()
        if "error" not in sync:
            col1, col2, col3, col4 = st.columns(4)
            col1.metric("Synchrony", f"{sync['average_synchrony']:.1%}")
            col2.metric("Baseline", f"{sync['baseline_chance']:.1%}")
            col3.metric("Above Chance?", "Yes ✓" if sync['above_chance'] else "No")
            col4.metric("Pairs", sync['n_pairs'])
        else:
            st.info("Record observations to see synchrony...")


def render_gcp_monitor(db: Database):
    """GCP monitoring interface"""
    st.header("Global Consciousness Project Monitor")
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        st.subheader("Manual Entry")
        st.markdown("Watch [GCP Dot](https://gcpdot.com/) and enter readings:")
        
        z_score = st.number_input("Z-Score", -5.0, 5.0, st.session_state.gcp_z, 0.1)
        
        if st.button("Update Reading"):
            st.session_state.gcp_z = z_score
            gcp_monitor = GCPMonitor(db)
            gcp_monitor.update_reading(z_score, "manual")
            st.success(f"Recorded: Z = {z_score}")
    
    with col2:
        st.subheader("Status")
        z = st.session_state.gcp_z
        if abs(z) >= 2:
            st.error(f"⚠️ SIGNIFICANT\nZ = {z:.2f}")
        elif abs(z) >= 1:
            st.warning(f"📊 Elevated\nZ = {z:.2f}")
        else:
            st.info(f"📊 Normal\nZ = {z:.2f}")
    
    st.divider()
    
    # Historical readings from database
    st.subheader("Recent GCP Readings")
    
    with sqlite3.connect(db.db_path) as conn:
        df = pd.read_sql_query(
            "SELECT timestamp_utc, z_score FROM gcp_readings ORDER BY timestamp_utc DESC LIMIT 100",
            conn
        )
    
    if len(df) > 0:
        df['timestamp'] = pd.to_datetime(df['timestamp_utc'])
        fig = px.line(df, x='timestamp', y='z_score', title="GCP Z-Score History")
        fig.add_hline(y=2, line_dash="dash", line_color="red")
        fig.add_hline(y=-2, line_dash="dash", line_color="red")
        st.plotly_chart(fig, use_container_width=True)
    else:
        st.info("No GCP readings recorded yet")
    
    st.divider()
    
    # Known events reference
    st.subheader("Reference: Known GCP Events")
    events = [
        {"Event": "Global Crisis", "Typical Z": ">3.0", "Example": "9/11 (Z=3.5)"},
        {"Event": "Major Mourning", "Typical Z": "2.5-3.0", "Example": "Diana funeral"},
        {"Event": "Historic Political", "Typical Z": "2.0-2.5", "Example": "Inaugurations"},
        {"Event": "Celebrations", "Typical Z": "1.5-2.0", "Example": "New Year's Eve"},
        {"Event": "Sports Finals", "Typical Z": "1.0-1.5", "Example": "World Cup"},
    ]
    st.dataframe(events, use_container_width=True)


def render_analysis(db: Database, registry: WebcamRegistry):
    """Analysis and visualization"""
    st.header("Synchrony Analysis")
    
    # Load observations
    observations = db.get_all_observations(limit=5000)
    
    if not observations:
        st.warning("No observations recorded yet!")
        return
    
    # Convert to DataFrame
    data = []
    for obs in observations:
        data.append({
            "timestamp": obs.timestamp_utc,
            "webcam": obs.webcam_name,
            "species": obs.species,
            "location": obs.location,
            "behavior": obs.behavior_code,
            "activity": obs.activity_level,
            "mood": obs.mood_score,
            "gcp_z": obs.gcp_z_score,
            "session": obs.session_id
        })
    df = pd.DataFrame(data)
    df['timestamp'] = pd.to_datetime(df['timestamp'])
    
    # Summary metrics
    st.subheader("Dataset Summary")
    col1, col2, col3, col4 = st.columns(4)
    col1.metric("Observations", len(df))
    col2.metric("Webcams", int(df['webcam'].nunique()))
    col3.metric("Species", int(df['species'].nunique()))
    col4.metric("Sessions", int(df['session'].nunique()))
    
    st.divider()
    
    # Visualizations
    col1, col2 = st.columns(2)
    
    with col1:
        st.subheader("Behavior Distribution")
        behavior_counts = df['behavior'].value_counts()
        fig = px.pie(
            values=behavior_counts.values, 
            names=behavior_counts.index,
            title="All Behaviors"
        )
        st.plotly_chart(fig, use_container_width=True)
    
    with col2:
        st.subheader("Activity by Species")
        fig = px.box(df, x='species', y='activity', title="Activity Levels")
        st.plotly_chart(fig, use_container_width=True)
    
    st.divider()
    
    # Synchrony analysis
    st.subheader("Synchrony Over Time")
    
    calc = SynchronyCalculator(db, registry)
    baseline = calc.calculate_baseline_chance(observations)
    
    st.metric("Baseline (Chance)", f"{baseline:.1%}")
    
    # Calculate synchrony for recent time windows
    if len(df) > 10:
        st.info("Synchrony calculated for paired observations within 30-second windows")
        
        # Activity over time
        fig = px.scatter(
            df, x='timestamp', y='activity', 
            color='species', title="Activity Over Time"
        )
        st.plotly_chart(fig, use_container_width=True)
    
    st.divider()
    
    # GCP Correlation
    st.subheader("GCP Correlation")
    
    gcp_data = df[df['gcp_z'].notna()].copy()
    if len(gcp_data) > 5:
        fig = px.scatter(
            gcp_data, x='gcp_z', y='activity', 
            color='species', title="Activity vs GCP Z-Score"
        )
        st.plotly_chart(fig, use_container_width=True)
        
        corr = float(gcp_data['gcp_z'].corr(gcp_data['activity']))
        
        col1, col2 = st.columns(2)
        col1.metric("Correlation", f"{corr:.3f}")
        
        if abs(corr) > 0.3:
            col2.success("Significant correlation!")
        elif abs(corr) > 0.1:
            col2.info("Weak correlation")
        else:
            col2.warning("No correlation")
    else:
        st.info("Need more GCP-tagged observations for correlation analysis")


def render_webcam_registry(registry: WebcamRegistry):
    """Webcam management"""
    st.header("Webcam Registry")
    
    # Current webcams
    data = []
    for name, cam in registry.webcams.items():
        data.append({
            "Name": name,
            "Species": cam.species,
            "Location": cam.location,
            "Est. R": cam.estimated_r,
            "Active": "✓" if cam.active else "✗"
        })
    
    st.dataframe(data, use_container_width=True)
    
    # Webcam links
    st.divider()
    st.subheader("Quick Access")
    
    cols = st.columns(4)
    for i, (name, cam) in enumerate(registry.webcams.items()):
        with cols[i % 4]:
            st.link_button(f"🔗 {cam.species.title()}", cam.url, use_container_width=True)


def render_database_info(db: Database):
    """Database information"""
    st.header("Database Information")
    
    st.subheader("Storage")
    st.code(str(DB_FILE))
    
    # Table counts
    st.subheader("Table Statistics")
    
    with sqlite3.connect(db.db_path) as conn:
        tables = ["observations", "gcp_readings", "sessions", "webcams", "synchrony_scores"]
        
        for table in tables:
            try:
                count = conn.execute(f"SELECT COUNT(*) FROM {table}").fetchone()[0]
                st.metric(table.title(), count)
            except Exception:
                st.metric(table.title(), "N/A")
    
    st.divider()
    
    # Recent observations
    st.subheader("Recent Observations")
    
    with sqlite3.connect(db.db_path) as conn:
        df = pd.read_sql_query(
            """SELECT timestamp_utc, webcam_name, species, behavior_code, 
                      activity_level, mood_score, gcp_z_score 
               FROM observations 
               ORDER BY timestamp_utc DESC LIMIT 20""",
            conn
        )
    
    st.dataframe(df, use_container_width=True)


if __name__ == "__main__":
    main()

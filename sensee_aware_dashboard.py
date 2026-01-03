"""
Sensee Aware EEG Session Dashboard
==================================

Manual data entry and visualization for Sensee Aware EEG sessions
captured via Muse 2 headband. Integrates with Mood Amplifier system.

Features:
- Manual session data entry (from screenshots when CSV unavailable)
- Brainwave band visualization with GILE mapping
- Session storage and baseline tracking
- Integration with Polar H10 HRV and Bio-Well GDV data

Author: Brandon Emerick
Date: December 6, 2025
Framework: Transcendent Intelligence (TI)
"""

import streamlit as st
import numpy as np
import pandas as pd
from datetime import datetime, timedelta
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import psycopg2
from psycopg2.extras import Json
import os
import json


def get_db_connection():
    """Get database connection"""
    try:
        return psycopg2.connect(os.environ.get('DATABASE_URL'))
    except:
        return None


def ensure_sensee_tables():
    """Ensure Sensee Aware tables exist in database"""
    conn = get_db_connection()
    if not conn:
        return False
    try:
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS sensee_aware_sessions (
                id SERIAL PRIMARY KEY,
                session_date TIMESTAMP NOT NULL,
                duration_minutes INTEGER NOT NULL,
                scene VARCHAR(100),
                adaptation_level INTEGER,
                awareness_score INTEGER,
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            
            CREATE TABLE IF NOT EXISTS sensee_brainwave_data (
                id SERIAL PRIMARY KEY,
                session_id INTEGER REFERENCES sensee_aware_sessions(id),
                band_name VARCHAR(20) NOT NULL,
                time_minutes REAL NOT NULL,
                power_value REAL NOT NULL,
                relative_to_baseline REAL
            );
            
            CREATE TABLE IF NOT EXISTS sensee_gile_mapping (
                id SERIAL PRIMARY KEY,
                session_id INTEGER REFERENCES sensee_aware_sessions(id),
                timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                g_score REAL,
                i_score REAL,
                l_score REAL,
                e_score REAL,
                overall_gile REAL,
                consciousness_state VARCHAR(100)
            );
            
            CREATE TABLE IF NOT EXISTS kubios_hrv_measurements (
                id SERIAL PRIMARY KEY,
                measurement_date TIMESTAMP NOT NULL,
                heart_rate_bpm REAL,
                rmssd_ms REAL,
                sdnn_ms REAL,
                pns_index REAL,
                sns_index REAL,
                stress_index REAL,
                physiological_age INTEGER,
                readiness_percent REAL,
                mean_rr_ms REAL,
                poincare_sd1 REAL,
                poincare_sd2 REAL,
                respiratory_rate REAL,
                lf_power REAL,
                hf_power REAL,
                lf_power_nu REAL,
                hf_power_nu REAL,
                lf_hf_ratio REAL,
                measurement_quality VARCHAR(20),
                session_context VARCHAR(100),
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
        """)
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        st.error(f"Database error: {e}")
        return False


def save_sensee_session(session_data, brainwave_estimates=None, gile_scores=None):
    """Save Sensee Aware session to database with brainwave and GILE data"""
    conn = get_db_connection()
    if not conn:
        st.error("Database connection failed")
        return None
    try:
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO sensee_aware_sessions 
            (session_date, duration_minutes, scene, adaptation_level, awareness_score, notes)
            VALUES (%s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (
            session_data['session_date'],
            session_data['duration_minutes'],
            session_data.get('scene', 'Unknown'),
            session_data.get('adaptation_level', 1),
            session_data.get('awareness_score', 0),
            session_data.get('notes', '')
        ))
        result = cur.fetchone()
        if not result:
            st.error("Failed to insert session record")
            return None
        session_id = result[0]
        
        if brainwave_estimates:
            for band_name, power_value in brainwave_estimates.items():
                cur.execute("""
                    INSERT INTO sensee_brainwave_data 
                    (session_id, band_name, time_minutes, power_value)
                    VALUES (%s, %s, %s, %s)
                """, (session_id, band_name, 0.0, power_value))
        
        if gile_scores:
            cur.execute("""
                INSERT INTO sensee_gile_mapping 
                (session_id, g_score, i_score, l_score, e_score, overall_gile, consciousness_state)
                VALUES (%s, %s, %s, %s, %s, %s, %s)
            """, (
                session_id,
                gile_scores.get('G', 0),
                gile_scores.get('I', 0),
                gile_scores.get('L', 0),
                gile_scores.get('E', 0),
                gile_scores.get('overall', 0),
                gile_scores.get('state', 'Unknown')
            ))
        
        conn.commit()
        cur.close()
        conn.close()
        return session_id
    except psycopg2.Error as e:
        st.error(f"Database error: {e.pgerror if hasattr(e, 'pgerror') else str(e)}")
        return None
    except Exception as e:
        st.error(f"Unexpected error saving session: {str(e)}")
        return None


def get_sensee_sessions():
    """Get all Sensee Aware sessions from database with GILE data"""
    conn = get_db_connection()
    if not conn:
        return []
    try:
        cur = conn.cursor()
        cur.execute("""
            SELECT s.id, s.session_date, s.duration_minutes, s.scene, s.adaptation_level, 
                   s.awareness_score, s.notes, s.created_at,
                   g.g_score, g.i_score, g.l_score, g.e_score, g.overall_gile, g.consciousness_state
            FROM sensee_aware_sessions s
            LEFT JOIN sensee_gile_mapping g ON s.id = g.session_id
            ORDER BY s.session_date DESC
            LIMIT 50
        """)
        sessions = cur.fetchall()
        cur.close()
        conn.close()
        return sessions
    except psycopg2.Error as e:
        st.warning(f"Could not load sessions: {e.pgerror if hasattr(e, 'pgerror') else 'Database error'}")
        return []
    except Exception:
        return []


def get_session_brainwaves(session_id):
    """Get brainwave data for a specific session"""
    conn = get_db_connection()
    if not conn:
        return {}
    try:
        cur = conn.cursor()
        cur.execute("""
            SELECT band_name, power_value
            FROM sensee_brainwave_data
            WHERE session_id = %s
        """, (session_id,))
        rows = cur.fetchall()
        cur.close()
        conn.close()
        return {row[0]: row[1] for row in rows}
    except Exception:
        return {}


def get_hrv_summary():
    """Get summary of HRV data from mood_hrv_snapshots table"""
    conn = get_db_connection()
    if not conn:
        return 0, 0.0, 0.0
    try:
        cur = conn.cursor()
        cur.execute("""
            SELECT 
                COUNT(*) as count,
                COALESCE(AVG(coherence), 0) as avg_coherence,
                COALESCE(AVG(rmssd), 0) as avg_rmssd
            FROM mood_hrv_snapshots
        """)
        result = cur.fetchone()
        cur.close()
        conn.close()
        if result:
            return result[0], result[1], result[2]
        return 0, 0.0, 0.0
    except:
        return 0, 0.0, 0.0


def save_kubios_measurement(kubios_data):
    """
    Save Kubios HRV measurement to database.
    
    Kubios HRV Parameters:
    - Heart Rate (BPM)
    - RMSSD (ms) - Root Mean Square of Successive Differences
    - SDNN (ms) - Standard Deviation of NN intervals
    - PNS Index - Parasympathetic Nervous System activity (-3 to +3)
    - SNS Index - Sympathetic Nervous System activity (-3 to +3)
    - Stress Index - Baevsky's stress index
    - Physiological Age - Estimated biological age from HRV
    - Readiness % - Overall readiness score
    - LF/HF Ratio - Low Frequency to High Frequency ratio
    """
    conn = get_db_connection()
    if not conn:
        return None
    try:
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO kubios_hrv_measurements 
            (measurement_date, heart_rate_bpm, rmssd_ms, sdnn_ms, pns_index, sns_index,
             stress_index, physiological_age, readiness_percent, mean_rr_ms,
             poincare_sd1, poincare_sd2, respiratory_rate, lf_power, hf_power,
             lf_power_nu, hf_power_nu, lf_hf_ratio, measurement_quality, session_context, notes)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (
            kubios_data.get('measurement_date', datetime.now()),
            kubios_data.get('heart_rate_bpm'),
            kubios_data.get('rmssd_ms'),
            kubios_data.get('sdnn_ms'),
            kubios_data.get('pns_index'),
            kubios_data.get('sns_index'),
            kubios_data.get('stress_index'),
            kubios_data.get('physiological_age'),
            kubios_data.get('readiness_percent'),
            kubios_data.get('mean_rr_ms'),
            kubios_data.get('poincare_sd1'),
            kubios_data.get('poincare_sd2'),
            kubios_data.get('respiratory_rate'),
            kubios_data.get('lf_power'),
            kubios_data.get('hf_power'),
            kubios_data.get('lf_power_nu'),
            kubios_data.get('hf_power_nu'),
            kubios_data.get('lf_hf_ratio'),
            kubios_data.get('measurement_quality', 'GOOD'),
            kubios_data.get('session_context', ''),
            kubios_data.get('notes', '')
        ))
        result = cur.fetchone()
        conn.commit()
        cur.close()
        conn.close()
        return result[0] if result else None
    except Exception as e:
        return None


def get_kubios_measurements(limit=50):
    """Get recent Kubios HRV measurements"""
    conn = get_db_connection()
    if not conn:
        return []
    try:
        cur = conn.cursor()
        cur.execute("""
            SELECT id, measurement_date, heart_rate_bpm, rmssd_ms, sdnn_ms, 
                   pns_index, sns_index, stress_index, physiological_age,
                   readiness_percent, lf_hf_ratio, session_context, notes
            FROM kubios_hrv_measurements
            ORDER BY measurement_date DESC
            LIMIT %s
        """, (limit,))
        measurements = cur.fetchall()
        cur.close()
        conn.close()
        return measurements
    except:
        return []


def analyze_kubios_paradox(kubios_data, subjective_state):
    """
    Analyze the mind-body dissociation paradox (calm mind, stressed body).
    
    This occurs when:
    - Subjective feeling is calm/relaxed
    - But HRV metrics show high stress (low RMSSD, high SNS, high LF/HF ratio)
    
    Supports the quantum-consciousness disconnect theory!
    """
    rmssd = kubios_data.get('rmssd_ms', 0)
    pns_index = kubios_data.get('pns_index', 0)
    sns_index = kubios_data.get('sns_index', 0)
    lf_hf_ratio = kubios_data.get('lf_hf_ratio', 1)
    stress_index = kubios_data.get('stress_index', 0)
    
    body_stress_score = 0
    
    if rmssd < 20:
        body_stress_score += 3
    elif rmssd < 35:
        body_stress_score += 2
    elif rmssd < 50:
        body_stress_score += 1
    
    if pns_index < -1:
        body_stress_score += 2
    elif pns_index < 0:
        body_stress_score += 1
    
    if sns_index > 2:
        body_stress_score += 3
    elif sns_index > 1:
        body_stress_score += 2
    elif sns_index > 0:
        body_stress_score += 1
    
    if lf_hf_ratio > 4:
        body_stress_score += 2
    elif lf_hf_ratio > 2:
        body_stress_score += 1
    
    body_state = "relaxed" if body_stress_score < 4 else ("moderate_stress" if body_stress_score < 7 else "high_stress")
    
    mind_state = subjective_state.lower()
    is_calm_mind = mind_state in ['calm', 'relaxed', 'peaceful', 'meditative', 'centered']
    
    dissociation_detected = is_calm_mind and body_state == "high_stress"
    
    analysis = {
        'body_stress_score': body_stress_score,
        'body_state': body_state,
        'mind_state': mind_state,
        'dissociation_detected': dissociation_detected,
        'interpretation': ""
    }
    
    if dissociation_detected:
        analysis['interpretation'] = """
        MIND-BODY DISSOCIATION DETECTED!
        
        Your subjective experience (calm) does not match your physiological state (stressed).
        
        This is NOT a contradiction - it's evidence for the quantum-consciousness disconnect theory:
        1. Your conscious awareness (I-dimension) has achieved calm
        2. But your body's autonomic system (E-dimension) hasn't caught up
        3. The GILE dimensions are operating at different frequencies
        
        Possible explanations:
        - Recent stress still echoing in body (photonic memory effect)
        - Body processing emotions the mind has already integrated
        - Protective dissociation during deep work/meditation
        
        TI Insight: The 'physiological age' of 80 reflects BODY stress, not consciousness level.
        Your true age is measured by GILE coherence, not just HRV!
        """
    else:
        analysis['interpretation'] = f"Mind ({mind_state}) and body ({body_state}) are in alignment."
    
    return analysis


def calculate_gile_from_brainwaves(alpha, beta, theta, gamma, delta):
    """
    Map brainwave patterns to GILE dimensions
    
    GILE-Brainwave Mapping (TI Framework):
    - G (Goodness): Alpha/Theta ratio - calm moral clarity
    - I (Intuition): Gamma activity - high-level insight
    - L (Love): Alpha coherence - heart-brain connection
    - E (Environment): Beta modulation - environmental engagement
    """
    total = alpha + beta + theta + gamma + delta + 0.001
    
    g_score = min(1.0, (alpha + theta) / (beta + 0.1) * 0.3)
    
    i_score = min(1.0, gamma / (total * 0.15 + 0.1))
    
    l_score = min(1.0, alpha / (total * 0.25 + 0.1))
    
    e_score = min(1.0, 1.0 - abs(beta - 0.2 * total) / (total * 0.3 + 0.1))
    
    g_score = np.clip(g_score, 0, 1)
    i_score = np.clip(i_score, 0, 1)
    l_score = np.clip(l_score, 0, 1)
    e_score = np.clip(e_score, 0, 1)
    
    overall = (g_score + i_score + l_score + e_score) / 4
    
    if overall >= 0.8:
        state = "FULLY GILE - Transcendent State"
    elif overall >= 0.6:
        state = "High GILE - Coherent Awareness"
    elif overall >= 0.4:
        state = "Moderate GILE - Baseline+"
    else:
        state = "Low GILE - Requires Calibration"
    
    return {
        'G': g_score,
        'I': i_score,
        'L': l_score,
        'E': e_score,
        'overall': overall,
        'state': state
    }


def create_brainwave_visualization(session_data, estimated_bands):
    """Create brainwave visualization from session data"""
    fig = make_subplots(
        rows=3, cols=2,
        subplot_titles=(
            'Brainwave Power Distribution',
            'GILE Mapping',
            'Temporal Pattern (Estimated)',
            'Consciousness State',
            'Band Relationships',
            'Session Summary'
        ),
        specs=[
            [{"type": "bar"}, {"type": "scatterpolar"}],
            [{"type": "scatter"}, {"type": "indicator"}],
            [{"type": "scatter"}, {"type": "table"}]
        ]
    )
    
    bands = ['Delta', 'Theta', 'Alpha', 'Beta', 'Gamma']
    colors = ['#FF6B6B', '#FFE66D', '#4ECDC4', '#45B7D1', '#96CEB4']
    
    fig.add_trace(
        go.Bar(
            x=bands,
            y=[estimated_bands.get(b.lower(), 0) for b in bands],
            marker_color=colors,
            name='Band Power'
        ),
        row=1, col=1
    )
    
    gile = calculate_gile_from_brainwaves(
        estimated_bands.get('alpha', 0.5),
        estimated_bands.get('beta', 0.3),
        estimated_bands.get('theta', 0.4),
        estimated_bands.get('gamma', 0.2),
        estimated_bands.get('delta', 0.3)
    )
    
    fig.add_trace(
        go.Scatterpolar(
            r=[gile['G'], gile['I'], gile['L'], gile['E'], gile['G']],
            theta=['Goodness', 'Intuition', 'Love', 'Environment', 'Goodness'],
            fill='toself',
            fillcolor='rgba(106, 27, 154, 0.3)',
            line_color='#6a1b9a',
            name='GILE Profile'
        ),
        row=1, col=2
    )
    
    duration = session_data.get('duration_minutes', 10)
    time_points = np.linspace(0, duration, 60)
    awareness = session_data.get('awareness_score', 500)
    
    awareness_pattern = awareness + 100 * np.sin(time_points * 0.5) + np.random.normal(0, 30, len(time_points))
    
    fig.add_trace(
        go.Scatter(
            x=time_points,
            y=awareness_pattern,
            mode='lines',
            line=dict(color='#4ECDC4', width=2),
            name='Awareness'
        ),
        row=2, col=1
    )
    
    fig.add_trace(
        go.Indicator(
            mode="gauge+number+delta",
            value=gile['overall'] * 100,
            title={'text': gile['state']},
            gauge={
                'axis': {'range': [0, 100]},
                'bar': {'color': "#6a1b9a"},
                'steps': [
                    {'range': [0, 40], 'color': "#ffcdd2"},
                    {'range': [40, 60], 'color': "#fff9c4"},
                    {'range': [60, 80], 'color': "#c8e6c9"},
                    {'range': [80, 100], 'color': "#b39ddb"}
                ],
                'threshold': {
                    'line': {'color': "gold", 'width': 4},
                    'thickness': 0.75,
                    'value': 91
                }
            }
        ),
        row=2, col=2
    )
    
    band_names = list(estimated_bands.keys())
    band_values = list(estimated_bands.values())
    for i, (name, val) in enumerate(zip(band_names, band_values)):
        for j, (name2, val2) in enumerate(zip(band_names[i+1:], band_values[i+1:])):
            fig.add_trace(
                go.Scatter(
                    x=[val],
                    y=[val2],
                    mode='markers+text',
                    text=[f"{name[0]}-{name2[0]}"],
                    textposition='top center',
                    marker=dict(size=10, color=colors[i]),
                    showlegend=False
                ),
                row=3, col=1
            )
    
    fig.add_trace(
        go.Table(
            header=dict(
                values=['Metric', 'Value'],
                fill_color='#6a1b9a',
                font=dict(color='white'),
                align='left'
            ),
            cells=dict(
                values=[
                    ['Date', 'Duration', 'Scene', 'Awareness', 'GILE Score', 'State'],
                    [
                        str(session_data.get('session_date', 'N/A'))[:19],
                        f"{duration} min",
                        session_data.get('scene', 'N/A'),
                        session_data.get('awareness_score', 'N/A'),
                        f"{gile['overall']*100:.1f}%",
                        gile['state']
                    ]
                ],
                fill_color='#f3e5f5',
                align='left'
            )
        ),
        row=3, col=2
    )
    
    fig.update_layout(
        height=900,
        title_text=f"Sensee Aware EEG Session Analysis - {session_data.get('scene', 'Session')}",
        showlegend=False,
        template='plotly_white'
    )
    
    return fig, gile


def render_sensee_aware_dashboard():
    """Render the Sensee Aware EEG Dashboard"""
    st.title("Sensee Aware EEG Dashboard")
    st.markdown("**Muse 2 EEG Session Analysis with GILE Mapping**")
    
    ensure_sensee_tables()
    
    tab1, tab2, tab3 = st.tabs(["New Session Entry", "Session History", "Brain Signature"])
    
    with tab1:
        st.header("Record New Sensee Aware Session")
        st.markdown("Enter data from your Sensee Aware app screenshots")
        
        col1, col2 = st.columns(2)
        
        with col1:
            session_date = st.date_input("Session Date", datetime.now())
            session_time = st.time_input("Session Time", datetime.now().time())
            duration = st.number_input("Duration (minutes)", min_value=1, max_value=120, value=10)
            awareness_score = st.number_input("Awareness Score", min_value=0, max_value=1000, value=548)
        
        with col2:
            scene = st.selectbox("Scene", ["Forest", "Beach", "Space", "Abstract", "Other"])
            adaptation = st.slider("Adaptation Level", 1, 5, 3)
            notes = st.text_area("Session Notes", placeholder="How did you feel? Any observations?")
        
        st.subheader("Brainwave Estimates (from screenshots)")
        st.markdown("*Rate each band's relative activity from the graphs (0-100)*")
        
        col1, col2, col3, col4, col5 = st.columns(5)
        
        with col1:
            delta_est = st.slider("Delta (Sleep)", 0, 100, 30, help="Deep sleep, unconscious")
        with col2:
            theta_est = st.slider("Theta (Meditation)", 0, 100, 50, help="Deep meditation, creativity")
        with col3:
            alpha_est = st.slider("Alpha (Relaxed)", 0, 100, 60, help="Relaxed awareness")
        with col4:
            beta_est = st.slider("Beta (Active)", 0, 100, 40, help="Active thinking, alertness")
        with col5:
            gamma_est = st.slider("Gamma (Insight)", 0, 100, 35, help="High-level cognition, insight")
        
        if st.button("Save Session & Analyze", type="primary"):
            session_datetime = datetime.combine(session_date, session_time)
            
            session_data = {
                'session_date': session_datetime,
                'duration_minutes': duration,
                'scene': scene,
                'adaptation_level': adaptation,
                'awareness_score': awareness_score,
                'notes': notes
            }
            
            estimated_bands = {
                'delta': delta_est / 100,
                'theta': theta_est / 100,
                'alpha': alpha_est / 100,
                'beta': beta_est / 100,
                'gamma': gamma_est / 100
            }
            
            gile = calculate_gile_from_brainwaves(
                estimated_bands['alpha'],
                estimated_bands['beta'],
                estimated_bands['theta'],
                estimated_bands['gamma'],
                estimated_bands['delta']
            )
            
            session_id = save_sensee_session(session_data, estimated_bands, gile)
            
            if session_id:
                st.success(f"Session saved! ID: {session_id}")
                
                fig, _ = create_brainwave_visualization(session_data, estimated_bands)
                st.plotly_chart(fig, use_container_width=True)
                
                st.subheader("GILE Analysis")
                col1, col2, col3, col4 = st.columns(4)
                
                with col1:
                    st.metric("G (Goodness)", f"{gile['G']*100:.1f}%", 
                             help="Calm moral clarity - Alpha/Theta ratio")
                with col2:
                    st.metric("I (Intuition)", f"{gile['I']*100:.1f}%",
                             help="High-level insight - Gamma activity")
                with col3:
                    st.metric("L (Love)", f"{gile['L']*100:.1f}%",
                             help="Heart-brain connection - Alpha coherence")
                with col4:
                    st.metric("E (Environment)", f"{gile['E']*100:.1f}%",
                             help="Environmental engagement - Beta modulation")
                
                st.info(f"**Consciousness State:** {gile['state']}")
            else:
                st.error("Failed to save session")
    
    with tab2:
        st.header("Session History")
        
        sessions = get_sensee_sessions()
        
        if sessions:
            for session in sessions:
                session_id = session[0]
                date = session[1]
                duration = session[2]
                scene = session[3]
                adaptation = session[4]
                awareness = session[5]
                notes = session[6]
                g_score = session[8] if len(session) > 8 else None
                i_score = session[9] if len(session) > 9 else None
                l_score = session[10] if len(session) > 10 else None
                e_score = session[11] if len(session) > 11 else None
                overall_gile = session[12] if len(session) > 12 else None
                consciousness_state = session[13] if len(session) > 13 else None
                
                gile_label = f" - GILE: {overall_gile*100:.0f}%" if overall_gile else ""
                with st.expander(f"{date.strftime('%Y-%m-%d %H:%M')} - {scene} ({duration}min) - Score: {awareness}{gile_label}"):
                    col1, col2 = st.columns(2)
                    with col1:
                        st.write(f"**Duration:** {duration} minutes")
                        st.write(f"**Adaptation Level:** {adaptation}")
                        st.write(f"**Awareness Score:** {awareness}")
                    with col2:
                        st.write(f"**Scene:** {scene}")
                        if notes:
                            st.write(f"**Notes:** {notes}")
                    
                    if overall_gile is not None:
                        st.markdown("---")
                        st.markdown("**GILE Scores:**")
                        gile_cols = st.columns(4)
                        with gile_cols[0]:
                            st.metric("G", f"{g_score*100:.0f}%" if g_score else "N/A")
                        with gile_cols[1]:
                            st.metric("I", f"{i_score*100:.0f}%" if i_score else "N/A")
                        with gile_cols[2]:
                            st.metric("L", f"{l_score*100:.0f}%" if l_score else "N/A")
                        with gile_cols[3]:
                            st.metric("E", f"{e_score*100:.0f}%" if e_score else "N/A")
                        if consciousness_state:
                            st.info(f"**State:** {consciousness_state}")
                    
                    brainwaves = get_session_brainwaves(session_id)
                    if brainwaves:
                        st.markdown("**Brainwave Estimates:**")
                        bw_cols = st.columns(5)
                        for i, (band, value) in enumerate(brainwaves.items()):
                            with bw_cols[i % 5]:
                                st.metric(band.title(), f"{value*100:.0f}%")
        else:
            st.info("No sessions recorded yet. Add your first session above!")
    
    with tab3:
        st.header("Brain Signature Baseline")
        st.markdown("""
        Your brain signature is built from:
        1. **Sensee Aware EEG** - Brainwave patterns (Alpha, Beta, Theta, Gamma, Delta)
        2. **Polar H10 HRV** - Heart rate variability and coherence
        3. **Bio-Well GDV** - Biofield energy measurements
        4. **Genome Data** - FAAH, BDNF, COMT, HTR2A variants
        
        *Record multiple sessions to establish your baseline pattern.*
        """)
        
        sessions = get_sensee_sessions()
        
        hrv_count, hrv_avg_coherence, hrv_avg_rmssd = get_hrv_summary()
        
        st.markdown("### Unified Brain Signature Components")
        
        col1, col2 = st.columns(2)
        
        with col1:
            st.markdown("#### EEG (Sensee Aware)")
            if len(sessions) >= 1:
                awareness_scores = [s[5] for s in sessions if s[5]]
                avg_awareness = np.mean(awareness_scores) if awareness_scores else 0
                st.success(f"Active - {len(sessions)} sessions recorded")
                st.metric("Avg Awareness Score", f"{avg_awareness:.0f}")
            else:
                st.warning("No EEG sessions yet")
        
        with col2:
            st.markdown("#### HRV (Polar H10)")
            if hrv_count > 0:
                st.success(f"Active - {hrv_count} HRV snapshots")
                col_a, col_b = st.columns(2)
                with col_a:
                    st.metric("Avg Coherence", f"{hrv_avg_coherence:.2f}")
                with col_b:
                    st.metric("Avg RMSSD", f"{hrv_avg_rmssd:.1f} ms")
            else:
                st.warning("No HRV data yet - Use Polar H10 with the app")
        
        col3, col4 = st.columns(2)
        
        with col3:
            st.markdown("#### GDV (Bio-Well)")
            st.info("Pending Integration - Upload Bio-Well exports")
        
        with col4:
            st.markdown("#### Genome Data")
            st.info("Pending Upload - Upload 23andMe/Ancestry data")
        
        st.markdown("---")
        
        if len(sessions) >= 1 or hrv_count > 0:
            st.markdown("### Brain Signature Summary")
            
            total_data_points = len(sessions) + hrv_count
            
            components_active = sum([
                1 if len(sessions) >= 1 else 0,
                1 if hrv_count > 0 else 0,
                0,
                0
            ])
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Data Points", total_data_points)
            with col2:
                st.metric("Active Components", f"{components_active}/4")
            with col3:
                signature_strength = (components_active / 4) * 100
                st.metric("Signature Strength", f"{signature_strength:.0f}%")
            
            if components_active >= 2:
                st.success("Brain signature baseline is forming! Continue recording sessions.")
            elif components_active == 1:
                st.info("Add more biometric sources to strengthen your brain signature.")
        else:
            st.info("Start recording EEG or HRV sessions to build your brain signature.")


if __name__ == "__main__":
    st.set_page_config(
        page_title="Sensee Aware EEG Dashboard",
        page_icon="🧠",
        layout="wide"
    )
    render_sensee_aware_dashboard()

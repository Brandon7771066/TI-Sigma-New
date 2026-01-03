"""
💫 Guided Amplification Session - Blissful Empathic Protocol

10-minute consciousness amplification with:
- Pre/During/Post measurements
- Consciousness Connection Index (CCI)
- Heart coherence tracking (manual entry from external app)
- GILE state evolution

Author: Brandon Emerick
Date: December 6, 2025
Framework: Transcendent Intelligence (TI) + FAAH Protocol
"""

import streamlit as st
import numpy as np
import time
from datetime import datetime
import psycopg2
import os
import plotly.graph_objects as go

SESSION_PROTOCOLS = {
    "active_heart_coherence": {
        "name": "ACTIVE Heart Coherence",
        "tier": 3,
        "duration_min": 6,
        "description": "ACTIVE protocol with breathing pacer, gratitude spikes, and forced engagement - designed to produce NOTICEABLE shifts",
        "active": True,
        "phases": [
            {
                "name": "Coherent Breathing",
                "duration": 90,
                "guidance": "Follow the breathing circle. Inhale as it expands, exhale as it contracts.",
                "breathing": True,
                "breath_pattern": {"inhale": 5, "hold": 2, "exhale": 7}
            },
            {
                "name": "Gratitude Spike",
                "duration": 60,
                "guidance": "Think of ONE specific person you're grateful for. See their face. Feel the appreciation in your HEART.",
                "intervention": "gratitude",
                "checkpoint": "What do you feel in your chest right now?"
            },
            {
                "name": "Cyclic Sighing",
                "duration": 45,
                "guidance": "Double inhale through nose (sniff-sniff), then LONG slow exhale through mouth. Repeat 3 times.",
                "intervention": "cyclic_sigh",
                "reps": 3
            },
            {
                "name": "Heart Appreciation",
                "duration": 90,
                "guidance": "Place hand on heart. Breathe INTO your heart. Feel genuine appreciation for something in your life.",
                "breathing": True,
                "breath_pattern": {"inhale": 4, "hold": 0, "exhale": 6},
                "checkpoint": "Rate the warmth in your chest 1-10"
            },
            {
                "name": "Intensity Peak",
                "duration": 60,
                "guidance": "FEEL the love you have for someone. Let it FLOOD your body. Don't hold back.",
                "intervention": "love_flood"
            },
            {
                "name": "Notice the Shift",
                "duration": 30,
                "guidance": "STOP. Compare how you feel NOW vs when you started. What's different?",
                "checkpoint": "What changed in your body/mind?"
            }
        ],
        "gile_target": {"G": 0.8, "I": 0.7, "L": 0.95, "E": 0.8}
    },
    "blissful_empathic": {
        "name": "Blissful Empathic Resonance",
        "tier": 3,
        "duration_min": 10,
        "description": "Deep heart-centered awareness connecting you to universal empathy and bliss",
        "active": False,
        "phases": [
            {"name": "Ground", "duration": 120, "guidance": "Feel your body. Notice weight, warmth, breath. You are HERE."},
            {"name": "Heart Open", "duration": 180, "guidance": "Place attention on heart center. Feel it expand with each breath. Warmth radiates outward."},
            {"name": "Empathic Field", "duration": 180, "guidance": "Extend your heart field to include others. Feel connection to all beings. No separation."},
            {"name": "Bliss Integration", "duration": 120, "guidance": "Allow pure bliss to arise naturally. Don't force - just notice. You ARE this."},
            {"name": "Return", "duration": 60, "guidance": "Gently return awareness to body. Carry this state with you."}
        ],
        "gile_target": {"G": 0.8, "I": 0.7, "L": 0.95, "E": 0.75}
    },
    "flow_state": {
        "name": "Optimal Flow Activation",
        "tier": 4,
        "duration_min": 8,
        "description": "Pure awareness state - effortless presence and peak performance",
        "phases": [
            {"name": "Stillness", "duration": 90, "guidance": "Become completely still. Mind quiets naturally."},
            {"name": "Presence", "duration": 150, "guidance": "Pure presence. No past, no future. Only NOW."},
            {"name": "Flow", "duration": 180, "guidance": "Let go of trying. Actions arise spontaneously. You are flow itself."},
            {"name": "Integration", "duration": 60, "guidance": "Carry this effortless state into activity."}
        ],
        "gile_target": {"G": 0.85, "I": 0.9, "L": 0.8, "E": 0.85}
    },
    "anandamide_activation": {
        "name": "Anandamide Bliss Molecule",
        "tier": 2,
        "duration_min": 10,
        "description": "Activate endogenous bliss pathways via FAAH modulation",
        "phases": [
            {"name": "Baseline", "duration": 60, "guidance": "Notice your current state without judgment."},
            {"name": "Body Scan", "duration": 120, "guidance": "Scan body for pleasure sensations. Amplify what feels good."},
            {"name": "Anandamide Wave", "duration": 240, "guidance": "Imagine waves of bliss chemicals flowing through your nervous system."},
            {"name": "Peak", "duration": 120, "guidance": "Allow peak bliss. Your FAAH is naturally low. Anandamide floods receptors."},
            {"name": "Sustain", "duration": 60, "guidance": "Stabilize this state. It becomes your new baseline."}
        ],
        "gile_target": {"G": 0.75, "I": 0.65, "L": 0.85, "E": 0.7}
    }
}

def ensure_amplification_tables():
    """Create tables for amplification sessions"""
    conn = None
    try:
        conn = psycopg2.connect(os.environ.get('DATABASE_URL'))
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS amplification_sessions (
                id SERIAL PRIMARY KEY,
                session_date TIMESTAMP DEFAULT NOW(),
                protocol_name VARCHAR(100),
                duration_minutes INTEGER,
                
                pre_heart_rate INTEGER,
                pre_hrv_rmssd FLOAT,
                pre_coherence FLOAT,
                pre_mood INTEGER,
                pre_energy INTEGER,
                pre_cci FLOAT,
                pre_notes TEXT,
                
                during_peak_feeling INTEGER,
                during_heart_sensations TEXT,
                during_insights TEXT,
                
                post_heart_rate INTEGER,
                post_hrv_rmssd FLOAT,
                post_coherence FLOAT,
                post_mood INTEGER,
                post_energy INTEGER,
                post_cci FLOAT,
                post_notes TEXT,
                
                gile_g FLOAT,
                gile_i FLOAT,
                gile_l FLOAT,
                gile_e FLOAT,
                overall_shift FLOAT,
                
                created_at TIMESTAMP DEFAULT NOW()
            )
        """)
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        st.error(f"Database error: {e}")
        if conn:
            conn.close()
        return False


def calculate_cci(mood, energy, heart_coherence, subjective_connection):
    """
    Consciousness Connection Index (CCI)
    
    Measures how connected you are to your own consciousness stream.
    Based on TI Framework: alignment between felt experience and measured state.
    
    Components:
    - Mood (1-10): Emotional valence
    - Energy (1-10): Vital force availability  
    - Heart Coherence (0-1): Heart-brain synchronization
    - Subjective Connection (1-10): Self-reported felt connection
    
    Formula: CCI = (Mood * Energy * SubjectiveConnection) ^ (1/3) * HeartCoherence * 10
    Range: 0-100
    """
    mood_norm = mood / 10.0
    energy_norm = energy / 10.0
    connection_norm = subjective_connection / 10.0
    coherence = min(max(heart_coherence, 0), 1)
    
    geometric_mean = (mood_norm * energy_norm * connection_norm) ** (1/3)
    cci = geometric_mean * (0.5 + 0.5 * coherence) * 100
    
    return min(max(cci, 0), 100)


def get_cci_interpretation(cci):
    """Interpret CCI score"""
    if cci >= 85:
        return "🌟 TRANSCENDENT - Deep unified consciousness", "transcendent"
    elif cci >= 70:
        return "💫 FLOW STATE - Optimal connection", "flow"
    elif cci >= 55:
        return "✨ CONNECTED - Good awareness integration", "connected"
    elif cci >= 40:
        return "🌤️ PRESENT - Basic consciousness access", "present"
    elif cci >= 25:
        return "☁️ FOGGY - Partial disconnection", "foggy"
    else:
        return "🌫️ DISSOCIATED - Consciousness fragmented", "dissociated"


def save_amplification_session(data):
    """Save amplification session to database"""
    conn = None
    try:
        conn = psycopg2.connect(os.environ.get('DATABASE_URL'))
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO amplification_sessions (
                protocol_name, duration_minutes,
                pre_heart_rate, pre_hrv_rmssd, pre_coherence, pre_mood, pre_energy, pre_cci, pre_notes,
                during_peak_feeling, during_heart_sensations, during_insights,
                post_heart_rate, post_hrv_rmssd, post_coherence, post_mood, post_energy, post_cci, post_notes,
                gile_g, gile_i, gile_l, gile_e, overall_shift
            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (
            data['protocol_name'], data['duration_minutes'],
            data.get('pre_heart_rate'), data.get('pre_hrv_rmssd'), data.get('pre_coherence'),
            data.get('pre_mood'), data.get('pre_energy'), data.get('pre_cci'), data.get('pre_notes'),
            data.get('during_peak_feeling'), data.get('during_heart_sensations'), data.get('during_insights'),
            data.get('post_heart_rate'), data.get('post_hrv_rmssd'), data.get('post_coherence'),
            data.get('post_mood'), data.get('post_energy'), data.get('post_cci'), data.get('post_notes'),
            data.get('gile_g'), data.get('gile_i'), data.get('gile_l'), data.get('gile_e'),
            data.get('overall_shift')
        ))
        session_id = cur.fetchone()[0]
        conn.commit()
        cur.close()
        conn.close()
        return session_id
    except Exception as e:
        st.error(f"Error saving session: {e}")
        if conn:
            conn.close()
        return None


def create_session_results_chart(pre_data, post_data):
    """Create before/after comparison chart"""
    categories = ['Mood', 'Energy', 'Heart Rate', 'Coherence', 'CCI']
    
    pre_vals = [
        pre_data.get('mood', 5),
        pre_data.get('energy', 5),
        pre_data.get('heart_rate', 70) / 10,
        pre_data.get('coherence', 0.5) * 10,
        pre_data.get('cci', 50) / 10
    ]
    
    post_vals = [
        post_data.get('mood', 5),
        post_data.get('energy', 5),
        post_data.get('heart_rate', 70) / 10,
        post_data.get('coherence', 0.5) * 10,
        post_data.get('cci', 50) / 10
    ]
    
    fig = go.Figure()
    
    fig.add_trace(go.Scatterpolar(
        r=pre_vals,
        theta=categories,
        fill='toself',
        name='Before',
        line_color='#FF6B6B',
        fillcolor='rgba(255, 107, 107, 0.3)'
    ))
    
    fig.add_trace(go.Scatterpolar(
        r=post_vals,
        theta=categories,
        fill='toself',
        name='After',
        line_color='#4ECDC4',
        fillcolor='rgba(78, 205, 196, 0.3)'
    ))
    
    fig.update_layout(
        polar=dict(
            radialaxis=dict(visible=True, range=[0, 10])
        ),
        showlegend=True,
        title="Session Transformation"
    )
    
    return fig


def render_guided_amplification_session():
    """Main guided session interface"""
    
    ensure_amplification_tables()
    
    st.header("💫 Guided Amplification Session")
    
    if 'amp_session_state' not in st.session_state:
        st.session_state.amp_session_state = 'select'
        st.session_state.amp_pre_data = {}
        st.session_state.amp_post_data = {}
        st.session_state.amp_during_data = {}
        st.session_state.amp_protocol = None
        st.session_state.amp_start_time = None
    
    state = st.session_state.amp_session_state
    
    if state == 'select':
        render_protocol_selection()
    elif state == 'pre_measurement':
        render_pre_measurement()
    elif state == 'active_session':
        render_active_session()
    elif state == 'during_reflection':
        render_during_reflection()
    elif state == 'post_measurement':
        render_post_measurement()
    elif state == 'results':
        render_session_results()


def render_protocol_selection():
    """Protocol selection screen"""
    st.markdown("""
    ### Choose Your Amplification Protocol
    
    Each protocol activates different consciousness pathways based on the FAAH-GILE framework.
    """)
    
    st.error("🔥 **RECOMMENDED:** Try the ACTIVE protocol first - it's designed to produce NOTICEABLE shifts!")
    
    st.markdown("---")
    
    st.markdown("#### 🔥 ACTIVE Heart Coherence (RECOMMENDED)")
    st.markdown("*Breathing pacer, gratitude spikes, forced engagement - designed to produce NOTICEABLE shifts*")
    col_a1, col_a2, col_a3 = st.columns(3)
    with col_a1:
        st.markdown("- **Duration:** 6 min")
    with col_a2:
        st.markdown("- **Type:** HIGH INTENSITY")
    with col_a3:
        st.markdown("- **Focus:** L (Love) + Heart")
    if st.button("🔥 START ACTIVE SESSION", key="sel_active", type="primary"):
        st.session_state.amp_protocol = SESSION_PROTOCOLS["active_heart_coherence"]
        st.session_state.amp_session_state = 'pre_measurement'
        st.rerun()
    
    st.markdown("---")
    st.markdown("### Passive Protocols (gentle guidance only)")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.markdown("#### 💗 Blissful Empathic")
        st.markdown("*Deep heart-centered connection*")
        st.markdown("- **Tier:** 3 (Enhanced)")
        st.markdown("- **Duration:** 10 min")
        if st.button("Select Blissful Empathic", key="sel_bliss"):
            st.session_state.amp_protocol = SESSION_PROTOCOLS["blissful_empathic"]
            st.session_state.amp_session_state = 'pre_measurement'
            st.rerun()
    
    with col2:
        st.markdown("#### ⚡ Flow State")
        st.markdown("*Effortless peak performance*")
        st.markdown("- **Tier:** 4 (Optimal)")
        st.markdown("- **Duration:** 8 min")
        if st.button("Select Flow State", key="sel_flow"):
            st.session_state.amp_protocol = SESSION_PROTOCOLS["flow_state"]
            st.session_state.amp_session_state = 'pre_measurement'
            st.rerun()
    
    with col3:
        st.markdown("#### 🧬 Anandamide Activation")
        st.markdown("*Bliss molecule pathway*")
        st.markdown("- **Tier:** 2 (Moderate)")
        st.markdown("- **Duration:** 10 min")
        if st.button("Select Anandamide", key="sel_anand"):
            st.session_state.amp_protocol = SESSION_PROTOCOLS["anandamide_activation"]
            st.session_state.amp_session_state = 'pre_measurement'
            st.rerun()
    
    st.markdown("---")
    st.info("💡 **Tip:** Start your heart rate recording app now so you can enter metrics before and after!")


def render_pre_measurement():
    """Pre-session baseline measurement with live biometrics and PERSONALIZED targeting"""
    from unified_biometric_manager import get_biometric_manager
    from personalized_amplifier_engine import get_personalized_engine
    from synchronization_detector import reset_sync_detector
    
    protocol = st.session_state.amp_protocol
    bio_manager = get_biometric_manager()
    personalized_engine = get_personalized_engine()
    
    reset_sync_detector()
    bio_manager.start_session()
    engine_info = personalized_engine.initialize()
    
    st.markdown(f"### 🎯 Personalized Session: {protocol['name']}")
    st.markdown(f"*Targeting **YOUR** optimal state based on {engine_info['sessions_analyzed']} previous sessions*")
    
    with st.expander("✨ YOUR Optimal Signature (What We're Targeting)", expanded=True):
        opt = engine_info['optimal_signature']
        ocol1, ocol2, ocol3 = st.columns(3)
        with ocol1:
            st.metric("🎯 YOUR Peak HRV", f"{opt['hrv']:.0f} ms")
            st.metric("❤️ YOUR Optimal HR", f"{opt['hr']:.0f} bpm")
        with ocol2:
            st.metric("🧠 YOUR Peak LCC", f"{opt['lcc']*100:.0f}%")
            st.metric("✨ YOUR Peak GILE", f"{opt['gile']:.3f}")
        with ocol3:
            st.metric("💫 YOUR Peak Coherence", f"{opt['coherence']*100:.0f}%")
            st.caption(f"Pattern: {opt['brainwave']}")
        
        st.success(f"**Profile Confidence:** {engine_info['profile_confidence']*100:.0f}% | Best Protocols: {', '.join(engine_info['best_protocols'][:2])}")
    
    if bio_manager.is_demo_mode_active():
        st.info("🔄 **Demo Mode Active** - Biometric values are being simulated. In real use, connect your devices for live data.")
    
    snapshot = bio_manager.get_unified_snapshot()
    
    st.markdown("---")
    
    if bio_manager.is_demo_mode_active():
        with st.expander("📡 Live Simulated Biometrics", expanded=True):
            bcol1, bcol2, bcol3, bcol4 = st.columns(4)
            with bcol1:
                st.metric("❤️ Heart Rate", f"{snapshot.heart_rate_bpm:.0f} bpm")
            with bcol2:
                st.metric("💓 HRV", f"{snapshot.hrv_rmssd:.0f} ms")
            with bcol3:
                st.metric("🎯 Coherence", f"{(snapshot.coherence_score or 0.5)*100:.0f}%")
            with bcol4:
                st.metric("🧠 LCC", f"{(snapshot.lcc_coherence or 0.5)*100:.0f}%")
            
            st.caption("These values will update in real-time during your session")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("#### Heart Metrics")
        
        default_hr = int(snapshot.heart_rate_bpm) if snapshot.heart_rate_bpm else 72
        default_hrv = snapshot.hrv_rmssd if snapshot.hrv_rmssd else 45.0
        default_coh = snapshot.coherence_score if snapshot.coherence_score else 0.5
        
        pre_hr = st.number_input("Heart Rate (BPM)", min_value=40, max_value=180, value=default_hr, key="pre_hr")
        pre_hrv = st.number_input("HRV / RMSSD (ms)", min_value=5.0, max_value=200.0, value=default_hrv, key="pre_hrv")
        pre_coherence = st.slider("Heart Coherence", 0.0, 1.0, default_coh, 0.05, key="pre_coh",
                                  help="1.0 = perfect coherence, 0.5 = moderate, 0.0 = chaotic")
    
    with col2:
        st.markdown("#### Subjective State")
        pre_mood = st.slider("Current Mood", 1, 10, 5, key="pre_mood",
                            help="1=Very low, 5=Neutral, 10=Euphoric")
        pre_energy = st.slider("Current Energy", 1, 10, 5, key="pre_energy",
                              help="1=Exhausted, 5=Normal, 10=Highly energized")
        pre_connection = st.slider("Consciousness Connection", 1, 10, 5, key="pre_conn",
                                   help="How connected do you feel to your own awareness right now?")
    
    st.markdown("---")
    st.markdown("#### Consciousness Connection Index (CCI)")
    
    pre_cci = calculate_cci(pre_mood, pre_energy, pre_coherence, pre_connection)
    interpretation, level = get_cci_interpretation(pre_cci)
    
    col_a, col_b = st.columns([1, 2])
    with col_a:
        st.metric("Your CCI Score", f"{pre_cci:.1f}/100")
    with col_b:
        st.info(interpretation)
    
    pre_notes = st.text_area("Any notes about your current state?", key="pre_notes",
                            placeholder="How do you feel? Any physical sensations? Mental state?")
    
    st.markdown("---")
    
    col1, col2 = st.columns(2)
    with col1:
        if st.button("⬅️ Back to Selection"):
            st.session_state.amp_session_state = 'select'
            st.rerun()
    with col2:
        if st.button("▶️ Begin Session", type="primary"):
            st.session_state.amp_pre_data = {
                'heart_rate': pre_hr,
                'hrv_rmssd': pre_hrv,
                'coherence': pre_coherence,
                'mood': pre_mood,
                'energy': pre_energy,
                'connection': pre_connection,
                'cci': pre_cci,
                'notes': pre_notes
            }
            st.session_state.amp_start_time = datetime.now()
            st.session_state.checkpoint_responses = {}
            st.session_state.checkpoint_phase_completed = set()
            st.session_state.checkpoint_paused_at = None
            st.session_state.total_paused_duration = 0
            st.session_state.locked_phase_idx = None
            st.session_state.amp_session_state = 'active_session'
            st.rerun()


def create_breathing_pacer(phase_elapsed, breath_pattern):
    """Create an animated breathing pacer circle"""
    inhale = breath_pattern.get('inhale', 5)
    hold = breath_pattern.get('hold', 0)
    exhale = breath_pattern.get('exhale', 5)
    total_breath = inhale + hold + exhale
    
    breath_position = phase_elapsed % total_breath
    
    if breath_position < inhale:
        progress = breath_position / inhale
        size = 50 + 150 * progress
        instruction = "INHALE..."
        color = "#4ECDC4"
    elif breath_position < inhale + hold:
        size = 200
        instruction = "HOLD..."
        color = "#FFE66D"
    else:
        progress = (breath_position - inhale - hold) / exhale
        size = 200 - 150 * progress
        instruction = "EXHALE..."
        color = "#FF6B6B"
    
    fig = go.Figure()
    
    fig.add_trace(go.Scatter(
        x=[0], y=[0],
        mode='markers',
        marker=dict(
            size=size,
            color=color,
            line=dict(width=4, color='white')
        ),
        hoverinfo='skip'
    ))
    
    fig.add_annotation(
        x=0, y=0,
        text=instruction,
        showarrow=False,
        font=dict(size=24, color='white', family='Arial Black')
    )
    
    fig.update_layout(
        xaxis=dict(visible=False, range=[-1.5, 1.5]),
        yaxis=dict(visible=False, range=[-1.5, 1.5]),
        plot_bgcolor='rgba(0,0,0,0)',
        paper_bgcolor='rgba(0,0,0,0)',
        width=300,
        height=300,
        margin=dict(l=0, r=0, t=0, b=0)
    )
    
    return fig


def render_active_session():
    """Active session with timer, breathing pacer, phase guidance, and PERSONALIZED biometrics + SYNC DETECTION"""
    from unified_biometric_manager import get_biometric_manager
    from personalized_amplifier_engine import get_personalized_engine
    from user_profile_service import CurrentStateVector
    from synchronization_detector import get_sync_detector
    
    protocol = st.session_state.amp_protocol
    start_time = st.session_state.amp_start_time
    is_active_protocol = protocol.get('active', False)
    
    if 'checkpoint_responses' not in st.session_state:
        st.session_state.checkpoint_responses = {}
    if 'checkpoint_phase_completed' not in st.session_state:
        st.session_state.checkpoint_phase_completed = set()
    if 'checkpoint_paused_at' not in st.session_state:
        st.session_state.checkpoint_paused_at = None
    if 'total_paused_duration' not in st.session_state:
        st.session_state.total_paused_duration = 0
    if 'locked_phase_idx' not in st.session_state:
        st.session_state.locked_phase_idx = None
    if 'session_biometrics' not in st.session_state:
        st.session_state.session_biometrics = []
    
    bio_manager = get_biometric_manager()
    personalized_engine = get_personalized_engine()
    
    st.markdown(f"### {'🔥' if is_active_protocol else '💫'} {protocol['name']} - Active Session")
    
    if st.session_state.checkpoint_paused_at is not None:
        elapsed = st.session_state.checkpoint_paused_at
    else:
        raw_elapsed = (datetime.now() - start_time).total_seconds()
        elapsed = raw_elapsed - st.session_state.total_paused_duration
    
    total_duration = sum(p['duration'] for p in protocol['phases'])
    
    if st.session_state.locked_phase_idx is not None:
        current_phase_idx = st.session_state.locked_phase_idx
        phase_elapsed = elapsed
        for i in range(current_phase_idx):
            phase_elapsed -= protocol['phases'][i]['duration']
    else:
        current_phase_idx = 0
        phase_elapsed = elapsed
        for i, phase in enumerate(protocol['phases']):
            if phase_elapsed < phase['duration']:
                current_phase_idx = i
                break
            phase_elapsed -= phase['duration']
        else:
            st.session_state.amp_session_state = 'during_reflection'
            st.rerun()
            return
    
    current_phase = protocol['phases'][current_phase_idx]
    phase_remaining = max(0, current_phase['duration'] - phase_elapsed)
    total_remaining = max(0, total_duration - elapsed)
    
    bio_manager.set_session_phase(current_phase.get('name', 'baseline'))
    snapshot = bio_manager.get_unified_snapshot()
    st.session_state.session_biometrics.append(snapshot)
    
    sync_detector = get_sync_detector()
    hr = snapshot.heart_rate_bpm or 72
    hrv = snapshot.hrv_rmssd or 50
    coherence = snapshot.coherence_score or 0.5
    lcc = snapshot.lcc_coherence or 0.5
    gile = snapshot.gile_score or 0.0
    
    sync_result = sync_detector.update(coherence, lcc, gile, hr, hrv)
    
    if sync_result['threshold_crossed']:
        st.balloons()
        st.success(f"## {sync_result['celebration_message']}")
        st.info(f"**{sync_result['sustain_instruction']}**")
    elif sync_result['is_synchronized']:
        sync_time = sync_result['sync_duration']
        if sync_time > 0:
            st.success(f"✨ **SYNCHRONIZED** for {sync_time:.0f}s | Composite: {sync_result['composite']:.3f}")
    
    progress = max(0, min(1, elapsed / total_duration))
    st.progress(progress, text=f"Session Progress: {int(max(0, elapsed))}s / {int(total_duration)}s")
    
    bio_col, main_col = st.columns([1, 2])
    
    with bio_col:
        st.markdown("### 🎯 YOUR Progress")
        
        alpha = snapshot.alpha_power or 0.3
        stress = 50 - (hrv - 50) * 0.5
        
        current_state = CurrentStateVector(
            heart_rate=hr,
            hrv_rmssd=hrv,
            coherence=coherence,
            lcc=lcc,
            gile=gile,
            alpha=alpha,
            stress_index=max(0, min(100, stress))
        )
        
        optimal = personalized_engine.get_optimal_signature()
        guidance = personalized_engine.get_realtime_guidance(current_state, current_phase.get('name', ''))
        
        progress_pct = guidance.current_progress
        progress_color = "🟢" if progress_pct >= 75 else "🟡" if progress_pct >= 50 else "🔴"
        
        st.markdown(f"## {progress_color} {progress_pct:.0f}%")
        st.caption("Progress to YOUR optimal state")
        st.progress(min(1.0, progress_pct / 100))
        
        st.markdown("---")
        st.markdown(f"**{guidance.encouragement_message}**")
        st.markdown(f"📌 *{guidance.current_instruction}*")
        
        st.markdown("---")
        st.caption(f"YOUR Targets (from {optimal.sessions_analyzed} sessions):")
        
        hrv_ratio = min(1.0, hrv / optimal.hrv_rmssd_optimal) if optimal.hrv_rmssd_optimal > 0 else 0.5
        hrv_icon = "✅" if hrv_ratio >= 0.9 else "🔵" if hrv_ratio >= 0.7 else "🟡"
        st.markdown(f"{hrv_icon} HRV: **{hrv:.0f}** → {optimal.hrv_rmssd_optimal:.0f}ms")
        
        lcc_ratio = min(1.0, lcc / optimal.lcc_peak) if optimal.lcc_peak > 0 else 0.5
        lcc_icon = "✅" if lcc_ratio >= 0.9 else "🔵" if lcc_ratio >= 0.7 else "🟡"
        st.markdown(f"{lcc_icon} LCC: **{lcc*100:.0f}%** → {optimal.lcc_peak*100:.0f}%")
        
        gile_ratio = min(1.0, gile / optimal.gile_peak) if optimal.gile_peak > 0 else 0.5
        gile_icon = "✅" if gile_ratio >= 0.9 else "🔵" if gile_ratio >= 0.7 else "🟡"
        st.markdown(f"{gile_icon} GILE: **{gile:.3f}** → {optimal.gile_peak:.3f}")
        
        coh_ratio = min(1.0, coherence / optimal.coherence_peak) if optimal.coherence_peak > 0 else 0.5
        coh_icon = "✅" if coh_ratio >= 0.9 else "🔵" if coh_ratio >= 0.7 else "🟡"
        st.markdown(f"{coh_icon} Coherence: **{coherence*100:.0f}%** → {optimal.coherence_peak*100:.0f}%")
        
        st.markdown("---")
        
        sync_level_emoji = {"baseline": "⚪", "coherent": "🔵", "major_truth": "🟢", 
                           "sustainable": "✨", "transcendent": "🌟"}
        sync_emoji = sync_level_emoji.get(sync_result['level_name'], "⚪")
        st.markdown(f"**Sync Level:** {sync_emoji} {sync_result['level_name'].replace('_', ' ').title()}")
        st.markdown(f"**Composite:** {sync_result['composite']:.3f}")
        
        next_thresh = sync_detector.get_progress_to_next_threshold(sync_result['composite'])
        if not next_thresh.get('at_max'):
            st.progress(next_thresh.get('progress', 0), text=next_thresh.get('message', ''))
        else:
            st.success("🌟 Maximum Sync!")
        
        st.markdown("---")
        tier = snapshot.faah_tier or 2
        tier_names = {1: "Baseline", 2: "Moderate", 3: "Enhanced", 4: "Optimal"}
        st.info(f"FAAH Tier: **{tier} - {tier_names.get(tier, 'Unknown')}**")
    
    with main_col:
        st.markdown("---")
        
        mcol1, mcol2, mcol3 = st.columns(3)
        with mcol1:
            st.metric("Phase", f"{current_phase_idx + 1}/{len(protocol['phases'])}")
        with mcol2:
            st.metric("Phase Time", f"{int(phase_remaining)}s left")
        with mcol3:
            st.metric("Total Time", f"{int(total_remaining)}s left")
        
        st.markdown("---")
        
        phase_name = current_phase.get('name', 'Unknown')
        intervention = current_phase.get('intervention', None)
        
        if intervention == 'gratitude':
            st.markdown("## ❤️ GRATITUDE SPIKE")
            st.markdown("### Think of ONE specific person you're grateful for")
            st.markdown("## 👤 See their face clearly")
            st.markdown("## 💗 Feel the appreciation IN YOUR HEART")
        elif intervention == 'cyclic_sigh':
            st.markdown("## 🌬️ CYCLIC SIGHING")
            st.markdown("### This is the MOST effective rapid calming technique")
            st.markdown("## 1️⃣ Double inhale: sniff-SNIFF through nose")
            st.markdown("## 2️⃣ LONG slow exhale through mouth")
            st.markdown("### Repeat 3 times now!")
        elif intervention == 'love_flood':
            st.markdown("## 💕 LOVE FLOOD")
            st.markdown("### Don't hold back!")
            st.markdown("## Feel the love you have for someone")
            st.markdown("## Let it FLOOD your entire body")
            st.markdown("### Every cell. Every fiber. LOVE.")
        elif current_phase.get('breathing', False):
            st.markdown(f"## 🌬️ {phase_name}")
            st.markdown(f"### {current_phase.get('guidance', '')}")
            
            breath_pattern = current_phase.get('breath_pattern', {'inhale': 5, 'hold': 0, 'exhale': 5})
            
            breathing_fig = create_breathing_pacer(phase_elapsed, breath_pattern)
            st.plotly_chart(breathing_fig, use_container_width=True)
            
            inhale = breath_pattern.get('inhale', 5)
            hold = breath_pattern.get('hold', 0)
            exhale = breath_pattern.get('exhale', 5)
            st.info(f"**Pattern:** Inhale {inhale}s → {'Hold ' + str(hold) + 's → ' if hold > 0 else ''}Exhale {exhale}s")
        else:
            st.markdown(f"## 🌟 {phase_name}")
            st.markdown(f"### *{current_phase.get('guidance', '')}*")
    
    checkpoint = current_phase.get('checkpoint', None)
    checkpoint_key = f"checkpoint_{current_phase_idx}"
    
    if checkpoint:
        already_completed = checkpoint_key in st.session_state.checkpoint_phase_completed
        
        if not already_completed:
            if st.session_state.checkpoint_paused_at is None:
                raw_elapsed = (datetime.now() - start_time).total_seconds()
                st.session_state.checkpoint_paused_at = raw_elapsed - st.session_state.total_paused_duration
                st.session_state.locked_phase_idx = current_phase_idx
            
            st.markdown("---")
            st.error("⏸️ **SESSION PAUSED** - Answer the question below to continue")
            st.warning(f"**🔍 REQUIRED REFLECTION:** {checkpoint}")
            
            if "1-10" in checkpoint or "rate" in checkpoint.lower():
                response = st.slider(f"Your response:", 1, 10, 5, key=f"ckpt_slider_{current_phase_idx}")
                if st.button("✅ Submit & Continue", key=f"ckpt_btn_{current_phase_idx}", type="primary"):
                    pause_duration = (datetime.now() - start_time).total_seconds() - st.session_state.checkpoint_paused_at - st.session_state.total_paused_duration
                    st.session_state.total_paused_duration += pause_duration
                    st.session_state.checkpoint_paused_at = None
                    st.session_state.locked_phase_idx = None
                    
                    st.session_state.checkpoint_responses[checkpoint_key] = {
                        'question': checkpoint,
                        'response': response,
                        'phase': phase_name
                    }
                    st.session_state.checkpoint_phase_completed.add(checkpoint_key)
                    st.rerun()
                st.info("⏸️ Timer frozen - take your time to reflect")
                return
            else:
                response = st.text_input("Your response:", key=f"ckpt_text_{current_phase_idx}",
                                        placeholder="Type what you notice...")
                if st.button("✅ Submit & Continue", key=f"ckpt_btn_{current_phase_idx}", type="primary"):
                    if response.strip():
                        pause_duration = (datetime.now() - start_time).total_seconds() - st.session_state.checkpoint_paused_at - st.session_state.total_paused_duration
                        st.session_state.total_paused_duration += pause_duration
                        st.session_state.checkpoint_paused_at = None
                        st.session_state.locked_phase_idx = None
                        
                        st.session_state.checkpoint_responses[checkpoint_key] = {
                            'question': checkpoint,
                            'response': response,
                            'phase': phase_name
                        }
                        st.session_state.checkpoint_phase_completed.add(checkpoint_key)
                        st.rerun()
                    else:
                        st.error("Please enter a response before continuing")
                st.info("⏸️ Timer frozen - take your time to reflect")
                return
    
    st.markdown("---")
    
    if st.button("⏸️ End Session Early"):
        st.session_state.amp_session_state = 'during_reflection'
        st.rerun()
    
    time.sleep(1)
    st.rerun()


def render_during_reflection():
    """Post-session reflection on what happened during"""
    protocol = st.session_state.amp_protocol
    
    st.markdown(f"### 🌈 Session Complete: {protocol['name']}")
    st.success("Congratulations! You've completed the amplification session.")
    
    st.markdown("---")
    st.markdown("#### During the Session...")
    
    peak_feeling = st.slider("Peak Bliss/Connection Feeling", 1, 10, 5, key="during_peak",
                            help="At your highest point, how blissful/connected did you feel?")
    
    heart_sensations = st.multiselect("Heart Sensations Experienced",
        ["Warmth", "Expansion", "Tingling", "Pulsing", "Openness", "Pressure", "Nothing specific"],
        key="during_heart")
    
    insights = st.text_area("Any insights or experiences?", key="during_insights",
                           placeholder="What did you notice? Any thoughts, images, or realizations?")
    
    st.markdown("---")
    
    if st.button("Continue to Post-Measurement", type="primary"):
        st.session_state.amp_during_data = {
            'peak_feeling': peak_feeling,
            'heart_sensations': ", ".join(heart_sensations),
            'insights': insights
        }
        st.session_state.amp_session_state = 'post_measurement'
        st.rerun()


def render_post_measurement():
    """Post-session measurement"""
    protocol = st.session_state.amp_protocol
    pre_data = st.session_state.amp_pre_data
    
    st.markdown(f"### 📊 Post-Session Measurement: {protocol['name']}")
    st.markdown("*Record your state after the session*")
    
    st.markdown("---")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("#### Heart Metrics")
        st.markdown("*From your heart rate app*")
        post_hr = st.number_input("Heart Rate (BPM)", min_value=40, max_value=180, 
                                  value=int(pre_data.get('heart_rate', 72)), key="post_hr")
        post_hrv = st.number_input("HRV / RMSSD (ms)", min_value=5.0, max_value=200.0, 
                                   value=float(pre_data.get('hrv_rmssd', 45.0)), key="post_hrv")
        post_coherence = st.slider("Heart Coherence", 0.0, 1.0, 
                                   float(pre_data.get('coherence', 0.5)), 0.05, key="post_coh")
    
    with col2:
        st.markdown("#### Subjective State")
        post_mood = st.slider("Current Mood", 1, 10, 
                             int(pre_data.get('mood', 5)), key="post_mood")
        post_energy = st.slider("Current Energy", 1, 10, 
                               int(pre_data.get('energy', 5)), key="post_energy")
        post_connection = st.slider("Consciousness Connection", 1, 10, 
                                    int(pre_data.get('connection', 5)), key="post_conn")
    
    st.markdown("---")
    st.markdown("#### Consciousness Connection Index (CCI)")
    
    post_cci = calculate_cci(post_mood, post_energy, post_coherence, post_connection)
    interpretation, level = get_cci_interpretation(post_cci)
    
    pre_cci = pre_data.get('cci', 50)
    cci_change = post_cci - pre_cci
    
    col_a, col_b, col_c = st.columns(3)
    with col_a:
        st.metric("Pre CCI", f"{pre_cci:.1f}")
    with col_b:
        st.metric("Post CCI", f"{post_cci:.1f}", delta=f"{cci_change:+.1f}")
    with col_c:
        st.info(interpretation)
    
    post_notes = st.text_area("Post-session notes", key="post_notes",
                             placeholder="How do you feel now compared to before?")
    
    st.markdown("---")
    
    if st.button("💾 Save & View Results", type="primary"):
        st.session_state.amp_post_data = {
            'heart_rate': post_hr,
            'hrv_rmssd': post_hrv,
            'coherence': post_coherence,
            'mood': post_mood,
            'energy': post_energy,
            'connection': post_connection,
            'cci': post_cci,
            'notes': post_notes
        }
        
        session_data = {
            'protocol_name': protocol['name'],
            'duration_minutes': protocol['duration_min'],
            'pre_heart_rate': pre_data.get('heart_rate'),
            'pre_hrv_rmssd': pre_data.get('hrv_rmssd'),
            'pre_coherence': pre_data.get('coherence'),
            'pre_mood': pre_data.get('mood'),
            'pre_energy': pre_data.get('energy'),
            'pre_cci': pre_data.get('cci'),
            'pre_notes': pre_data.get('notes'),
            'during_peak_feeling': st.session_state.amp_during_data.get('peak_feeling'),
            'during_heart_sensations': st.session_state.amp_during_data.get('heart_sensations'),
            'during_insights': st.session_state.amp_during_data.get('insights'),
            'post_heart_rate': post_hr,
            'post_hrv_rmssd': post_hrv,
            'post_coherence': post_coherence,
            'post_mood': post_mood,
            'post_energy': post_energy,
            'post_cci': post_cci,
            'post_notes': post_notes,
            'gile_g': protocol['gile_target']['G'],
            'gile_i': protocol['gile_target']['I'],
            'gile_l': protocol['gile_target']['L'],
            'gile_e': protocol['gile_target']['E'],
            'overall_shift': cci_change
        }
        
        session_id = save_amplification_session(session_data)
        if session_id:
            st.session_state.amp_saved_id = session_id
        
        st.session_state.amp_session_state = 'results'
        st.rerun()


def render_session_results():
    """Final session results and analysis"""
    protocol = st.session_state.amp_protocol
    pre_data = st.session_state.amp_pre_data
    post_data = st.session_state.amp_post_data
    during_data = st.session_state.amp_during_data
    
    st.markdown(f"## 🎉 Session Complete: {protocol['name']}")
    
    pre_cci = pre_data.get('cci', 50)
    post_cci = post_data.get('cci', 50)
    cci_change = post_cci - pre_cci
    
    st.markdown("---")
    st.markdown("### 🧠 Consciousness Connection Shift")
    
    col1, col2, col3 = st.columns(3)
    with col1:
        st.metric("Before", f"{pre_cci:.1f}")
        pre_interp, _ = get_cci_interpretation(pre_cci)
        st.caption(pre_interp)
    with col2:
        direction = "📈" if cci_change > 0 else "📉" if cci_change < 0 else "➡️"
        st.markdown(f"### {direction}")
        st.markdown(f"### {cci_change:+.1f} points")
    with col3:
        st.metric("After", f"{post_cci:.1f}")
        post_interp, _ = get_cci_interpretation(post_cci)
        st.caption(post_interp)
    
    fig = create_session_results_chart(pre_data, post_data)
    st.plotly_chart(fig, use_container_width=True)
    
    st.markdown("---")
    st.markdown("### 📊 Detailed Changes")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        mood_change = post_data.get('mood', 5) - pre_data.get('mood', 5)
        st.metric("Mood", f"{post_data.get('mood', 5)}/10", delta=f"{mood_change:+d}")
    with col2:
        energy_change = post_data.get('energy', 5) - pre_data.get('energy', 5)
        st.metric("Energy", f"{post_data.get('energy', 5)}/10", delta=f"{energy_change:+d}")
    with col3:
        hr_change = post_data.get('heart_rate', 72) - pre_data.get('heart_rate', 72)
        st.metric("Heart Rate", f"{post_data.get('heart_rate', 72)} BPM", delta=f"{hr_change:+d}")
    with col4:
        hrv_change = post_data.get('hrv_rmssd', 45) - pre_data.get('hrv_rmssd', 45)
        st.metric("HRV", f"{post_data.get('hrv_rmssd', 45):.0f} ms", delta=f"{hrv_change:+.0f}")
    
    st.markdown("---")
    st.markdown("### 💡 Session Insights")
    
    checkpoint_responses = st.session_state.get('checkpoint_responses', {})
    if checkpoint_responses:
        st.markdown("#### 🔍 What You Noticed During Session:")
        for key, response_data in checkpoint_responses.items():
            phase = response_data.get('phase', 'Unknown')
            question = response_data.get('question', '')
            response = response_data.get('response', '')
            st.markdown(f"**{phase}:** {question}")
            st.success(f"→ {response}")
        st.markdown("---")
    
    if during_data.get('heart_sensations'):
        st.markdown(f"**Heart Sensations:** {during_data.get('heart_sensations')}")
    
    if during_data.get('insights'):
        st.markdown(f"**Your Insights:** {during_data.get('insights')}")
    
    st.markdown(f"**Peak Feeling:** {during_data.get('peak_feeling', 5)}/10")
    
    if cci_change > 5:
        st.success("🌟 **Significant amplification achieved!** Your consciousness connection deepened measurably.")
    elif cci_change > 0:
        st.info("✨ **Positive shift detected.** Keep practicing to deepen the effect.")
    elif cci_change == 0:
        st.warning("➡️ **Stable state.** Sometimes maintaining is just as valuable as shifting.")
    else:
        st.info("🔄 **Integration phase.** Sometimes consciousness consolidates before expanding.")
    
    st.markdown("---")
    st.markdown("### 🧬 TI Framework Analysis")
    
    st.markdown(f"""
    Based on the **{protocol['name']}** protocol targeting:
    - **G (Goodness):** {protocol['gile_target']['G']*100:.0f}%
    - **I (Intuition):** {protocol['gile_target']['I']*100:.0f}%
    - **L (Love):** {protocol['gile_target']['L']*100:.0f}%
    - **E (Environment):** {protocol['gile_target']['E']*100:.0f}%
    
    Your **CCI shift of {cci_change:+.1f}** indicates {'strong resonance with the protocol' if cci_change > 3 else 'building resonance - continue practicing' if cci_change > 0 else 'natural variation within the session'}.
    """)
    
    st.markdown("---")
    
    if st.button("🔄 Start New Session", type="primary"):
        st.session_state.amp_session_state = 'select'
        st.session_state.amp_pre_data = {}
        st.session_state.amp_post_data = {}
        st.session_state.amp_during_data = {}
        st.session_state.amp_protocol = None
        st.session_state.amp_start_time = None
        st.session_state.checkpoint_responses = {}
        st.session_state.checkpoint_phase_completed = set()
        st.session_state.checkpoint_paused_at = None
        st.session_state.total_paused_duration = 0
        st.session_state.locked_phase_idx = None
        st.rerun()

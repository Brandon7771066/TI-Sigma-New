"""
Real-Time Mood Amplifier Protocols

Live visual entrainment system with measurable before/after results.
Uses scientifically validated frequencies for consciousness state modulation.
"""

import streamlit as st
import time
import math
import json
import os
from datetime import datetime

# Entrainment frequencies and their effects
ENTRAINMENT_FREQUENCIES = {
    "alpha_relaxation": {
        "name": "Alpha Relaxation (10 Hz)",
        "frequency": 10.0,
        "duration_sec": 60,
        "color1": "#4169E1",  # Royal blue
        "color2": "#1E3A5F",  # Deep blue
        "description": "Alpha waves (8-12 Hz) are associated with relaxed alertness, reduced anxiety, and enhanced creativity.",
        "expected_effect": "Calm focus, reduced stress, creative flow state"
    },
    "theta_meditation": {
        "name": "Theta Meditation (6 Hz)",
        "frequency": 6.0,
        "duration_sec": 90,
        "color1": "#9370DB",  # Medium purple
        "color2": "#4B0082",  # Indigo
        "description": "Theta waves (4-8 Hz) are linked to deep meditation, memory consolidation, and intuitive insights.",
        "expected_effect": "Deep relaxation, enhanced intuition, meditative calm"
    },
    "gamma_focus": {
        "name": "Gamma Focus (40 Hz)",
        "frequency": 40.0,
        "duration_sec": 45,
        "color1": "#FFD700",  # Gold
        "color2": "#FF8C00",  # Dark orange
        "description": "Gamma waves (30-100 Hz) are associated with heightened perception, cognitive processing, and peak performance.",
        "expected_effect": "Sharp focus, enhanced perception, peak mental clarity"
    },
    "beta_alertness": {
        "name": "Beta Alertness (18 Hz)",
        "frequency": 18.0,
        "duration_sec": 45,
        "color1": "#32CD32",  # Lime green
        "color2": "#228B22",  # Forest green
        "description": "Beta waves (12-30 Hz) are linked to active thinking, concentration, and problem-solving.",
        "expected_effect": "Increased alertness, enhanced concentration, active thinking"
    },
    "delta_deep_rest": {
        "name": "Delta Deep Rest (2 Hz)",
        "frequency": 2.0,
        "duration_sec": 120,
        "color1": "#2F4F4F",  # Dark slate gray
        "color2": "#1C1C1C",  # Almost black
        "description": "Delta waves (0.5-4 Hz) are associated with deep sleep, healing, and regeneration.",
        "expected_effect": "Deep relaxation, restorative state, physical healing"
    }
}

# Mood assessment questions
MOOD_QUESTIONS = [
    ("energy", "Energy Level", "How energized do you feel?"),
    ("focus", "Mental Focus", "How focused and clear is your mind?"),
    ("calm", "Calmness", "How calm and relaxed do you feel?"),
    ("mood", "Overall Mood", "How positive is your current mood?"),
    ("presence", "Present Awareness", "How present and aware do you feel?")
]


def get_session_key():
    """Generate unique session key for storing results."""
    return f"mood_session_{datetime.now().strftime('%Y%m%d_%H%M%S')}"


def save_session_results(session_data):
    """Save session results to database."""
    try:
        import psycopg2
        database_url = os.environ.get('DATABASE_URL', '')
        if not database_url:
            return False
            
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        
        # Create table if not exists
        cur.execute('''
            CREATE TABLE IF NOT EXISTS mood_amplifier_sessions (
                id SERIAL PRIMARY KEY,
                session_key VARCHAR(100),
                protocol_name VARCHAR(100),
                frequency_hz FLOAT,
                duration_sec INTEGER,
                before_scores JSONB,
                after_scores JSONB,
                improvement_scores JSONB,
                total_improvement FLOAT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        cur.execute('''
            INSERT INTO mood_amplifier_sessions 
            (session_key, protocol_name, frequency_hz, duration_sec, 
             before_scores, after_scores, improvement_scores, total_improvement)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
        ''', (
            session_data['session_key'],
            session_data['protocol_name'],
            session_data['frequency'],
            session_data['duration'],
            json.dumps(session_data['before_scores']),
            json.dumps(session_data['after_scores']),
            json.dumps(session_data['improvements']),
            session_data['total_improvement']
        ))
        
        conn.commit()
        conn.close()
        return True
    except Exception as e:
        st.warning(f"Could not save to database: {e}")
        return False


def get_session_history():
    """Get past session results from database."""
    try:
        import psycopg2
        database_url = os.environ.get('DATABASE_URL', '')
        if not database_url:
            return []
            
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        
        cur.execute('''
            SELECT protocol_name, frequency_hz, total_improvement, created_at
            FROM mood_amplifier_sessions
            ORDER BY created_at DESC
            LIMIT 20
        ''')
        
        results = cur.fetchall()
        conn.close()
        return results
    except:
        return []


def render_mood_assessment(prefix: str, title: str):
    """Render mood assessment sliders."""
    st.markdown(f"### {title}")
    
    scores = {}
    cols = st.columns(len(MOOD_QUESTIONS))
    
    for i, (key, label, question) in enumerate(MOOD_QUESTIONS):
        with cols[i]:
            st.markdown(f"**{label}**")
            scores[key] = st.slider(
                question,
                min_value=1,
                max_value=10,
                value=5,
                key=f"{prefix}_{key}",
                label_visibility="collapsed"
            )
            st.caption(f"{scores[key]}/10")
    
    return scores


def render_entrainment_display(protocol: dict, placeholder):
    """Render the visual entrainment animation."""
    frequency = protocol['frequency']
    color1 = protocol['color1']
    color2 = protocol['color2']
    
    # Calculate cycle parameters
    period = 1.0 / frequency
    
    # Create pulsing animation using CSS
    animation_html = f"""
    <style>
    @keyframes pulse {{
        0% {{ 
            background-color: {color1}; 
            transform: scale(1);
            box-shadow: 0 0 50px {color1};
        }}
        50% {{ 
            background-color: {color2}; 
            transform: scale(0.95);
            box-shadow: 0 0 100px {color2};
        }}
        100% {{ 
            background-color: {color1}; 
            transform: scale(1);
            box-shadow: 0 0 50px {color1};
        }}
    }}
    
    .entrainment-circle {{
        width: 300px;
        height: 300px;
        border-radius: 50%;
        margin: 40px auto;
        animation: pulse {period:.4f}s ease-in-out infinite;
        display: flex;
        align-items: center;
        justify-content: center;
    }}
    
    .entrainment-text {{
        color: white;
        font-size: 24px;
        font-weight: bold;
        text-shadow: 2px 2px 4px rgba(0,0,0,0.5);
    }}
    
    .container {{
        background: linear-gradient(135deg, #0a0a0a 0%, #1a1a2e 100%);
        padding: 40px;
        border-radius: 20px;
        text-align: center;
    }}
    
    .frequency-display {{
        color: {color1};
        font-size: 48px;
        font-weight: bold;
        margin-bottom: 10px;
    }}
    
    .instruction {{
        color: #888;
        font-size: 18px;
        margin-top: 20px;
    }}
    </style>
    
    <div class="container">
        <div class="frequency-display">{frequency} Hz</div>
        <div class="entrainment-circle">
            <span class="entrainment-text">BREATHE</span>
        </div>
        <p class="instruction">Softly gaze at the pulsing light. Breathe slowly and naturally.</p>
    </div>
    """
    
    placeholder.markdown(animation_html, unsafe_allow_html=True)


def render_results_comparison(before: dict, after: dict, protocol_name: str):
    """Display before/after comparison with improvements."""
    st.markdown("---")
    st.markdown("## 📊 Your Results")
    
    improvements = {}
    total_improvement = 0
    
    st.markdown("### Before vs After Comparison")
    
    cols = st.columns(len(MOOD_QUESTIONS))
    
    for i, (key, label, _) in enumerate(MOOD_QUESTIONS):
        with cols[i]:
            before_val = before.get(key, 5)
            after_val = after.get(key, 5)
            change = after_val - before_val
            improvements[key] = change
            total_improvement += change
            
            # Color based on improvement
            if change > 0:
                delta_color = "normal"  # Green
                arrow = "↑"
            elif change < 0:
                delta_color = "inverse"  # Red
                arrow = "↓"
            else:
                delta_color = "off"
                arrow = "→"
            
            st.metric(
                label=label,
                value=f"{after_val}/10",
                delta=f"{arrow} {abs(change)}" if change != 0 else "No change",
                delta_color=delta_color
            )
    
    # Overall summary
    st.markdown("---")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        avg_before = sum(before.values()) / len(before)
        st.metric("Average Before", f"{avg_before:.1f}/10")
    
    with col2:
        avg_after = sum(after.values()) / len(after)
        st.metric("Average After", f"{avg_after:.1f}/10")
    
    with col3:
        pct_change = ((avg_after - avg_before) / avg_before * 100) if avg_before > 0 else 0
        st.metric(
            "Total Improvement",
            f"+{total_improvement} points" if total_improvement >= 0 else f"{total_improvement} points",
            delta=f"{pct_change:+.1f}%" if pct_change != 0 else None
        )
    
    # Interpretation
    st.markdown("### 🧠 Interpretation")
    
    if total_improvement >= 5:
        st.success(f"""
        **Excellent Response!** Your consciousness state showed significant positive modulation 
        from the {protocol_name} protocol. This suggests strong neural entrainment to the 
        target frequency band.
        """)
    elif total_improvement >= 2:
        st.info(f"""
        **Positive Response.** The {protocol_name} protocol produced measurable improvements 
        in your subjective state. With regular practice, effects typically become more pronounced.
        """)
    elif total_improvement >= 0:
        st.warning(f"""
        **Subtle Response.** Minimal change detected. This is normal for first-time use. 
        Neural entrainment often requires multiple sessions to establish robust patterns.
        """)
    else:
        st.error(f"""
        **Unexpected Response.** Your scores decreased slightly. This might indicate the 
        protocol wasn't well-matched to your current state. Try a different frequency or duration.
        """)
    
    return improvements, total_improvement


def main():
    st.set_page_config(page_title="Mood Amplifier Protocols", page_icon="🌀", layout="wide")
    
    st.title("🌀 Real-Time Mood Amplifier Protocols")
    st.markdown("""
    **Experience neural entrainment with measurable before/after results.**
    
    These protocols use visual flicker at specific frequencies to gently guide your brain 
    into target consciousness states. This is based on the scientifically validated phenomenon 
    of Steady-State Visual Evoked Potentials (SSVEP).
    """)
    
    # Initialize session state
    if 'protocol_stage' not in st.session_state:
        st.session_state.protocol_stage = 'select'
    if 'before_scores' not in st.session_state:
        st.session_state.before_scores = None
    if 'selected_protocol' not in st.session_state:
        st.session_state.selected_protocol = None
    if 'session_key' not in st.session_state:
        st.session_state.session_key = None
    
    # Sidebar: Session History
    with st.sidebar:
        st.markdown("### 📜 Session History")
        history = get_session_history()
        if history:
            for name, freq, improvement, created in history:
                delta = f"+{improvement:.1f}" if improvement >= 0 else f"{improvement:.1f}"
                st.markdown(f"**{name}** ({freq} Hz): {delta} pts")
                st.caption(str(created)[:16])
        else:
            st.caption("No sessions recorded yet.")
        
        st.markdown("---")
        st.markdown("### ⚠️ Safety Note")
        st.caption("""
        If you have epilepsy or a history of seizures, 
        consult a healthcare provider before using 
        visual entrainment protocols.
        """)
    
    # Main content based on stage
    if st.session_state.protocol_stage == 'select':
        st.markdown("## Step 1: Choose Your Protocol")
        
        cols = st.columns(3)
        for i, (key, protocol) in enumerate(ENTRAINMENT_FREQUENCIES.items()):
            with cols[i % 3]:
                with st.container(border=True):
                    st.markdown(f"### {protocol['name']}")
                    st.markdown(protocol['description'])
                    st.markdown(f"**Duration:** {protocol['duration_sec']} seconds")
                    st.markdown(f"**Expected:** {protocol['expected_effect']}")
                    
                    if st.button(f"Select {protocol['name']}", key=f"select_{key}", use_container_width=True):
                        st.session_state.selected_protocol = key
                        st.session_state.protocol_stage = 'before'
                        st.session_state.session_key = get_session_key()
                        st.rerun()
    
    elif st.session_state.protocol_stage == 'before':
        # Guard: Ensure protocol is selected
        if st.session_state.selected_protocol is None or st.session_state.selected_protocol not in ENTRAINMENT_FREQUENCIES:
            st.session_state.protocol_stage = 'select'
            st.rerun()
        
        protocol = ENTRAINMENT_FREQUENCIES[st.session_state.selected_protocol]
        st.markdown(f"## Step 2: Before Assessment - {protocol['name']}")
        st.info("Rate how you feel RIGHT NOW, before starting the protocol.")
        
        before_scores = render_mood_assessment("before", "Current State")
        
        col1, col2 = st.columns(2)
        with col1:
            if st.button("← Back to Protocol Selection", use_container_width=True):
                st.session_state.protocol_stage = 'select'
                st.rerun()
        with col2:
            if st.button("Start Protocol →", type="primary", use_container_width=True):
                st.session_state.before_scores = before_scores
                st.session_state.protocol_stage = 'running'
                st.rerun()
    
    elif st.session_state.protocol_stage == 'running':
        # Guard: Ensure protocol and before_scores exist
        if st.session_state.selected_protocol is None or st.session_state.selected_protocol not in ENTRAINMENT_FREQUENCIES:
            st.session_state.protocol_stage = 'select'
            st.rerun()
        if st.session_state.before_scores is None:
            st.session_state.protocol_stage = 'before'
            st.rerun()
        
        protocol = ENTRAINMENT_FREQUENCIES[st.session_state.selected_protocol]
        duration = protocol['duration_sec']
        
        st.markdown(f"## {protocol['name']}")
        st.markdown(f"**Duration:** {duration} seconds | **Frequency:** {protocol['frequency']} Hz")
        
        # Create placeholder for animation
        animation_placeholder = st.empty()
        progress_bar = st.progress(0)
        time_display = st.empty()
        
        # Render entrainment display
        render_entrainment_display(protocol, animation_placeholder)
        
        # Countdown timer
        start_time = time.time()
        while True:
            elapsed = time.time() - start_time
            remaining = max(0, duration - elapsed)
            progress = min(1.0, elapsed / duration)
            
            progress_bar.progress(progress)
            time_display.markdown(f"**Time remaining:** {int(remaining)} seconds")
            
            if elapsed >= duration:
                break
            
            time.sleep(0.1)
        
        # Protocol complete
        animation_placeholder.empty()
        st.success("Protocol complete! Please rate how you feel now.")
        time.sleep(1)
        
        st.session_state.protocol_stage = 'after'
        st.rerun()
    
    elif st.session_state.protocol_stage == 'after':
        # Guard: Ensure protocol and before_scores exist
        if st.session_state.selected_protocol is None or st.session_state.selected_protocol not in ENTRAINMENT_FREQUENCIES:
            st.session_state.protocol_stage = 'select'
            st.rerun()
        if st.session_state.before_scores is None:
            st.session_state.protocol_stage = 'before'
            st.rerun()
        
        protocol = ENTRAINMENT_FREQUENCIES[st.session_state.selected_protocol]
        st.markdown(f"## Step 3: After Assessment - {protocol['name']}")
        st.info("Rate how you feel RIGHT NOW, after completing the protocol.")
        
        after_scores = render_mood_assessment("after", "Current State")
        
        if st.button("See My Results", type="primary", use_container_width=True):
            improvements, total = render_results_comparison(
                st.session_state.before_scores,
                after_scores,
                protocol['name']
            )
            
            # Save session data
            session_data = {
                'session_key': st.session_state.session_key,
                'protocol_name': protocol['name'],
                'frequency': protocol['frequency'],
                'duration': protocol['duration_sec'],
                'before_scores': st.session_state.before_scores,
                'after_scores': after_scores,
                'improvements': improvements,
                'total_improvement': total
            }
            
            if save_session_results(session_data):
                st.success("Session saved to database!")
            
            st.session_state.protocol_stage = 'results'
            st.session_state.after_scores = after_scores
            st.session_state.improvements = improvements
            st.session_state.total_improvement = total
    
    elif st.session_state.protocol_stage == 'results':
        # Guard: Ensure all required state exists
        if (st.session_state.selected_protocol is None or 
            st.session_state.selected_protocol not in ENTRAINMENT_FREQUENCIES or
            st.session_state.before_scores is None or 
            st.session_state.after_scores is None):
            st.session_state.protocol_stage = 'select'
            st.session_state.before_scores = None
            st.session_state.after_scores = None
            st.rerun()
        
        protocol = ENTRAINMENT_FREQUENCIES[st.session_state.selected_protocol]
        
        render_results_comparison(
            st.session_state.before_scores,
            st.session_state.after_scores,
            protocol['name']
        )
        
        st.markdown("---")
        
        col1, col2 = st.columns(2)
        with col1:
            if st.button("🔄 Try Another Protocol", use_container_width=True):
                st.session_state.protocol_stage = 'select'
                st.session_state.before_scores = None
                st.session_state.after_scores = None
                st.rerun()
        with col2:
            if st.button("🔁 Repeat Same Protocol", use_container_width=True):
                st.session_state.protocol_stage = 'before'
                st.session_state.before_scores = None
                st.session_state.session_key = get_session_key()
                st.rerun()


if __name__ == "__main__":
    main()

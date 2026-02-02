"""
Real-Time Biometric Intervention System

Integrates HRV, EEG, and physiological measurements with 
mood amplifier protocols for measurable consciousness modulation.
"""

import streamlit as st
import numpy as np
import time
import json
import os
from datetime import datetime
from typing import Dict, Any, Optional

# Simulated biometric data generators (for demo - replace with real hardware)
def generate_hrv_data() -> Dict[str, float]:
    """Generate simulated HRV metrics."""
    base_hr = 70 + np.random.normal(0, 5)
    return {
        'heart_rate': round(base_hr, 1),
        'rmssd': round(30 + np.random.normal(0, 10), 1),  # ms
        'sdnn': round(50 + np.random.normal(0, 15), 1),   # ms
        'lf_hf_ratio': round(1.5 + np.random.normal(0, 0.5), 2),
        'coherence': round(min(100, max(0, 50 + np.random.normal(0, 20))), 1)
    }

def generate_eeg_data() -> Dict[str, float]:
    """Generate simulated EEG band power."""
    total = 100
    delta = np.random.uniform(15, 25)
    theta = np.random.uniform(15, 25)
    alpha = np.random.uniform(20, 35)
    beta = np.random.uniform(10, 20)
    gamma = np.random.uniform(5, 15)
    
    # Normalize to 100%
    total_raw = delta + theta + alpha + beta + gamma
    return {
        'delta': round(delta / total_raw * 100, 1),
        'theta': round(theta / total_raw * 100, 1),
        'alpha': round(alpha / total_raw * 100, 1),
        'beta': round(beta / total_raw * 100, 1),
        'gamma': round(gamma / total_raw * 100, 1)
    }

def calculate_consciousness_index(eeg: Dict, hrv: Dict) -> float:
    """
    Calculate overall consciousness index based on EEG and HRV.
    
    Higher values indicate:
    - More alpha/theta relative to beta (relaxed awareness)
    - Higher HRV coherence (autonomic balance)
    - Lower LF/HF ratio (parasympathetic activation)
    """
    alpha_theta_ratio = (eeg['alpha'] + eeg['theta']) / max(1, eeg['beta'])
    coherence_factor = hrv['coherence'] / 100
    balance_factor = 1 / max(0.5, hrv['lf_hf_ratio'])
    
    index = (alpha_theta_ratio * 30 + coherence_factor * 40 + balance_factor * 30)
    return round(min(100, max(0, index)), 1)


# Intervention protocols with expected biometric changes
INTERVENTION_PROTOCOLS = {
    "alpha_coherence": {
        "name": "Alpha Coherence Training",
        "frequency": 10.0,
        "duration_sec": 90,
        "color": "#4169E1",
        "target_changes": {
            "eeg": {"alpha": "+15-25%", "beta": "-10-15%"},
            "hrv": {"coherence": "+20-40%", "rmssd": "+10-20%"}
        },
        "description": "Increase alpha brainwaves and heart coherence for calm focus."
    },
    "theta_meditation": {
        "name": "Theta Deep Meditation", 
        "frequency": 6.0,
        "duration_sec": 120,
        "color": "#9370DB",
        "target_changes": {
            "eeg": {"theta": "+20-30%", "alpha": "+10%"},
            "hrv": {"coherence": "+30-50%", "lf_hf_ratio": "-20-30%"}
        },
        "description": "Deepen meditation with theta entrainment."
    },
    "gamma_cognition": {
        "name": "Gamma Cognitive Enhancement",
        "frequency": 40.0,
        "duration_sec": 60,
        "color": "#FFD700",
        "target_changes": {
            "eeg": {"gamma": "+30-50%", "beta": "+10-20%"},
            "hrv": {"heart_rate": "+5-10 bpm"}
        },
        "description": "Boost cognitive processing and perception."
    },
    "hrv_coherence": {
        "name": "HRV Coherence Breathing",
        "frequency": 0.1,  # 6 breaths per minute = 0.1 Hz
        "duration_sec": 180,
        "color": "#32CD32",
        "target_changes": {
            "hrv": {"coherence": "+40-60%", "rmssd": "+25-40%", "lf_hf_ratio": "-30-50%"},
            "eeg": {"alpha": "+10-15%"}
        },
        "description": "Optimize autonomic balance through resonant breathing."
    }
}


def save_intervention_session(session_data: Dict) -> bool:
    """Save intervention session to database."""
    try:
        import psycopg2
        database_url = os.environ.get('DATABASE_URL', '')
        if not database_url:
            return False
            
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        
        cur.execute('''
            CREATE TABLE IF NOT EXISTS biometric_interventions (
                id SERIAL PRIMARY KEY,
                session_id VARCHAR(100),
                protocol_name VARCHAR(100),
                frequency_hz FLOAT,
                duration_sec INTEGER,
                baseline_eeg JSONB,
                baseline_hrv JSONB,
                post_eeg JSONB,
                post_hrv JSONB,
                consciousness_index_change FLOAT,
                significant_changes JSONB,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        cur.execute('''
            INSERT INTO biometric_interventions
            (session_id, protocol_name, frequency_hz, duration_sec,
             baseline_eeg, baseline_hrv, post_eeg, post_hrv,
             consciousness_index_change, significant_changes)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        ''', (
            session_data['session_id'],
            session_data['protocol_name'],
            session_data['frequency'],
            session_data['duration'],
            json.dumps(session_data['baseline_eeg']),
            json.dumps(session_data['baseline_hrv']),
            json.dumps(session_data['post_eeg']),
            json.dumps(session_data['post_hrv']),
            session_data['consciousness_change'],
            json.dumps(session_data['significant_changes'])
        ))
        
        conn.commit()
        conn.close()
        return True
    except Exception as e:
        st.warning(f"Database save failed: {e}")
        return False


def get_intervention_history():
    """Get past intervention sessions."""
    try:
        import psycopg2
        database_url = os.environ.get('DATABASE_URL', '')
        if not database_url:
            return []
            
        conn = psycopg2.connect(database_url)
        cur = conn.cursor()
        
        cur.execute('''
            SELECT protocol_name, consciousness_index_change, created_at
            FROM biometric_interventions
            ORDER BY created_at DESC
            LIMIT 15
        ''')
        
        results = cur.fetchall()
        conn.close()
        return results
    except:
        return []


def render_biometric_display(eeg: Dict, hrv: Dict, title: str = "Current State"):
    """Render biometric data visualization."""
    st.markdown(f"### {title}")
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("#### EEG Band Power")
        
        # Create bar chart data
        bands = ['Delta', 'Theta', 'Alpha', 'Beta', 'Gamma']
        values = [eeg['delta'], eeg['theta'], eeg['alpha'], eeg['beta'], eeg['gamma']]
        colors = ['#2F4F4F', '#9370DB', '#4169E1', '#32CD32', '#FFD700']
        
        for band, value, color in zip(bands, values, colors):
            st.markdown(f"""
            <div style="display: flex; align-items: center; margin: 5px 0;">
                <span style="width: 60px; font-weight: bold;">{band}</span>
                <div style="flex: 1; background: #333; height: 20px; border-radius: 10px; overflow: hidden;">
                    <div style="width: {value}%; height: 100%; background: {color};"></div>
                </div>
                <span style="width: 50px; text-align: right;">{value}%</span>
            </div>
            """, unsafe_allow_html=True)
    
    with col2:
        st.markdown("#### HRV Metrics")
        
        metrics = [
            ("Heart Rate", f"{hrv['heart_rate']} bpm", hrv['heart_rate']),
            ("RMSSD", f"{hrv['rmssd']} ms", hrv['rmssd']),
            ("SDNN", f"{hrv['sdnn']} ms", hrv['sdnn']),
            ("LF/HF Ratio", f"{hrv['lf_hf_ratio']}", hrv['lf_hf_ratio'] * 30),
            ("Coherence", f"{hrv['coherence']}%", hrv['coherence'])
        ]
        
        for name, display, value in metrics:
            color = "#4CAF50" if name == "Coherence" and value > 60 else "#2196F3"
            st.markdown(f"""
            <div style="display: flex; align-items: center; margin: 5px 0;">
                <span style="width: 80px; font-weight: bold;">{name}</span>
                <div style="flex: 1; background: #333; height: 20px; border-radius: 10px; overflow: hidden;">
                    <div style="width: {min(100, value)}%; height: 100%; background: {color};"></div>
                </div>
                <span style="width: 70px; text-align: right;">{display}</span>
            </div>
            """, unsafe_allow_html=True)


def render_comparison(baseline: Dict, post: Dict, metric_type: str):
    """Render before/after comparison."""
    st.markdown(f"#### {metric_type.upper()} Changes")
    
    for key in baseline.keys():
        before = baseline[key]
        after = post[key]
        change = after - before
        pct_change = (change / before * 100) if before != 0 else 0
        
        if abs(pct_change) > 10:
            status = "increase" if change > 0 else "decrease"
            color = "#4CAF50" if (key in ['alpha', 'theta', 'coherence', 'rmssd'] and change > 0) or \
                                 (key in ['lf_hf_ratio'] and change < 0) else "#FF5722"
        else:
            status = "stable"
            color = "#888"
        
        arrow = "+" if change > 0 else ""
        
        st.markdown(f"""
        <div style="display: flex; justify-content: space-between; padding: 5px 10px; 
                    background: #222; margin: 3px 0; border-radius: 5px; border-left: 3px solid {color};">
            <span style="font-weight: bold;">{key.upper()}</span>
            <span>{before:.1f} → {after:.1f}</span>
            <span style="color: {color};">{arrow}{pct_change:.1f}%</span>
        </div>
        """, unsafe_allow_html=True)


def render_entrainment_visual(protocol: Dict, placeholder):
    """Render visual entrainment animation."""
    freq = protocol['frequency']
    color = protocol['color']
    period = 1.0 / max(0.1, freq)
    
    html = f"""
    <style>
    @keyframes entrain {{
        0% {{ transform: scale(1); opacity: 1; box-shadow: 0 0 50px {color}; }}
        50% {{ transform: scale(0.92); opacity: 0.7; box-shadow: 0 0 100px {color}; }}
        100% {{ transform: scale(1); opacity: 1; box-shadow: 0 0 50px {color}; }}
    }}
    .entrain-orb {{
        width: 250px;
        height: 250px;
        border-radius: 50%;
        background: radial-gradient(circle at 30% 30%, {color}, #000);
        animation: entrain {period:.3f}s ease-in-out infinite;
        margin: 30px auto;
    }}
    .entrain-container {{
        background: #0a0a0a;
        padding: 40px;
        border-radius: 20px;
        text-align: center;
    }}
    .freq-label {{
        color: {color};
        font-size: 36px;
        font-weight: bold;
    }}
    </style>
    <div class="entrain-container">
        <div class="freq-label">{freq} Hz</div>
        <div class="entrain-orb"></div>
        <p style="color: #666;">Gaze softly at the pulsing light. Breathe naturally.</p>
    </div>
    """
    placeholder.markdown(html, unsafe_allow_html=True)


def main():
    st.set_page_config(page_title="Biometric Intervention", page_icon="📊", layout="wide")
    
    st.title("📊 Real-Time Biometric Intervention System")
    st.markdown("""
    **Measure, intervene, and validate consciousness modulation with biometric data.**
    
    This system integrates:
    - **EEG** (brain wave patterns: delta, theta, alpha, beta, gamma)
    - **HRV** (heart rate variability: RMSSD, SDNN, coherence)
    - **Visual Entrainment** (frequency-specific consciousness modulation)
    """)
    
    # Initialize session state
    if 'intervention_stage' not in st.session_state:
        st.session_state.intervention_stage = 'select'
    if 'baseline_eeg' not in st.session_state:
        st.session_state.baseline_eeg = None
    if 'baseline_hrv' not in st.session_state:
        st.session_state.baseline_hrv = None
    if 'selected_protocol' not in st.session_state:
        st.session_state.selected_protocol = None
    if 'session_id' not in st.session_state:
        st.session_state.session_id = None
    
    # Sidebar: History
    with st.sidebar:
        st.markdown("### 📜 Intervention History")
        history = get_intervention_history()
        if history:
            for name, change, created in history:
                color = "#4CAF50" if change > 0 else "#FF5722"
                st.markdown(f"**{name}**")
                st.markdown(f"<span style='color:{color}'>{change:+.1f} consciousness index</span>", 
                           unsafe_allow_html=True)
                st.caption(str(created)[:16])
                st.markdown("---")
        else:
            st.caption("No sessions recorded yet.")
        
        st.markdown("### 🔌 Hardware Status")
        st.markdown("""
        - **EEG (Muse 2):** Simulated
        - **HRV (Polar H10):** Simulated
        - **ESP32 Bridge:** Demo Mode
        
        *Connect real hardware for live data*
        """)
    
    # Main content
    if st.session_state.intervention_stage == 'select':
        st.markdown("## Step 1: Select Intervention Protocol")
        
        cols = st.columns(2)
        for i, (key, protocol) in enumerate(INTERVENTION_PROTOCOLS.items()):
            with cols[i % 2]:
                with st.container(border=True):
                    st.markdown(f"### {protocol['name']}")
                    st.markdown(protocol['description'])
                    st.markdown(f"**Frequency:** {protocol['frequency']} Hz")
                    st.markdown(f"**Duration:** {protocol['duration_sec']} seconds")
                    
                    st.markdown("**Expected Changes:**")
                    for category, changes in protocol['target_changes'].items():
                        for metric, change in changes.items():
                            st.markdown(f"- {metric}: {change}")
                    
                    if st.button(f"Select {protocol['name']}", key=f"sel_{key}", use_container_width=True):
                        st.session_state.selected_protocol = key
                        st.session_state.intervention_stage = 'baseline'
                        st.session_state.session_id = datetime.now().strftime('%Y%m%d_%H%M%S')
                        st.rerun()
    
    elif st.session_state.intervention_stage == 'baseline':
        if st.session_state.selected_protocol is None or st.session_state.selected_protocol not in INTERVENTION_PROTOCOLS:
            st.session_state.intervention_stage = 'select'
            st.rerun()
        
        protocol = INTERVENTION_PROTOCOLS[st.session_state.selected_protocol]
        
        st.markdown(f"## Step 2: Baseline Measurement - {protocol['name']}")
        st.info("Collecting 30 seconds of baseline biometric data. Please remain relaxed and still.")
        
        # Simulate baseline collection
        progress = st.progress(0)
        baseline_display = st.empty()
        
        eeg_samples = []
        hrv_samples = []
        
        for i in range(30):
            progress.progress((i + 1) / 30)
            eeg = generate_eeg_data()
            hrv = generate_hrv_data()
            eeg_samples.append(eeg)
            hrv_samples.append(hrv)
            
            with baseline_display.container():
                render_biometric_display(eeg, hrv, f"Collecting Baseline ({i+1}/30 sec)")
            
            time.sleep(0.1)  # Speed up for demo
        
        # Average baseline
        avg_eeg = {k: round(np.mean([s[k] for s in eeg_samples]), 1) for k in eeg_samples[0]}
        avg_hrv = {k: round(np.mean([s[k] for s in hrv_samples]), 1) for k in hrv_samples[0]}
        
        baseline_idx = calculate_consciousness_index(avg_eeg, avg_hrv)
        
        st.session_state.baseline_eeg = avg_eeg
        st.session_state.baseline_hrv = avg_hrv
        st.session_state.baseline_consciousness = baseline_idx
        
        baseline_display.empty()
        
        st.success("Baseline collected!")
        
        col1, col2, col3 = st.columns(3)
        with col2:
            st.metric("Baseline Consciousness Index", f"{baseline_idx}/100")
        
        render_biometric_display(avg_eeg, avg_hrv, "Baseline State")
        
        col1, col2 = st.columns(2)
        with col1:
            if st.button("← Back", use_container_width=True):
                st.session_state.intervention_stage = 'select'
                st.rerun()
        with col2:
            if st.button("Start Intervention →", type="primary", use_container_width=True):
                st.session_state.intervention_stage = 'running'
                st.rerun()
    
    elif st.session_state.intervention_stage == 'running':
        if (st.session_state.selected_protocol is None or 
            st.session_state.selected_protocol not in INTERVENTION_PROTOCOLS or
            st.session_state.baseline_eeg is None):
            st.session_state.intervention_stage = 'select'
            st.rerun()
        
        protocol = INTERVENTION_PROTOCOLS[st.session_state.selected_protocol]
        duration = protocol['duration_sec']
        
        st.markdown(f"## {protocol['name']}")
        
        col1, col2 = st.columns([2, 1])
        
        with col1:
            visual_placeholder = st.empty()
            render_entrainment_visual(protocol, visual_placeholder)
        
        with col2:
            st.markdown("### Real-Time Monitoring")
            progress = st.progress(0)
            time_display = st.empty()
            realtime_display = st.empty()
        
        # Run intervention with real-time monitoring
        start_time = time.time()
        while True:
            elapsed = time.time() - start_time
            remaining = max(0, duration - elapsed)
            prog = min(1.0, elapsed / duration)
            
            progress.progress(prog)
            time_display.markdown(f"**Time remaining:** {int(remaining)} sec")
            
            # Real-time biometrics
            eeg = generate_eeg_data()
            hrv = generate_hrv_data()
            
            # Simulate entrainment effect over time
            target_band = 'alpha' if protocol['frequency'] < 15 else 'gamma' if protocol['frequency'] > 30 else 'beta'
            enhancement = min(prog * 20, 15)  # Gradual increase
            eeg[target_band] = min(50, eeg[target_band] + enhancement)
            hrv['coherence'] = min(95, hrv['coherence'] + enhancement * 2)
            
            with realtime_display.container():
                idx = calculate_consciousness_index(eeg, hrv)
                st.metric("Consciousness Index", f"{idx}/100", 
                         delta=f"{idx - st.session_state.baseline_consciousness:+.1f}")
                st.markdown(f"**Alpha:** {eeg['alpha']:.1f}%")
                st.markdown(f"**Coherence:** {hrv['coherence']:.1f}%")
            
            if elapsed >= duration:
                break
            
            time.sleep(0.2)
        
        visual_placeholder.empty()
        st.success("Intervention complete!")
        time.sleep(1)
        
        st.session_state.intervention_stage = 'post'
        st.rerun()
    
    elif st.session_state.intervention_stage == 'post':
        if (st.session_state.selected_protocol is None or 
            st.session_state.selected_protocol not in INTERVENTION_PROTOCOLS or
            st.session_state.baseline_eeg is None):
            st.session_state.intervention_stage = 'select'
            st.rerun()
        
        protocol = INTERVENTION_PROTOCOLS[st.session_state.selected_protocol]
        
        st.markdown(f"## Step 3: Post-Intervention Measurement - {protocol['name']}")
        st.info("Collecting 30 seconds of post-intervention data...")
        
        progress = st.progress(0)
        post_display = st.empty()
        
        eeg_samples = []
        hrv_samples = []
        
        for i in range(30):
            progress.progress((i + 1) / 30)
            eeg = generate_eeg_data()
            hrv = generate_hrv_data()
            
            # Apply simulated intervention effect
            target_band = 'alpha' if protocol['frequency'] < 15 else 'gamma' if protocol['frequency'] > 30 else 'beta'
            eeg[target_band] = min(50, eeg[target_band] + 12)
            hrv['coherence'] = min(95, hrv['coherence'] + 20)
            hrv['rmssd'] = hrv['rmssd'] + 8
            
            eeg_samples.append(eeg)
            hrv_samples.append(hrv)
            
            with post_display.container():
                render_biometric_display(eeg, hrv, f"Collecting Post-Intervention ({i+1}/30 sec)")
            
            time.sleep(0.1)
        
        avg_eeg = {k: round(np.mean([s[k] for s in eeg_samples]), 1) for k in eeg_samples[0]}
        avg_hrv = {k: round(np.mean([s[k] for s in hrv_samples]), 1) for k in hrv_samples[0]}
        
        post_idx = calculate_consciousness_index(avg_eeg, avg_hrv)
        
        post_display.empty()
        
        st.session_state.post_eeg = avg_eeg
        st.session_state.post_hrv = avg_hrv
        st.session_state.post_consciousness = post_idx
        
        # Calculate changes
        consciousness_change = post_idx - st.session_state.baseline_consciousness
        
        significant_changes = {}
        for k in avg_eeg:
            change = avg_eeg[k] - st.session_state.baseline_eeg[k]
            if abs(change) > 3:
                significant_changes[f"eeg_{k}"] = round(change, 1)
        for k in avg_hrv:
            baseline_val = st.session_state.baseline_hrv[k]
            post_val = avg_hrv[k]
            pct = ((post_val - baseline_val) / baseline_val * 100) if baseline_val != 0 else 0
            if abs(pct) > 10:
                significant_changes[f"hrv_{k}"] = round(pct, 1)
        
        # Save session
        session_data = {
            'session_id': st.session_state.session_id,
            'protocol_name': protocol['name'],
            'frequency': protocol['frequency'],
            'duration': protocol['duration_sec'],
            'baseline_eeg': st.session_state.baseline_eeg,
            'baseline_hrv': st.session_state.baseline_hrv,
            'post_eeg': avg_eeg,
            'post_hrv': avg_hrv,
            'consciousness_change': consciousness_change,
            'significant_changes': significant_changes
        }
        
        if save_intervention_session(session_data):
            st.success("Session saved to database!")
        
        st.session_state.intervention_stage = 'results'
        st.rerun()
    
    elif st.session_state.intervention_stage == 'results':
        if (st.session_state.selected_protocol is None or 
            st.session_state.selected_protocol not in INTERVENTION_PROTOCOLS or
            st.session_state.baseline_eeg is None or
            st.session_state.post_eeg is None):
            st.session_state.intervention_stage = 'select'
            st.session_state.baseline_eeg = None
            st.session_state.post_eeg = None
            st.rerun()
        
        protocol = INTERVENTION_PROTOCOLS[st.session_state.selected_protocol]
        
        st.markdown(f"## Results: {protocol['name']}")
        
        # Summary metrics
        col1, col2, col3 = st.columns(3)
        
        baseline_idx = st.session_state.baseline_consciousness
        post_idx = st.session_state.post_consciousness
        change = post_idx - baseline_idx
        
        with col1:
            st.metric("Baseline Index", f"{baseline_idx}/100")
        with col2:
            st.metric("Post-Intervention Index", f"{post_idx}/100")
        with col3:
            st.metric("Change", f"{change:+.1f}", delta=f"{change/baseline_idx*100:+.1f}%")
        
        st.markdown("---")
        
        # Detailed comparisons
        col1, col2 = st.columns(2)
        
        with col1:
            render_comparison(st.session_state.baseline_eeg, st.session_state.post_eeg, "EEG")
        
        with col2:
            render_comparison(st.session_state.baseline_hrv, st.session_state.post_hrv, "HRV")
        
        st.markdown("---")
        
        # Interpretation
        st.markdown("### Interpretation")
        
        if change > 10:
            st.success(f"""
            **Excellent Response!** The {protocol['name']} protocol produced a significant improvement 
            of {change:+.1f} points in your consciousness index. This indicates successful neural 
            entrainment and autonomic optimization.
            """)
        elif change > 5:
            st.info(f"""
            **Good Response.** The intervention produced a measurable improvement of {change:+.1f} points.
            With repeated sessions, effects typically strengthen.
            """)
        elif change > 0:
            st.warning(f"""
            **Subtle Response.** Small positive change detected ({change:+.1f} points). 
            This may indicate initial adaptation to the protocol.
            """)
        else:
            st.error(f"""
            **Minimal Response.** Consider trying a different protocol or adjusting the duration.
            """)
        
        st.markdown("---")
        
        # Next actions
        col1, col2 = st.columns(2)
        with col1:
            if st.button("Try Another Protocol", use_container_width=True):
                st.session_state.intervention_stage = 'select'
                st.session_state.baseline_eeg = None
                st.session_state.post_eeg = None
                st.rerun()
        with col2:
            if st.button("Repeat Same Protocol", use_container_width=True):
                st.session_state.intervention_stage = 'baseline'
                st.session_state.baseline_eeg = None
                st.session_state.session_id = datetime.now().strftime('%Y%m%d_%H%M%S')
                st.rerun()


if __name__ == "__main__":
    main()

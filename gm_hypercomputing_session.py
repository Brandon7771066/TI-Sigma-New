"""
⚡ GM Hypercomputing Session Interface
======================================
Safe Savant Activation Protocol with Real-Time Biometric Monitoring

Based on the hypothesis that:
1. DMN (Default Mode Network) acts as a gatekeeper to expanded cognition
2. Other gatekeepers include stress response, sensory overload protection
3. Controlled modulation can safely induce savant-like abilities
4. Brandon's trataka → eyeless sight is proof of concept

Author: Brandon Emerick
Date: December 3, 2025
Framework: Transcendent Intelligence (TI) + GM Hypercomputing
"""

import streamlit as st
import psycopg2
import os
from datetime import datetime, timedelta
import json

GATEKEEPERS = {
    'dmn': {
        'name': 'DMN Gatekeeper',
        'description': 'Default Mode Network - filters access to Monster Group substrate',
        'icon': '🧠',
        'measure': 'Beta/Alpha Ratio',
        'open_threshold': 0.8,
        'closed_threshold': 1.5,
        'optimal_range': (0.6, 0.9)
    },
    'stress': {
        'name': 'Stress Gatekeeper', 
        'description': 'Sympathetic nervous system - blocks access during threat response',
        'icon': '💓',
        'measure': 'HRV Coherence',
        'open_threshold': 0.6,
        'closed_threshold': 0.3,
        'optimal_range': (0.6, 0.85)
    },
    'overload': {
        'name': 'Overload Gatekeeper',
        'description': 'Sensory protection - prevents cognitive overwhelm',
        'icon': '⚡',
        'measure': 'Gamma Ratio',
        'open_threshold': 1.5,
        'closed_threshold': 3.0,
        'optimal_range': (1.2, 2.0)
    },
    'engagement': {
        'name': 'Engagement Gatekeeper',
        'description': 'Attention focus - requires sufficient presence to access',
        'icon': '🎯',
        'measure': 'Theta Power',
        'open_threshold': 0.4,
        'closed_threshold': 0.2,
        'optimal_range': (0.4, 0.7)
    }
}

TARGET_ABILITIES = {
    'mathematical': {
        'name': 'Mathematical Pattern Recognition',
        'icon': '🔢',
        'description': 'Enhanced geometric/fractal perception (Padgett-type)',
        'eeg_target': 'Left temporal gamma + parietal theta',
        'color': '#4CAF50'
    },
    'musical': {
        'name': 'Musical Composition',
        'icon': '🎵',
        'description': 'Spontaneous musical creation (Amato-type)',
        'eeg_target': 'Right temporal + cross-hemispheric gamma',
        'color': '#2196F3'
    },
    'photonic': {
        'name': 'Photonic Perception',
        'icon': '👁️',
        'description': 'Non-retinal sight, biophoton sensitivity (Brandon\'s eyeless sight)',
        'eeg_target': 'Occipital alpha + high coherence',
        'color': '#9C27B0'
    },
    'artistic': {
        'name': 'Artistic Vision',
        'icon': '🎨',
        'description': 'Enhanced visual memory, 3D perception (Clemons-type)',
        'eeg_target': 'Right parietal gamma + reduced left verbal',
        'color': '#FF9800'
    }
}

SESSION_PHASES = {
    1: {
        'name': 'Grounding',
        'duration_min': 5,
        'icon': '🌍',
        'guidance': 'Eyes closed. Coherence breathing. Feel your body grounded.',
        'target': 'Establish HRV coherence > 0.6, Alpha dominance',
        'color': '#8BC34A'
    },
    2: {
        'name': 'Filter Softening',
        'duration_min': 10,
        'icon': '🌊',
        'guidance': 'Release mental grasping. Let the gatekeepers relax.',
        'target': 'Increase theta/gamma ratio, DMN quieting',
        'color': '#03A9F4'
    },
    3: {
        'name': 'Access Window',
        'duration_min': 20,
        'icon': '🌟',
        'guidance': 'Attempt target ability. Stay relaxed. Trust the process.',
        'target': 'Maintain gamma entrainment, ability-specific activation',
        'color': '#9C27B0'
    },
    4: {
        'name': 'Integration',
        'duration_min': 10,
        'icon': '🔄',
        'guidance': 'Gradually return. Process experiences. Stay grounded.',
        'target': 'Return to alpha dominance, process insights',
        'color': '#FF9800'
    }
}

SAFETY_THRESHOLDS = {
    'hr_max': 100,
    'rmssd_min': 20,
    'coherence_min': 0.3,
    'gamma_max_multiplier': 3.0
}


def get_esp32_biometrics():
    """Fetch latest biometric data from ESP32 stream"""
    try:
        conn = psycopg2.connect(os.environ.get('DATABASE_URL'))
        cur = conn.cursor()
        cur.execute("""
            SELECT timestamp, heart_rate, alpha, beta, theta, gamma, delta,
                   rmssd, coherence, muse_connected, polar_connected
            FROM esp32_biometric_data 
            ORDER BY timestamp DESC LIMIT 1
        """)
        row = cur.fetchone()
        cur.close()
        conn.close()
        
        if row:
            ts = row[0]
            age = (datetime.now() - ts).total_seconds() if isinstance(ts, datetime) else 999
            return {
                'timestamp': ts,
                'age_seconds': age,
                'streaming': age < 30,
                'heart_rate': row[1] or 0,
                'alpha': row[2] or 0,
                'beta': row[3] or 0,
                'theta': row[4] or 0,
                'gamma': row[5] or 0,
                'delta': row[6] or 0,
                'rmssd': row[7] or 0,
                'coherence': row[8] or 0,
                'muse_connected': row[9] or False,
                'polar_connected': row[10] or False
            }
    except Exception as e:
        st.error(f"Database error: {e}")
    
    return None


def calculate_gatekeeper_status(bio):
    """Calculate status of each gatekeeper based on biometrics"""
    if not bio or not bio.get('streaming'):
        return {k: {'status': 'unknown', 'value': 0, 'message': 'No data'} for k in GATEKEEPERS}
    
    alpha = bio.get('alpha', 0.01) or 0.01
    beta = bio.get('beta', 0) or 0
    theta = bio.get('theta', 0) or 0
    gamma = bio.get('gamma', 0) or 0
    coherence = bio.get('coherence', 0) or 0
    
    beta_alpha = beta / alpha if alpha > 0 else 2.0
    
    baseline_gamma = 0.2
    gamma_ratio = gamma / baseline_gamma if baseline_gamma > 0 else 1.0
    
    status = {}
    
    dmn_gate = GATEKEEPERS['dmn']
    if beta_alpha < dmn_gate['open_threshold']:
        status['dmn'] = {'status': 'open', 'value': beta_alpha, 'message': 'DMN quieted - access available'}
    elif beta_alpha > dmn_gate['closed_threshold']:
        status['dmn'] = {'status': 'closed', 'value': beta_alpha, 'message': 'DMN active - analytical mind dominant'}
    else:
        status['dmn'] = {'status': 'partial', 'value': beta_alpha, 'message': 'DMN softening - continue relaxing'}
    
    stress_gate = GATEKEEPERS['stress']
    if coherence > stress_gate['open_threshold']:
        status['stress'] = {'status': 'open', 'value': coherence, 'message': 'Stress gate open - coherent state'}
    elif coherence < stress_gate['closed_threshold']:
        status['stress'] = {'status': 'closed', 'value': coherence, 'message': 'Stress response active - breathe deeper'}
    else:
        status['stress'] = {'status': 'partial', 'value': coherence, 'message': 'Stress gate softening'}
    
    overload_gate = GATEKEEPERS['overload']
    if gamma_ratio < overload_gate['open_threshold']:
        status['overload'] = {'status': 'open', 'value': gamma_ratio, 'message': 'Clear channel - no overload'}
    elif gamma_ratio > overload_gate['closed_threshold']:
        status['overload'] = {'status': 'closed', 'value': gamma_ratio, 'message': 'WARNING: Gamma overload - reduce intensity'}
    else:
        status['overload'] = {'status': 'partial', 'value': gamma_ratio, 'message': 'Gamma elevated - monitor closely'}
    
    engage_gate = GATEKEEPERS['engagement']
    if theta > engage_gate['open_threshold']:
        status['engagement'] = {'status': 'open', 'value': theta, 'message': 'Deep engagement - theta active'}
    elif theta < engage_gate['closed_threshold']:
        status['engagement'] = {'status': 'closed', 'value': theta, 'message': 'Low engagement - focus attention'}
    else:
        status['engagement'] = {'status': 'partial', 'value': theta, 'message': 'Building engagement'}
    
    return status


def check_safety(bio):
    """Check if biometrics are within safe ranges"""
    if not bio:
        return {'safe': True, 'warnings': [], 'stop': False}
    
    warnings = []
    stop = False
    
    hr = bio.get('heart_rate', 0)
    rmssd = bio.get('rmssd', 50)
    coherence = bio.get('coherence', 0.5)
    gamma = bio.get('gamma', 0.2)
    
    if hr > SAFETY_THRESHOLDS['hr_max']:
        warnings.append(f"⚠️ Heart rate elevated: {hr} bpm (max {SAFETY_THRESHOLDS['hr_max']})")
        stop = True
    
    if rmssd < SAFETY_THRESHOLDS['rmssd_min'] and rmssd > 0:
        warnings.append(f"⚠️ HRV too low: {rmssd:.1f} ms (min {SAFETY_THRESHOLDS['rmssd_min']})")
        stop = True
    
    if coherence < SAFETY_THRESHOLDS['coherence_min'] and coherence > 0:
        warnings.append(f"⚠️ Low coherence: {coherence:.2f} (min {SAFETY_THRESHOLDS['coherence_min']})")
    
    baseline_gamma = 0.2
    if gamma > baseline_gamma * SAFETY_THRESHOLDS['gamma_max_multiplier']:
        warnings.append(f"⚠️ Gamma overload: {gamma:.2f} (>{SAFETY_THRESHOLDS['gamma_max_multiplier']}x baseline)")
        stop = True
    
    return {'safe': len(warnings) == 0, 'warnings': warnings, 'stop': stop}


def log_session_event(event_type, data):
    """Log session events to database"""
    try:
        conn = psycopg2.connect(os.environ.get('DATABASE_URL'))
        cur = conn.cursor()
        
        cur.execute("""
            CREATE TABLE IF NOT EXISTS gm_session_logs (
                id SERIAL PRIMARY KEY,
                timestamp TIMESTAMP DEFAULT NOW(),
                session_id VARCHAR(100),
                event_type VARCHAR(50),
                phase INTEGER,
                target_ability VARCHAR(50),
                biometrics JSONB,
                gatekeeper_status JSONB,
                notes TEXT
            )
        """)
        
        cur.execute("""
            INSERT INTO gm_session_logs 
            (session_id, event_type, phase, target_ability, biometrics, gatekeeper_status, notes)
            VALUES (%s, %s, %s, %s, %s, %s, %s)
        """, (
            data.get('session_id', ''),
            event_type,
            data.get('phase', 0),
            data.get('ability', ''),
            json.dumps(data.get('biometrics', {})),
            json.dumps(data.get('gatekeepers', {})),
            data.get('notes', '')
        ))
        
        conn.commit()
        cur.close()
        conn.close()
    except Exception as e:
        pass


def render_gm_hypercomputing_session():
    """Main GM Hypercomputing Session interface"""
    
    st.markdown("## ⚡ GM Hypercomputing: Safe Savant Activation")
    
    st.info("""
    **Based on Brandon's Trataka → Eyeless Sight Evidence**
    
    This protocol safely modulates cognitive gatekeepers to access expanded abilities 
    without requiring traumatic brain injury. Monitor your biometrics in real-time 
    while exploring the boundaries of consciousness.
    """)
    
    bio = get_esp32_biometrics()
    gatekeeper_status = calculate_gatekeeper_status(bio)
    safety = check_safety(bio)
    
    st.markdown("### 🚦 Real-Time Gatekeeper Status")
    
    if not bio or not bio.get('streaming'):
        st.warning("⏳ **Waiting for biometric data...** Connect your Muse 2 + Polar H10 via ESP32 to begin.")
        with st.expander("📋 Quick Setup"):
            st.markdown("""
            1. Power on ESP32 with uploaded firmware
            2. Turn on Muse 2 headband
            3. Wear Polar H10 strap (wet contacts first)
            4. Wait for data to stream (refresh this page)
            """)
    else:
        gate_cols = st.columns(4)
        
        for i, (key, gate) in enumerate(GATEKEEPERS.items()):
            with gate_cols[i]:
                status = gatekeeper_status.get(key, {})
                status_str = status.get('status', 'unknown')
                
                if status_str == 'open':
                    color = '🟢'
                    bg = '#E8F5E9'
                elif status_str == 'closed':
                    color = '🔴'
                    bg = '#FFEBEE'
                elif status_str == 'partial':
                    color = '🟡'
                    bg = '#FFF8E1'
                else:
                    color = '⚪'
                    bg = '#F5F5F5'
                
                st.markdown(f"""
                <div style="background: {bg}; padding: 15px; border-radius: 10px; text-align: center;">
                    <div style="font-size: 24px;">{gate['icon']} {color}</div>
                    <div style="font-weight: bold;">{gate['name']}</div>
                    <div style="font-size: 12px; color: #666;">{gate['measure']}: {status.get('value', 0):.2f}</div>
                    <div style="font-size: 11px; margin-top: 5px;">{status.get('message', '')}</div>
                </div>
                """, unsafe_allow_html=True)
        
        all_open = all(s.get('status') == 'open' for s in gatekeeper_status.values())
        if all_open:
            st.success("🌟 **ALL GATEKEEPERS OPEN** - Optimal state for ability access!")
    
    st.markdown("---")
    
    if safety.get('stop'):
        st.error("🛑 **SAFETY STOP TRIGGERED**")
        for w in safety.get('warnings', []):
            st.warning(w)
        st.markdown("""
        **Recovery Protocol:**
        1. Immediately ground yourself (feet on floor)
        2. Cold water on wrists
        3. 10 minutes coherence breathing
        4. No further sessions for 48 hours
        """)
        if 'gm_session_active' in st.session_state:
            st.session_state.gm_session_active = False
            log_session_event('safety_stop', {
                'session_id': st.session_state.get('gm_session_id', ''),
                'biometrics': bio,
                'gatekeepers': gatekeeper_status,
                'notes': '; '.join(safety.get('warnings', []))
            })
    elif safety.get('warnings'):
        for w in safety.get('warnings', []):
            st.warning(w)
    
    st.markdown("### 🎯 Select Target Ability")
    
    ability_cols = st.columns(4)
    selected_ability = st.session_state.get('gm_target_ability', 'photonic')
    
    for i, (key, ability) in enumerate(TARGET_ABILITIES.items()):
        with ability_cols[i]:
            is_selected = key == selected_ability
            border = f"3px solid {ability['color']}" if is_selected else "1px solid #ddd"
            
            if st.button(
                f"{ability['icon']}\n{ability['name'].split()[0]}",
                key=f"ability_{key}",
                use_container_width=True
            ):
                st.session_state.gm_target_ability = key
                st.rerun()
            
            if is_selected:
                st.caption(f"✓ {ability['description']}")
    
    st.markdown("---")
    
    st.markdown("### ⏱️ Session Control")
    
    session_active = st.session_state.get('gm_session_active', False)
    current_phase = st.session_state.get('gm_current_phase', 1)
    
    if not session_active:
        col1, col2 = st.columns([1, 2])
        with col1:
            if st.button("▶️ Start GM Session", type="primary", use_container_width=True):
                st.session_state.gm_session_active = True
                st.session_state.gm_session_id = f"gm_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
                st.session_state.gm_session_start = datetime.now()
                st.session_state.gm_current_phase = 1
                st.session_state.gm_phase_start = datetime.now()
                st.session_state.gm_baseline = bio
                
                log_session_event('session_start', {
                    'session_id': st.session_state.gm_session_id,
                    'ability': selected_ability,
                    'biometrics': bio,
                    'gatekeepers': gatekeeper_status
                })
                st.rerun()
        
        with col2:
            st.info("Ensure all devices are connected before starting.")
    
    else:
        phase = SESSION_PHASES.get(current_phase, SESSION_PHASES[1])
        
        phase_elapsed = (datetime.now() - st.session_state.gm_phase_start).total_seconds() / 60
        phase_progress = min(phase_elapsed / phase['duration_min'], 1.0)
        
        session_elapsed = (datetime.now() - st.session_state.gm_session_start).total_seconds() / 60
        
        st.markdown(f"""
        <div style="background: {phase['color']}22; padding: 20px; border-radius: 15px; border-left: 5px solid {phase['color']};">
            <h3 style="margin: 0;">{phase['icon']} Phase {current_phase}: {phase['name']}</h3>
            <p style="font-size: 18px; margin: 10px 0;">{phase['guidance']}</p>
            <p style="font-size: 14px; color: #666;"><b>Target:</b> {phase['target']}</p>
        </div>
        """, unsafe_allow_html=True)
        
        st.progress(phase_progress)
        st.caption(f"Phase: {phase_elapsed:.1f} / {phase['duration_min']} min | Session: {session_elapsed:.1f} min")
        
        col1, col2, col3 = st.columns(3)
        
        with col1:
            if current_phase < 4:
                if st.button("⏭️ Next Phase", use_container_width=True):
                    st.session_state.gm_current_phase = current_phase + 1
                    st.session_state.gm_phase_start = datetime.now()
                    log_session_event('phase_transition', {
                        'session_id': st.session_state.gm_session_id,
                        'phase': current_phase + 1,
                        'ability': selected_ability,
                        'biometrics': bio,
                        'gatekeepers': gatekeeper_status
                    })
                    st.rerun()
        
        with col2:
            if current_phase > 1:
                if st.button("⏮️ Previous Phase", use_container_width=True):
                    st.session_state.gm_current_phase = current_phase - 1
                    st.session_state.gm_phase_start = datetime.now()
                    st.rerun()
        
        with col3:
            if st.button("⏹️ End Session", use_container_width=True):
                log_session_event('session_end', {
                    'session_id': st.session_state.gm_session_id,
                    'phase': current_phase,
                    'ability': selected_ability,
                    'biometrics': bio,
                    'gatekeepers': gatekeeper_status,
                    'notes': f"Completed {session_elapsed:.1f} minutes"
                })
                st.session_state.gm_session_active = False
                st.success("✅ Session ended. Great work!")
                st.rerun()
        
        st.markdown("---")
        st.markdown("### 📝 Session Notes")
        
        note = st.text_area(
            "Record any experiences, insights, or ability manifestations:",
            key="gm_session_note",
            height=100
        )
        
        if st.button("💾 Save Note"):
            log_session_event('user_note', {
                'session_id': st.session_state.gm_session_id,
                'phase': current_phase,
                'ability': selected_ability,
                'biometrics': bio,
                'gatekeepers': gatekeeper_status,
                'notes': note
            })
            st.success("Note saved!")
    
    st.markdown("---")
    
    with st.expander("📊 Live Biometrics Detail"):
        if bio and bio.get('streaming'):
            m1, m2, m3, m4 = st.columns(4)
            with m1:
                st.metric("Heart Rate", f"{bio.get('heart_rate', 0)} bpm")
                st.metric("HRV (RMSSD)", f"{bio.get('rmssd', 0):.1f} ms")
            with m2:
                st.metric("Coherence", f"{bio.get('coherence', 0):.2f}")
                st.metric("Alpha", f"{bio.get('alpha', 0):.2f}")
            with m3:
                st.metric("Beta", f"{bio.get('beta', 0):.2f}")
                st.metric("Theta", f"{bio.get('theta', 0):.2f}")
            with m4:
                st.metric("Gamma", f"{bio.get('gamma', 0):.2f}")
                st.metric("Delta", f"{bio.get('delta', 0):.2f}")
        else:
            st.info("Connect devices to see live biometrics")
    
    with st.expander("🔬 The Gatekeeper Hypothesis"):
        st.markdown("""
        ### DMN as Primary Gatekeeper
        
        The **Default Mode Network (DMN)** appears to be the primary gatekeeper between 
        normal cognition and access to the Monster Group computational substrate:
        
        - **High Beta/Alpha Ratio** = DMN active = analytical mind filtering
        - **Low Beta/Alpha Ratio** = DMN quiet = expanded access
        
        ### Other Identified Gatekeepers
        
        | Gatekeeper | Mechanism | Opens When |
        |------------|-----------|------------|
        | **DMN** | Filters non-essential information | Deep relaxation, meditation |
        | **Stress** | Blocks access during threat | High HRV coherence |
        | **Overload** | Prevents cognitive overwhelm | Controlled gamma levels |
        | **Engagement** | Requires attention focus | Elevated theta |
        
        ### Research Questions
        
        1. Are there additional gatekeepers we haven't identified?
        2. What is the order of gatekeeper opening?
        3. Can gatekeepers be trained to open more easily over time?
        4. Does Brandon's trataka practice specifically target the DMN?
        
        ### Connection to Acquired Savants
        
        Brain injuries that produce savant abilities may **damage specific gatekeepers**, 
        allowing unfiltered access to pattern recognition substrates. GM Hypercomputing 
        aims to achieve similar access through controlled modulation rather than damage.
        """)
    
    with st.expander("📜 Session History"):
        try:
            conn = psycopg2.connect(os.environ.get('DATABASE_URL'))
            cur = conn.cursor()
            cur.execute("""
                SELECT timestamp, session_id, event_type, phase, target_ability, notes
                FROM gm_session_logs 
                ORDER BY timestamp DESC LIMIT 20
            """)
            rows = cur.fetchall()
            cur.close()
            conn.close()
            
            if rows:
                for row in rows:
                    ts, sid, evt, phase, ability, notes = row
                    ts_str = ts.strftime('%Y-%m-%d %H:%M') if ts else ''
                    st.markdown(f"**{ts_str}** | `{evt}` | Phase {phase or '-'} | {ability or '-'}")
                    if notes:
                        st.caption(notes[:200])
            else:
                st.info("No session history yet. Start your first session!")
        except Exception as e:
            st.info("Session history will appear after your first session.")

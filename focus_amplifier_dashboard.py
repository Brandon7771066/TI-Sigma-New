"""
Focus Amplifier Dashboard
Real-time biometric-driven focus optimization for ADHD management.
"""

import streamlit as st
import time
import numpy as np
from datetime import datetime
from engines.focus_amplifier import FocusAmplifierProtocol, FOCUS_MODES


def render_focus_amplifier():
    st.header("🎯 Focus Amplifier")
    st.caption("Biometric-driven focus optimization — Concentration, Open Awareness, and Flow")

    if 'focus_protocol' not in st.session_state:
        st.session_state.focus_protocol = FocusAmplifierProtocol()
    if 'focus_running' not in st.session_state:
        st.session_state.focus_running = False
    if 'focus_mode' not in st.session_state:
        st.session_state.focus_mode = 'concentration'
    if 'focus_duration' not in st.session_state:
        st.session_state.focus_duration = 30

    protocol = st.session_state.focus_protocol

    if not st.session_state.focus_running:
        _render_setup(protocol)
    else:
        _render_active_session(protocol)


def _render_setup(protocol: FocusAmplifierProtocol):
    st.markdown("### Choose Your Focus Mode")

    mode_cols = st.columns(3)
    for i, (mode_key, mode_info) in enumerate(FOCUS_MODES.items()):
        with mode_cols[i]:
            selected = st.session_state.focus_mode == mode_key
            border_color = "#00ff88" if selected else "#333"
            st.markdown(f"""
            <div style="border: 2px solid {border_color}; border-radius: 12px; 
                        padding: 16px; text-align: center; min-height: 220px;
                        background: {'rgba(0,255,136,0.05)' if selected else 'transparent'};">
                <h2>{mode_info['icon']}</h2>
                <h4>{mode_info['name']}</h4>
                <p style="font-size: 0.85em; color: #aaa;">{mode_info['description']}</p>
                <p style="font-size: 0.8em; color: #888;"><b>Best for:</b> {mode_info['best_for']}</p>
            </div>
            """, unsafe_allow_html=True)
            if st.button(f"Select {mode_info['name']}", key=f"select_{mode_key}",
                        use_container_width=True,
                        type="primary" if selected else "secondary"):
                st.session_state.focus_mode = mode_key
                st.rerun()

    st.markdown("---")

    col_dur, col_tip = st.columns([1, 2])
    with col_dur:
        st.markdown("### Session Duration")
        duration = st.selectbox(
            "How long do you want to focus?",
            options=[15, 30, 45, 60, 90, 120],
            index=1,
            format_func=lambda x: f"{x} minutes",
            key="duration_select"
        )
        st.session_state.focus_duration = duration

        custom = st.number_input("Or enter custom minutes:", min_value=5,
                                max_value=480, value=30, step=5,
                                key="custom_duration")
        if st.button("Use custom duration"):
            st.session_state.focus_duration = custom

    with col_tip:
        mode_info = FOCUS_MODES[st.session_state.focus_mode]
        st.markdown(f"### {mode_info['icon']} {mode_info['name']} Tips")
        st.info(f"**ADHD Tip:** {mode_info['adhd_tip']}")

        if mode_info['breathing']['inhale'] > 0:
            b = mode_info['breathing']
            parts = [f"Inhale {b['inhale']}s"]
            if b.get('hold', 0) > 0:
                parts.append(f"Hold {b['hold']}s")
            parts.append(f"Exhale {b['exhale']}s")
            if b.get('pause', 0) > 0:
                parts.append(f"Pause {b['pause']}s")
            st.markdown(f"**Breathing Pattern:** {' → '.join(parts)}")
            total = b['inhale'] + b.get('hold', 0) + b['exhale'] + b.get('pause', 0)
            bpm = round(60 / total, 1) if total > 0 else 0
            st.markdown(f"**Breathing Rate:** ~{bpm} breaths/min")
        else:
            st.markdown("**Breathing:** Natural, unforced — let rhythm emerge")

        st.markdown(f"**Target Arousal:** {mode_info['target_arousal']}")
        st.markdown(f"**Optimal LF/HF:** {mode_info['target_lf_hf']}")

    st.markdown("---")

    col_start, col_heart = st.columns(2)
    with col_start:
        if st.button("🚀 Start Focus Session", type="primary", use_container_width=True):
            result = protocol.start_session(
                mode=st.session_state.focus_mode,
                duration_minutes=st.session_state.focus_duration
            )
            st.session_state.focus_running = True
            st.rerun()

    with col_heart:
        heart = protocol.read_heart()
        if heart['connected']:
            st.success(f"💓 Polar H10 Connected — HR: {heart['hr']} bpm")
        else:
            st.warning("💔 No heart rate data. Connect Polar H10 via Pulsoid for biometric feedback.")
            st.caption("Session will work without biometrics, but feedback will be limited.")

    history = protocol.get_session_history()
    if history:
        st.markdown("### 📊 Recent Sessions")
        for sess in history[:5]:
            mode_name = FOCUS_MODES.get(sess.get('mode', ''), {}).get('name', sess.get('mode', 'Unknown'))
            dur = sess.get('duration_minutes', 0)
            avg_focus = sess.get('avg_focus_score', 0)
            time_zone = sess.get('time_in_zone_pct', 0)
            ts = sess.get('timestamp', '')
            st.markdown(
                f"**{ts[:16]}** — {mode_name} | "
                f"{dur:.0f} min | "
                f"Avg Focus: {avg_focus*100:.0f}% | "
                f"In Zone: {time_zone:.0f}%"
            )


def _render_active_session(protocol: FocusAmplifierProtocol):
    state = protocol.get_focus_state()

    session = state['session']
    phase = state['phase']
    focus = state['focus']
    heart = state['heart']
    hrv = state['hrv']
    coherence = state['coherence']
    trends = state['trends']
    mode_info = session['mode_info']

    top_left, top_mid, top_right = st.columns([2, 1, 1])

    with top_left:
        remaining = session['remaining_minutes']
        elapsed = session['elapsed_minutes']
        progress = session['progress_pct']

        if remaining > 0:
            mins = int(remaining)
            secs = int((remaining - mins) * 60)
            st.markdown(f"""
            <div style="text-align: center; padding: 8px; background: rgba(0,0,0,0.3); 
                        border-radius: 12px; border: 1px solid #444;">
                <div style="font-size: 2.5em; font-weight: bold; color: #00ff88; 
                            font-family: monospace;">{mins:02d}:{secs:02d}</div>
                <div style="color: #aaa; font-size: 0.9em;">remaining</div>
            </div>
            """, unsafe_allow_html=True)
        else:
            st.markdown(f"""
            <div style="text-align: center; padding: 8px; background: rgba(0,255,136,0.1); 
                        border-radius: 12px; border: 1px solid #00ff88;">
                <div style="font-size: 2em; font-weight: bold; color: #00ff88;">Session Complete!</div>
            </div>
            """, unsafe_allow_html=True)

        st.progress(min(1.0, progress / 100))

    with top_mid:
        st.metric("Mode", f"{mode_info['icon']} {mode_info['name']}")
        st.metric("Phase", phase['name'])

    with top_right:
        if heart['connected']:
            st.metric("💓 HR", f"{heart['hr']} bpm")
        else:
            st.metric("💓 HR", "—")
        st.metric("Zone Entries", session['zone_entries'])

    st.markdown("---")

    focus_col, details_col = st.columns([1, 1])

    with focus_col:
        score = focus['focus_score']
        pct = focus['focus_pct']
        grade = focus['grade']

        if score > 0.8:
            color = "#00ff88"
        elif score > 0.6:
            color = "#88ff00"
        elif score > 0.4:
            color = "#ffaa00"
        else:
            color = "#ff4444"

        st.markdown(f"""
        <div style="text-align: center; padding: 20px; background: rgba(0,0,0,0.3); 
                    border-radius: 16px; border: 2px solid {color};">
            <div style="font-size: 3em; font-weight: bold; color: {color};">{pct:.0f}%</div>
            <div style="font-size: 1.2em; color: {color}; margin-top: 4px;">{grade}</div>
            <div style="color: #888; font-size: 0.85em; margin-top: 8px;">Focus Score</div>
        </div>
        """, unsafe_allow_html=True)

        st.markdown(f"**💡 Guidance:** {focus['recommendation']}")

    with details_col:
        st.markdown("#### Component Scores")
        if focus.get('components'):
            for comp_key, comp in focus['components'].items():
                comp_score = comp.get('score', 0)
                label = comp.get('label', comp_key)
                bar_color = "green" if comp_score > 0.6 else ("orange" if comp_score > 0.3 else "red")
                st.markdown(f"**{label}** — {comp_score*100:.0f}%")
                st.progress(min(1.0, comp_score))

    st.markdown("---")

    if hrv.get('sufficient_data'):
        hrv_cols = st.columns(4)
        with hrv_cols[0]:
            st.metric("RMSSD", f"{hrv['rmssd']:.1f} ms")
        with hrv_cols[1]:
            st.metric("LF/HF Ratio", f"{hrv['lf_hf_ratio']:.2f}")
        with hrv_cols[2]:
            st.metric("Coherence", f"{coherence['coherence_pct']:.0f}%")
        with hrv_cols[3]:
            st.metric("Arousal", f"{hrv['arousal_level']*100:.0f}%")

    if trends['focus_trend'] and len(trends['focus_trend']) > 2:
        st.markdown("#### 📈 Focus Trend")
        import pandas as pd
        focus_data = trends['focus_trend']
        df = pd.DataFrame({
            'Time (samples)': range(len(focus_data)),
            'Focus Score': [s * 100 for s in focus_data]
        })
        st.line_chart(df.set_index('Time (samples)'), height=200)

    if trends['hr_trend'] and len(trends['hr_trend']) > 2:
        hr_data = trends['hr_trend']
        hrv_data = trends['hrv_trend']
        hr_col, hrv_col = st.columns(2)
        with hr_col:
            st.markdown("#### Heart Rate")
            import pandas as pd
            df_hr = pd.DataFrame({'HR (bpm)': hr_data})
            st.line_chart(df_hr, height=150)
        with hrv_col:
            st.markdown("#### HRV (RMSSD)")
            df_hrv = pd.DataFrame({'RMSSD (ms)': hrv_data})
            st.line_chart(df_hrv, height=150)

    st.markdown("---")

    breathing = state.get('breathing', {})
    if breathing.get('inhale', 0) > 0:
        st.markdown("#### 🫁 Breathing Guide")
        b = breathing
        parts = []
        if b['inhale'] > 0:
            parts.append(f"**Inhale {b['inhale']}s**")
        if b.get('hold', 0) > 0:
            parts.append(f"**Hold {b['hold']}s**")
        if b['exhale'] > 0:
            parts.append(f"**Exhale {b['exhale']}s**")
        if b.get('pause', 0) > 0:
            parts.append(f"**Pause {b['pause']}s**")
        st.markdown(" → ".join(parts))

    st.markdown("---")
    ctrl_cols = st.columns(4)

    with ctrl_cols[0]:
        if st.button("⏹️ End Session", type="secondary", use_container_width=True):
            summary = protocol.stop_session()
            st.session_state.focus_running = False
            st.success(
                f"Session complete! Avg focus: {summary['avg_focus_score']*100:.0f}% | "
                f"Time in zone: {summary['time_in_zone_pct']:.0f}% | "
                f"Duration: {summary['duration_minutes']:.1f} min"
            )
            time.sleep(3)
            st.rerun()

    with ctrl_cols[1]:
        if st.button("🎯 Concentration", use_container_width=True,
                     disabled=session['mode'] == 'concentration'):
            protocol.switch_mode('concentration')

    with ctrl_cols[2]:
        if st.button("🌊 Open Awareness", use_container_width=True,
                     disabled=session['mode'] == 'open_awareness'):
            protocol.switch_mode('open_awareness')

    with ctrl_cols[3]:
        if st.button("⚡ Flow", use_container_width=True,
                     disabled=session['mode'] == 'flow'):
            protocol.switch_mode('flow')

    if session['remaining'] <= 0 and st.session_state.focus_running:
        st.balloons()
        st.success("🎉 Session target reached! You can keep going or end the session.")

    if st.session_state.focus_running:
        time.sleep(2)
        st.rerun()

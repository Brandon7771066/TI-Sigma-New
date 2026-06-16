"""
LCC Sleep Induction Protocol Dashboard
==========================================
Calming night-mode UI for sleep induction using LCC attractor basins.
"""

import streamlit as st
import os
import time
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from engines.lcc_sleep_induction import LCCSleepProtocol

st.set_page_config(page_title="LCC Sleep Protocol", page_icon="\U0001F319", layout="wide")

st.markdown("""
<style>
    .stApp { background-color: #050510; }
    h1, h2, h3 { color: #aabbcc !important; }
    .stMarkdown { color: #8899aa; }
    .sleep-title {
        text-align: center;
        font-size: 2.2em;
        background: linear-gradient(135deg, #1a3a5c, #4a6fa5, #2a4a7a);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0;
    }
    .sleep-subtitle {
        text-align: center;
        color: #556677;
        font-size: 1.0em;
        margin-top: 0;
    }
    .phase-card {
        padding: 16px;
        border-radius: 12px;
        margin: 6px 0;
        background: linear-gradient(135deg, #050515, #0a0a20);
    }
    .phase-active {
        border: 2px solid #4a6fa5;
        box-shadow: 0 0 15px #4a6fa522;
    }
    .phase-completed {
        border: 1px solid #3a5a3a44;
        opacity: 0.7;
    }
    .phase-pending {
        border: 1px solid #222;
        opacity: 0.4;
    }
    .gate-pass { color: #5a8a5a; }
    .gate-fail { color: #8a5a5a; }
    .breathing-guide {
        text-align: center;
        padding: 30px;
        border-radius: 15px;
        background: linear-gradient(135deg, #050520, #0a0a30);
        border: 1px solid #2a3a5a33;
    }
    .sleep-meter {
        height: 16px;
        border-radius: 8px;
        background: #0a0a1a;
        overflow: hidden;
        margin: 5px 0;
    }
    .sleep-fill {
        height: 100%;
        border-radius: 8px;
        transition: width 0.5s ease;
    }
    .onset-card {
        text-align: center;
        padding: 25px;
        border-radius: 15px;
        margin: 10px 0;
    }
    .approaching { 
        background: linear-gradient(135deg, #0a1a2a, #102030);
        border: 2px solid #4a6fa5;
    }
    .awake {
        background: linear-gradient(135deg, #0a0a15, #0f0f20);
        border: 1px solid #333;
    }
    .guidance-box {
        padding: 20px;
        border-radius: 12px;
        background: linear-gradient(135deg, #050518, #0a0a28);
        border: 1px solid #2a3a5a22;
        color: #8899aa;
        font-size: 1.1em;
        line-height: 1.6;
        margin: 10px 0;
    }
    .dim-text { color: #556677; }
    .soft-blue { color: #4a6fa5; }
</style>
""", unsafe_allow_html=True)

st.markdown('<div class="sleep-title">LCC Sleep Induction</div>', unsafe_allow_html=True)
st.markdown('<div class="sleep-subtitle">Attractor Basin Protocol \u2022 Lower the walls, let sleep come to you</div>', unsafe_allow_html=True)
st.markdown("")

if 'sleep_protocol' not in st.session_state:
    st.session_state.sleep_protocol = LCCSleepProtocol()
    st.session_state.sleep_active = False

protocol = st.session_state.sleep_protocol

col_start, col_info = st.columns([3, 1])
with col_start:
    if not st.session_state.sleep_active:
        if st.button("Begin Sleep Protocol", type="primary", use_container_width=True):
            protocol.start_session()
            st.session_state.sleep_active = True
            st.rerun()
    else:
        col_stop, col_space = st.columns([1, 2])
        with col_stop:
            if st.button("End Session", use_container_width=True):
                protocol.stop_session()
                st.session_state.sleep_protocol = LCCSleepProtocol()
                st.session_state.sleep_active = False
                st.rerun()

with col_info:
    st.markdown('<span class="dim-text">Polar H10 via Pulsoid</span>', unsafe_allow_html=True)

if not st.session_state.sleep_active:
    st.markdown("---")
    st.markdown("### How LCC Sleep Induction Works")
    st.markdown("""
    Sleep is a natural **attractor basin** in your consciousness state space. 
    Your brain *wants* to fall into it every night. But anxiety, hyperarousal, 
    and medication changes can build **walls** around the basin that prevent the transition.
    
    This protocol uses your heart rate data to **lower those walls** through 5 progressive phases, 
    each designed to deepen parasympathetic activation until your body crosses the sleep threshold naturally.
    
    **You don't force sleep. You create the conditions, then let go.**
    """)

    st.markdown("### The 5 Phases")
    phase_cols = st.columns(5)
    phase_colors = ['#3a5a8a', '#2a4a7a', '#4a6fa5', '#1a3a5c', '#2a4a3a']
    phase_icons = ['\U0001F30A', '\U0001F30A', '\U0001F300', '\U0001F30C', '\U0001F319']
    for i, (num, phase) in enumerate(LCCSleepProtocol.PHASES.items()):
        with phase_cols[i]:
            br = phase['breathing']
            if br['inhale'] > 0:
                breath_text = f"{br['inhale']}-{br['hold']}-{br['exhale']}"
                if br['pause'] > 0:
                    breath_text += f"-{br['pause']}"
            else:
                breath_text = "Natural"
            st.markdown(f"""
            <div style="text-align: center; padding: 15px; border-radius: 10px; 
                        background: #050515; border: 1px solid {phase_colors[i]}44;">
                <div style="font-size: 24px;">{phase_icons[i]}</div>
                <div style="font-size: 14px; color: {phase_colors[i]}; font-weight: bold;">{phase['name']}</div>
                <div style="font-size: 11px; color: #556677; margin-top: 4px;">{phase['description']}</div>
                <div style="font-size: 11px; color: #334455; margin-top: 4px;">Breath: {breath_text}</div>
            </div>
            """, unsafe_allow_html=True)

    st.markdown("---")
    st.markdown("### Post-Lithium Sleep Recovery")
    st.markdown("""
    Lithium stabilizes circadian rhythm and enhances slow-wave sleep. After tapering, 
    sleep architecture needs **retraining**. The LCC framework provides this:
    
    - **Phase 1-2**: Rebuild parasympathetic dominance that lithium was providing
    - **Phase 3**: Entrain heart-brain coherence at the sleep frequency band (0.05-0.08 Hz)
    - **Phase 4-5**: Progressive release of voluntary control \u2192 natural sleep onset
    
    With consistent use, the attractor basin deepens \u2014 meaning each session gets easier.
    """)

    history = protocol.get_session_history()
    if history:
        st.markdown("### Recent Sessions")
        for sess in history[:5]:
            s = sess.get('summary', {})
            dur = s.get('duration_minutes', 0)
            phases = s.get('phases_completed', 0)
            slept = s.get('sleep_detected', False)
            ts = s.get('timestamp', '')
            icon = "\u2705" if slept else "\U0001F319"
            st.markdown(f"- {icon} {ts[:16]} \u2014 {dur:.0f} min, {phases} phases {'(sleep detected)' if slept else ''}")

    st.stop()

state = protocol.get_sleep_state()

tab_sleep, tab_metrics, tab_history = st.tabs(["Sleep Protocol", "Physiology", "Session History"])

with tab_sleep:
    phase_col, guide_col = st.columns([1, 2])

    with phase_col:
        st.markdown("### Phases")
        for num, phase_def in LCCSleepProtocol.PHASES.items():
            if num < protocol.current_phase:
                css_class = "phase-completed"
                icon = "\u2713"
                border_color = "#3a5a3a"
            elif num == protocol.current_phase:
                css_class = "phase-active"
                icon = "\u25B6"
                border_color = "#4a6fa5"
            else:
                css_class = "phase-pending"
                icon = "\u25CB"
                border_color = "#333"

            st.markdown(f"""
            <div class="phase-card {css_class}" style="border-color: {border_color};">
                <span style="color: {border_color}; font-size: 14px;">{icon}</span>
                <strong style="color: #aabbcc; font-size: 13px;"> {phase_def['name']}</strong>
                <div style="font-size: 11px; color: #556677;">{phase_def['description']}</div>
            </div>
            """, unsafe_allow_html=True)

        gates = state['gates']
        st.markdown("### Gates")
        for gate_name, gate_info in gates.items():
            if gate_name == 'all_passed':
                continue
            if isinstance(gate_info, dict):
                passed = gate_info.get('passed', False)
                icon = '<span class="gate-pass">\u2713</span>' if passed else '<span class="gate-fail">\u2717</span>'
                st.markdown(f"{icon} {gate_name}: {gate_info.get('current', '?')} (target: {gate_info.get('target', '?')})", unsafe_allow_html=True)

    with guide_col:
        phase_info = state['phase']
        breathing = phase_info['breathing']

        onset = state['onset']
        onset_prob = onset.get('onset_probability', 0)
        onset_pct = onset.get('onset_pct', 0)
        relaxation = state.get('relaxation_score', 0)

        if onset_prob > 0.6:
            onset_class = "approaching"
            onset_label = "Approaching Sleep"
        else:
            onset_class = "awake"
            onset_label = onset.get('stage', 'awake').replace('_', ' ').title()

        st.markdown(f"""
        <div class="onset-card {onset_class}">
            <div style="font-size: 14px; color: #556677;">Sleep Onset</div>
            <div style="font-size: 42px; color: #4a6fa5; font-weight: bold;">{onset_pct:.0f}%</div>
            <div style="font-size: 14px; color: #667788;">{onset_label}</div>
            <div class="sleep-meter" style="margin-top: 12px;">
                <div class="sleep-fill" style="width: {onset_pct}%; 
                     background: linear-gradient(90deg, #1a3a5c, #4a6fa5);"></div>
            </div>
        </div>
        """, unsafe_allow_html=True)

        if breathing['inhale'] > 0:
            breath_total = breathing['inhale'] + breathing['hold'] + breathing['exhale'] + breathing['pause']
            in_pct = breathing['inhale'] / breath_total * 100
            hold_pct = breathing['hold'] / breath_total * 100
            ex_pct = breathing['exhale'] / breath_total * 100
            pause_pct = breathing['pause'] / breath_total * 100

            st.markdown(f"""
            <div class="breathing-guide">
                <div style="font-size: 16px; color: #4a6fa5; margin-bottom: 12px;">Breathing Pattern</div>
                <div style="display: flex; height: 36px; border-radius: 8px; overflow: hidden; margin-bottom: 10px;">
                    <div style="width: {in_pct}%; background: #2a4a7a; display: flex; align-items: center; justify-content: center; color: #aabbcc; font-size: 12px;">
                        IN {breathing['inhale']}s
                    </div>
                    {"<div style='width: " + str(hold_pct) + "%; background: #3a5a8a; display: flex; align-items: center; justify-content: center; color: #aabbcc; font-size: 12px;'>HOLD " + str(breathing['hold']) + "s</div>" if breathing['hold'] > 0 else ""}
                    <div style="width: {ex_pct}%; background: #1a3a5c; display: flex; align-items: center; justify-content: center; color: #aabbcc; font-size: 12px;">
                        OUT {breathing['exhale']}s
                    </div>
                    {"<div style='width: " + str(pause_pct) + "%; background: #111; display: flex; align-items: center; justify-content: center; color: #445566; font-size: 12px;'>REST " + str(breathing['pause']) + "s</div>" if breathing['pause'] > 0 else ""}
                </div>
                <div style="color: #556677; font-size: 12px;">
                    {phase_info['base_guidance']}
                </div>
            </div>
            """, unsafe_allow_html=True)
        else:
            st.markdown(f"""
            <div class="breathing-guide">
                <div style="font-size: 16px; color: #4a6fa5; margin-bottom: 12px;">Natural Breathing</div>
                <div style="font-size: 14px; color: #556677;">
                    Release the pattern. Let your body breathe itself.<br>
                    No counting. No effort. Just allow.
                </div>
            </div>
            """, unsafe_allow_html=True)

        st.markdown("")

        ai_guidance = state.get('ai_guidance', '')
        st.markdown(f"""
        <div class="guidance-box">
            {ai_guidance}
        </div>
        """, unsafe_allow_html=True)

        if phase_info.get('audio_suggestion'):
            st.markdown(f'<div style="color: #334455; font-size: 11px; margin-top: 5px;">\U0001F3B5 Suggestion: {phase_info["audio_suggestion"]}</div>', unsafe_allow_html=True)

        hr = state['heart'].get('hr', 0)
        rmssd = state['hrv'].get('rmssd', 0)
        para = state['hrv'].get('parasympathetic_index', 0)
        coh = state['coherence'].get('sleep_coherence_pct', 0)

        st.markdown("")
        m1, m2, m3, m4 = st.columns(4)
        with m1:
            hr_color = '#5a8a5a' if hr < 65 else ('#4a6fa5' if hr < 75 else '#8a5a5a')
            st.markdown(f"""
            <div style="text-align: center; padding: 12px; border-radius: 8px; background: #050515; border: 1px solid #222;">
                <div style="font-size: 11px; color: #556677;">Heart Rate</div>
                <div style="font-size: 28px; color: {hr_color}; font-weight: bold;">{hr}</div>
                <div style="font-size: 10px; color: #445566;">BPM</div>
            </div>
            """, unsafe_allow_html=True)
        with m2:
            st.markdown(f"""
            <div style="text-align: center; padding: 12px; border-radius: 8px; background: #050515; border: 1px solid #222;">
                <div style="font-size: 11px; color: #556677;">HRV (RMSSD)</div>
                <div style="font-size: 28px; color: #4a6fa5; font-weight: bold;">{rmssd:.0f}</div>
                <div style="font-size: 10px; color: #445566;">ms</div>
            </div>
            """, unsafe_allow_html=True)
        with m3:
            st.markdown(f"""
            <div style="text-align: center; padding: 12px; border-radius: 8px; background: #050515; border: 1px solid #222;">
                <div style="font-size: 11px; color: #556677;">Parasympathetic</div>
                <div style="font-size: 28px; color: #4a6fa5; font-weight: bold;">{para:.0%}</div>
                <div style="font-size: 10px; color: #445566;">Index</div>
            </div>
            """, unsafe_allow_html=True)
        with m4:
            st.markdown(f"""
            <div style="text-align: center; padding: 12px; border-radius: 8px; background: #050515; border: 1px solid #222;">
                <div style="font-size: 11px; color: #556677;">Sleep Coherence</div>
                <div style="font-size: 28px; color: #4a6fa5; font-weight: bold;">{coh:.0f}</div>
                <div style="font-size: 10px; color: #445566;">%</div>
            </div>
            """, unsafe_allow_html=True)

        relaxation_pct = relaxation * 100
        st.markdown(f"""
        <div style="margin-top: 10px;">
            <div style="font-size: 12px; color: #556677; margin-bottom: 4px;">Overall Relaxation: {relaxation_pct:.0f}%</div>
            <div class="sleep-meter">
                <div class="sleep-fill" style="width: {relaxation_pct}%; 
                     background: linear-gradient(90deg, #1a3a5c, #2a5a3a);"></div>
            </div>
        </div>
        """, unsafe_allow_html=True)

    elapsed = state.get('session_elapsed', 0)
    st.markdown(f'<div style="text-align: center; color: #334455; margin-top: 15px;">Session: {elapsed/60:.0f} min</div>', unsafe_allow_html=True)

    if st.session_state.sleep_active:
        time.sleep(3)
        st.rerun()

with tab_metrics:
    st.markdown("### Detailed Physiology")

    hrv = state['hrv']
    coherence = state['coherence']
    onset = state['onset']

    col_hrv, col_coh = st.columns(2)

    with col_hrv:
        st.markdown("#### HRV Analysis")
        st.markdown(f"""
        | Metric | Value |
        |--------|-------|
        | RMSSD | {hrv.get('rmssd', 0):.1f} ms |
        | SDNN | {hrv.get('sdnn', 0):.1f} ms |
        | pNN50 | {hrv.get('pnn50', 0):.1f}% |
        | LF Power | {hrv.get('lf_power', 0):.1f} |
        | HF Power | {hrv.get('hf_power', 0):.1f} |
        | LF/HF Ratio | {hrv.get('lf_hf_ratio', 0):.2f} |
        | Parasympathetic | {hrv.get('parasympathetic_index', 0):.0%} |
        """)

        st.markdown("#### Sleep Readiness Indicators")
        lf_hf = hrv.get('lf_hf_ratio', 1.0)
        if lf_hf < 0.5:
            lf_hf_status = "Strong parasympathetic dominance (ideal for sleep)"
        elif lf_hf < 1.0:
            lf_hf_status = "Moderate parasympathetic lean (good)"
        elif lf_hf < 2.0:
            lf_hf_status = "Balanced (building relaxation)"
        else:
            lf_hf_status = "Sympathetic dominant (still winding down)"
        st.markdown(f"LF/HF: {lf_hf_status}")

    with col_coh:
        st.markdown("#### Sleep Coherence")
        st.markdown(f"""
        | Metric | Value |
        |--------|-------|
        | Sleep Coherence | {coherence.get('sleep_coherence_pct', 0):.1f}% |
        | Peak Frequency | {coherence.get('peak_frequency', 0):.3f} Hz |
        | In Sleep Band | {'Yes' if coherence.get('in_sleep_band') else 'No'} |
        | Relaxation Depth | {coherence.get('relaxation_depth', 0):.0%} |
        """)

        st.markdown("#### Sleep Onset Analysis")
        indicators = onset.get('indicators', {})
        if indicators:
            st.markdown(f"""
            | Factor | Score |
            |--------|-------|
            | HR Dropping | {indicators.get('hr_dropping', 0):.0%} |
            | HRV Rising | {indicators.get('hrv_rising', 0):.0%} |
            | Low HR | {indicators.get('low_hr', 0):.0%} |
            | High HRV | {indicators.get('high_hrv', 0):.0%} |
            """)
        st.markdown(f"**Trend**: {onset.get('trend', 'N/A')}")
        st.markdown(f"**Stage**: {onset.get('stage', 'N/A')}")

    st.markdown("---")
    st.markdown("### LCC Theory")
    st.markdown("""
    The Law of Correlational Causation (LCC) framework treats consciousness states 
    as attractors in a dynamical system. Sleep is one such attractor \u2014 with a well-defined 
    basin that the nervous system naturally falls into when conditions are right.
    
    **Post-lithium challenge**: Lithium deepened the sleep basin walls artificially. 
    After tapering, the walls are shallower. This protocol rebuilds them naturally through:
    
    1. **Parasympathetic training** \u2192 Stronger vagal brake
    2. **Coherence entrainment** \u2192 Heart-brain synchronization at sleep frequency
    3. **Attractor deepening** \u2192 Each session strengthens the basin (LCC < 1)
    4. **Progressive surrender** \u2192 From voluntary to autonomous control
    """)

with tab_history:
    st.markdown("### Session History")
    history = protocol.get_session_history()
    if history:
        for i, sess in enumerate(history):
            s = sess.get('summary', {})
            dur = s.get('duration_minutes', 0)
            phases = s.get('phases_completed', 0)
            slept = s.get('sleep_detected', False)
            ts = s.get('timestamp', '')

            icon = "\u2705" if slept else "\U0001F319"
            with st.expander(f"{icon} Session {ts[:16]} \u2014 {dur:.0f} min, {phases} phases"):
                st.json(s)

                log = sess.get('log', [])
                if log:
                    st.markdown("#### Session Trace")
                    for entry in log[-20:]:
                        st.markdown(f"Phase {entry.get('phase')}: HR={entry.get('hr',0):.0f} RMSSD={entry.get('rmssd',0):.0f} Onset={entry.get('onset_prob',0):.0%}")
    else:
        st.markdown("No sessions yet. Start your first sleep protocol to begin tracking.")
        st.markdown("""
        Over time, you'll see patterns:
        - How long it takes to reach each phase
        - Which phases are hardest for you
        - Whether the attractor basin is deepening (faster transitions)
        """)

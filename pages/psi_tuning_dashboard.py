"""
PSI Tuning Protocol Dashboard
================================
Pre-experiment optimization of heart-brain dynamics.
AI-guided tuning through 5 progressive phases.
"""

import streamlit as st
import os
import time
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from engines.psi_tuning_protocol import PSITuningProtocol

st.set_page_config(page_title="PSI Tuning Protocol", page_icon="🎯", layout="wide")

st.markdown("""
<style>
    .stApp { background-color: #0a0a1a; }
    h1, h2, h3 { color: white !important; }
    .stMarkdown { color: #cccccc; }
    .tuning-title {
        text-align: center;
        font-size: 2.2em;
        background: linear-gradient(135deg, #ff6b6b, #a855f7, #4d96ff);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0;
    }
    .tuning-subtitle {
        text-align: center;
        color: #888;
        font-size: 1.0em;
        margin-top: 0;
    }
    .phase-card {
        padding: 18px;
        border-radius: 12px;
        margin: 8px 0;
        background: linear-gradient(135deg, #0a0a2a, #151530);
    }
    .phase-active {
        border: 2px solid #a855f7;
        box-shadow: 0 0 20px #a855f744;
    }
    .phase-completed {
        border: 1px solid #6bcb7744;
        opacity: 0.8;
    }
    .phase-pending {
        border: 1px solid #333;
        opacity: 0.5;
    }
    .gate-pass { color: #6bcb77; }
    .gate-fail { color: #ff6b6b; }
    .breathing-guide {
        text-align: center;
        padding: 30px;
        border-radius: 15px;
        background: linear-gradient(135deg, #0a0020, #100030);
        border: 1px solid #a855f744;
    }
    .readiness-card {
        text-align: center;
        padding: 25px;
        border-radius: 15px;
        margin: 10px 0;
    }
    .go-card {
        background: linear-gradient(135deg, #0a2a0a, #103010);
        border: 2px solid #6bcb77;
    }
    .nogo-card {
        background: linear-gradient(135deg, #1a0a0a, #301010);
        border: 2px solid #ff6b6b44;
    }
    .coupling-meter {
        height: 20px;
        border-radius: 10px;
        background: #1a1a2a;
        overflow: hidden;
        margin: 5px 0;
    }
    .coupling-fill {
        height: 100%;
        border-radius: 10px;
        transition: width 0.5s ease;
    }
</style>
""", unsafe_allow_html=True)

st.markdown('<div class="tuning-title">PSI Tuning Protocol</div>', unsafe_allow_html=True)
st.markdown('<div class="tuning-subtitle">Optimize Heart-Brain Coupling for Maximum Information Exchange</div>', unsafe_allow_html=True)
st.markdown("")

if 'psi_protocol' not in st.session_state:
    st.session_state.psi_protocol = PSITuningProtocol()
    st.session_state.tuning_active = False
    st.session_state.auto_advance = True

protocol = st.session_state.psi_protocol

col_start, col_auto = st.columns([3, 1])
with col_start:
    if not st.session_state.tuning_active:
        if st.button("Begin PSI Tuning Protocol", type="primary", use_container_width=True):
            protocol.start_tuning_session()
            st.session_state.tuning_active = True
            st.rerun()
    else:
        if st.button("Reset Protocol", use_container_width=True):
            st.session_state.psi_protocol = PSITuningProtocol()
            st.session_state.tuning_active = False
            st.rerun()

with col_auto:
    st.session_state.auto_advance = st.checkbox("Auto-advance phases", value=True)

if not st.session_state.tuning_active:
    st.markdown("---")
    st.markdown("### How This Works")
    st.markdown("""
    This protocol tunes your heart-brain dynamics through **5 progressive phases**, 
    each with specific physiological gates that must be passed before advancing.
    
    Unlike simple HRV biofeedback, this system optimizes the **information exchange** 
    between heart and brain - the key to PSI performance.
    """)

    phase_cols = st.columns(5)
    for i, (num, phase) in enumerate(PSITuningProtocol.PHASES.items()):
        with phase_cols[i]:
            colors = ['#ff6b6b', '#ffd93d', '#4d96ff', '#a855f7', '#6bcb77']
            st.markdown(f"""
            <div style="text-align: center; padding: 15px; border-radius: 10px; 
                        background: #0a0a2a; border: 1px solid {colors[i]}44;">
                <div style="font-size: 24px; color: {colors[i]};">Phase {num}</div>
                <div style="font-size: 16px; color: white; font-weight: bold;">{phase['name']}</div>
                <div style="font-size: 12px; color: #888; margin-top: 5px;">{phase['description']}</div>
            </div>
            """, unsafe_allow_html=True)

    st.markdown("---")
    st.markdown("### Multi-Modal Vision")
    modal_cols = st.columns(3)
    with modal_cols[0]:
        st.markdown("""
        **Polar H10** (Active)
        - Heart rate variability
        - Coherence tracking
        - Pre-cognitive signals
        - CHSH threshold monitoring
        """)
    with modal_cols[1]:
        st.markdown("""
        **Muse 2 EEG** (Available)
        - Alpha/theta brainwaves
        - Attention metrics
        - Meditation state
        - Neural entrainment
        """)
    with modal_cols[2]:
        st.markdown("""
        **Mendi fNIRS** (Coming Soon)
        - Cerebral blood flow
        - Cortical activation
        - Photonic i-cell proxy
        - Prefrontal coherence
        """)
    st.stop()

state = protocol.get_tuning_state()

tab_tune, tab_metrics, tab_summary = st.tabs(["Tuning", "Deep Metrics", "Session Summary"])

with tab_tune:
    phase_col, guide_col = st.columns([1, 2])

    with phase_col:
        st.markdown("### Phase Progression")
        for num, phase_def in PSITuningProtocol.PHASES.items():
            if num < protocol.current_phase:
                css_class = "phase-completed"
                icon = "&#10003;"
                border_color = "#6bcb77"
            elif num == protocol.current_phase:
                css_class = "phase-active"
                icon = "&#9654;"
                border_color = "#a855f7"
            else:
                css_class = "phase-pending"
                icon = "&#9675;"
                border_color = "#555"

            st.markdown(f"""
            <div class="phase-card {css_class}" style="border-color: {border_color};">
                <span style="color: {border_color}; font-size: 16px;">{icon}</span>
                <strong style="color: white;"> Phase {num}: {phase_def['name']}</strong>
                <div style="font-size: 12px; color: #888;">{phase_def['description']}</div>
            </div>
            """, unsafe_allow_html=True)

        if protocol.current_phase < 5:
            gates = state['gates']
            if gates.get('all_passed', False):
                if st.button(f"Advance to Phase {protocol.current_phase + 1}", type="primary",
                           use_container_width=True):
                    protocol.advance_phase()
                    st.rerun()

    with guide_col:
        phase_info = state['phase']
        breathing = phase_info['breathing']
        ai = state['ai_guidance']

        if ai.get('breathing_adjust'):
            breathing = ai['breathing_adjust']

        phase_colors = {1: '#ff6b6b', 2: '#ffd93d', 3: '#4d96ff', 4: '#a855f7', 5: '#6bcb77'}
        pc = phase_colors.get(protocol.current_phase, '#a855f7')

        st.markdown(f"""
        <div style="text-align: center; margin-bottom: 15px;">
            <span style="font-size: 36px; color: {pc}; font-weight: bold;">
                Phase {phase_info['number']}: {phase_info['name']}
            </span>
        </div>
        """, unsafe_allow_html=True)

        breath_total = breathing['inhale'] + breathing['hold'] + breathing['exhale'] + breathing['pause']
        in_pct = breathing['inhale'] / breath_total * 100
        hold_pct = breathing['hold'] / breath_total * 100
        ex_pct = breathing['exhale'] / breath_total * 100
        pause_pct = breathing['pause'] / breath_total * 100

        st.markdown(f"""
        <div class="breathing-guide">
            <div style="font-size: 18px; color: #a855f7; margin-bottom: 15px;">Breathing Pattern</div>
            <div style="display: flex; height: 40px; border-radius: 8px; overflow: hidden; margin-bottom: 10px;">
                <div style="width: {in_pct}%; background: #4d96ff; display: flex; align-items: center; justify-content: center; color: white; font-size: 13px;">
                    IN {breathing['inhale']}s
                </div>
                {"<div style='width: " + str(hold_pct) + "%; background: #a855f7; display: flex; align-items: center; justify-content: center; color: white; font-size: 13px;'>HOLD " + str(breathing['hold']) + "s</div>" if breathing['hold'] > 0 else ""}
                <div style="width: {ex_pct}%; background: #ff6b6b; display: flex; align-items: center; justify-content: center; color: white; font-size: 13px;">
                    OUT {breathing['exhale']}s
                </div>
                {"<div style='width: " + str(pause_pct) + "%; background: #333; display: flex; align-items: center; justify-content: center; color: #888; font-size: 13px;'>PAUSE " + str(breathing['pause']) + "s</div>" if breathing['pause'] > 0 else ""}
            </div>
            <div style="color: #888; font-size: 13px;">
                {phase_info['base_guidance']}
            </div>
        </div>
        """, unsafe_allow_html=True)

        st.markdown("")

        st.markdown("#### AI Guidance")
        for msg in ai['messages']:
            priority = ai['priority']
            if priority == 'critical':
                st.error(msg)
            elif priority == 'adjust':
                st.warning(msg)
            elif priority in ['optimal', 'ready']:
                st.success(msg)
            else:
                st.info(msg)

        st.markdown("---")
        st.markdown("#### Gate Status")

        gates = state['gates']
        for gate_name, gate_info in gates.items():
            if gate_name == 'all_passed':
                continue
            passed = gate_info['passed']
            icon = "&#10003;" if passed else "&#10007;"
            color = "#6bcb77" if passed else "#ff6b6b"
            display_name = gate_name.replace('_', ' ').title()
            st.markdown(
                f'<span style="color: {color}; font-size: 16px;">{icon}</span> '
                f'<strong style="color: white;">{display_name}</strong>: '
                f'<span style="color: #aaa;">{gate_info["current"]} (target: {gate_info["target"]})</span>',
                unsafe_allow_html=True
            )

        if gates.get('all_passed', False):
            st.success("ALL GATES PASSED - Ready to advance!")

        st.markdown("---")

        hr_val = state['heart'].get('hr', 0)
        coupling_s = state['coupling']['coupling_score']
        coh_pct = state['coherence'].get('coherence_pct', 0)

        m1, m2, m3, m4 = st.columns(4)
        with m1:
            st.metric("Heart Rate", f"{hr_val} BPM" if hr_val > 0 else "--")
        with m2:
            st.metric("Coupling", f"{coupling_s:.0%}")
        with m3:
            st.metric("Coherence", f"{coh_pct:.0f}%")
        with m4:
            psi_r = state['psi_readiness']
            st.metric("PSI Ready", f"{psi_r['score']}%")

        readiness = state['psi_readiness']
        if readiness['status'] == 'GO':
            card_class = 'go-card'
            emoji = '🟢'
        else:
            card_class = 'nogo-card'
            emoji = '🔴' if readiness['status'] == 'NOT_READY' else '🟡'

        st.markdown(f"""
        <div class="readiness-card {card_class}">
            <div style="font-size: 32px;">{emoji}</div>
            <div style="font-size: 20px; font-weight: bold; color: white;">{readiness['status']}</div>
            <div style="color: #aaa; margin-top: 5px;">{readiness['message']}</div>
        </div>
        """, unsafe_allow_html=True)

    live_placeholder = st.empty()
    if st.session_state.tuning_active:
        for tick in range(60):
            state = protocol.get_tuning_state()
            hr = state['heart'].get('hr', '--')
            coupling_s = state['coupling']['coupling_score']
            coh = state['coherence'].get('coherence_pct', 0)
            te_complex = state['transfer_entropy'].get('complexity', '?')
            phase_elapsed = state['phase']['elapsed']

            mins = int(phase_elapsed // 60)
            secs = int(phase_elapsed % 60)

            coupling_color = '#6bcb77' if coupling_s > 0.6 else '#ffd93d' if coupling_s > 0.4 else '#ff6b6b'
            coupling_width = min(100, coupling_s * 100)

            live_placeholder.markdown(
                f"**Phase {protocol.current_phase} | {mins}:{secs:02d}** | "
                f"HR: {hr} BPM | "
                f"Coupling: {coupling_s:.2f} | "
                f"Coherence: {coh:.0f}% | "
                f"Info Flow: {te_complex} | "
                f"Tick {tick+1}/60"
            )

            if st.session_state.auto_advance and state['gates'].get('all_passed', False):
                if protocol.current_phase < 5:
                    protocol.advance_phase()
                    st.rerun()

            time.sleep(2)
        st.rerun()

with tab_metrics:
    st.markdown("### Heart-Brain Coupling Components")

    coupling = state['coupling']
    if coupling['grade'] != 'INSUFFICIENT_DATA':
        components = coupling['components']

        for comp_name, comp_data in components.items():
            display_name = comp_name.replace('_', ' ').title()
            score = comp_data['score']
            weight = comp_data['weight']

            bar_color = '#6bcb77' if score > 0.7 else '#ffd93d' if score > 0.4 else '#ff6b6b'
            bar_width = min(100, score * 100)

            details = []
            for k, v in comp_data.items():
                if k not in ['score', 'weight']:
                    if isinstance(v, float):
                        details.append(f"{k}: {v:.2f}")
                    else:
                        details.append(f"{k}: {v}")
            detail_str = " | ".join(details)

            st.markdown(f"""
            <div style="margin-bottom: 15px;">
                <div style="display: flex; justify-content: space-between;">
                    <strong style="color: white;">{display_name}</strong>
                    <span style="color: #888;">Weight: {weight:.0%} | Score: {score:.2f}</span>
                </div>
                <div class="coupling-meter">
                    <div class="coupling-fill" style="width: {bar_width}%; background: {bar_color};"></div>
                </div>
                <div style="font-size: 12px; color: #666;">{detail_str}</div>
            </div>
            """, unsafe_allow_html=True)

        st.markdown(f"""
        <div style="text-align: center; padding: 20px; background: #0a0a2a; border-radius: 12px; margin-top: 20px;">
            <div style="font-size: 48px; font-weight: bold; color: {'#6bcb77' if coupling['coupling_score'] > 0.7 else '#ffd93d'};">
                {coupling['coupling_score']:.2f}
            </div>
            <div style="font-size: 18px; color: #888;">Master Coupling Score</div>
            <div style="font-size: 14px; color: {'#6bcb77' if coupling['coupling_score'] > 0.7 else '#ffd93d'};">
                {coupling['grade']}
            </div>
        </div>
        """, unsafe_allow_html=True)
    else:
        st.info("Collecting data... Heart-brain coupling metrics will appear as data accumulates.")

    st.markdown("---")
    st.markdown("### HRV Deep Analysis")
    hrv = state['hrv']
    if hrv['sufficient_data']:
        h1, h2, h3 = st.columns(3)
        with h1:
            st.metric("RMSSD", f"{hrv['rmssd']:.1f} ms",
                      help="Root mean square of successive RR differences. Higher = more parasympathetic tone.")
        with h2:
            st.metric("SDNN", f"{hrv['sdnn']:.1f} ms",
                      help="Standard deviation of NN intervals. Overall HRV indicator.")
        with h3:
            st.metric("pNN50", f"{hrv['pnn50']:.1f}%",
                      help="Percentage of successive intervals differing by >50ms.")

        f1, f2, f3 = st.columns(3)
        with f1:
            st.metric("LF Power", f"{hrv['lf_power']:.0f}",
                      help="Low frequency power (0.04-0.15 Hz). Sympathetic + parasympathetic.")
        with f2:
            st.metric("HF Power", f"{hrv['hf_power']:.0f}",
                      help="High frequency power (0.15-0.4 Hz). Parasympathetic / vagal tone.")
        with f3:
            lf_hf = hrv['lf_hf_ratio']
            balance_label = "Balanced" if 0.5 <= lf_hf <= 2.0 else "Sympathetic" if lf_hf > 2 else "Parasympathetic"
            st.metric("LF/HF Ratio", f"{lf_hf:.2f}", help=f"Autonomic balance: {balance_label}")
    else:
        st.info("Collecting HRV data... Need at least 10 heartbeats.")

    st.markdown("---")
    st.markdown("### Transfer Entropy (Heart Information Flow)")
    te = state['transfer_entropy']
    te1, te2, te3 = st.columns(3)
    with te1:
        st.metric("Sample Entropy", f"{te.get('heart_info_rate', 0):.3f}",
                  help="Information generation rate of cardiac neural network.")
    with te2:
        st.metric("Complexity", te.get('complexity', 'N/A'),
                  help="Optimal = heart generating meaningful predictive signals.")
    with te3:
        optimal = te.get('psi_optimal', False)
        st.metric("PSI Optimal", "YES" if optimal else "NO")

    st.markdown("""
    **Why Transfer Entropy matters for PSI:**
    The heart's neural network (~40,000 neurons) generates information that
    the brain processes. For PSI, we need MODERATE complexity - not too regular 
    (no information) and not too chaotic (noise). The sweet spot is where the 
    heart generates meaningful pre-cognitive signals that can propagate to 
    conscious awareness.
    """)

    st.markdown("---")
    st.markdown("### Mendi fNIRS Integration")
    mendi = state['mendi']
    if mendi['available']:
        st.success("Mendi connected! Photonic brain imaging active.")
        if mendi['data']:
            st.metric("Cortical Activity", f"{mendi['data'].get('cortical_activity', 0):.1f}")
            st.metric("Focus Score", f"{mendi['data'].get('focus_score', 0):.1f}")
    else:
        st.markdown(f"""
        <div style="padding: 20px; background: #0a0a2a; border-radius: 12px; border: 1px solid #a855f744;">
            <div style="font-size: 18px; color: #a855f7; margin-bottom: 10px;">Mendi fNIRS - Ready to Integrate</div>
            <div style="color: #888;">
                {mendi['message']}
            </div>
            <div style="margin-top: 15px; color: #666; font-size: 13px;">
                <strong>What Mendi adds:</strong><br>
                - Real-time cerebral blood flow (hemodynamic response)<br>
                - Prefrontal cortex activation patterns<br>
                - Photonic data to test i-cell hypothesis<br>
                - Third modality for complete consciousness mapping<br><br>
                <strong>Combined with Polar H10 + Muse 2:</strong><br>
                Heart (electromagnetic) + Brain (electrical) + Photonic (optical) = 
                Complete multi-modal consciousness lab
            </div>
        </div>
        """, unsafe_allow_html=True)

with tab_summary:
    st.markdown("### Tuning Session Summary")

    summary = protocol.get_session_summary()
    if 'message' in summary and summary.get('data_points', 1) == 0:
        st.info("Start tuning to see session metrics.")
    else:
        duration = summary.get('duration', 0)
        mins = int(duration // 60)
        secs = int(duration % 60)

        s1, s2, s3, s4 = st.columns(4)
        with s1:
            st.metric("Duration", f"{mins}:{secs:02d}")
        with s2:
            st.metric("Current Phase", f"{summary.get('current_phase', 1)}")
        with s3:
            st.metric("Peak Coupling", f"{summary.get('peak_coupling', 0):.2f}")
        with s4:
            st.metric("Avg HR", f"{summary.get('avg_hr', 0):.0f} BPM")

        if summary.get('phase_history'):
            st.markdown("#### Phase Completion History")
            for ph in summary['phase_history']:
                dur = ph['duration']
                st.markdown(
                    f"Phase {ph['phase']} completed in {int(dur//60)}:{int(dur%60):02d} "
                    f"at {ph['completed_at']}"
                )

    st.markdown("---")
    st.markdown("### The Science")
    st.markdown("""
    **Why this is different from simple HRV biofeedback:**
    
    Traditional biofeedback optimizes a single metric (usually RMSSD or coherence).
    This protocol optimizes the **coupling** - the dynamic information exchange
    between heart and brain systems.
    
    **The 4 coupling components:**
    1. **HRV Health** (20%) - Baseline autonomic flexibility
    2. **Coherence** (30%) - Heart rhythm ordering toward the 0.1Hz resonance frequency
    3. **Information Flow** (30%) - Transfer entropy proxy measuring heart's predictive signal generation
    4. **Autonomic Balance** (20%) - LF/HF ratio in the sweet spot for bidirectional communication
    
    **The CHSH Connection:**
    When coherence exceeds 85%, correlations exceed what classical hidden variable
    models can produce (Bell/CHSH inequality). This is the quantum probability
    boundary - the same threshold where our TI Framework predicts nonlocal
    information transfer becomes possible.
    
    **Multi-Modal Future:**
    With Polar H10 (heart), Muse 2 (brain), and Mendi (photonic), we can measure
    all three information channels simultaneously - electromagnetic, electrical,
    and optical. This is the complete consciousness lab needed to test the
    photonic i-cell hypothesis.
    """)

"""
Cognitive Resource Model Dashboard
Visualizes the inverted Yerkes-Dodson relationship, NFC profiling,
and the Wood-on-Fire hypothesis with empirical biometric evidence.
"""

import streamlit as st
import numpy as np
import pandas as pd
import plotly.graph_objects as go
from datetime import datetime
from engines.cognitive_resource_model import CognitiveResourceModel


def render_cognitive_resource_model():
    st.header("🔥 Cognitive Resource Model")
    st.caption("Testing the Wood-on-Fire hypothesis — does YOUR cognition defy the Yerkes-Dodson law?")

    if 'crm' not in st.session_state:
        st.session_state.crm = CognitiveResourceModel()

    crm = st.session_state.crm

    tab_overview, tab_curve, tab_nfc, tab_evidence, tab_simulate = st.tabs([
        "🔥 Overview", "📈 Your Curve", "🧠 Need for Cognition",
        "📊 Evidence Log", "🎮 Simulate"
    ])

    with tab_overview:
        _render_overview(crm)

    with tab_curve:
        _render_curve_analysis(crm)

    with tab_nfc:
        _render_nfc_profile(crm)

    with tab_evidence:
        _render_evidence_log(crm)

    with tab_simulate:
        _render_simulation(crm)


def _render_overview(crm: CognitiveResourceModel):
    st.markdown("### The Wood-on-Fire Hypothesis")

    st.markdown("""
    > *"It would SEEM that throwing wood on a fire would squelch it... and it may even SEEM to AT FIRST! 
    > But the truth is that the fire burns ever brighter!"*

    **Standard Yerkes-Dodson Law** says cognitive performance peaks at moderate arousal and 
    drops off at high arousal — like an inverted U.

    **The Wood-on-Fire Hypothesis** proposes that for individuals with high cognitive resources 
    and high Need for Cognition, this curve is **inverted** — performance keeps climbing with arousal.

    **Why?** Two key factors:
    1. **Cognitive Resource Capacity** — a larger "fire" can absorb more "wood" without being smothered
    2. **Need for Cognition (NFC)** — high-NFC individuals experience cognitive load as fuel, not burden
    """)

    summary = crm.get_session_summary()
    verdict = summary.get('wood_on_fire_verdict', {})
    total = summary.get('total_observations', 0)

    st.markdown("---")

    fire_data = crm.get_fire_visualization_data()
    _render_fire_meter(fire_data)

    st.markdown("---")

    v = verdict.get('verdict', 'TESTING')
    if v == 'CONFIRMED':
        st.success(f"🔥 **VERDICT: {v}** — {verdict.get('explanation', '')}")
    elif v == 'SUPPORTED':
        st.info(f"🔥 **VERDICT: {v}** — {verdict.get('explanation', '')}")
    elif v == 'TESTING':
        st.warning(f"🔬 **VERDICT: {v}** — {verdict.get('explanation', '')}")
    else:
        st.info(f"📊 **VERDICT: {v}** — {verdict.get('explanation', '')}")

    st.markdown("---")

    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("Data Points", total)
    with col2:
        curve_type = summary.get('curve_analysis', {}).get('curve_type', 'unknown')
        display_type = curve_type.replace('_', ' ').title()
        st.metric("Curve Type", display_type)
    with col3:
        nfc_level = summary.get('nfc_analysis', {}).get('nfc_level', 'unknown')
        st.metric("NFC Level", nfc_level.title())
    with col4:
        cap = summary.get('capacity_analysis', {}).get('capacity', 0)
        st.metric("Capacity", f"{cap*100:.0f}%")

    st.markdown("---")
    st.markdown("### Quick Record")
    st.markdown("Manually log a cognitive observation to build your profile.")

    qc1, qc2, qc3 = st.columns(3)
    with qc1:
        q_arousal = st.slider("Arousal Level", 0.0, 1.0, 0.7,
                              help="How stimulated/activated were you? 0=calm, 1=peak intensity",
                              key="q_arousal")
    with qc2:
        q_performance = st.slider("Performance Level", 0.0, 1.0, 0.8,
                                  help="How well did you perform? 0=poor, 1=excellent",
                                  key="q_perf")
    with qc3:
        q_mode = st.selectbox("Context", [
            'excited_concentration', 'calm_concentration',
            'excited_flow', 'calm_flow',
            'excited_open_awareness', 'calm_open_awareness',
            'active_relaxation', 'general'
        ], key="q_mode")

    if st.button("Record Observation", type="primary", key="record_obs"):
        obs = crm.record_observation(
            arousal=q_arousal,
            performance=q_performance,
            nfc_state='high',
            focus_mode=q_mode
        )
        st.success(f"Recorded: Arousal {q_arousal:.0%} → Performance {q_performance:.0%}")
        st.rerun()


def _render_fire_meter(fire_data: dict):
    cap = fire_data.get('capacity', 0.5)
    flames = fire_data.get('flames', 2)
    color = fire_data.get('color', '#FF8C00')
    label = fire_data.get('label', 'Building')
    intensity = fire_data.get('intensity', 'Moderate')

    fire_emojis = '🔥' * flames
    bar_pct = cap * 100

    st.markdown(f"""
    <div style="text-align: center; padding: 20px; background: linear-gradient(180deg, rgba(0,0,0,0.1) 0%, rgba(255,69,0,0.08) 100%); 
                border-radius: 16px; border: 2px solid {color};">
        <div style="font-size: 3em;">{fire_emojis}</div>
        <div style="font-size: 1.5em; font-weight: bold; color: {color}; margin-top: 8px;">{label}</div>
        <div style="font-size: 0.9em; color: #aaa;">Cognitive Fire Intensity: {intensity}</div>
        <div style="margin-top: 12px; background: rgba(0,0,0,0.3); border-radius: 8px; overflow: hidden; height: 20px;">
            <div style="width: {bar_pct}%; height: 100%; background: linear-gradient(90deg, {color}, #FFD700); 
                        border-radius: 8px; transition: width 0.5s;"></div>
        </div>
        <div style="font-size: 0.8em; color: #888; margin-top: 4px;">{bar_pct:.0f}% Cognitive Resource Capacity</div>
    </div>
    """, unsafe_allow_html=True)


def _render_curve_analysis(crm: CognitiveResourceModel):
    st.markdown("### Your Arousal-Performance Curve vs Standard Yerkes-Dodson")

    comparison = crm.generate_yerkes_dodson_comparison()

    if not comparison.get('arousal_range'):
        st.info("No data yet. Record observations or complete Focus Amplifier sessions to build your curve.")
        return

    fig = go.Figure()

    fig.add_trace(go.Scatter(
        x=comparison['arousal_range'],
        y=comparison['standard_yd'],
        mode='lines',
        name='Standard Yerkes-Dodson',
        line=dict(color='rgba(150,150,150,0.7)', width=2, dash='dash'),
        fill=None
    ))

    fig.add_trace(go.Scatter(
        x=comparison['arousal_range'],
        y=comparison['personal_curve'],
        mode='lines',
        name='Your Personal Curve',
        line=dict(color='#FF6B00', width=3),
        fill='tonexty',
        fillcolor='rgba(255,107,0,0.1)'
    ))

    if comparison.get('actual_arousal') and len(comparison['actual_arousal']) > 0:
        fig.add_trace(go.Scatter(
            x=comparison['actual_arousal'],
            y=comparison['actual_performance'],
            mode='markers',
            name='Actual Data Points',
            marker=dict(color='#FFD700', size=8, symbol='circle',
                       line=dict(color='#FF4500', width=1)),
            opacity=0.7
        ))

    fig.update_layout(
        title='Yerkes-Dodson Comparison: Standard vs Your Pattern',
        xaxis_title='Arousal Level',
        yaxis_title='Cognitive Performance',
        xaxis=dict(range=[0, 1], tickformat='.0%'),
        yaxis=dict(range=[0, 1.05], tickformat='.0%'),
        template='plotly_dark',
        height=500,
        legend=dict(yanchor="top", y=0.99, xanchor="left", x=0.01),
        plot_bgcolor='rgba(0,0,0,0)',
        paper_bgcolor='rgba(0,0,0,0)'
    )

    st.plotly_chart(fig, use_container_width=True)

    curve = crm.analyze_curve()
    st.markdown(f"**Curve Type:** {curve.get('curve_type', 'unknown').replace('_', ' ').title()}")
    st.markdown(f"**Description:** {curve.get('description', 'Analyzing...')}")

    if curve.get('data_points', 0) > 0:
        ev_cols = st.columns(4)
        with ev_cols[0]:
            st.metric("Evidence Against Y-D", f"{curve.get('evidence_against_yd', 0)*100:.0f}%")
        with ev_cols[1]:
            st.metric("Correlation (Arousal→Perf)", f"{curve.get('correlation', 0):.3f}")
        with ev_cols[2]:
            st.metric("High Arousal Performance", f"{curve.get('high_arousal_performance', 0)*100:.0f}%")
        with ev_cols[3]:
            st.metric("Confidence", f"{curve.get('confidence', 0)*100:.0f}%")


def _render_nfc_profile(crm: CognitiveResourceModel):
    st.markdown("### Need for Cognition Profile")

    st.markdown("""
    **Need for Cognition (NFC)** is a stable personality trait measuring how much a person 
    enjoys effortful cognitive activity. High-NFC individuals:
    - Seek out complex problems
    - Find thinking inherently rewarding
    - Experience cognitive load as energizing rather than draining
    - Often have ADHD traits that channel into hyperfocus under stimulation
    """)

    nfc = crm.estimate_nfc_level()

    if nfc['nfc_level'] == 'unknown':
        st.info("Need more data to estimate your NFC profile. Record observations to get started.")
        return

    level_info = nfc.get('level_info', {})
    nfc_score = nfc.get('nfc_score', 0)

    nfc_color = {
        'exceptional': '#FF4500',
        'high': '#FF8C00',
        'moderate': '#FFD700',
        'low': '#87CEEB'
    }.get(nfc['nfc_level'], '#888')

    st.markdown(f"""
    <div style="text-align: center; padding: 20px; background: rgba(0,0,0,0.2); 
                border-radius: 16px; border: 2px solid {nfc_color};">
        <div style="font-size: 2em; font-weight: bold; color: {nfc_color};">
            {level_info.get('label', nfc['nfc_level'].title())}
        </div>
        <div style="font-size: 1.1em; color: #ccc; margin-top: 4px;">
            {level_info.get('description', '')}
        </div>
        <div style="font-size: 0.9em; color: #888; margin-top: 8px;">
            NFC Score: {nfc_score:.2f} | Confidence: {nfc.get('confidence', 0)*100:.0f}%
        </div>
    </div>
    """, unsafe_allow_html=True)

    st.markdown("---")
    st.markdown("#### NFC Indicators")

    indicators = nfc.get('indicators', {})
    if indicators:
        ind_cols = st.columns(3)
        with ind_cols[0]:
            v = indicators.get('high_arousal_performance', 0)
            st.metric("High-Arousal Performance", f"{v*100:.0f}%")
            st.progress(min(1.0, v))
        with ind_cols[1]:
            v = indicators.get('arousal_preference', 0)
            st.metric("Arousal Preference", f"{v*100:.0f}%")
            st.progress(min(1.0, v))
        with ind_cols[2]:
            v = indicators.get('complex_mode_performance', 0)
            st.metric("Complex Mode Performance", f"{v*100:.0f}%")
            st.progress(min(1.0, v))

        ind_cols2 = st.columns(2)
        with ind_cols2[0]:
            v = indicators.get('performance_consistency', 0)
            st.metric("Performance Consistency", f"{v*100:.0f}%")
            st.progress(min(1.0, v))
        with ind_cols2[1]:
            v = indicators.get('overall_performance', 0)
            st.metric("Overall Performance", f"{v*100:.0f}%")
            st.progress(min(1.0, v))


def _render_evidence_log(crm: CognitiveResourceModel):
    st.markdown("### Evidence Log")
    st.markdown("All recorded arousal-performance observations, building the empirical case.")

    obs = crm.observations
    if not obs:
        st.info("No observations recorded yet. Use the Quick Record on the Overview tab or complete Focus Amplifier sessions.")
        return

    st.markdown(f"**Total Observations:** {len(obs)}")

    df_data = []
    for o in obs[-100:]:
        df_data.append({
            'Timestamp': o.get('timestamp', '')[:19],
            'Arousal': f"{o['arousal']*100:.0f}%",
            'Performance': f"{o['performance']*100:.0f}%",
            'Mode': o.get('focus_mode', 'general').replace('_', ' ').title(),
            'HR': f"{o.get('hr', 0):.0f}" if o.get('hr', 0) > 0 else '—',
            'HRV': f"{o.get('hrv_rmssd', 0):.1f}" if o.get('hrv_rmssd', 0) > 0 else '—',
            'LF/HF': f"{o.get('lf_hf_ratio', 0):.2f}" if o.get('lf_hf_ratio', 0) > 0 else '—'
        })

    df = pd.DataFrame(df_data)
    st.dataframe(df, use_container_width=True, height=400)

    st.markdown("---")
    st.markdown("#### Arousal vs Performance Scatter")

    arousal_vals = [o['arousal'] for o in obs]
    perf_vals = [o['performance'] for o in obs]

    fig = go.Figure()
    fig.add_trace(go.Scatter(
        x=arousal_vals,
        y=perf_vals,
        mode='markers',
        marker=dict(
            color=perf_vals,
            colorscale='YlOrRd',
            size=10,
            colorbar=dict(title='Performance'),
            line=dict(color='white', width=1)
        ),
        text=[o.get('focus_mode', '').replace('_', ' ').title() for o in obs],
        hovertemplate='Arousal: %{x:.0%}<br>Performance: %{y:.0%}<br>Mode: %{text}<extra></extra>'
    ))

    fig.update_layout(
        title='Raw Data: Arousal vs Performance',
        xaxis_title='Arousal Level',
        yaxis_title='Cognitive Performance',
        xaxis=dict(range=[0, 1], tickformat='.0%'),
        yaxis=dict(range=[0, 1.05], tickformat='.0%'),
        template='plotly_dark',
        height=400,
        plot_bgcolor='rgba(0,0,0,0)',
        paper_bgcolor='rgba(0,0,0,0)'
    )

    st.plotly_chart(fig, use_container_width=True)


def _render_simulation(crm: CognitiveResourceModel):
    st.markdown("### Performance Predictor")
    st.markdown("Use your cognitive profile to predict performance at different arousal levels.")

    sim_arousal = st.slider("Simulated Arousal Level", 0.0, 1.0, 0.5, 0.05,
                            help="Drag to see predicted performance at different arousal levels",
                            key="sim_arousal")

    prediction = crm.predict_performance(sim_arousal)

    pred_pct = prediction['predicted_pct']
    if pred_pct >= 80:
        pred_color = '#00ff88'
    elif pred_pct >= 60:
        pred_color = '#88ff00'
    elif pred_pct >= 40:
        pred_color = '#ffaa00'
    else:
        pred_color = '#ff4444'

    col_pred, col_info = st.columns([1, 1])

    with col_pred:
        st.markdown(f"""
        <div style="text-align: center; padding: 30px; background: rgba(0,0,0,0.2); 
                    border-radius: 16px; border: 2px solid {pred_color};">
            <div style="font-size: 3.5em; font-weight: bold; color: {pred_color};">{pred_pct:.0f}%</div>
            <div style="font-size: 1em; color: #aaa; margin-top: 4px;">Predicted Performance</div>
            <div style="font-size: 0.85em; color: #666; margin-top: 8px;">
                at {sim_arousal*100:.0f}% arousal
            </div>
        </div>
        """, unsafe_allow_html=True)

    with col_info:
        st.markdown(f"**Model Used:** {prediction.get('model_used', 'standard').replace('_', ' ').title()}")
        st.markdown(f"**Curve Type:** {prediction.get('curve_type', 'unknown').replace('_', ' ').title()}")
        st.markdown(f"**NFC Level:** {prediction.get('nfc_level', 'unknown').title()}")
        st.markdown(f"**Capacity:** {prediction.get('capacity', 0)*100:.0f}%")

        fire = prediction.get('fire_metaphor', 'unknown')
        fire_emoji = {'bonfire': '🔥🔥🔥🔥🔥', 'campfire': '🔥🔥🔥🔥',
                     'flame': '🔥🔥🔥', 'candle': '🔥🔥'}.get(fire, '🔥')
        st.markdown(f"**Fire Size:** {fire_emoji} ({fire.title()})")

    st.markdown("---")
    st.markdown("#### Full Arousal-Performance Prediction Curve")

    arousal_range = np.linspace(0, 1, 50)
    predictions = [crm.predict_performance(a) for a in arousal_range]
    pred_perfs = [p['predicted_performance'] for p in predictions]

    standard_yd = [max(0.1, 0.9 - 2.0 * (a - 0.5) ** 2) for a in arousal_range]

    fig = go.Figure()
    fig.add_trace(go.Scatter(
        x=arousal_range.tolist(), y=standard_yd,
        mode='lines', name='Standard Yerkes-Dodson',
        line=dict(color='rgba(150,150,150,0.5)', width=2, dash='dash')
    ))
    fig.add_trace(go.Scatter(
        x=arousal_range.tolist(), y=pred_perfs,
        mode='lines', name='Your Predicted Curve',
        line=dict(color='#FF6B00', width=3)
    ))
    fig.add_trace(go.Scatter(
        x=[sim_arousal], y=[prediction['predicted_performance']],
        mode='markers', name='Current Prediction',
        marker=dict(color='#FFD700', size=15, symbol='star',
                   line=dict(color='#FF4500', width=2))
    ))

    fig.update_layout(
        xaxis_title='Arousal Level',
        yaxis_title='Predicted Performance',
        xaxis=dict(range=[0, 1], tickformat='.0%'),
        yaxis=dict(range=[0, 1.05], tickformat='.0%'),
        template='plotly_dark',
        height=400,
        plot_bgcolor='rgba(0,0,0,0)',
        paper_bgcolor='rgba(0,0,0,0)'
    )

    st.plotly_chart(fig, use_container_width=True)

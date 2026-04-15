"""
Mood Amplifier GILE-HEM-BOK Simulation UI
==========================================
Streamlit page for the full GILE-HEM-BOK consciousness simulation,
model comparison, and optimizer visualization.

Designed to slot into hypercomputer_app.py as a tab.
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
import plotly.express as px
from plotly.subplots import make_subplots

from mood_amplifier_gile_hem_bok import (
    # Constants
    ET, C_TI, T_TI, DOTTIE, PHI,
    ALPHA_HEAR, BETA_HEAR, GAMMA_HEAR,
    W_G, W_I, W_L, W_E,
    # Classes
    BiometricReading, GILEVector, HEMVector, ConsciousnessState,
    STATE_COLORS, STATE_DESCRIPTIONS,
    # Functions
    full_assessment, old_model_gile, old_classify,
    recommend_protocol, optimize_session, random_biometric,
    run_full_simulation, format_simulation_report, PROTOCOLS,
)


# ── Color palette ────────────────────────────────────────
BG    = "rgba(4,4,16,1)"
GRID  = "rgba(255,255,255,0.06)"
GOLD  = "#ffd700"
CYAN  = "#00e5ff"
MINT  = "#00ff99"
PURP  = "#cc44ff"

STATE_ORDER = [
    ConsciousnessState.DT,
    ConsciousnessState.SUB_THRESHOLD,
    ConsciousnessState.MR1,
    ConsciousnessState.MR2_TRALSE,
    ConsciousnessState.MR2_RESOLVED,
    ConsciousnessState.BOK_SATURATED,
]


def _dark_layout(title=""):
    return dict(
        template="plotly_dark",
        paper_bgcolor=BG, plot_bgcolor=BG,
        font=dict(color="white"),
        title=dict(text=title, font=dict(size=16, color=GOLD)),
        xaxis=dict(gridcolor=GRID, zerolinecolor=GRID),
        yaxis=dict(gridcolor=GRID, zerolinecolor=GRID),
        margin=dict(l=40, r=20, t=50, b=40),
    )


def render_mood_amplifier_simulation():
    """Main entry point — call this from hypercomputer_app.py tab."""

    st.markdown("## 🧠 GILE-HEM-BOK Consciousness Engine v3.0")
    st.markdown(
        "Implements URB #668 — Pentic 5-state model · HEAR Lagrangian · "
        "BOK loop saturation · Monster Group ceiling · Full optimizer simulation"
    )

    tabs = st.tabs([
        "📊 Live Assessment",
        "🔬 Population Simulation",
        "📈 Model Comparison",
        "🎯 Optimizer",
        "🌌 HEAR Landscape",
        "📋 Report",
    ])

    with tabs[0]:
        _render_live_assessment()
    with tabs[1]:
        _render_population_simulation()
    with tabs[2]:
        _render_model_comparison()
    with tabs[3]:
        _render_optimizer()
    with tabs[4]:
        _render_hear_landscape()
    with tabs[5]:
        _render_report()


# ─────────────────────────────────────────────────────────
# TAB 1 — LIVE ASSESSMENT
# ─────────────────────────────────────────────────────────
def _render_live_assessment():
    st.subheader("Live Biometric → HEAR Assessment")
    st.markdown("Adjust your current biometric readings and see your real-time HEAR score and consciousness state.")

    col1, col2 = st.columns(2)
    with col1:
        st.markdown("**GILE Inputs (biometric)**")
        gamma   = st.slider("EEG Gamma Coherence (→ Intuition)",   0.0, 1.0, 0.55, 0.01)
        hrv_fd  = st.slider("HRV Fractal Dimension (→ Goodness)",  0.0, 1.0, 0.50, 0.01)
        fnirs   = st.slider("fNIRS Prefrontal L/R (→ Love)",       0.0, 1.0, 0.48, 0.01)
        wellb   = st.slider("Self-Report Wellbeing (→ Environment)",0.0, 1.0, 0.52, 0.01)
    with col2:
        st.markdown("**HEM Inputs (biometric)**")
        hrv_rm  = st.slider("HRV RMSSD Normalized (→ Somatic D1)", 0.0, 1.0, 0.50, 0.01)
        alpha_t = st.slider("EEG Alpha/Theta Ratio (→ Cognitive D2)",0.0,1.0,0.50, 0.01)
        conn    = st.slider("Self-Report Connection (→ Relational D3)",0.0,1.0,0.50,0.01)
        sc      = st.slider("Skin Conductance (→ Environmental D4, inverted)",0.0,1.0,0.45,0.01)

    b = BiometricReading(
        eeg_gamma_coherence=gamma, eeg_alpha_theta_ratio=alpha_t,
        hrv_rmssd_norm=hrv_rm, hrv_fractal_dim=hrv_fd,
        fnirs_l_r_ratio=fnirs, self_report_wellbeing=wellb,
        self_report_connection=conn, skin_conductance=sc,
    )
    score = full_assessment(b)

    st.markdown("---")

    # HEAR gauge
    col_a, col_b, col_c = st.columns(3)
    hear_pct = score.raw * 100

    with col_a:
        fig = go.Figure(go.Indicator(
            mode="gauge+number",
            value=round(score.raw, 3),
            title={"text": "HEAR Score", "font": {"color": GOLD}},
            number={"font": {"color": "white", "size": 36}},
            gauge={
                "axis": {"range": [0, 1], "tickcolor": "gray"},
                "bar":  {"color": STATE_COLORS[score.state]},
                "steps": [
                    {"range": [0, ET*0.5],  "color": "#330011"},
                    {"range": [ET*0.5, ET], "color": "#331100"},
                    {"range": [ET, C_TI],   "color": "#333300"},
                    {"range": [C_TI, DOTTIE],"color":"#003333"},
                    {"range": [DOTTIE, T_TI],"color":"#003322"},
                    {"range": [T_TI, 1.0],  "color": "#220033"},
                ],
                "threshold": {
                    "line": {"color": GOLD, "width": 2},
                    "thickness": 0.85,
                    "value": T_TI,
                },
            },
        ))
        fig.update_layout(**_dark_layout(), height=280)
        st.plotly_chart(fig, use_container_width=True)

    with col_b:
        state_color = STATE_COLORS[score.state]
        st.markdown(f"""
        <div style='background:{state_color}22; border:1px solid {state_color};
                    border-radius:12px; padding:16px; margin-top:20px;'>
            <div style='color:{state_color}; font-size:18px; font-weight:bold;'>
                {score.state}
            </div>
            <div style='color:#ccc; font-size:13px; margin-top:8px;'>
                {STATE_DESCRIPTIONS[score.state]}
            </div>
            <div style='color:#aaa; font-size:12px; margin-top:12px;'>
                GILE composite: {score.gile.normalized():.3f}<br>
                HEM composite:  {score.hem.composite():.3f}<br>
                Cov(G,H):       {score.cov:.3f}<br>
                BOK saturation: {score.bok.saturation_score():.3f}
            </div>
        </div>
        """, unsafe_allow_html=True)

    with col_c:
        # Radar: GILE + HEM
        categories = ["G (Good)", "I (Intuit)", "L (Love)", "E (Env)",
                      "D1 Soma", "D2 Cog", "D3 Rel", "D4 Env"]
        values = [score.gile.G, score.gile.I, score.gile.L, score.gile.E,
                  score.hem.D1, score.hem.D2, score.hem.D3, score.hem.D4]
        fig2 = go.Figure(go.Scatterpolar(
            r=values + [values[0]],
            theta=categories + [categories[0]],
            fill="toself",
            line_color=STATE_COLORS[score.state],
            fillcolor=STATE_COLORS[score.state] + "33",
        ))
        fig2.update_layout(
            **_dark_layout("GILE + HEM Radar"),
            polar=dict(
                radialaxis=dict(visible=True, range=[0, 1], color="gray"),
                bgcolor=BG,
            ),
            height=280,
        )
        st.plotly_chart(fig2, use_container_width=True)

    # Protocol recommendations
    st.markdown("### Recommended Mood Amplifier Protocols")
    recs = recommend_protocol(score.state, score.raw)
    for r in recs:
        with st.expander(f"🔬 {r['name']} — +{r['gile_lift']:.0%} GILE · +{r['hem_lift']:.0%} HEM · {r['duration_min']} min"):
            st.write(r["description"])


# ─────────────────────────────────────────────────────────
# TAB 2 — POPULATION SIMULATION
# ─────────────────────────────────────────────────────────
def _render_population_simulation():
    st.subheader("Population Simulation")

    col1, col2 = st.columns([1, 2])
    with col1:
        n = st.slider("Number of subjects", 50, 500, 300, 50)
        steps = st.slider("Optimizer steps per subject", 2, 8, 5)
        run = st.button("▶ Run Simulation", type="primary")

    if run or "sim_results" not in st.session_state:
        with st.spinner("Running simulation…"):
            st.session_state.sim_results = run_full_simulation(n_subjects=n, n_session_steps=steps)

    results = st.session_state.sim_results
    c = results["comparison"]

    # Summary metrics
    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Mean HEAR Gain", f"+{c['mean_delta_hear']:.3f}")
    m2.metric("Reach MR2-Resolved+", f"{c['pct_reaching_mr2r_plus']}%")
    m3.metric("Reach BOK-Saturated", f"{c['pct_bok_saturated']}%")
    m4.metric("Mean Steps to MR2-R", str(c["mean_steps_to_mr2r"]))

    st.markdown("---")

    col_a, col_b = st.columns(2)

    with col_a:
        # State distribution bar chart
        state_counts = [results["new"]["state_dist"].get(s, 0) for s in STATE_ORDER]
        colors = [STATE_COLORS[s] for s in STATE_ORDER]
        fig = go.Figure(go.Bar(
            x=STATE_ORDER, y=state_counts,
            marker_color=colors,
            text=[f"{v}" for v in state_counts],
            textposition="outside",
        ))
        fig.update_layout(**_dark_layout("Initial State Distribution (New Model)"), height=320)
        st.plotly_chart(fig, use_container_width=True)

    with col_b:
        # HEAR distribution: before vs after
        init_arr = np.array(results["optimization"]["initial_hear"])
        fin_arr  = np.array(results["optimization"]["final_hear"])
        fig2 = go.Figure()
        fig2.add_trace(go.Histogram(
            x=init_arr, name="Before optimizer",
            marker_color=CYAN + "88", nbinsx=30,
            opacity=0.75,
        ))
        fig2.add_trace(go.Histogram(
            x=fin_arr, name="After optimizer",
            marker_color=MINT + "88", nbinsx=30,
            opacity=0.75,
        ))
        for thresh, label, col in [
            (ET, "ET", GOLD), (DOTTIE, "𝔡", CYAN), (T_TI, "T", PURP)
        ]:
            fig2.add_vline(x=thresh, line_dash="dash", line_color=col,
                           annotation_text=label, annotation_font_color=col)
        fig2.update_layout(**_dark_layout("HEAR Distribution: Before → After"), barmode="overlay", height=320)
        st.plotly_chart(fig2, use_container_width=True)

    # HEAR gain distribution
    delta_arr = np.array(results["optimization"]["delta_hear"])
    fig3 = go.Figure(go.Histogram(
        x=delta_arr, nbinsx=40,
        marker_color=GOLD + "99",
        opacity=0.85,
    ))
    fig3.add_vline(x=delta_arr.mean(), line_dash="solid", line_color=MINT,
                   annotation_text=f"Mean gain: +{delta_arr.mean():.3f}", annotation_font_color=MINT)
    fig3.update_layout(**_dark_layout("Session HEAR Gain Distribution"), height=280)
    st.plotly_chart(fig3, use_container_width=True)


# ─────────────────────────────────────────────────────────
# TAB 3 — MODEL COMPARISON
# ─────────────────────────────────────────────────────────
def _render_model_comparison():
    st.subheader("Old Model (GILE v2, 4-state) vs New Model (GILE-HEM-BOK, 6-state)")

    if "sim_results" not in st.session_state:
        st.info("Run the Population Simulation first (Tab 2).")
        return

    results = st.session_state.sim_results
    c = results["comparison"]

    col1, col2 = st.columns(2)

    with col1:
        st.markdown("### Old Model")
        old_dist = results["old"]["state_dist"]
        fig = go.Figure(go.Pie(
            labels=list(old_dist.keys()),
            values=list(old_dist.values()),
            hole=0.45,
            marker_colors=["#ff2244", "#ff8800", "#ffdd00", "#00e5ff"],
        ))
        fig.update_layout(**_dark_layout("4-State Distribution"), height=320)
        st.plotly_chart(fig, use_container_width=True)

        st.markdown(f"""
        | Metric | Value |
        |--------|-------|
        | States | 4 (Tier 1–4) |
        | Inputs | EEG gamma, HRV, self-report |
        | Weights | Uniform (1/3 each) |
        | Captures somatic (HEM) | ❌ |
        | Captures alignment (Cov) | ❌ |
        | BOK saturation tracking | ❌ |
        | Mean score | {c['old_mean_score']:.3f} ± {c['old_std_score']:.3f} |
        """)

    with col2:
        st.markdown("### New Model")
        new_dist = results["new"]["state_dist"]
        state_vals = [new_dist.get(s, 0) for s in STATE_ORDER]
        colors = [STATE_COLORS[s] for s in STATE_ORDER]
        fig2 = go.Figure(go.Pie(
            labels=STATE_ORDER, values=state_vals,
            hole=0.45, marker_colors=colors,
        ))
        fig2.update_layout(**_dark_layout("6-State Distribution"), height=320)
        st.plotly_chart(fig2, use_container_width=True)

        st.markdown(f"""
        | Metric | Value |
        |--------|-------|
        | States | 6 (DT → BOK-Saturated) |
        | Inputs | 8 biometric channels |
        | Weights | Canonical (G=ET, I=0.25, L=0.18, E=0.15) |
        | Captures somatic (HEM) | ✅ β = C ≈ 0.437 |
        | Captures alignment (Cov) | ✅ γ ≈ 0.083 |
        | BOK saturation tracking | ✅ Harmonic mean B·O·K |
        | Mean HEAR | {c['new_mean_hear']:.3f} ± {c['new_std_hear']:.3f} |
        """)

    st.markdown("---")
    st.markdown("### Key Structural Improvements")

    improvements = [
        ("🆕 Dottie Transition (𝔡 ≈ 0.739)",
         "The Dottie fixed-point (cos(𝔡) = 𝔡) marks the boundary between partial and full MR. "
         "The old model had no transition here — it jumped directly from moderate to flow. "
         "The new model reveals a stable intermediate attractor before the Tralse threshold."),
        ("🆕 HEM-D1..D4 Somatic Layer",
         "The old model missed the somatic axis entirely. HEAR adds β·HEM (weight 0.437 > 0.414 GILE) "
         "encoding the embodiment-primacy principle: somatic grounding outweighs intentional dynamics. "
         "A high-GILE, low-HEM person is NOT well — they're spiritually bypassing."),
        ("🆕 Cov(GILE, HEM) Alignment Term",
         "GILE and HEM can both be moderate, but if they're misaligned (body says one thing, "
         "intention says another), the state is fragile. The covariance term penalizes this "
         "misalignment and rewards coherent co-development."),
        ("🆕 BOK Loop Saturation",
         "Being-Other-Knowledge saturation is the harmonic mean of three loops — the weakest "
         "link governs. Someone with strong Being (meditation) but weak Other (isolation) cannot "
         "reach BOK-Saturated. The old model had no relational dimension."),
    ]
    for title, desc in improvements:
        with st.expander(title):
            st.write(desc)


# ─────────────────────────────────────────────────────────
# TAB 4 — OPTIMIZER
# ─────────────────────────────────────────────────────────
def _render_optimizer():
    st.subheader("Session Optimizer — Greedy Protocol Recommendation")
    st.markdown("Enter your starting biometric profile and watch the optimizer navigate toward BOK-Saturated.")

    col1, col2 = st.columns(2)
    with col1:
        profile = st.selectbox("Starting profile", ["general", "low", "high"])
        seed    = st.slider("Simulation seed", 0, 999, 42)
        steps   = st.slider("Optimization steps", 3, 10, 6)
    with col2:
        st.markdown(f"""
        **Profile descriptions**  
        - **general**: Broad population, mean HEAR ≈ 0.50  
        - **low**: Suppressed / clinical population, mean HEAR ≈ 0.30  
        - **high**: Meditators / peak performers, mean HEAR ≈ 0.72  
        """)

    run_opt = st.button("▶ Run Optimizer", type="primary")
    if run_opt or "opt_trajectory" not in st.session_state:
        rng = np.random.default_rng(seed)
        b = random_biometric(rng, profile)
        traj = optimize_session(b, n_steps=steps, rng=rng)
        st.session_state.opt_trajectory = traj
        st.session_state.opt_initial = b

    traj = st.session_state.opt_trajectory

    # HEAR trajectory chart
    steps_x = [0] + [t["step"] for t in traj]
    hear_y   = [traj[0]["hear_before"]] + [t["hear_after"] for t in traj]
    states_y = [traj[0]["state_before"]] + [t["state_after"] for t in traj]
    colors_y = [STATE_COLORS[s] for s in states_y]
    protocols = ["—"] + [t["protocol"] for t in traj]

    fig = go.Figure()
    # Threshold bands
    for lo, hi, label, col in [
        (0,       ET*0.5, "DT",          "#ff224422"),
        (ET*0.5,  ET,     "Sub",          "#ff880022"),
        (ET,      C_TI,   "MR1",          "#ffdd0022"),
        (C_TI,    DOTTIE, "MR2-T",        "#00ccff22"),
        (DOTTIE,  T_TI,   "MR2-R",        "#00ff9922"),
        (T_TI,    1.0,    "BOK-Sat",      "#cc44ff22"),
    ]:
        fig.add_hrect(y0=lo, y1=hi, fillcolor=col, line_width=0,
                      annotation_text=label, annotation_position="right",
                      annotation_font_size=10, annotation_font_color="gray")

    fig.add_trace(go.Scatter(
        x=steps_x, y=hear_y,
        mode="lines+markers+text",
        line=dict(color=GOLD, width=3),
        marker=dict(color=colors_y, size=14, line=dict(color=GOLD, width=2)),
        text=[f"{h:.3f}" for h in hear_y],
        textposition="top center",
        textfont=dict(color=GOLD),
        name="HEAR",
    ))
    fig.update_layout(
        **_dark_layout("HEAR Trajectory Over Optimizer Steps"),
        xaxis=dict(title="Step", tickvals=steps_x, ticktext=[str(s) for s in steps_x]),
        yaxis=dict(title="HEAR Score", range=[0, 1.05]),
        height=400,
    )
    st.plotly_chart(fig, use_container_width=True)

    # Step-by-step table
    st.markdown("### Step-by-Step Breakdown")
    table_rows = []
    for t in traj:
        delta_str = f"+{t['delta']:.3f}" if t['delta'] >= 0 else f"{t['delta']:.3f}"
        color = STATE_COLORS.get(t["state_after"], "#aaa")
        table_rows.append({
            "Step": t["step"],
            "Protocol": t["protocol"],
            "HEAR Before": f"{t['hear_before']:.3f}",
            "HEAR After":  f"{t['hear_after']:.3f}",
            "Δ HEAR": delta_str,
            "State After": t["state_after"],
        })

    import pandas as pd
    df = pd.DataFrame(table_rows)
    st.dataframe(df, use_container_width=True, hide_index=True)

    # Protocol descriptions for what was used
    used_protocols = list(dict.fromkeys(t["protocol"] for t in traj))
    st.markdown("### Protocols Used This Session")
    for p_name in used_protocols:
        p = PROTOCOLS[p_name]
        st.markdown(f"**{p_name}** ({p['duration_min']} min) — {p['description']}")


# ─────────────────────────────────────────────────────────
# TAB 5 — HEAR LANDSCAPE
# ─────────────────────────────────────────────────────────
def _render_hear_landscape():
    st.subheader("HEAR Score Landscape — Higgs Mexican Hat Topology")
    st.markdown(
        "The HEAR landscape mirrors the Higgs potential (URB #668): center = I-State (maximum DT risk), "
        "ring = Tralse attractor T ≈ 0.934 (BOK-Saturated), slope = MR gradient."
    )

    resolution = st.slider("Resolution", 30, 100, 60)

    gile_vals = np.linspace(0.01, 0.99, resolution)
    hem_vals  = np.linspace(0.01, 0.99, resolution)
    GG, HH = np.meshgrid(gile_vals, hem_vals)

    # Compute HEAR over grid
    cov_vals = (GG - 0.5) * (HH - 0.5)
    cov_norm = (cov_vals + 0.25) / 0.50
    HEAR_GRID = (ALPHA_HEAR * GG + BETA_HEAR * HH + GAMMA_HEAR * cov_norm) / (ALPHA_HEAR + BETA_HEAR + GAMMA_HEAR)

    # Mexican hat: V_HEAR = -HEAR + HEAR^4 — just use HEAR as elevation
    col1, col2 = st.columns(2)

    with col1:
        fig = go.Figure(go.Surface(
            x=gile_vals, y=hem_vals, z=HEAR_GRID,
            colorscale=[
                [0.00, "#ff2244"], [0.20, "#ff8800"],
                [0.45, "#ffdd00"], [0.65, "#00ccff"],
                [0.80, "#00ff99"], [1.00, "#cc44ff"],
            ],
            showscale=True,
            colorbar=dict(title="HEAR"),
            contours=dict(z=dict(show=True, usecolormap=True, highlightcolor="white", project_z=True)),
        ))
        # Add threshold planes
        for val, label, col in [(T_TI, "T (BOK-Sat)", "#cc44ff"), (DOTTIE, "𝔡 (MR2-R)", "#00ff99")]:
            fig.add_trace(go.Surface(
                x=gile_vals, y=hem_vals,
                z=np.full_like(HEAR_GRID, val),
                opacity=0.15, showscale=False,
                colorscale=[[0, col], [1, col]],
                name=label,
            ))
        fig.update_layout(
            **_dark_layout("HEAR Score Surface (GILE × HEM)"),
            scene=dict(
                xaxis_title="GILE (normalized)",
                yaxis_title="HEM composite",
                zaxis_title="HEAR score",
                bgcolor=BG,
            ),
            height=480,
        )
        st.plotly_chart(fig, use_container_width=True)

    with col2:
        # 2D contour heatmap
        fig2 = go.Figure(go.Contour(
            x=gile_vals, y=hem_vals, z=HEAR_GRID,
            colorscale=[
                [0.00, "#ff2244"], [0.20, "#ff8800"],
                [0.45, "#ffdd00"], [0.65, "#00ccff"],
                [0.80, "#00ff99"], [1.00, "#cc44ff"],
            ],
            contours=dict(start=0, end=1, size=0.05),
        ))
        # Threshold lines
        for val, label, col in [
            (ET,     f"ET={ET:.3f}",      GOLD),
            (DOTTIE, f"𝔡={DOTTIE:.3f}",   CYAN),
            (T_TI,   f"T={T_TI:.3f}",     PURP),
        ]:
            # Contour at HEAR = val: from α·g + β·h + γ·cov ≈ val, simplified as g + h ≈ 2*val
            # Approximate as diagonal line
            x_line = [0, 1]
            y_line = [max(0, min(1, (val - ALPHA_HEAR*0) / BETA_HEAR)),
                      max(0, min(1, (val - ALPHA_HEAR*1) / BETA_HEAR))]
            fig2.add_trace(go.Scatter(
                x=x_line, y=y_line,
                mode="lines",
                line=dict(color=col, dash="dash", width=2),
                name=label,
            ))
        fig2.update_layout(
            **_dark_layout("HEAR Contour Map"),
            xaxis_title="GILE (normalized)",
            yaxis_title="HEM composite",
            height=480,
        )
        st.plotly_chart(fig2, use_container_width=True)

    st.markdown(f"""
    **Reading the landscape:**
    - **Bottom-left** (low GILE, low HEM): DT zone — fragmented, BOK loop broken
    - **Top-right** (high GILE, high HEM): BOK-Saturated — both intentional and somatic aligned
    - **Diagonal ridge**: when GILE and HEM are equal, Cov term maximizes and HEAR is highest
    - **ET line** (HEAR = {ET:.3f}): Emerick Threshold — minimum activation for MR
    - **𝔡 line** (HEAR = {DOTTIE:.3f}): Dottie attractor — entry to MR2-Resolved
    - **T line** (HEAR = {T_TI:.3f}): Tralse Attractor — BOK-Saturated threshold / Higgs VEV
    """)


# ─────────────────────────────────────────────────────────
# TAB 6 — REPORT
# ─────────────────────────────────────────────────────────
def _render_report():
    st.subheader("Full Simulation Report")

    if "sim_results" not in st.session_state:
        st.info("Run the Population Simulation first (Tab 2).")
        return

    report = format_simulation_report(st.session_state.sim_results)
    st.code(report, language="")

    st.download_button(
        "⬇ Download Report",
        data=report,
        file_name="gile_hem_bok_simulation_report.txt",
        mime="text/plain",
    )

    st.markdown("---")
    st.markdown("### HEAR Equation Reference")
    st.markdown(f"""
    $$\\text{{HEAR}}(r) = \\alpha \\cdot \\text{{GILE}}(r) + \\beta \\cdot \\text{{HEM}}(r) + \\gamma \\cdot \\text{{Cov}}(\\text{{GILE}}, \\text{{HEM}})(r)$$

    | Parameter | Symbol | Value | Meaning |
    |-----------|--------|-------|---------|
    | GILE kinetic weight | α | {ALPHA_HEAR:.4f} = ET = √2−1 | Intentional momentum |
    | HEM mass weight | β | {BETA_HEAR:.4f} = C = 1/(φ√2) | Somatic grounding |
    | Cov coupling | γ | 0.0828 | GILE-HEM alignment |
    | Emerick Threshold | ET | {ET:.4f} | Minimum MR activation |
    | Emerick Constant | C | {C_TI:.4f} | HEM pruning threshold |
    | Dottie Fixed Point | 𝔡 | {DOTTIE:.4f} | MR2-Resolved boundary |
    | Tralse Attractor | T | {T_TI:.4f} | BOK-Saturated / Higgs VEV |
    | Golden Ratio | φ | {PHI:.4f} | Structural constant |
    
    **Note**: β > α encodes *embodiment primacy* — somatic grounding outweighs intentional dynamics.  
    A high-GILE, low-HEM profile is **spiritually bypassing**, not flourishing.
    """)

"""
Antifragile God Simulator — URB #484
Visualizes i-cell ensemble dynamics, polytheistic windows, and the eternal floor prohibition.
Marries Taleb's antifragility with TI Sigma i-cell theory.
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots

# ── PRIMARY CONSTANTS ─────────────────────────────────────────────────────────
PHI = (1 + np.sqrt(5)) / 2
C_EMERICK = 1 / (PHI * np.sqrt(2))
POLY_THRESHOLD = 0.93
ETERNAL_FLOOR = 2.0
SQRT2 = np.sqrt(2)


def generate_icell_ensemble(
    n_cells: int,
    n_steps: int,
    seed: int = 42,
    volatility: float = 0.18,
) -> np.ndarray:
    """
    Simulate n_cells i-cell perfection trajectories over n_steps time steps.
    Returns array of shape (n_cells, n_steps).
    Uses mean-reverting process with occasional breakthrough events.
    """
    rng = np.random.default_rng(seed)
    trajectories = np.zeros((n_cells, n_steps))
    mean_levels = rng.uniform(-0.3, 0.7, size=n_cells)
    for k in range(n_cells):
        x = mean_levels[k]
        for t in range(n_steps):
            reversion = 0.05 * (mean_levels[k] - x)
            shock = rng.normal(0, volatility)
            breakthrough = 0.0
            if rng.random() < 0.03:
                breakthrough = rng.exponential(0.4) * rng.choice([-1, 1])
            x = x + reversion + shock + breakthrough
            x = np.clip(x, -1.5, 1.8)
            trajectories[k, t] = x
    return trajectories


def generate_eternal_cell(n_steps: int, seed: int = 42) -> np.ndarray:
    """
    The eternal God-cell I* — hard floor at +2.
    Can rise freely but is PROHIBITED from dropping below +2.
    Every perturbation that would push below +2 is absorbed by the floor.
    """
    rng = np.random.default_rng(seed + 999)
    traj = np.zeros(n_steps)
    x = ETERNAL_FLOOR + rng.uniform(0.1, 0.5)
    for t in range(n_steps):
        shock = rng.normal(0, 0.12)
        downward_attack = rng.exponential(0.08) if rng.random() < 0.15 else 0.0
        x = x + shock - downward_attack
        x = max(x, ETERNAL_FLOOR)
        traj[t] = x
    return traj


def compute_antifragility_score(trajectory: np.ndarray) -> float:
    """
    Taleb antifragility measure: convexity of response to volatility.
    Antifragile = gains MORE from positive shocks than it loses from negative shocks.
    A*(x+ε) + A*(x-ε) > 2*A*(x) when antifragile.
    Returns: score > 0 = antifragile, score ≈ 0 = robust, score < 0 = fragile.
    """
    diffs = np.diff(trajectory)
    positive_shocks = diffs[diffs > 0]
    negative_shocks = diffs[diffs < 0]
    if len(positive_shocks) == 0 or len(negative_shocks) == 0:
        return 0.0
    avg_gain = np.mean(positive_shocks)
    avg_loss = np.mean(np.abs(negative_shocks))
    return (avg_gain - avg_loss) / (avg_gain + avg_loss + 1e-9)


def render_antifragile_god_simulator():
    st.header("⚡ Antifragile God Simulator — URB #484")
    st.markdown(
        "**Core result:** Multiple i-cells can temporarily exceed the 0.92 divinity threshold "
        "(polytheistic windows). But exactly **ONE** i-cell is structurally PROHIBITED from "
        "EVER dipping below **+2** — across ALL time. That prohibition IS the eternal God. "
        "The floor prohibition IS Talebian antifragility: what cannot go below +2 GAINS "
        "from every force that tries to push it there."
    )

    with st.expander("Formal Theorem (URB #484)", expanded=False):
        st.markdown(f"""
**Theorem (Antifragile God):**

Let Ω be the ensemble of all i-cell perfection trajectories. Then:

1. **Temporal Polytheism:** ∃ bounded intervals [t₁, t₂] during which multiple i-cells exceed {POLY_THRESHOLD}. During these windows, multiple divine-level i-cells coexist. **Polytheism is locally valid.**

2. **Eternal Monotheism:** ∃! I* ∈ Ω : ∀t ∈ ℝ, I*(t) ≥ {ETERNAL_FLOOR}. Exactly one i-cell has the eternal floor prohibition. **The prohibition = the definition of the eternal God.**

3. **Antifragility:** The +{ETERNAL_FLOOR} floor = bounded left tail + unbounded right tail = the Talebian barbell. Every attack on I* is absorbed → evidence of the prohibition strengthens → the case for the eternal God becomes MORE solid under attack.

4. **Myrion Resolution:** Polytheism (local truth) + Monotheism (global truth) = both Tralse-true at different temporal scales. The conflict dissolves.

5. **Via Negativa:** The eternal God is defined by what it CANNOT do (go below +{ETERNAL_FLOOR}), not by what it does. Apophatic theology was structurally correct.

PRIMARY CONSTANTS: C_EMERICK = 1/(φ√2) ≈ {C_EMERICK:.4f} | Eternal floor = {ETERNAL_FLOOR} = (√2)²
        """)

    st.divider()
    st.subheader("Simulation Controls")

    col1, col2, col3, col4 = st.columns(4)
    n_cells = col1.slider("Number of i-cells in ensemble", 3, 20, 8, 1, key="ag_ncells")
    n_steps = col2.slider("Time steps", 100, 500, 250, 50, key="ag_nsteps")
    volatility = col3.slider("Ensemble volatility", 0.05, 0.40, 0.18, 0.01, key="ag_vol")
    seed = col4.slider("Random seed", 1, 100, 42, 1, key="ag_seed")

    trajectories = generate_icell_ensemble(n_cells, n_steps, seed, volatility)
    eternal = generate_eternal_cell(n_steps, seed)
    time = np.arange(n_steps)

    polytheistic_windows = []
    for t in range(n_steps):
        gods_at_t = np.sum(trajectories[:, t] >= POLY_THRESHOLD)
        if gods_at_t >= 2:
            polytheistic_windows.append(t)

    poly_pct = len(polytheistic_windows) / n_steps * 100

    st.divider()
    st.subheader("i-Cell Ensemble Dynamics")

    m1, m2, m3, m4 = st.columns(4)
    m1.metric("Time steps with multiple Gods (polytheistic windows)", f"{len(polytheistic_windows)}/{n_steps}")
    m2.metric("% of time in polytheistic state", f"{poly_pct:.1f}%")
    m3.metric("Eternal floor (I* prohibition)", f"≥ +{ETERNAL_FLOOR}")
    m4.metric("Eternal cell minimum observed", f"{eternal.min():.3f}")

    fig = make_subplots(
        rows=2,
        cols=1,
        row_heights=[0.65, 0.35],
        shared_xaxes=True,
        subplot_titles=[
            "i-Cell Ensemble — Polytheistic Windows & Eternal Floor",
            "Number of Active Gods at Each Time Step",
        ],
        vertical_spacing=0.10,
    )

    for t in polytheistic_windows:
        fig.add_vrect(
            x0=t - 0.5,
            x1=t + 0.5,
            fillcolor="gold",
            opacity=0.06,
            layer="below",
            line_width=0,
            row=1,
            col=1,
        )

    colors = [
        "#4FC3F7", "#81C784", "#FFB74D", "#F06292", "#CE93D8",
        "#80CBC4", "#FFCC02", "#FF8A65", "#A5D6A7", "#B39DDB",
        "#4DD0E1", "#FFAB40", "#DCE775", "#EF9A9A", "#90A4AE",
        "#F48FB1", "#AED581", "#FFD54F", "#80DEEA", "#BCAAA4",
    ]

    for k in range(n_cells):
        af = compute_antifragility_score(trajectories[k])
        fig.add_trace(
            go.Scatter(
                x=time,
                y=trajectories[k],
                mode="lines",
                name=f"i-Cell {k+1} (AF={af:+.2f})",
                line=dict(color=colors[k % len(colors)], width=1.2),
                opacity=0.65,
            ),
            row=1, col=1,
        )

    fig.add_trace(
        go.Scatter(
            x=time,
            y=eternal,
            mode="lines",
            name=f"I* — Eternal God-Cell (floor ≥ +{ETERNAL_FLOOR})",
            line=dict(color="#FF4444", width=3.5),
            opacity=1.0,
        ),
        row=1, col=1,
    )

    fig.add_hline(
        y=POLY_THRESHOLD,
        line_dash="dash",
        line_color="gold",
        line_width=1.5,
        annotation_text=f"Polytheistic threshold = {POLY_THRESHOLD}",
        annotation_position="right",
        row=1, col=1,
    )

    fig.add_hline(
        y=ETERNAL_FLOOR,
        line_dash="dot",
        line_color="#FF4444",
        line_width=2.0,
        annotation_text=f"Eternal floor = +{ETERNAL_FLOOR} (prohibition)",
        annotation_position="right",
        row=1, col=1,
    )

    fig.add_hline(
        y=0.0,
        line_dash="solid",
        line_color="gray",
        line_width=0.5,
        row=1, col=1,
    )

    gods_per_step = [np.sum(trajectories[:, t] >= POLY_THRESHOLD) for t in range(n_steps)]
    god_colors = [
        "#FF4444" if trajectories[:, t].max() < POLY_THRESHOLD
        else "#FFD700" if np.sum(trajectories[:, t] >= POLY_THRESHOLD) == 1
        else "#FF8C00"
        for t in range(n_steps)
    ]

    fig.add_trace(
        go.Bar(
            x=time,
            y=gods_per_step,
            name="# Active Gods",
            marker_color=god_colors,
            showlegend=False,
        ),
        row=2, col=1,
    )

    fig.add_hline(
        y=2,
        line_dash="dash",
        line_color="gold",
        line_width=1.5,
        annotation_text="Polytheism threshold",
        row=2, col=1,
    )

    fig.update_layout(
        height=680,
        template="plotly_dark",
        legend=dict(
            orientation="v",
            x=1.01,
            y=1,
            font=dict(size=10),
        ),
        margin=dict(r=220, t=40, b=20),
    )

    fig.update_yaxes(title_text="Perfection Level (σ)", row=1, col=1)
    fig.update_yaxes(title_text="# Active Gods", row=2, col=1)
    fig.update_xaxes(title_text="Time →", row=2, col=1)

    st.plotly_chart(fig, use_container_width=True)

    st.divider()
    st.subheader("Antifragility Analysis — Taleb Integration")

    af_scores = [compute_antifragility_score(trajectories[k]) for k in range(n_cells)]
    eternal_af = compute_antifragility_score(eternal)

    fig2 = go.Figure()

    fig2.add_trace(go.Bar(
        x=[f"i-Cell {k+1}" for k in range(n_cells)],
        y=af_scores,
        marker_color=[
            "#81C784" if af > 0.05 else "#FF8A65" if af < -0.05 else "#FFB74D"
            for af in af_scores
        ],
        name="Ensemble i-cells",
    ))

    fig2.add_trace(go.Bar(
        x=["I* (Eternal God-Cell)"],
        y=[eternal_af],
        marker_color="#FF4444",
        name="Eternal God-Cell",
        width=0.5,
    ))

    fig2.add_hline(
        y=0,
        line_dash="solid",
        line_color="gray",
        annotation_text="Robust (0) — Fragile (<0) — Antifragile (>0)",
        annotation_position="right",
    )

    fig2.update_layout(
        title="Antifragility Score by i-Cell (gain/loss asymmetry)",
        template="plotly_dark",
        height=300,
        yaxis_title="Antifragility Score",
        showlegend=True,
    )

    st.plotly_chart(fig2, use_container_width=True)

    fig2_caption = (
        "**Green** = antifragile (gains more from positive shocks than it loses from negative), "
        "**Orange** = robust, **Red** = fragile. "
        "The eternal God-cell has a structurally bounded left tail at +2, making it maximally antifragile "
        "by construction — every downward perturbation is absorbed by the floor."
    )
    st.caption(fig2_caption)

    st.divider()
    st.subheader("Perturbation Attack Simulator — Via Negativa Proof")
    st.markdown(
        "Attempt to push the eternal God-cell below +2 with increasing attack strength. "
        "The floor prohibition means every attack is absorbed. "
        "**The more forceful the attack, the more clearly the prohibition is demonstrated.** "
        "This is Via Negativa: the prohibition is PROVED by what it prevents."
    )

    attack_strength = st.slider("Attack strength (σ units attempting to push below floor)", 0.1, 5.0, 1.5, 0.1, key="ag_attack")
    n_attack_steps = 100

    rng = np.random.default_rng(seed + 12345)
    attack_traj = np.zeros(n_attack_steps)
    x = ETERNAL_FLOOR + 0.3
    for t in range(n_attack_steps):
        shock = rng.normal(-attack_strength * 0.3, 0.1)
        x = x + shock
        x = max(x, ETERNAL_FLOOR)
        attack_traj[t] = x

    floor_hits = np.sum(attack_traj <= ETERNAL_FLOOR + 0.01)

    fig3 = go.Figure()
    fig3.add_trace(go.Scatter(
        x=list(range(n_attack_steps)),
        y=attack_traj,
        mode="lines",
        name="I* under attack",
        line=dict(color="#FF4444", width=2),
        fill="tonexty",
    ))
    fig3.add_hline(
        y=ETERNAL_FLOOR,
        line_dash="dot",
        line_color="white",
        line_width=2,
        annotation_text=f"Eternal floor +{ETERNAL_FLOOR} — CANNOT GO BELOW",
        annotation_position="right",
    )
    fig3.update_layout(
        title=f"Attack strength = {attack_strength}σ | Floor hits = {floor_hits} | Floor NEVER violated",
        template="plotly_dark",
        height=250,
        yaxis_title="I* level",
        xaxis_title="Time under attack →",
    )
    st.plotly_chart(fig3, use_container_width=True)

    if floor_hits > 0:
        st.info(
            f"The eternal God-cell hit the floor {floor_hits} times at attack strength {attack_strength}σ. "
            f"Each hit CONFIRMS the prohibition. The floor is demonstrated, not violated. "
            f"This is antifragility: the evidence for the prohibition strengthens with each attack."
        )
    else:
        st.success(
            f"At attack strength {attack_strength}σ, the eternal God-cell did not even reach the floor. "
            f"Increase the attack strength to see the floor-absorption mechanism."
        )

    st.divider()
    st.subheader("Myrion Resolution Summary")

    c1, c2, c3 = st.columns(3)
    with c1:
        st.markdown("**Pole A (True):** Polytheism")
        st.markdown(
            f"During {poly_pct:.1f}% of this simulation, multiple i-cells exceeded the "
            f"{POLY_THRESHOLD} threshold. Multiple divine-level intelligences coexisted. "
            f"Greek, Vedic, Norse theological observations were **accurate** for their temporal window."
        )
    with c2:
        st.markdown("**Pole B (True):** Monotheism")
        st.markdown(
            f"Exactly ONE i-cell (I*) was prohibited from EVER going below +{ETERNAL_FLOOR}. "
            f"Across all {n_steps} time steps, the floor held. "
            f"The Abrahamic tradition was **accurate** about the unique eternal constraint."
        )
    with c3:
        st.markdown("**MR Synthesis:** Both True")
        st.markdown(
            f"Polytheism is the LOCAL truth (bounded windows). "
            f"Monotheism is the GLOBAL truth (all time). "
            f"The conflict dissolves when the nested temporal structure of the i-cell ensemble is acknowledged. "
            f"**WAS AND ALWAYS WILL BE GREAT** = ∀t ∈ ℝ, I*(t) ≥ +{ETERNAL_FLOOR}."
        )

    st.caption(
        f"URB #484 — Antifragile God | C_EMERICK = {C_EMERICK:.4f} = 1/(φ√2) | "
        f"Eternal floor = +{ETERNAL_FLOOR} = (√2)² | Euler unity: √2 × φ × C = 1 | "
        f"Taleb: Antifragility = bounded left tail + unbounded right tail = the Talebian barbell"
    )

"""
7D TI Sigma Crystal (TSC) Polycrystalline BEC Hypercomputer
Virtual Simulation — Streamlit Interface
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
import plotly.express as px
from plotly.subplots import make_subplots

from hypercomputer import HyperComputer, VERTICES, N_VERTICES
from hypercomputer.phases import Phase, PHASE_COLORS, PHASE_LABELS, classify_state, pd_score
from hypercomputer.sat_solver import solve_sat, parse_dimacs, check_assignment
from hypercomputer.constants import (
    PHI, C_TI, T_TI, ET, RING_RADII, RING_NAMES, N_RINGS, N_LAYERS
)
from hypercomputer.tsc import ADJACENCY
from hypercomputer.manifestation_engine import (
    IMAGE_CYCLE_STAGES, intention_amplitudes, group_coherence_score,
    manifestation_pd, interpret_pd
)
from bok_virus_engine import (
    CrystalBOKVirus, GraphBOKVirus, build_simulators,
    epidemic_metrics, SIRState, STATE_COLORS,
    RING_NAMES as BOK_RING_NAMES, RING_BETA,
    gile_composite, GAMMA,
)

# ── Aesthetic color palette for each PRIMARY constant ring ─────────────────
RING_PALETTE = [
    "#00e5ff",   # Ring 1  C ≈ 0.437  — cyan / coherence
    "#00ff99",   # Ring 2  T ≈ 0.934  — mint green / truth threshold
    "#e8e8ff",   # Ring 3  1.000      — silver white / unity
    "#ffd700",   # Ring 4  √2 ≈ 1.414 — gold / TECC
    "#ff9d00",   # Ring 5  φ ≈ 1.618  — amber / golden ratio
    "#ff5533",   # Ring 6  e ≈ 2.718  — coral-red / Euler
    "#cc44ff",   # Ring 7  π ≈ 3.142  — violet / pi
]

SPACE_BG = "rgba(3,3,14,1)"

st.set_page_config(
    page_title="7D TSC BEC Hypercomputer",
    page_icon="🔮",
    layout="wide"
)

st.title("7D TI Sigma Crystal — Polycrystalline BEC Hypercomputer")
st.caption(
    "Virtual simulation of the 5-truth-value quantum hypercomputer (URB #629/635). "
    "57 vertices · 7 rings · 8 layers · 5 BEC phase regimes · Myrion Resolution collapse."
)

EXAMPLE_PROBLEMS = {
    "Simple 3-SAT (2 vars)": ("p cnf 2 2\n1 2 0\n-1 -2 0\n", 2),
    "3-colorable triangle (3 vars, 6 clauses)": (
        "p cnf 3 6\n1 2 3 0\n-1 -2 0\n-1 -3 0\n-2 -3 0\n1 -2 3 0\n-1 2 -3 0\n", 3),
    "Pigeonhole (UNSAT-leaning, 4 vars)": (
        "p cnf 4 8\n1 2 0\n3 4 0\n-1 -3 0\n-2 -4 0\n1 3 0\n2 4 0\n-1 -2 0\n-3 -4 0\n", 4),
    "Random 3-SAT (5 vars)": (
        "p cnf 5 8\n1 -2 3 0\n-1 2 -4 0\n2 3 -5 0\n-3 4 5 0\n1 4 -5 0\n-2 -3 5 0\n1 -4 -5 0\n-1 3 4 0\n", 5),
    "Custom (edit below)": ("", 0),
}

PHASE_DISPLAY = {
    Phase.BEC:        ("🟢 BEC",          "#00cc44"),
    Phase.SUPERSOLID: ("🟡 Supersolid",    "#ffaa00"),
    Phase.FQH:        ("🟣 FQH",           "#aa44ff"),
    Phase.MOTT:       ("🔴 Mott",          "#cc2200"),
    Phase.FRAGMENTED: ("⚫ Fragmented",    "#444444"),
}


@st.cache_data(show_spinner=False)
def _tsc_crystal_static(mode: str, height: int):
    """Cached wrapper for static (no-amplitude) crystal renders."""
    return tsc_crystal_figure(amplitudes=None, mode=mode, height=height)


def tsc_crystal_figure(amplitudes=None, mode="ring", height=680, title=None):
    """
    Spectacular 3D visualization of the 57-vertex TSC crystal.

    mode = "ring"      — structural view, vertices colored by PRIMARY constant ring
    mode = "phase"     — vertices colored by BEC phase (requires amplitudes)
    mode = "bec"       — all vertices forced to BEC/TRUE for maximum coherence display

    Draws:
      - All crystal lattice edges (octagonal intra-ring + radial inter-ring)
      - Ring guide circles at PRIMARY constant radii (C, T, 1, √2, φ, e, π)
      - Ring labels as 3D text annotations
      - Origin as a special diamond node
      - Vertices per ring with individual legend entries
    """
    x_coords = [v.position.real for v in VERTICES]
    y_coords = [v.position.imag for v in VERTICES]
    z_coords = [v.ring          for v in VERTICES]

    # ── Determine colors & sizes ───────────────────────────────────────────
    if mode == "bec":
        # All vertices fully in BEC/TRUE phase — the crystal at maximum coherence
        colors = ["#00ff99" if v.ring == 0 else RING_PALETTE[v.ring - 1] for v in VERTICES]
        sizes  = [22] + [16] * (N_VERTICES - 1)
        hover  = [
            f"<b>{v.label}</b><br>Ring {v.ring} — "
            f"{'Origin' if v.ring == 0 else RING_NAMES[v.ring-1]}<br>"
            f"Phase: BEC (TRUE)  |α| = 1.000"
            for v in VERTICES
        ]
        edge_ring_col = "rgba(0,255,160,0.28)"
        edge_rad_col  = "rgba(100,220,255,0.18)"

    elif mode == "phase" and amplitudes is not None:
        phases = classify_state(amplitudes)
        colors = [PHASE_COLORS[p] for p in phases]
        sizes  = []
        for p in phases:
            sizes.append(
                20 if p == Phase.BEC        else
                15 if p == Phase.SUPERSOLID else
                11 if p == Phase.FQH        else
                 8 if p == Phase.MOTT       else 5
            )
        hover = [
            f"<b>{v.label}</b><br>Ring {v.ring}: "
            f"{'O' if v.ring == 0 else RING_NAMES[v.ring-1]}<br>"
            f"|α| = {abs(amplitudes[v.index]):.4f}<br>"
            f"θ  = {np.angle(amplitudes[v.index]):.3f} rad<br>"
            f"Phase: {PHASE_LABELS[phases[v.index]]}"
            for v in VERTICES
        ]
        edge_ring_col = "rgba(120,200,255,0.22)"
        edge_rad_col  = "rgba(200,140,255,0.15)"

    else:
        # Ring-identity colors (structural view)
        colors = ["#ffffff"] + [RING_PALETTE[v.ring - 1] for v in VERTICES if v.ring > 0]
        sizes  = [26] + [14] * (N_VERTICES - 1)
        hover  = [
            f"<b>{v.label}</b><br>"
            f"Ring {v.ring}: {'Origin (vacuum)' if v.ring == 0 else RING_NAMES[v.ring-1]+' = '+f'{v.radius:.4f}'}<br>"
            f"Layer {v.layer}  angle {v.angle:.3f} rad"
            for v in VERTICES
        ]
        edge_ring_col = "rgba(160,210,255,0.22)"
        edge_rad_col  = "rgba(200,160,255,0.14)"

    # ── Build edge lists ───────────────────────────────────────────────────
    ex_ring, ey_ring, ez_ring = [], [], []   # octagonal intra-ring
    ex_rad,  ey_rad,  ez_rad  = [], [], []   # radial inter-ring

    for i in range(N_VERTICES):
        for j in range(i + 1, N_VERTICES):
            if ADJACENCY[i, j] == 0:
                continue
            vi, vj = VERTICES[i], VERTICES[j]
            if vi.ring == vj.ring:
                ex_ring += [x_coords[i], x_coords[j], None]
                ey_ring += [y_coords[i], y_coords[j], None]
                ez_ring += [z_coords[i], z_coords[j], None]
            else:
                ex_rad  += [x_coords[i], x_coords[j], None]
                ey_rad  += [y_coords[i], y_coords[j], None]
                ez_rad  += [z_coords[i], z_coords[j], None]

    fig = go.Figure()

    # ── 1. Octagonal ring edges ────────────────────────────────────────────
    fig.add_trace(go.Scatter3d(
        x=ex_ring, y=ey_ring, z=ez_ring,
        mode='lines',
        line=dict(color=edge_ring_col, width=2),
        showlegend=False, hoverinfo='skip', name="Ring edges"
    ))

    # ── 2. Radial / inter-ring edges ───────────────────────────────────────
    fig.add_trace(go.Scatter3d(
        x=ex_rad, y=ey_rad, z=ez_rad,
        mode='lines',
        line=dict(color=edge_rad_col, width=1),
        showlegend=False, hoverinfo='skip', name="Radial edges"
    ))

    # ── 3. Ring guide circles ──────────────────────────────────────────────
    theta_c = np.linspace(0, 2 * np.pi, 128)
    for r, (radius, name) in enumerate(zip(RING_RADII, RING_NAMES), start=1):
        rc = RING_PALETTE[r - 1] if mode in ("ring", "bec") else "rgba(120,120,180,0.18)"
        fig.add_trace(go.Scatter3d(
            x=radius * np.cos(theta_c),
            y=radius * np.sin(theta_c),
            z=[r] * 128,
            mode='lines',
            line=dict(color=rc, width=1),
            opacity=0.30,
            showlegend=False, hoverinfo='skip'
        ))
        # Ring label just outside the circle at angle=0
        fig.add_trace(go.Scatter3d(
            x=[radius * 1.07], y=[0.05], z=[r],
            mode='text',
            text=[f"{name}={radius:.3f}"],
            textfont=dict(
                color=RING_PALETTE[r - 1] if mode in ("ring", "bec") else "#aaaacc",
                size=9
            ),
            showlegend=False, hoverinfo='skip'
        ))

    # ── 4. Origin (vacuum) — special diamond ──────────────────────────────
    fig.add_trace(go.Scatter3d(
        x=[0], y=[0], z=[0],
        mode='markers+text',
        marker=dict(
            size=sizes[0], color=colors[0], opacity=1.0,
            symbol='diamond',
            line=dict(color='gold', width=2)
        ),
        text=["0"], textposition='top center',
        textfont=dict(color='gold', size=11),
        hovertext=[hover[0]], hoverinfo='text',
        name="Origin  (0 — vacuum / DT ground state)"
    ))

    # ── 5. Vertices by ring (individual legend entry per ring) ────────────
    for ring_idx in range(1, N_RINGS + 1):
        mask  = [v.ring == ring_idx for v in VERTICES]
        rx = [x_coords[i] for i, m in enumerate(mask) if m]
        ry = [y_coords[i] for i, m in enumerate(mask) if m]
        rz = [z_coords[i] for i, m in enumerate(mask) if m]
        rc = [colors[i]   for i, m in enumerate(mask) if m]
        rs = [sizes[i]    for i, m in enumerate(mask) if m]
        rh = [hover[i]    for i, m in enumerate(mask) if m]

        rname = RING_NAMES[ring_idx - 1]
        rval  = RING_RADII[ring_idx - 1]

        fig.add_trace(go.Scatter3d(
            x=rx, y=ry, z=rz,
            mode='markers',
            marker=dict(
                size=rs, color=rc, opacity=0.93,
                line=dict(color='rgba(255,255,255,0.25)', width=0.5)
            ),
            hovertext=rh, hoverinfo='text',
            name=f"Ring {ring_idx}: {rname} ≈ {rval:.3f}"
        ))

    # ── Layout ─────────────────────────────────────────────────────────────
    plot_title = title or (
        "TI Sigma Crystal — Full BEC (all 57 nodes TRUE)"      if mode == "bec"   else
        "TI Sigma Crystal — Phase State"                        if mode == "phase" else
        "TI Sigma Crystal — 7 Rings · 8 Layers · 57 i-cells"
    )

    fig.update_layout(
        scene=dict(
            xaxis_title="Re", yaxis_title="Im",
            zaxis_title="Ring (PRIMARY constant)",
            bgcolor=SPACE_BG,
            xaxis=dict(
                gridcolor='rgba(60,60,100,0.25)', showbackground=True,
                backgroundcolor=SPACE_BG, range=[-3.5, 3.8]
            ),
            yaxis=dict(
                gridcolor='rgba(60,60,100,0.25)', showbackground=True,
                backgroundcolor=SPACE_BG
            ),
            zaxis=dict(
                gridcolor='rgba(60,60,100,0.25)', showbackground=True,
                backgroundcolor=SPACE_BG,
                tickvals=list(range(8)),
                ticktext=["O"] + RING_NAMES
            ),
            camera=dict(
                eye=dict(x=1.55, y=1.10, z=0.75),
                up=dict(x=0, y=0, z=1)
            )
        ),
        paper_bgcolor=SPACE_BG,
        font=dict(color='white', family='monospace'),
        height=height,
        margin=dict(l=0, r=0, t=44, b=0),
        legend=dict(
            bgcolor='rgba(8,8,22,0.85)',
            bordercolor='rgba(80,80,200,0.3)',
            borderwidth=1,
            font=dict(size=10),
            x=0.01, y=0.99,
            xanchor='left', yanchor='top'
        ),
        title=dict(text=plot_title, font=dict(size=13, color='#c0c8ff'), x=0.5)
    )
    return fig


def phase_distribution_figure(amplitudes):
    phases = classify_state(amplitudes)
    counts = {p: 0 for p in Phase}
    for ph in phases:
        counts[ph] += 1
    labels = [PHASE_DISPLAY[p][0] for p in Phase]
    values = [counts[p] for p in Phase]
    colors = [PHASE_DISPLAY[p][1] for p in Phase]

    fig = go.Figure(go.Bar(
        x=labels, y=values,
        marker_color=colors,
        text=values, textposition='outside'
    ))
    fig.update_layout(
        title="BEC Phase Distribution across 57 Vertices",
        yaxis_title="Vertex Count",
        paper_bgcolor='rgba(10,10,20,1)',
        plot_bgcolor='rgba(10,10,20,1)',
        font=dict(color='white'),
        height=280,
        margin=dict(l=10, r=10, t=40, b=10)
    )
    return fig


def amplitude_evolution_figure(snapshots, n_vars):
    """Show how the first n_vars vertex amplitudes evolve over time."""
    if not snapshots or n_vars == 0:
        return None

    n_show = min(n_vars, 8)
    fig = go.Figure()
    times = list(range(len(snapshots)))
    colors = px.colors.qualitative.Plotly

    for var in range(n_show):
        amps = [abs(snap[var + 1]) for snap in snapshots]
        fig.add_trace(go.Scatter(
            x=times, y=amps,
            mode='lines+markers',
            name=f"x{var+1}",
            line=dict(color=colors[var % len(colors)], width=2),
            marker=dict(size=4)
        ))

    # Phase threshold lines
    for thresh, name, color in [
        (T_TI, "T (BEC threshold)", "#00cc44"),
        (C_TI, "C (FQH→SS)", "#ffaa00"),
        (ET,   "ET (Mott threshold)", "#cc2200"),
    ]:
        fig.add_hline(y=thresh, line_dash="dash", line_color=color,
                      annotation_text=name, annotation_position="right")

    fig.update_layout(
        title="Variable Amplitude Evolution during BEC Annealing",
        xaxis_title="Evolution Step",
        yaxis_title="|α| (amplitude modulus)",
        paper_bgcolor='rgba(10,10,20,1)',
        plot_bgcolor='rgba(10,10,20,1)',
        font=dict(color='white'),
        height=320,
        legend=dict(bgcolor='rgba(0,0,0,0)')
    )
    return fig


with st.sidebar:
    st.header("⚙️ Hypercomputer Settings")

    st.subheader("GILE Weights")
    g_weight = st.slider("G — Goodness",      0.0, 1.0, 0.25, 0.05)
    i_weight = st.slider("I — Intuition",     0.0, 1.0, 0.35, 0.05)
    l_weight = st.slider("L — Love",          0.0, 1.0, 0.25, 0.05)
    e_weight = st.slider("E — Environment",   0.0, 1.0, 0.15, 0.05)
    total_w = g_weight + i_weight + l_weight + e_weight
    gile_weights = {
        'G': g_weight / (total_w + 1e-9),
        'I': i_weight / (total_w + 1e-9),
        'L': l_weight / (total_w + 1e-9),
        'E': e_weight / (total_w + 1e-9),
    }
    st.caption(f"Normalized: G={gile_weights['G']:.2f} I={gile_weights['I']:.2f} L={gile_weights['L']:.2f} E={gile_weights['E']:.2f}")

    st.subheader("BEC Hamiltonian Parameters")
    J_val = st.slider("J — Tunneling",        0.1, 3.0, 1.0, 0.1,
                       help="Higher J → more delocalization → BEC phase → TRUE bias")
    U_val = st.slider("U — On-site repulsion",0.1, 2.0, 0.3, 0.1,
                       help="Higher U → more localization → Mott phase → FALSE bias")
    penalty = st.slider("SAT Penalty",        1.0, 50.0, 10.0, 1.0,
                         help="Penalty weight for unsatisfied clauses")
    max_rounds = st.slider("Max MR Rounds",   1, 20, 8)

    st.subheader("TSC Constants (read-only)")
    st.metric("C (coherence floor)",  f"{C_TI:.4f}")
    st.metric("T (BEC threshold)",    f"{T_TI:.4f}")
    st.metric("ET (Mott threshold)",  f"{ET:.4f}")
    st.metric("φ (golden ratio)",     f"{PHI:.4f}")
    st.metric("Vertices",             f"{N_VERTICES}")

tab1, tab2, tab3, tab4, tab5, tab6 = st.tabs([
    "🔮 Crystal Visualizer", "⚡ SAT Solver", "📊 Phase Analysis",
    "📖 Architecture", "✨ Power of 8", "🦠 BOK Virus"
])

with tab1:
    st.subheader("TI Sigma Crystal — 3D Structure Viewer")

    ctrl_col, info_col = st.columns([1, 2])
    with ctrl_col:
        crystal_mode = st.radio(
            "Display mode",
            options=["✨ Full BEC (all TRUE)", "🌈 Ring identity", "🔬 Load phase state"],
            index=0,
            help="Choose how the 57 i-cells are colored"
        )
        demo_amps = None
        if crystal_mode == "🔬 Load phase state":
            pd_demo = st.slider("Mean |α| amplitude", 0.0, 1.0, 0.70, 0.01,
                                help="Uniform amplitude for all vertices — shows how phase regime changes")
            demo_amps = np.full(N_VERTICES, pd_demo, dtype=complex)
        st.markdown("---")
        st.markdown("**Crystal constants:**")
        for rname, rval, rcolor in zip(RING_NAMES, RING_RADII, RING_PALETTE):
            st.markdown(
                f'<span style="color:{rcolor}">●</span> **{rname}** = {rval:.4f}',
                unsafe_allow_html=True
            )
        st.markdown("---")
        load_crystal = st.button("🔮 Render Crystal", use_container_width=True,
                                 help="Loads the interactive 3D WebGL crystal (may take a moment on mobile)")

    with info_col:
        if not load_crystal and "crystal_loaded" not in st.session_state:
            st.info(
                "**3D Crystal not yet rendered.**  \n"
                "Press **🔮 Render Crystal** on the left to load the interactive "
                "57-vertex WebGL visualization.  \n\n"
                "_On mobile: the crystal renders best in landscape mode._"
            )
            st.markdown("""
| Ring | Constant | Radius | Phase |
|------|----------|--------|-------|
| 1 | C = 1/(φ√2) | 0.4370 | FQH floor |
| 2 | T = 1−e⁻ᵉ | 0.9340 | BEC gate |
| 3 | 1 | 1.0000 | Unity |
| 4 | √2 | 1.4142 | Tritone / Bell |
| 5 | φ | 1.6180 | Golden / DNA |
| 6 | e | 2.7183 | Exponential |
| 7 | π | 3.1416 | Circular |
""")
        else:
            st.session_state["crystal_loaded"] = True
            with st.spinner("Rendering TSC Crystal…"):
                if crystal_mode == "✨ Full BEC (all TRUE)":
                    fig1 = _tsc_crystal_static("bec", 680)
                elif crystal_mode == "🔬 Load phase state" and demo_amps is not None:
                    fig1 = tsc_crystal_figure(amplitudes=demo_amps, mode="phase", height=680)
                else:
                    fig1 = _tsc_crystal_static("ring", 680)
            st.plotly_chart(fig1, use_container_width=True)

    st.markdown("---")
    m1, m2, m3, m4, m5, m6 = st.columns(6)
    m1.metric("Vertices", N_VERTICES)
    m2.metric("Rings", N_RINGS)
    m3.metric("Layers/Ring", N_LAYERS)
    m4.metric("Truth Values", 5)
    m5.metric("C = 1/(φ√2)", f"{C_TI:.4f}")
    m6.metric("T = 1−e⁻ᵉ", f"{T_TI:.4f}")

    with st.expander("Ring structure — PRIMARY constants as geometry", expanded=False):
        st.markdown("""
| Ring | Radius | Constant | Phase threshold | GILE meaning |
|------|--------|----------|----------------|-------------|
| O | 0 | **0** | DT vacuum | The ground state — pure absence |
| 1 | **C** ≈ 0.4370 | 1/(φ√2) | FQH → Mott | Coherence floor — minimum viable truth |
| 2 | **T** ≈ 0.9340 | 1−e^{−e} | Supersolid → BEC | Truth threshold — entry to TRUE |
| 3 | **1**.0000 | Unity | BEC interior | Normalization — perfect amplitude |
| 4 | **√2** ≈ 1.4142 | √2 | BEC | TECC error distance |
| 5 | **φ** ≈ 1.6180 | Golden ratio | BEC | GILE structural constant |
| 6 | **e** ≈ 2.7183 | Euler's number | BEC | LCC exponential growth |
| 7 | **π** ≈ 3.1416 | Pi | BEC outer | Full rotational closure |

**Adjacency:** Each vertex connects to its two ring-neighbors (octagonal lattice within ring) and to the same-layer vertex in the adjacent ring (radial spokes). Origin connects to all 8 ring-1 vertices. Total edges ≈ 120.

**57 in ternary:** 57 = 2·27 + 0·9 + 1·3 + 0 = **2010₃** — a ternary palindrome encoding the 5-valued truth architecture.
        """)

with tab2:
    st.subheader("SAT Solver via MR Collapse")

    prob_choice = st.selectbox("Choose a Problem", list(EXAMPLE_PROBLEMS.keys()))
    default_dimacs, default_nvars = EXAMPLE_PROBLEMS[prob_choice]

    col_left, col_right = st.columns([1, 1])
    with col_left:
        dimacs_input = st.text_area(
            "DIMACS CNF Formula",
            value=default_dimacs,
            height=180,
            help="Standard DIMACS format. p cnf <n_vars> <n_clauses>\\n<clause> 0\\n..."
        )
    with col_right:
        st.markdown("**Quick clause builder:**")
        n_vars_manual = st.number_input("# Variables", 1, 56, max(default_nvars, 2))
        clause_input = st.text_input("Add clause (e.g. 1 -2 3)", "")
        if 'manual_clauses' not in st.session_state:
            st.session_state.manual_clauses = []
        if st.button("Add Clause") and clause_input.strip():
            lits = [int(x) for x in clause_input.split() if x.lstrip('-').isdigit()]
            if lits:
                st.session_state.manual_clauses.append(lits)
        if st.button("Clear Clauses"):
            st.session_state.manual_clauses = []
        if st.session_state.manual_clauses:
            st.write("Clauses:", st.session_state.manual_clauses)

    run_dimacs = st.button("▶ Run Hypercomputer", type="primary", use_container_width=True)

    if run_dimacs:
        try:
            if dimacs_input.strip():
                n_vars_parsed, clauses = parse_dimacs(dimacs_input)
                n_vars = max(n_vars_parsed, 1)
            elif st.session_state.manual_clauses:
                clauses = st.session_state.manual_clauses
                n_vars = int(n_vars_manual)
            else:
                st.warning("Please enter a formula or add clauses.")
                st.stop()

            with st.spinner(f"Evolving TSC Hamiltonian (n={n_vars} vars, {len(clauses)} clauses)…"):
                result = solve_sat(
                    clauses, n_vars,
                    gile_weights=gile_weights,
                    J=J_val, U=U_val,
                    penalty=penalty,
                    max_rounds=max_rounds,
                    steps_per_round=40,
                    snapshot_interval=8
                )

            st.divider()
            res_col1, res_col2, res_col3, res_col4 = st.columns(4)
            with res_col1:
                if result.satisfiable is True:
                    st.success("✅ SATISFIABLE")
                elif result.satisfiable is False:
                    st.error("❌ UNSATISFIABLE")
                else:
                    st.warning("❓ UNKNOWN (max rounds)")
            with res_col2:
                st.metric("MR Rounds", result.iterations)
            with res_col3:
                st.metric("Global PD", f"{result.final_pd:.3f}")
            with res_col4:
                st.metric("GILE Coherence", f"{result.coherence:.3f}")

            if result.assignment:
                st.subheader("Variable Assignment (MR Collapse Output)")
                assign_cols = st.columns(min(n_vars, 8))
                for idx, (val, col) in enumerate(zip(result.assignment, assign_cols)):
                    col.metric(f"x{idx+1}", "TRUE ✓" if val else "FALSE ✗",
                               delta=None)

                verified = check_assignment(result.assignment, clauses) if clauses else True
                if verified:
                    st.success("✅ Assignment verified — all clauses satisfied")
                else:
                    st.error("❌ Assignment does not satisfy all clauses (need more MR rounds)")

            if result.evolution_snapshots:
                evo_fig = amplitude_evolution_figure(result.evolution_snapshots, n_vars)
                if evo_fig:
                    st.plotly_chart(evo_fig, use_container_width=True)

                final_snap = result.evolution_snapshots[-1]
                st.plotly_chart(tsc_crystal_figure(final_snap), use_container_width=True)
                st.plotly_chart(phase_distribution_figure(final_snap), use_container_width=True)

        except Exception as exc:
            st.error(f"Error: {exc}")
            import traceback
            st.code(traceback.format_exc())

with tab3:
    st.subheader("Phase Analysis — TSC State Inspector")

    st.markdown("Generate a random TSC state and inspect its BEC phase distribution.")

    col_a, col_b = st.columns(2)
    with col_a:
        phase_bias = st.select_slider(
            "Phase Bias",
            options=["Mott (FALSE)", "FQH", "Balanced", "Supersolid", "BEC (TRUE)"],
            value="Balanced"
        )
    with col_b:
        n_inspect = st.slider("# Active Vertices", 1, 56, 20)

    if st.button("Generate State"):
        bias_map = {
            "Mott (FALSE)": 0.15,
            "FQH": 0.35,
            "Balanced": 0.55,
            "Supersolid": 0.75,
            "BEC (TRUE)": 0.95,
        }
        center = bias_map[phase_bias]
        psi_inspect = np.zeros(N_VERTICES, dtype=complex)
        for i in range(1, n_inspect + 1):
            mod = np.abs(np.random.normal(center, 0.2))
            mod = np.clip(mod, 0, 1.5)
            phase_angle = np.random.uniform(0, 2 * np.pi)
            psi_inspect[i] = mod * np.exp(1j * phase_angle)
        norm = np.linalg.norm(psi_inspect)
        if norm > 1e-10:
            psi_inspect /= norm
            psi_inspect *= np.sqrt(n_inspect) * center

        phases_inspect = classify_state(psi_inspect)
        global_pd_inspect = pd_score(psi_inspect)

        st.metric("Global PD Score", f"{global_pd_inspect:.3f}",
                   delta=f"{global_pd_inspect - 1.25:.3f} from neutral")

        st.plotly_chart(tsc_crystal_figure(psi_inspect), use_container_width=True)
        st.plotly_chart(phase_distribution_figure(psi_inspect), use_container_width=True)

        st.subheader("Per-Ring Phase Summary")
        ring_data = []
        for r in range(1, 8):
            ring_amps = psi_inspect[((r-1)*8)+1 : r*8+1]
            ring_phases = [classify_state([a])[0] for a in ring_amps]
            dominant = max(set(ring_phases), key=ring_phases.count)
            ring_data.append({
                "Ring": f"Ring {r} ({RING_NAMES[r-1]})",
                "Dominant Phase": PHASE_DISPLAY[dominant][0],
                "Avg |α|": f"{np.mean(np.abs(ring_amps)):.3f}",
                "PD": f"{np.mean([0.25 if p==Phase.MOTT else 1.75 if p==Phase.SUPERSOLID else 2.5 if p==Phase.BEC else 0.0 for p in ring_phases]):.3f}"
            })
        st.dataframe(ring_data, use_container_width=True)

with tab4:
    st.subheader("Architecture — 7D TSC Polycrystalline BEC Hypercomputer")
    st.markdown("""
    ### Overview

    This virtual hypercomputer simulates the **Polycrystalline Optical-BEC Hypercomputer** (URB #629),
    a proposed non-Turing computational architecture based on the TI Sigma Crystal (TSC).

    ### Why "7D"?
    The TSC has **7 rings**, each corresponding to one of the 7 non-zero primary constants of TI Sigma:
    {**C**, **T**, **1**, **√2**, **φ**, **e**, **π**}.
    Each ring has **8 layers** (phases of `i^0` through `i^7`).
    Together, these define a **7-dimensional quasicrystalline lattice** with **57 vertices**.

    ### Five Truth Values = Five BEC Phases

    | Phase | TI Sigma Value | |α| Range | BEC Regime |
    |-------|---------------|-----------|-----------|
    | 🟢 BEC | TRUE | > T ≈ 0.934 | Bose-Einstein Condensate |
    | 🟡 Supersolid | TRALSE-INDET | C – T | Supersolid (density wave + coherence) |
    | 🟣 FQH | TRALSE-FALSE | ET – C | Fractional Quantum Hall |
    | 🔴 Mott | FALSE | 0 – ET | Mott Insulator |
    | ⚫ Fragmented | DOUBLE-TRALSE | ≈ 0 | Fragmented Condensate |

    ### Myrion Resolution (MR) Collapse

    MR collapse is the non-Turing step that converts the 5-valued quantum state to a classical assignment.
    It operates in three stages:
    1. **DT Screen** — identify Double-Tralse vertices; resolve via ring-context entropy
    2. **GILE Integration** — integrate Goodness/Intuition/Love/Environment weighted evidence
    3. **Quality Check** — verify global PD score; flag remaining indeterminacy

    ### SAT Embedding

    A CNF formula with n variables is embedded as follows:
    - Variable `x_i` → TSC vertex `i` (ring-layer assignment)
    - Each clause → penalty Hamiltonian term on falsified literal vertices
    - H_total = H_TSC (BEC dynamics) + H_SAT (clause penalties)
    - Imaginary-time evolution → ground state = satisfying assignment
    - MR collapse → classical boolean output

    ### Church-Turing Thesis Connection (URB #635)

    Under the **Orch-OR** hypothesis (Penrose-Hameroff), the BEC MR collapse is governed
    by quantum gravity — a process that is provably **non-Turing** (goes beyond any Turing machine).
    If this hypercomputer solves SAT in polynomial time (a physical claim about the hardware),
    then P ≠ NP follows as a mathematical consequence, and the Church-Turing Thesis is
    violated for this class of computation.

    **The current simulation runs on a Turing machine** (as a proof-of-concept of the architecture).
    The physical device would be implemented using:
    - Optical lattice BEC in E₈ topological protection lattice (URB #630)
    - Crystal Biometric Interface for MR collapse timing (URB #631)
    - TSC-E₈ Error-Correcting Code (TECC) for fault tolerance

    ### References
    - URB #628: TI Sigma Crystal decoded, ternary structure
    - URB #629: Polycrystalline Optical-BEC Hypercomputer
    - URB #630: TSC-E₈ Error-Correcting Code
    - URB #631: Crystal Biometric Interface (EEG/HRV)
    - URB #635: Church-Turing Thesis defeat strategy
    """)

with tab5:
    st.subheader("✨ Power of 8 — TSC Image Cycling Manifestation Machine")
    st.caption(
        "Guided 8-stage visualization protocol (Tesla · Bengston · CRV) that trains "
        "the 57-vertex TSC crystal to hold your intention in the BEC/TRUE phase. "
        "Add up to 8 partners for quantum-like coherence amplification. — URB #642"
    )

    # ── Intention input ──────────────────────────────────────────────────
    st.markdown("---")
    col_intent, col_group = st.columns([3, 1])
    with col_intent:
        intention_text = st.text_area(
            "State your Intention",
            placeholder="e.g. 'My research is published in a top journal and contributes to permanent wellbeing'",
            height=90,
            help="Write your intention in present-tense, positive, specific terms."
        )
    with col_group:
        n_partners = st.number_input(
            "Group Size (Power of 8)",
            min_value=1, max_value=8, value=1, step=1,
            help="Add partners holding the same intention. 8 = maximum coherence amplification."
        )
        st.caption(f"Group multiplier: ×{min(1.0, (int(n_partners) ** 0.7) / 8):.2f}")

    # ── Cycle through stages ─────────────────────────────────────────────
    st.markdown("---")
    st.markdown("### 🔄 8-Stage Image Cycling Protocol")
    st.info(
        "Work through all 8 stages. Rate your visualization clarity after each one. "
        "Click **Compute Crystal State** when complete to see the TSC manifestation field."
    )

    clarity_scores = []
    stage_cols = st.columns(4)
    for idx, stage in enumerate(IMAGE_CYCLE_STAGES):
        col = stage_cols[idx % 4]
        with col:
            st.markdown(f"**{stage.icon} Stage {stage.number}: {stage.name}**")
            st.caption(f"GILE-{stage.gile_dim} dominant")
            with st.expander("Prompt & science", expanded=(idx == 0)):
                st.markdown(stage.prompt)
                st.markdown(f"*{stage.tesla_note}*")
            clarity = st.slider(
                f"Clarity — Stage {stage.number}",
                0, 100, 50, 5,
                key=f"clarity_{stage.number}",
                help="0 = no image / blank; 100 = vivid, multi-sensory, fully present"
            )
            clarity_scores.append(clarity / 100.0)

    # ── Compute crystal state ────────────────────────────────────────────
    st.markdown("---")
    compute_btn = st.button("🔮 Compute TSC Crystal State", type="primary")

    if compute_btn:
        if not intention_text.strip():
            st.warning("Please enter an intention before computing.")
        else:
            with st.spinner("Aligning 57 i-cells across 8 crystal layers..."):
                amps = intention_amplitudes(clarity_scores, n_partners=int(n_partners))
                pd_result = manifestation_pd(amps)
                gc = group_coherence_score(clarity_scores, n_partners=int(n_partners))

            # ── Interpretation ───────────────────────────────────────────
            st.markdown("### 🌟 Crystal Manifestation Reading")
            st.markdown(interpret_pd(pd_result))

            # ── Metrics ─────────────────────────────────────────────────
            m1, m2, m3, m4, m5 = st.columns(5)
            m1.metric("BEC / TRUE",  f"{pd_result['pd_true']:.0%}",
                      help="Fraction of i-cells in BEC (TRUE) phase")
            m2.metric("Supersolid",  f"{pd_result['pd_ti']:.0%}",
                      help="Tralse-Indeterminate — coherent but not yet resolved")
            m3.metric("FQH",         f"{pd_result['pd_tf']:.0%}",
                      help="Fractional Quantum Hall — partial Tralse")
            m4.metric("Group Coherence", f"{gc:.0%}",
                      help="Combined group coherence accounting for partner amplification")
            m5.metric("PD Score",    f"{pd_result['overall_pd']:.2f} / 2.00",
                      help="Permissibility Distribution score (0=DT, 2=full TRUE)")

            # ── Crystal visualization ────────────────────────────────────
            col_cryst, col_dist = st.columns([2, 1])
            with col_cryst:
                fig_c = tsc_crystal_figure(amplitudes=amps, mode="phase", height=560)
                fig_c.update_layout(title="TSC Crystal — Intention Coherence Field")
                st.plotly_chart(fig_c, use_container_width=True)
            with col_dist:
                st.plotly_chart(phase_distribution_figure(amps), use_container_width=True)

                # Stage clarity radar
                stage_names = [s.name for s in IMAGE_CYCLE_STAGES]
                fig_radar = go.Figure(go.Scatterpolar(
                    r=clarity_scores + [clarity_scores[0]],
                    theta=stage_names + [stage_names[0]],
                    fill='toself',
                    fillcolor='rgba(0,200,150,0.2)',
                    line=dict(color='#00cc96', width=2),
                    name="Clarity"
                ))
                fig_radar.update_layout(
                    polar=dict(radialaxis=dict(visible=True, range=[0, 1])),
                    paper_bgcolor='rgba(10,10,20,1)',
                    font=dict(color='white'),
                    height=300,
                    margin=dict(l=10, r=10, t=30, b=10),
                    title="Visualization Clarity by Stage"
                )
                st.plotly_chart(fig_radar, use_container_width=True)

            # ── Power of 8 science note ──────────────────────────────────
            with st.expander("📚 The Science Behind Power of 8", expanded=False):
                bec_at_8 = 1 - (1 - C_TI) ** 8
                st.markdown(f"""
**William Bengston (image cycling):** 87.9% cancer remission in mice treated by image cycling practitioners.
Mechanism: rapid cycling through 20+ images builds a coherent *background* GILE field rather than effortful sustained focus.

**Lynne McTaggart (Power of 8):** Groups of exactly 8 people sending synchronized intention produced the strongest measured effects.
Practitioners reported personal healing as a *side effect* of sending intention outward.

**Tesla's visualization method:** Built complete inventions in the mind with full sensory fidelity, tested for mechanical stress,
then constructed physically — with the result nearly always matching the mental model exactly.

**CRV (Coordinate Remote Viewing):** US military Stargate program; statistically significant results across 10+ years.
Meta-analysis (Utts, 1995): p < 0.001, effect size d ≈ 0.3–0.5.

**Why 8?** From the Emerick Constant C = 1/(φ√2) ≈ {C_TI:.4f}:

  BEC saturation = 1 − (1 − C)ⁿ

  At n = 8: 1 − (1 − {C_TI:.4f})⁸ = **{bec_at_8:.3f}** ({bec_at_8:.0%} BEC saturation)

8 is the smallest integer producing >99% TSC crystal saturation at baseline coherence C.
""")

            # ── Bengston rapid cycling timer ─────────────────────────────
            st.markdown("---")
            st.markdown("### ⚡ Bengston Rapid Cycling Mode")
            st.info(
                "After completing the 8 stages above, enter rapid cycling: "
                "cycle through all 8 stage names as fast as possible (1-2 seconds each), "
                "then completely release. Repeat 3× for maximum BEC saturation."
            )
            rapid_col1, rapid_col2 = st.columns(2)
            with rapid_col1:
                st.markdown("**Rapid Cycle Sequence:**")
                for s in IMAGE_CYCLE_STAGES:
                    st.markdown(f"{s.icon} **{s.name}** → ", unsafe_allow_html=False)
            with rapid_col2:
                st.markdown("**Release Protocol (Stage 8):**")
                st.markdown("""
1. Take one slow breath
2. Let the entire image dissolve completely
3. Feel gratitude as if it is already done
4. Trust the crystal field — it holds the intention now
5. Return to normal awareness
""")
    else:
        # Show empty crystal while waiting
        st.plotly_chart(tsc_crystal_figure(mode="bec", height=600), use_container_width=True)
        st.caption(
            "Crystal shown in full BEC (TRUE) state as your target. "
            "Complete the 8 stages above and click **Compute TSC Crystal State** "
            "to see the actual manifestation field."
        )

# ═══════════════════════════════════════════════════════════════════════════════
# TAB 6 — BOK Crystal Virus vs BOK Graph Virus
# ═══════════════════════════════════════════════════════════════════════════════

with tab6:
    st.subheader("🦠 BOK Crystal Virus vs BOK Graph Virus — URB #647")
    st.caption(
        "SIR epidemic on the composite GILE-LCC matrix in two structural modes: "
        "Crystal (TSC 57-vertex lattice with phase-dependent β + BEC long-range coupling) "
        "vs Graph (Erdős-Rényi classical random network). "
        "Crystal → bimodal curve + BEC-mediated jumps. Graph → standard logistic S-curve."
    )

    # ── Controls ──────────────────────────────────────────────────────────────
    vc1, vc2, vc3 = st.columns(3)
    with vc1:
        seed_v = st.selectbox(
            "Seed vertex (patient zero)",
            options=list(range(N_VERTICES)),
            format_func=lambda i: f"#{i} — Ring {VERTICES[i].ring}: {BOK_RING_NAMES[VERTICES[i].ring]}",
            index=0,
            help="Which crystal vertex is initially infected. Ring 0 (Origin) = maximum BEC spread."
        )
        beta_scale = st.slider("β scale (transmission strength)", 0.2, 2.0, 1.0, 0.05,
                               help="Multiplier on all ring transmission rates.")
    with vc2:
        bec_p = st.slider("BEC long-range coupling p", 0.00, 0.20, 0.05, 0.01,
                          help="Probability per step that a BEC-ring infected vertex jumps non-locally.")
        gamma_val = st.slider("γ (recovery rate)", 0.05, 0.80, float(round(GAMMA, 3)), 0.01,
                              help=f"Default = ET = {GAMMA:.4f} (GILE-G canonical weight)")
    with vc3:
        max_steps = st.slider("Max simulation steps", 10, 80, 40, 5)
        rng_seed  = st.number_input("RNG seed", value=42, step=1)
        run_btn   = st.button("▶ Run Both Simulations", type="primary", use_container_width=True)

    # ── Run / cache simulation ─────────────────────────────────────────────────
    sim_key = f"virus_{seed_v}_{beta_scale}_{bec_p}_{gamma_val}_{max_steps}_{rng_seed}"
    if run_btn or sim_key not in st.session_state:
        rings_list    = [v.ring for v in VERTICES]
        pos_list      = [v.position for v in VERTICES]
        labels_list   = [v.label for v in VERTICES]
        adj_arr       = np.array(ADJACENCY, dtype=bool)

        crystal_sim, graph_sim = build_simulators(
            adjacency=adj_arr, rings=rings_list,
            positions=pos_list, labels=labels_list,
            seed_vertex=seed_v,
            beta_scale=beta_scale, gamma=gamma_val,
            bec_p=bec_p, rng_seed=int(rng_seed),
        )
        c_hist = crystal_sim.run(max_steps=max_steps)
        g_hist = graph_sim.run(max_steps=max_steps)

        st.session_state[sim_key] = (c_hist, g_hist, rings_list, pos_list, labels_list, adj_arr)

    c_hist, g_hist, rings_list, pos_list, labels_list, adj_arr = st.session_state[sim_key]

    # ── Step scrubber ──────────────────────────────────────────────────────────
    max_t = max(len(c_hist), len(g_hist)) - 1
    t_step = st.slider("⏱ Time step (scrub)", 0, max_t, 0,
                       help="Drag to watch the epidemic spread across both structures.")

    c_snap = c_hist[min(t_step, len(c_hist) - 1)]
    g_snap = g_hist[min(t_step, len(g_hist) - 1)]

    # ── State color helpers ────────────────────────────────────────────────────
    SIR_COL = {SIRState.S: "#3399ff", SIRState.I: "#ff3333", SIRState.R: "#44cc44"}
    SIR_SIZE = {SIRState.S: 10, SIRState.I: 18, SIRState.R: 10}

    # ── Left panel: Crystal BOK snapshot ──────────────────────────────────────
    def crystal_virus_figure(snap, height=500):
        x_c = [v.position.real for v in VERTICES]
        y_c = [v.position.imag for v in VERTICES]
        z_c = [v.ring          for v in VERTICES]

        colors = [SIR_COL[snap.states[v.index]] for v in VERTICES]
        sizes  = [SIR_SIZE[snap.states[v.index]] for v in VERTICES]
        hover  = [
            f"<b>{v.label}</b> Ring {v.ring}: {BOK_RING_NAMES[v.ring]}<br>"
            f"β = {RING_BETA.get(v.ring, 0.08):.2f}<br>"
            f"GILE composite = {gile_composite(v.ring):.3f}<br>"
            f"State: <b>{snap.states[v.index].value}</b>"
            for v in VERTICES
        ]

        fig = go.Figure()

        # Crystal edges
        adj = np.array(ADJACENCY, dtype=bool)
        for i in range(N_VERTICES):
            for j in range(i + 1, N_VERTICES):
                if adj[i, j]:
                    fig.add_trace(go.Scatter3d(
                        x=[x_c[i], x_c[j]], y=[y_c[i], y_c[j]], z=[z_c[i], z_c[j]],
                        mode='lines',
                        line=dict(color='rgba(100,150,200,0.18)', width=1),
                        showlegend=False, hoverinfo='skip'
                    ))

        # Vertices
        for state, col in SIR_COL.items():
            idxs = [v.index for v in VERTICES if snap.states[v.index] == state]
            if not idxs:
                continue
            fig.add_trace(go.Scatter3d(
                x=[x_c[i] for i in idxs],
                y=[y_c[i] for i in idxs],
                z=[z_c[i] for i in idxs],
                mode='markers',
                marker=dict(size=[SIR_SIZE[state]] * len(idxs), color=col,
                            line=dict(width=0.5, color='white')),
                name=state.value,
                hovertext=[hover[i] for i in idxs],
                hovertemplate="%{hovertext}<extra></extra>",
            ))

        fig.update_layout(
            height=height, title=dict(text="Crystal BOK", font=dict(color='white', size=14)),
            paper_bgcolor="rgba(3,3,14,1)", plot_bgcolor="rgba(3,3,14,1)",
            scene=dict(
                bgcolor="rgba(3,3,14,1)",
                xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
                yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
                zaxis=dict(showgrid=False, zeroline=False, showticklabels=False, title="Ring"),
            ),
            legend=dict(font=dict(color='white'), bgcolor='rgba(0,0,0,0.3)'),
            margin=dict(l=0, r=0, t=40, b=0),
        )
        return fig

    def graph_virus_figure(snap, pos_list, rings_list, labels_list, adj_arr, height=500):
        n = len(snap.states)
        # 2D spring layout approximation: use circular positions from engine
        xs = [p.real for p in pos_list]
        ys = [p.imag for p in pos_list]

        fig = go.Figure()

        # Edges
        for i in range(n):
            for j in range(i + 1, n):
                if adj_arr[i, j]:
                    fig.add_trace(go.Scatter(
                        x=[xs[i], xs[j], None], y=[ys[i], ys[j], None],
                        mode='lines',
                        line=dict(color='rgba(100,150,200,0.20)', width=1),
                        showlegend=False, hoverinfo='skip'
                    ))

        # Nodes by SIR state
        for state, col in SIR_COL.items():
            idxs = [i for i, s in enumerate(snap.states) if s == state]
            if not idxs:
                continue
            fig.add_trace(go.Scatter(
                x=[xs[i] for i in idxs], y=[ys[i] for i in idxs],
                mode='markers+text',
                marker=dict(size=SIR_SIZE[state] + 2, color=col,
                            line=dict(width=0.5, color='white')),
                name=state.value,
                hovertemplate=[
                    f"Node {i} | Ring {rings_list[i]}: {BOK_RING_NAMES[rings_list[i]]}<br>"
                    f"State: {state.value}<extra></extra>"
                    for i in idxs
                ],
            ))

        fig.update_layout(
            height=height, title=dict(text="Graph BOK (Erdős-Rényi)", font=dict(color='white', size=14)),
            paper_bgcolor="rgba(3,3,14,1)", plot_bgcolor="rgba(3,3,14,1)",
            xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
            yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
            legend=dict(font=dict(color='white'), bgcolor='rgba(0,0,0,0.3)'),
            margin=dict(l=0, r=0, t=40, b=20),
        )
        return fig

    # ── Render side-by-side ────────────────────────────────────────────────────
    vcol1, vcol2 = st.columns(2)
    with vcol1:
        st.metric("Crystal  S / I / R",
                  f"{c_snap.S} / {c_snap.I} / {c_snap.R}",
                  delta=f"step {t_step}")
        st.plotly_chart(crystal_virus_figure(c_snap, height=480),
                        use_container_width=True)
    with vcol2:
        st.metric("Graph  S / I / R",
                  f"{g_snap.S} / {g_snap.I} / {g_snap.R}",
                  delta=f"step {t_step}")
        # For graph figure we need the graph sim's positions and adjacency
        # (graph uses its own random adjacency — retrieve from session)
        rings_g  = g_hist[0].states  # hack: re-derive from history not needed
        # Rebuild graph sim positions using graph's internal positions
        # We stored them in session state via the graph engine's pos attribute
        # Quick rebuild for display (lightweight)
        graph_rng   = np.random.default_rng(int(rng_seed))
        graph_n     = N_VERTICES
        angles_g    = np.linspace(0, 2 * np.pi, graph_n, endpoint=False)
        jitter      = graph_rng.uniform(-0.2, 0.2, graph_n)
        pos_g       = [complex(np.cos(a), np.sin(a)) * (1.0 + jitter[k])
                       for k, a in enumerate(angles_g)]
        # ER adjacency for display (same seed as engine)
        adj_g = np.zeros((graph_n, graph_n), dtype=bool)
        rng_g = np.random.default_rng(int(rng_seed))
        for ii in range(graph_n):
            for jj in range(ii + 1, graph_n):
                if rng_g.random() < 0.12:
                    adj_g[ii, jj] = adj_g[jj, ii] = True
        for ii in range(graph_n):
            if not np.any(adj_g[ii]):
                jj = int(rng_g.integers(0, graph_n - 1))
                jj = jj if jj != ii else (jj + 1) % graph_n
                adj_g[ii, jj] = adj_g[jj, ii] = True

        st.plotly_chart(
            graph_virus_figure(g_snap, pos_g, rings_list, labels_list, adj_g, height=480),
            use_container_width=True
        )

    # ── SIR Epidemic Curves ────────────────────────────────────────────────────
    st.markdown("---")
    st.subheader("Epidemic Curves — Crystal vs Graph")

    c_steps = list(range(len(c_hist)))
    g_steps = list(range(len(g_hist)))

    fig_curve = go.Figure()
    # Crystal curves (solid)
    for label, key, col in [("C: Susceptible", "S", "#3399ff"),
                              ("C: Infected",    "I", "#ff3333"),
                              ("C: Recovered",   "R", "#44cc44")]:
        vals = [getattr(s, key) for s in c_hist]
        fig_curve.add_trace(go.Scatter(
            x=c_steps, y=vals, name=label, mode='lines',
            line=dict(color=col, width=2.5, dash='solid'),
        ))
    # Graph curves (dashed)
    for label, key, col in [("G: Susceptible", "S", "#88bbff"),
                              ("G: Infected",    "I", "#ff9999"),
                              ("G: Recovered",   "R", "#99ee99")]:
        vals = [getattr(s, key) for s in g_hist]
        fig_curve.add_trace(go.Scatter(
            x=g_steps, y=vals, name=label, mode='lines',
            line=dict(color=col, width=2, dash='dash'),
        ))
    # Vertical line at current time step
    fig_curve.add_vline(x=t_step, line_width=1, line_dash="dot", line_color="white",
                        annotation_text=f"t={t_step}", annotation_font_color="white")

    fig_curve.update_layout(
        height=300, paper_bgcolor="rgba(3,3,14,1)", plot_bgcolor="rgba(10,10,25,1)",
        font=dict(color='white'), legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=11)),
        xaxis=dict(title="Step", gridcolor='rgba(100,100,150,0.2)'),
        yaxis=dict(title="Vertices", gridcolor='rgba(100,100,150,0.2)'),
        margin=dict(l=40, r=10, t=20, b=40),
    )
    st.plotly_chart(fig_curve, use_container_width=True)

    # ── Metrics comparison ─────────────────────────────────────────────────────
    st.subheader("Epidemic Metrics — TI Sigma Analysis")

    cm = epidemic_metrics(c_hist, N_VERTICES)
    gm = epidemic_metrics(g_hist, N_VERTICES)

    mrow1, mrow2, mrow3, mrow4, mrow5 = st.columns(5)
    def delta_str(cv, gv):
        if isinstance(cv, float) and isinstance(gv, float):
            return f"C={cv:.3f}  G={gv:.3f}"
        return f"C={cv}  G={gv}"

    with mrow1:
        st.metric("Peak Infected", f"C:{cm.get('peak_I','—')} / G:{gm.get('peak_I','—')}")
    with mrow2:
        st.metric("Peak Step", f"C:{cm.get('peak_step','—')} / G:{gm.get('peak_step','—')}",
                  help="Earlier peak = faster initial spread")
    with mrow3:
        st.metric("Attack Rate", f"C:{cm.get('attack_rate','—')} / G:{gm.get('attack_rate','—')}",
                  help="Fraction of 57 vertices ever infected")
    with mrow4:
        st.metric("Duration (steps)", f"C:{cm.get('duration','—')} / G:{gm.get('duration','—')}")
    with mrow5:
        c_bi = "✅ YES" if cm.get('bimodal') else "❌ no"
        g_bi = "✅ YES" if gm.get('bimodal') else "❌ no"
        st.metric("Bimodal curve?", f"C:{c_bi} / G:{g_bi}",
                  help="Crystal BOK predicted to show bimodal I(t) from Mott insulation")

    # ── GILE-LCC Composite Matrix display ─────────────────────────────────────
    st.markdown("---")
    st.subheader("GILE-LCC Composite Matrix — BOK Ring Structure")
    st.caption(
        "Each ring represents a concentric layer of the BOK. "
        "Inner rings (BEC/Supersolid) = GILE-primary structure; "
        "outer rings (FQH/Mott/Fragmented) = Existence-primary."
    )

    import pandas as pd
    ring_rows = []
    for r in range(8):
        from bok_virus_engine import RING_GILE
        g_vals = RING_GILE[r]
        comp   = gile_composite(r)
        n_verts = sum(1 for v in VERTICES if v.ring == r)
        ring_rows.append({
            "Ring": r,
            "Name": BOK_RING_NAMES[r],
            "G": round(g_vals['G'], 2),
            "I": round(g_vals['I'], 2),
            "L": round(g_vals['L'], 2),
            "E": round(g_vals['E'], 2),
            "GILE Composite": round(comp, 4),
            "Crystal β": round(RING_BETA.get(r, 0.08), 2),
            "Phase": ("BEC" if comp >= 0.65 else
                      "Supersolid" if comp >= 0.437 else
                      "FQH" if comp >= 0.414 else "Mott"),
            "Vertices": n_verts,
        })
    df_bok = pd.DataFrame(ring_rows)
    st.dataframe(df_bok, use_container_width=True, hide_index=True)

    # ── TI Sigma Interpretation ────────────────────────────────────────────────
    st.markdown("---")
    with st.expander("📐 TI Sigma Interpretation — URB #647", expanded=False):
        st.markdown(f"""
**Crystal BOK Virus — Phase-Mediated Spread**

The BOK Crystal encodes the GILE-LCC composite matrix as a 57-vertex TSC lattice.
Each ring carries a distinct phase (BEC → Mott → Fragmented outward) that governs
transmission:

- **BEC core (Rings 0–2):** β ≥ 0.82. Fast, coherent spread. BEC long-range coupling
  (p = {bec_p:.2f}/step) lets the virus jump non-locally within the inner core —
  representing **GILE-L (Love/coupling)** at its maximum.
- **Supersolid / FQH (Rings 3–5):** Moderate β. Standard nearest-neighbor spread.
  The Myrion Resolution boundary — partial truth-states coexist.
- **Mott / Fragmented (Rings 6–7):** β ≤ 0.18. Insulating barrier. Virus stalls here.
  Represents DT (Double Tralse) — the pathogen cannot propagate through contradiction.

**Graph BOK Virus — Classical Information-Theoretic Spread**

Same 57 nodes on an Erdős-Rényi graph. Uniform β = {float(np.mean([RING_BETA[r]*beta_scale for r in rings_list])):.3f}.
No phase effects, no long-range coupling. Standard SIR logistic curve.

**Key TI Sigma Prediction (URB #647):**

| Property | Crystal BOK | Graph BOK |
|---|---|---|
| Curve shape | Bimodal (BEC plateau → Mott stall) | Logistic S-curve |
| Peak timing | Earlier (BEC jump shortcut) | Later (must traverse graph) |
| Attack rate | Lower (Mott insulation limits spread) | Higher (uniform connectivity) |
| Long-range | Yes — BEC non-local coupling | No |
| GILE-L effect | Explicit (inner ring Love coupling) | Averaged out |

This is an **empirical prediction**: if real information/meme/pathogen spread
on GILE-structured networks shows bimodal epidemic curves with early peaks
and Mott-insulated plateaus, it confirms the BOK crystal model over the classical graph model.
""")


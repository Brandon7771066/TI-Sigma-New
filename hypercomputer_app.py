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

tab1, tab2, tab3, tab4, tab5 = st.tabs([
    "🔮 Crystal Visualizer", "⚡ SAT Solver", "📊 Phase Analysis",
    "📖 Architecture", "✨ Power of 8"
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
        show_phase_demo = False
        if crystal_mode == "🔬 Load phase state":
            pd_demo = st.slider("Mean |α| amplitude", 0.0, 1.0, 0.70, 0.01,
                                help="Uniform amplitude for all vertices — shows how phase regime changes")
            demo_amps = np.full(N_VERTICES, pd_demo, dtype=complex)
            show_phase_demo = True
        st.markdown("---")
        st.markdown("**Crystal constants:**")
        for rname, rval, rcolor in zip(RING_NAMES, RING_RADII, RING_PALETTE):
            st.markdown(
                f'<span style="color:{rcolor}">●</span> **{rname}** = {rval:.4f}',
                unsafe_allow_html=True
            )

    with info_col:
        if crystal_mode == "✨ Full BEC (all TRUE)":
            fig1 = tsc_crystal_figure(mode="bec", height=700)
        elif crystal_mode == "🔬 Load phase state":
            fig1 = tsc_crystal_figure(amplitudes=demo_amps, mode="phase", height=700)
        else:
            fig1 = tsc_crystal_figure(mode="ring", height=700)
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

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
from bok_harmonics import (
    DIM_NOTES, DIM_ORDER, CHORD_REGISTRY, CHORD_LOOKUP,
    CATEGORY_COLORS, CATEGORY_LABELS,
    detect_chord, note_activation_level,
    generate_note_audio, generate_chord_audio,
    chord_reference_table,
    THRESHOLD_NOTE_ON, THRESHOLD_CHORD_IN, THRESHOLD_STRONG, THRESHOLD_BEC,
    ET as H_ET, C_TI as H_C_TI, T_TI as H_T_TI,
)
from gile_lcc_ratio_engine import (
    DOMAIN_REGISTRY, DomainGLSpec, GLTransform, ICellGLRatio,
    apply_transform, apply_transform_array,
    fit_gl_ratio_linear, best_fit_transform, linearity_test,
    transform_curve, describe_ratio,
)
from gile_lcc_test_suite import (
    run_all_tests, run_T1, run_T2, run_T3, run_T4, run_T5, run_T6,
    summarize, PASS_COLOR, FAIL_COLOR, WARN_COLOR,
)
from mood_amplifier_simulation_ui import render_mood_amplifier_simulation
from halting_experiment_ui import render_halting_experiment
from oea_protocol_tracker import render_oea_tracker

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

tab_career, tab1, tab2, tab3, tab4, tab5, tab6, tab7, tab8, tab9, tab10, tab11, tab12, tab13 = st.tabs([
    "💼 Career",
    "🔮 Crystal Visualizer", "⚡ SAT Solver", "📊 Phase Analysis",
    "📖 Architecture", "✨ Power of 8", "🦠 BOK Virus", "🎵 BOK Harmonics",
    "🧪 GL Ratio Tests", "🧠 GILE-HEM-BOK Engine", "🔬 Halting Experiment",
    "💊 OEA Protocol", "🎯 Spectre (VMP)", "🍄 Mycelial Resonance",
])

with tab_career:
    st.subheader("💼 Brandon Charles Emerick — Career")
    st.caption("AI Trainer & SME · Formal Verification · Mathematics & Philosophy of Mind")

    st.markdown(
        "**📍 Watertown, CT · 📞 860-483-1425 · ✉️ brandonemerick91@gmail.com**  \n"
        "**🔗 [LinkedIn](https://www.linkedin.com/in/brandon-emerick) · "
        "🌐 [Zenodo (100+ papers)](https://zenodo.org/search?q=Brandon+Emerick)**"
    )

    _career_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "career")

    # Resume downloads — separate PDF (styled) and Markdown (plain) one-tap buttons
    _resume_pdf = os.path.join(_career_dir, "resume.pdf")
    _resume_md = os.path.join(_career_dir, "AI_TRAINER_RESUME_BRANDON_EMERICK_v3_2026-05-20.md")
    import datetime as _dt_mod
    _md_mtime = _dt_mod.datetime.fromtimestamp(os.path.getmtime(_resume_md)).strftime("%Y-%m-%d %H:%M") if os.path.exists(_resume_md) else "n/a"
    _pdf_mtime = _dt_mod.datetime.fromtimestamp(os.path.getmtime(_resume_pdf)).strftime("%Y-%m-%d %H:%M") if os.path.exists(_resume_pdf) else "n/a"
    st.caption(f"📌 Current version: **v3 (2026-05-20)** · Markdown updated {_md_mtime} · PDF regenerated {_pdf_mtime}. If you don't see the latest, hard-refresh your browser (Ctrl+Shift+R / Cmd+Shift+R, or pull-to-refresh on mobile).")
    _dl_col1, _dl_col2 = st.columns(2)
    with _dl_col1:
        if os.path.exists(_resume_pdf):
            with open(_resume_pdf, "rb") as _f:
                st.download_button(
                    "⬇️ Styled Resume (PDF)",
                    data=_f.read(),
                    file_name="Brandon_Emerick_Resume.pdf",
                    mime="application/pdf",
                    use_container_width=True,
                    help="Aesthetic single-page PDF — best for emailing to recruiters or printing.",
                )
    with _dl_col2:
        if os.path.exists(_resume_md):
            with open(_resume_md, "rb") as _f:
                st.download_button(
                    "⬇️ Plain Resume (Markdown)",
                    data=_f.read(),
                    file_name="Brandon_Emerick_Resume.md",
                    mime="text/markdown",
                    use_container_width=True,
                    help="Plain-text Markdown — best for ATS systems, copy-pasting into job applications, or editing.",
                )

    # xAI-targeted v4 variant — for the Grok Truth-Seeking AI Tutor role
    _resume_pdf_xai = os.path.join(_career_dir, "resume_xai.pdf")
    _resume_md_xai = os.path.join(_career_dir, "AI_TUTOR_RESUME_BRANDON_EMERICK_v4_xAI_2026-05-20.md")
    if os.path.exists(_resume_pdf_xai) or os.path.exists(_resume_md_xai):
        st.markdown("##### 🎯 xAI-Targeted Variant — Grok Truth-Seeking AI Tutor")
        st.caption("Rewritten to surface xAI's Jobscan keywords: motivated reasoning, primary sources, base rates, steel-manning, philosophy of science, cognitive psychology, forecasting (Kalshi), MM/YYYY dates, soft skills.")
        _xai_md_mtime = _dt_mod.datetime.fromtimestamp(os.path.getmtime(_resume_md_xai)).strftime("%Y-%m-%d %H:%M") if os.path.exists(_resume_md_xai) else "n/a"
        _xai_pdf_mtime = _dt_mod.datetime.fromtimestamp(os.path.getmtime(_resume_pdf_xai)).strftime("%Y-%m-%d %H:%M") if os.path.exists(_resume_pdf_xai) else "n/a"
        st.caption(f"📌 v4 (xAI) · Markdown updated {_xai_md_mtime} · PDF regenerated {_xai_pdf_mtime}")
        _xc1, _xc2 = st.columns(2)
        with _xc1:
            if os.path.exists(_resume_pdf_xai):
                with open(_resume_pdf_xai, "rb") as _f:
                    st.download_button(
                        "⬇️ xAI Resume (PDF)",
                        data=_f.read(),
                        file_name="Brandon_Emerick_Resume_xAI.pdf",
                        mime="application/pdf",
                        use_container_width=True,
                        help="xAI-targeted styled PDF — upload to Jobscan to compare against the v3 score of 43.",
                    )
        with _xc2:
            if os.path.exists(_resume_md_xai):
                with open(_resume_md_xai, "rb") as _f:
                    st.download_button(
                        "⬇️ xAI Resume (Markdown)",
                        data=_f.read(),
                        file_name="Brandon_Emerick_Resume_xAI.md",
                        mime="text/markdown",
                        use_container_width=True,
                        help="xAI-targeted plain Markdown — best for pasting into xAI's application form.",
                    )

    st.markdown("---")

    career_sub_resume, career_sub_linkedin, career_sub_recruiter = st.tabs([
        "📄 Resume", "🔗 LinkedIn Profile", "🎯 Recruiter Summary",
    ])

    def _safe_read(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return f.read()
        except Exception as e:
            return f"_(could not load `{os.path.basename(path)}`: {e})_"

    with career_sub_resume:
        st.markdown(_safe_read(os.path.join(_career_dir, "AI_TRAINER_RESUME_BRANDON_EMERICK_v3_2026-05-20.md")))

    with career_sub_linkedin:
        st.markdown(_safe_read(os.path.join(_career_dir, "LINKEDIN_PROFILE_PASTE_READY_2026-05-17.md")))

    with career_sub_recruiter:
        st.markdown(_safe_read(os.path.join(_career_dir, "RECRUITER_SUMMARY.md")))

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

| Property | Crystal BOK | TI Sigma Graph | ER-Random Graph |
|---|---|---|---|
| Curve shape | Bimodal (BEC plateau → Mott stall) | Possibly bimodal (hub structure) | Logistic S-curve |
| Peak timing | Earliest (BEC jump shortcut) | Middle (GILE hubs) | Latest |
| Attack rate | Lowest (Mott insulation) | Middle | Highest |
| Long-range | Yes — BEC non-local coupling | No | No |
| GILE-L effect | Explicit (inner ring Love coupling) | Structural only | Averaged out |

This is an **empirical prediction**: if real information/meme/pathogen spread
on GILE-structured networks shows bimodal epidemic curves with early peaks
and Mott-insulated plateaus, it confirms the BOK crystal model over the classical graph model.
""")

    # ══════════════════════════════════════════════════════════════════════════
    # EMPIRICAL TEST SUITE — URB #673
    # Three-way Monte Carlo: Crystal vs TI-Graph vs ER-Random
    # ══════════════════════════════════════════════════════════════════════════
    st.markdown("---")
    st.subheader("🧬 Empirical Test Suite — URB #673: Crystal vs TI-Graph vs ER-Random")
    st.caption(
        "Monte Carlo N=100 simulations per network type. "
        "TI Sigma Graph: GILE-weighted attachment (inner BEC nodes = hubs), "
        "uniform β, no BEC long-range coupling. "
        "Tests whether Crystal signatures arise from structure, quantum dynamics, or both."
    )

    et_col1, et_col2, et_col3 = st.columns(3)
    with et_col1:
        mc_n_runs = st.selectbox("Monte Carlo runs (N)", [50, 100, 200], index=1,
                                 help="More runs = tighter confidence intervals.")
    with et_col2:
        mc_max_steps = st.number_input("Max steps per run", value=60, min_value=30, max_value=120)
    with et_col3:
        mc_seed_vertex = st.selectbox(
            "Seed vertex (H1–H4)",
            options=list(range(N_VERTICES)),
            format_func=lambda i: f"#{i} Ring {VERTICES[i].ring}: {BOK_RING_NAMES[VERTICES[i].ring]}",
            index=0,
        )

    mc_btn = st.button("🔬 Run Empirical Tests (Monte Carlo)", type="primary",
                       use_container_width=True)

    mc_key = f"mc_{mc_n_runs}_{mc_max_steps}_{mc_seed_vertex}_{beta_scale}_{bec_p}_{gamma_val}"

    if mc_btn or mc_key in st.session_state:
        if mc_btn or mc_key not in st.session_state:
            with st.spinner(f"Running {mc_n_runs}×3 simulations + BEC ablation + seed test..."):
                from ti_sigma_graph import run_monte_carlo
                mc_result = run_monte_carlo(
                    adjacency=np.array(ADJACENCY, dtype=bool),
                    rings=[v.ring for v in VERTICES],
                    positions=[v.position for v in VERTICES],
                    labels=[v.label for v in VERTICES],
                    n_runs=int(mc_n_runs),
                    max_steps=int(mc_max_steps),
                    beta_scale=beta_scale,
                    gamma=gamma_val,
                    bec_p=bec_p,
                    seed_vertex=mc_seed_vertex,
                )
                st.session_state[mc_key] = mc_result

        mc = st.session_state[mc_key]
        summ = mc['summary']

        # ── Summary metrics ────────────────────────────────────────────────
        st.markdown("### Monte Carlo Summary (N={})".format(mc['n_runs']))
        mc_names = {"crystal": "🔮 Crystal", "ti_graph": "🕸 TI-Graph", "er_graph": "🎲 ER-Random"}

        import pandas as pd
        rows = []
        for k, label in mc_names.items():
            s = summ[k]
            rows.append({
                "Network":         label,
                "Bimodal rate":    f"{s['bimodal_rate']:.0%}",
                "Peak step (mean ± σ)": f"{s['peak_step_mean']:.1f} ± {s['peak_step_std']:.1f}",
                "Attack rate (mean ± σ)": f"{s['attack_rate_mean']:.3f} ± {s['attack_rate_std']:.3f}",
                "Duration (mean)": f"{s['duration_mean']:.1f}",
            })
        st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)

        # ── Distribution charts: Attack rate & Peak step ───────────────────
        st.markdown("### Distribution Comparison")
        dist_c1, dist_c2 = st.columns(2)

        raw = mc['raw_stats']
        with dist_c1:
            fig_ar = go.Figure()
            for k, col, label in [
                ('crystal',  '#00e5ff', '🔮 Crystal'),
                ('ti_graph', '#ffcc00', '🕸 TI-Graph'),
                ('er_graph', '#ff6666', '🎲 ER-Random'),
            ]:
                fig_ar.add_trace(go.Histogram(
                    x=raw[k]['attack_rate'], nbinsx=20,
                    name=label, marker_color=col, opacity=0.7,
                ))
            fig_ar.update_layout(
                barmode='overlay', height=280,
                title=dict(text="Attack Rate Distribution", font=dict(color='white', size=13)),
                paper_bgcolor="rgba(3,3,14,1)", plot_bgcolor="rgba(10,10,25,1)",
                font=dict(color='white'), xaxis_title="Attack Rate",
                yaxis_title="Count", margin=dict(l=30, r=10, t=40, b=30),
                legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
            )
            st.plotly_chart(fig_ar, use_container_width=True)

        with dist_c2:
            fig_ps = go.Figure()
            for k, col, label in [
                ('crystal',  '#00e5ff', '🔮 Crystal'),
                ('ti_graph', '#ffcc00', '🕸 TI-Graph'),
                ('er_graph', '#ff6666', '🎲 ER-Random'),
            ]:
                fig_ps.add_trace(go.Histogram(
                    x=raw[k]['peak_step'], nbinsx=20,
                    name=label, marker_color=col, opacity=0.7,
                ))
            fig_ps.update_layout(
                barmode='overlay', height=280,
                title=dict(text="Peak Step Distribution", font=dict(color='white', size=13)),
                paper_bgcolor="rgba(3,3,14,1)", plot_bgcolor="rgba(10,10,25,1)",
                font=dict(color='white'), xaxis_title="Step at Peak I",
                yaxis_title="Count", margin=dict(l=30, r=10, t=40, b=30),
                legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
            )
            st.plotly_chart(fig_ps, use_container_width=True)

        # ── BEC ablation bar chart ─────────────────────────────────────────
        st.markdown("### BEC Ablation (H4) & Seed Ring (H5)")
        abl_c1, abl_c2 = st.columns(2)
        with abl_c1:
            fig_bec = go.Figure(go.Bar(
                x=['BEC ON (p={:.2f})'.format(bec_p), 'BEC OFF (p=0.00)'],
                y=[mc['bec_on_mean'], mc['bec_off_mean']],
                marker_color=['#00e5ff', '#4455aa'],
                text=[f"{mc['bec_on_mean']:.1f}", f"{mc['bec_off_mean']:.1f}"],
                textposition='outside',
            ))
            fig_bec.update_layout(
                height=260,
                title=dict(text="H4: BEC Coupling → Peak Step", font=dict(color='white', size=12)),
                paper_bgcolor="rgba(3,3,14,1)", plot_bgcolor="rgba(10,10,25,1)",
                font=dict(color='white'), yaxis_title="Mean Peak Step",
                margin=dict(l=30, r=10, t=40, b=30),
            )
            st.plotly_chart(fig_bec, use_container_width=True)

        with abl_c2:
            r0_ar = mc.get('r0_ar', 0.0)
            r7_ar = mc.get('r7_ar', 0.0)
            r0_pi = mc.get('r0_pi', 0.0)
            r7_pi = mc.get('r7_pi', 0.0)
            fig_seed = go.Figure(go.Bar(
                x=['Ring-0 Seed (Origin / BEC)', 'Ring-7 Seed (Fragmented / Mott)'],
                y=[r0_ar, r7_ar],
                marker_color=['#44ff88', '#ff4444'],
                text=[f"AR={r0_ar:.3f}\npeak-I={r0_pi:.1f}",
                      f"AR={r7_ar:.3f}\npeak-I={r7_pi:.1f}"],
                textposition='outside',
            ))
            fig_seed.update_layout(
                height=260,
                title=dict(text="H5: Patient-Zero Ring → Attack Rate", font=dict(color='white', size=12)),
                paper_bgcolor="rgba(3,3,14,1)", plot_bgcolor="rgba(10,10,25,1)",
                font=dict(color='white'), yaxis_title="Mean Attack Rate",
                yaxis=dict(range=[0, 1.1]),
                margin=dict(l=30, r=10, t=40, b=30),
            )
            st.plotly_chart(fig_seed, use_container_width=True)

        # ── Hypothesis verdict table ───────────────────────────────────────
        st.markdown("### Hypothesis Verdicts (URB #673)")
        hyp_rows = []
        for h in mc['hypotheses']:
            hyp_rows.append({
                "Hypothesis":  h.name,
                "Prediction":  h.prediction,
                "Observed":    h.observed,
                "Result":      "✅ PASS" if h.passed else "❌ FAIL",
                "Interpretation": h.detail,
            })
        df_hyp = pd.DataFrame(hyp_rows)
        st.dataframe(df_hyp, use_container_width=True, hide_index=True)

        # Pass/fail summary
        n_pass = sum(1 for h in mc['hypotheses'] if h.passed)
        n_total = len(mc['hypotheses'])
        if n_pass == n_total:
            st.success(f"🎯 All {n_total}/{n_total} hypotheses passed — TI Sigma BOK Virus model confirmed at N={mc['n_runs']}")
        elif n_pass >= 3:
            st.warning(f"⚠️ {n_pass}/{n_total} hypotheses passed — partial confirmation. Review failed hypotheses.")
        else:
            st.error(f"❌ Only {n_pass}/{n_total} hypotheses passed — model revision needed.")

        with st.expander("📋 URB #673 — What the Three Networks Test", expanded=False):
            st.markdown("""
**Three-network design:**

| Network | Structure | Dynamics | What it isolates |
|---------|-----------|----------|-----------------|
| 🔮 Crystal | TSC lattice (deterministic) | Phase β + BEC long-range | Full TI Sigma model |
| 🕸 TI-Graph | GILE-weighted attachment (structural) | Uniform β, no BEC | Structure without quantum |
| 🎲 ER-Random | Erdős-Rényi (random) | Uniform β, no BEC | Classical null model |

**Logic of the test:**

- If Crystal signatures (bimodality, early peak, low attack rate) appear in **Crystal only**:
  → Signatures require quantum BEC dynamics. Structure alone is insufficient.
  
- If signatures appear in **Crystal + TI-Graph**:
  → Structure (GILE-hub network) alone explains the signatures. BEC not required.
  
- If signatures appear in **all three**:
  → Signatures are properties of any SIR model, not specific to TI Sigma. (Null result.)

**TI Sigma prediction:** Crystal-only bimodality (quantum required); Crystal + TI-Graph early peak (hub structure contributes); Crystal < TI-Graph < ER attack rate (gradient of insulation).
""")


# ═══════════════════════════════════════════════════════════════════════════════
# TAB 7 — BOK Harmonics: 8 Dimensions as Musical Notes & Chords
# ═══════════════════════════════════════════════════════════════════════════════

with tab7:
    import pandas as pd

    st.subheader("🎵 BOK Harmonics — URB #648")
    st.caption(
        "Each of the 8 GILE-HEM dimensions is a musical note. "
        "When multiple dimensions cross the C_TI threshold (≈0.437) simultaneously, "
        "they form named chords — abstract GILE love, composite GILE-LCC love, HEM existence chords, and more."
    )

    # ── Threshold legend ──────────────────────────────────────────────────────
    thr_cols = st.columns(4)
    with thr_cols[0]:
        st.info(f"**Faint** › ET = {H_ET:.4f}\nNote activates (audible, dim)")
    with thr_cols[1]:
        st.success(f"**Active** › C = {H_C_TI:.4f}\nEnters chord pool")
    with thr_cols[2]:
        st.warning(f"**Strong** › 0.65\nFull note volume")
    with thr_cols[3]:
        st.success(f"**BEC** › T = {H_T_TI:.4f}\nMaximum coherence glow")

    st.markdown("---")

    # ── Input mode toggle ─────────────────────────────────────────────────────
    harm_mode = st.radio(
        "Input mode",
        ["🎼 Direct GILE values", "⚖️ LCC → GILE via Domain Ratio (URB #649)"],
        horizontal=True, key="harm_mode",
        help="Direct: set GILE dimensions directly. LCC mode: set raw LCC weights, "
             "convert to GILE using the domain-specific GL ratio."
    )
    st.markdown("---")

    # ── LCC → GILE Conversion panel ───────────────────────────────────────────
    lcc_vals_raw: dict = {}
    domain_spec: DomainGLSpec = None

    if harm_mode.startswith("⚖️"):
        st.markdown("### ⚖️ GILE-LCC Ratio Engine — URB #649")
        st.caption(
            "The GL ratio (LCC_value / GILE_value) varies by domain, i-cell, and time. "
            "It is determined empirically — not assumed. Set LCC weights below; "
            "GILE values are derived via the domain transform."
        )

        ratio_c1, ratio_c2, ratio_c3 = st.columns(3)
        with ratio_c1:
            domain_name = st.selectbox("Domain", list(DOMAIN_REGISTRY.keys()),
                                       key="harm_domain")
            domain_spec = DOMAIN_REGISTRY[domain_name]

        with ratio_c2:
            # Allow overriding ratio
            gl_ratio_override = st.slider(
                "GL Ratio override (LCC ÷ GILE)",
                0.2, 8.0, float(round(domain_spec.gl_ratio, 2)), 0.05,
                key="harm_gl_ratio",
                help=f"Domain default: {domain_spec.gl_ratio:.2f}. "
                     f"{describe_ratio(domain_spec.gl_ratio)}"
            )
            tf_name = st.selectbox(
                "Transform",
                [t.value for t in GLTransform],
                index=[t.value for t in GLTransform].index(domain_spec.transform.value),
                key="harm_transform",
            )
            tf_enum = next(t for t in GLTransform if t.value == tf_name)

        with ratio_c3:
            alpha_val = st.slider("Power α (POWER only)", 0.2, 4.0,
                                  float(round(domain_spec.alpha, 2)), 0.05,
                                  key="harm_alpha")
            k_val     = st.slider("Steepness k (non-linear)", 1.0, 20.0,
                                  float(round(domain_spec.k, 1)), 0.5,
                                  key="harm_k")
            mu_val    = st.slider("Midpoint μ (SIGMOID only)", 0.1, 0.9,
                                  float(round(domain_spec.mu, 2)), 0.01,
                                  key="harm_mu")

        # Ratio description
        st.info(f"**{domain_name}** · GL ratio = {gl_ratio_override:.2f} · "
                f"Transform: {tf_name} · {describe_ratio(gl_ratio_override)}")
        if domain_spec.notes:
            st.caption(f"Domain note: {domain_spec.notes}")

        # Transform curve
        lcc_x = np.linspace(0.0, 1.0, 300)
        gile_y = apply_transform_array(lcc_x, gl_ratio_override, tf_enum,
                                       alpha_val, k_val, mu_val)
        fig_curve_tf = go.Figure()
        fig_curve_tf.add_trace(go.Scatter(x=lcc_x, y=gile_y, mode='lines',
                                          line=dict(color='#aa44ff', width=2.5),
                                          name='GILE = f(LCC)'))
        # Reference diagonal (linear 1:1)
        fig_curve_tf.add_trace(go.Scatter(x=[0,1], y=[0,1], mode='lines',
                                          line=dict(color='rgba(150,150,150,0.4)',
                                                    width=1, dash='dot'),
                                          name='1:1 reference'))
        # TI thresholds
        for thr, lbl, col in [(H_ET, 'ET', '#7777ff'),
                               (H_C_TI, 'C', '#00ff99'),
                               (H_T_TI, 'T', '#ffffff')]:
            fig_curve_tf.add_hline(y=thr, line_dash='dot', line_color=col,
                                   annotation_text=f'GILE {lbl}',
                                   annotation_font_color=col, annotation_font_size=9)
            fig_curve_tf.add_vline(x=thr, line_dash='dot', line_color=col,
                                   annotation_text=f'LCC {lbl}',
                                   annotation_font_color=col, annotation_font_size=9)
        fig_curve_tf.update_layout(
            height=260,
            paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
            font=dict(color='white'),
            xaxis=dict(title='LCC value', range=[0,1],
                       gridcolor='rgba(100,100,150,0.2)'),
            yaxis=dict(title='GILE value', range=[0,1],
                       gridcolor='rgba(100,100,150,0.2)'),
            legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
            margin=dict(l=50, r=20, t=20, b=40),
            title=dict(text=f"LCC → GILE Transform: {tf_name} (ratio={gl_ratio_override:.2f})",
                       font=dict(color='white', size=12)),
        )
        st.plotly_chart(fig_curve_tf, use_container_width=True)

        # LCC sliders
        st.markdown("### Set LCC Dimension Values")
        lcc_g_col, lcc_h_col = st.columns(2)
        with lcc_g_col:
            st.markdown("**LCC weights — GILE dimensions**")
            for key in ['G', 'I', 'L', 'E']:
                d = DIM_NOTES[key]
                lcc_vals_raw[key] = st.slider(
                    f"LCC→{key}  [{d.label}]",
                    0.0, 1.0, 0.5, 0.01, key=f"lcc_{key}",
                    help=f"Raw LCC weight for {d.label}. Will be converted to GILE via the ratio."
                )
        with lcc_h_col:
            st.markdown("**LCC weights — HEM dimensions**")
            for key in ['D1', 'D2', 'D3', 'D4']:
                d = DIM_NOTES[key]
                lcc_vals_raw[key] = st.slider(
                    f"LCC→{key}  [{d.label}]",
                    0.0, 1.0, 0.3, 0.01, key=f"lcc_{key}",
                    help=f"Raw LCC weight for {d.label}. Will be converted to GILE via the ratio."
                )

        # Convert LCC → GILE
        dim_vals = {
            k: apply_transform(v, gl_ratio_override, tf_enum, alpha_val, k_val, mu_val)
            for k, v in lcc_vals_raw.items()
        }

        # Show the conversion table
        with st.expander("📊 LCC → GILE Conversion Table", expanded=False):
            import pandas as pd
            conv_rows = []
            for k in DIM_ORDER:
                d = DIM_NOTES[k]
                lcc_v = lcc_vals_raw[k]
                gile_v = dim_vals[k]
                inferred_ratio = lcc_v / max(gile_v, 1e-9)
                conv_rows.append({
                    'Dim': k, 'Note': d.note_name,
                    'LCC raw': round(lcc_v, 3),
                    'GILE computed': round(gile_v, 3),
                    'Effective ratio': round(inferred_ratio, 3),
                    'Activation': note_activation_level(gile_v),
                })
            st.dataframe(pd.DataFrame(conv_rows), use_container_width=True, hide_index=True)

        # ── Calibration tool ──────────────────────────────────────────────────
        st.markdown("---")
        with st.expander("🔬 Empirical Calibration Tool (URB #649)", expanded=False):
            st.markdown(
                "Enter observed (LCC, GILE) pairs from exemplar individuals in this domain. "
                "The engine will fit the best GL ratio and test whether the relationship is linear."
            )
            cal_c1, cal_c2 = st.columns(2)
            with cal_c1:
                cal_lcc  = st.number_input("Observed LCC value", 0.0, 1.0, 0.42, 0.01,
                                           key="cal_lcc")
                cal_gile = st.number_input("Observed GILE value", 0.0, 1.0, 0.21, 0.01,
                                           key="cal_gile")
                cal_btn  = st.button("➕ Add data point", key="cal_add")

            if cal_btn:
                if "cal_data" not in st.session_state:
                    st.session_state["cal_data"] = []
                st.session_state["cal_data"].append((float(cal_lcc), float(cal_gile)))

            cal_data = st.session_state.get("cal_data", [])

            with cal_c2:
                if cal_data:
                    import pandas as pd
                    cal_df = pd.DataFrame(cal_data, columns=["LCC", "GILE"])
                    cal_df["Inferred ratio"] = cal_df["LCC"] / cal_df["GILE"].clip(lower=1e-9)
                    st.dataframe(cal_df.round(4), use_container_width=True, hide_index=True)
                    if st.button("🗑 Clear calibration data", key="cal_clear"):
                        st.session_state["cal_data"] = []
                        st.rerun()
                else:
                    st.caption("No calibration data yet. Add observed (LCC, GILE) pairs above.")

            if len(cal_data) >= 2:
                lcc_cal  = [p[0] for p in cal_data]
                gile_cal = [p[1] for p in cal_data]
                fitted_ratio = fit_gl_ratio_linear(lcc_cal, gile_cal)
                lt = linearity_test(lcc_cal, gile_cal, fitted_ratio)

                st.markdown(f"**Fitted GL ratio: {fitted_ratio:.3f}**  "
                            f"({describe_ratio(fitted_ratio)})")
                st.markdown(f"**Linearity test:** {lt['conclusion']}")

                cal_cols = st.columns(4)
                cal_cols[0].metric("R²", f"{lt['r_squared']:.4f}")
                cal_cols[1].metric("RMSE (linear)", f"{lt['rmse_linear']:.4f}")
                cal_cols[2].metric("RMSE (power)", f"{lt['rmse_power']:.4f}")
                cal_cols[3].metric("Power α", f"{lt['power_alpha']:.3f}")

                # Plot calibration scatter vs fit
                fig_cal = go.Figure()
                lcc_plot = np.linspace(0, 1, 200)
                gile_plot_fit = apply_transform_array(lcc_plot, fitted_ratio,
                                                      GLTransform.LINEAR)
                fig_cal.add_trace(go.Scatter(x=lcc_plot, y=gile_plot_fit,
                                             mode='lines',
                                             line=dict(color='#aa44ff', width=2),
                                             name='Linear fit'))
                if lt['power_alpha'] != 1.0:
                    gile_plot_pw = apply_transform_array(
                        lcc_plot, fitted_ratio, GLTransform.POWER,
                        alpha=lt['power_alpha'])
                    fig_cal.add_trace(go.Scatter(x=lcc_plot, y=gile_plot_pw,
                                                 mode='lines',
                                                 line=dict(color='#ff9d00', width=2,
                                                           dash='dash'),
                                                 name=f'Power fit (α={lt["power_alpha"]:.2f})'))
                fig_cal.add_trace(go.Scatter(
                    x=lcc_cal, y=gile_cal,
                    mode='markers',
                    marker=dict(size=10, color='#00ff99',
                                line=dict(width=1, color='white')),
                    name='Observed pairs',
                ))
                fig_cal.update_layout(
                    height=220,
                    paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                    font=dict(color='white'),
                    xaxis=dict(title='LCC', range=[0,1],
                               gridcolor='rgba(100,100,150,0.2)'),
                    yaxis=dict(title='GILE', range=[0,1],
                               gridcolor='rgba(100,100,150,0.2)'),
                    legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
                    margin=dict(l=50, r=20, t=20, b=40),
                    title=dict(text="Calibration: Observed vs Fitted",
                               font=dict(color='white', size=12)),
                )
                st.plotly_chart(fig_cal, use_container_width=True)

                if len(cal_data) >= 3:
                    tf_best, ratio_best, alpha_best, k_best, rmse_best = best_fit_transform(
                        lcc_cal, gile_cal
                    )
                    st.success(
                        f"Best-fit transform: **{tf_best.value}** "
                        f"(ratio={ratio_best:.2f}, α={alpha_best:.2f}, "
                        f"k={k_best:.1f}, RMSE={rmse_best:.4f})"
                    )

        st.markdown("---")

    else:
        # ── Direct GILE mode sliders ───────────────────────────────────────────
        st.markdown("### Set GILE Dimension Values")
        domain_spec = None

    # ── Standard GILE sliders (always shown in Direct mode; shown as computed in LCC mode) ──
    if harm_mode.startswith("🎼"):
        gile_col, hem_col = st.columns(2)
        dim_vals: dict = {}
        with gile_col:
            st.markdown("**GILE — Inner BOK Loops**")
            for key in ['G', 'I', 'L', 'E']:
                d = DIM_NOTES[key]
                dim_vals[key] = st.slider(
                    f"{d.label}  [{d.note_name} = {d.freq:.1f} Hz]",
                    0.0, 1.0, 0.5, 0.01, key=f"harm_{key}",
                    help=d.description,
                )
        with hem_col:
            st.markdown("**HEM — Outer BOK Loops**")
            for key in ['D1', 'D2', 'D3', 'D4']:
                d = DIM_NOTES[key]
                dim_vals[key] = st.slider(
                    f"{d.label}  [{d.note_name} = {d.freq:.1f} Hz]",
                    0.0, 1.0, 0.3, 0.01, key=f"harm_{key}",
                    help=d.description,
                )

    # ── Detect chord ──────────────────────────────────────────────────────────
    best_chord, chord_dims, active_dims = detect_chord(dim_vals)

    # ── Piano keyboard visualization ──────────────────────────────────────────
    st.markdown("---")
    st.markdown("### 🎹 BOK Piano — Activation State")

    KEY_ORDER = ['G', 'D1', 'I', 'D2', 'L', 'E', 'D3', 'D4']
    NOTE_NAMES_ORDERED = ['C4', 'D4', 'E4', 'F4', 'G4', 'B4', 'A4', 'C5']

    def key_color(key: str, val: float) -> str:
        level = note_activation_level(val)
        base = DIM_NOTES[key].color
        if level == 'Silent':
            return '#1a1a2e'
        elif level == 'Faint':
            return '#2a2a4e'
        elif level == 'Active':
            return base + 'aa'
        elif level == 'Strong':
            return base
        else:  # BEC
            return '#ffffff'

    fig_keys = go.Figure()
    key_w = 1.0
    gap   = 0.08
    total = len(KEY_ORDER)

    for idx, key in enumerate(KEY_ORDER):
        val   = dim_vals[key]
        d     = DIM_NOTES[key]
        level = note_activation_level(val)
        col   = key_color(key, val)
        x0    = idx * (key_w + gap)
        x1    = x0 + key_w

        # Key rectangle
        fig_keys.add_shape(type='rect', x0=x0, y0=0, x1=x1, y1=2.8,
                           fillcolor=col, line=dict(color='rgba(200,200,255,0.4)', width=1))

        # Glow for BEC
        if level == 'BEC':
            fig_keys.add_shape(type='rect', x0=x0-0.04, y0=-0.04, x1=x1+0.04, y1=2.84,
                               fillcolor='rgba(255,255,255,0.08)',
                               line=dict(color='rgba(255,255,255,0.6)', width=2))

        # Note name
        fig_keys.add_annotation(x=(x0 + x1) / 2, y=2.5, text=d.note_name,
                                font=dict(size=12, color='white'), showarrow=False)
        # Dim abbreviation
        fig_keys.add_annotation(x=(x0 + x1) / 2, y=1.9, text=key,
                                font=dict(size=14, color='white', family='monospace'),
                                showarrow=False)
        # Level
        level_color = ('#aaaaaa' if level == 'Silent' else
                       '#7777ff' if level == 'Faint'  else
                       '#00ff99' if level == 'Active' else
                       '#ffff00' if level == 'Strong' else '#ffffff')
        fig_keys.add_annotation(x=(x0 + x1) / 2, y=1.2, text=level,
                                font=dict(size=10, color=level_color), showarrow=False)
        # Value
        fig_keys.add_annotation(x=(x0 + x1) / 2, y=0.5, text=f"{val:.2f}",
                                font=dict(size=11, color='white'), showarrow=False)

    piano_w = total * (key_w + gap)
    fig_keys.update_layout(
        height=160, paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(3,3,14,1)',
        xaxis=dict(range=[-0.1, piano_w], showgrid=False, zeroline=False, showticklabels=False),
        yaxis=dict(range=[-0.1, 3.1],    showgrid=False, zeroline=False, showticklabels=False),
        margin=dict(l=0, r=0, t=10, b=0),
    )
    st.plotly_chart(fig_keys, use_container_width=True)

    # ── Chord display ──────────────────────────────────────────────────────────
    st.markdown("---")
    chord_left, chord_right = st.columns([1, 2])

    with chord_left:
        if best_chord:
            cat_col = CATEGORY_COLORS.get(best_chord.category, '#888888')
            cat_lbl = CATEGORY_LABELS.get(best_chord.category, best_chord.category)
            st.markdown(
                f"<div style='background:{cat_col}22; border:2px solid {cat_col}; "
                f"border-radius:12px; padding:16px; text-align:center;'>"
                f"<div style='color:{cat_col}; font-size:11px; font-weight:bold; "
                f"letter-spacing:2px;'>{cat_lbl}</div>"
                f"<div style='color:white; font-size:22px; font-weight:bold; "
                f"margin:8px 0;'>{best_chord.name}</div>"
                f"<div style='color:#aaaaaa; font-size:13px;'>"
                f"Dims: {' + '.join(sorted(chord_dims))}</div>"
                f"<div style='color:{cat_col}; font-size:13px; margin-top:6px;'>"
                f"PD ≈ {best_chord.pd_score:.1f}</div>"
                f"</div>",
                unsafe_allow_html=True
            )
        elif len(active_dims) == 1:
            key = active_dims[0]
            d   = DIM_NOTES[key]
            st.markdown(
                f"<div style='background:#333355; border:2px solid {d.color}; "
                f"border-radius:12px; padding:16px; text-align:center;'>"
                f"<div style='color:{d.color}; font-size:11px; font-weight:bold; "
                f"letter-spacing:2px;'>SINGLE NOTE</div>"
                f"<div style='color:white; font-size:22px; font-weight:bold; "
                f"margin:8px 0;'>{d.note_name}</div>"
                f"<div style='color:#cccccc; font-size:13px;'>{d.label}</div>"
                f"</div>",
                unsafe_allow_html=True
            )
        elif not active_dims:
            st.markdown(
                "<div style='background:#111122; border:2px solid #333355; "
                "border-radius:12px; padding:16px; text-align:center; color:#555566;'>"
                "No dimensions active.<br>Raise any slider above ET (0.4142)</div>",
                unsafe_allow_html=True
            )
        else:
            st.markdown(
                f"<div style='background:#222233; border:2px dashed #555566; "
                f"border-radius:12px; padding:16px; text-align:center;'>"
                f"<div style='color:#aaaaaa; font-size:12px;'>UNNAMED COMBINATION</div>"
                f"<div style='color:white; font-size:16px; margin:8px 0;'>"
                f"{' + '.join(sorted(chord_dims))}</div>"
                f"<div style='color:#777788; font-size:12px;'>No named chord for this set</div>"
                f"</div>",
                unsafe_allow_html=True
            )

    with chord_right:
        if best_chord:
            st.markdown(f"**TI Sigma Meaning:**")
            st.markdown(f"> {best_chord.ti_meaning}")
        if active_dims:
            st.markdown("**Active notes:**")
            note_cols = st.columns(min(len(active_dims), 4))
            for ni, key in enumerate(active_dims):
                d     = DIM_NOTES[key]
                level = note_activation_level(dim_vals[key])
                with note_cols[ni % 4]:
                    st.markdown(
                        f"<div style='background:{d.color}22; border:1px solid {d.color}; "
                        f"border-radius:8px; padding:8px; text-align:center; margin:2px;'>"
                        f"<div style='color:{d.color}; font-weight:bold;'>{d.note_name}</div>"
                        f"<div style='color:white; font-size:11px;'>{key}</div>"
                        f"<div style='color:#aaaaaa; font-size:10px;'>{level}</div>"
                        f"<div style='color:white; font-size:10px;'>{dim_vals[key]:.2f}</div>"
                        f"</div>",
                        unsafe_allow_html=True
                    )

    # ── Audio ─────────────────────────────────────────────────────────────────
    st.markdown("---")
    st.markdown("### 🔊 Listen")
    aud_cols = st.columns(len(active_dims) + 1 if active_dims else 1)

    if active_dims:
        for ni, key in enumerate(active_dims):
            d = DIM_NOTES[key]
            with aud_cols[ni]:
                if st.button(f"▶ {d.note_name} ({key})", key=f"play_{key}"):
                    st.session_state[f"audio_note_{key}"] = generate_note_audio(key)
                if f"audio_note_{key}" in st.session_state:
                    st.audio(st.session_state[f"audio_note_{key}"], format="audio/wav")

        with aud_cols[-1]:
            if st.button("▶ Play Chord", type="primary", key="play_chord"):
                st.session_state["audio_chord"] = generate_chord_audio(dim_vals)
            if "audio_chord" in st.session_state:
                st.audio(st.session_state["audio_chord"], format="audio/wav")
    else:
        st.caption("Activate dimensions (slider › 0.4142) to hear notes and chords.")

    # ── Radar chart ───────────────────────────────────────────────────────────
    st.markdown("---")
    st.markdown("### 📡 GILE-HEM Radar")

    radar_dims   = DIM_ORDER
    radar_vals   = [dim_vals[k] for k in radar_dims]
    radar_labels = [DIM_NOTES[k].note_name + ' ' + k for k in radar_dims]

    fig_radar = go.Figure()
    fig_radar.add_trace(go.Scatterpolar(
        r=radar_vals + [radar_vals[0]],
        theta=radar_labels + [radar_labels[0]],
        fill='toself', fillcolor='rgba(170,68,255,0.18)',
        line=dict(color='#aa44ff', width=2),
        name='Current state',
    ))
    # Threshold reference rings
    for thr, col, lbl in [
        (H_ET,  'rgba(100,100,200,0.3)', f'ET {H_ET:.3f}'),
        (H_C_TI,'rgba(0,200,150,0.3)',   f'C  {H_C_TI:.3f}'),
        (0.65,  'rgba(255,200,0,0.3)',   '0.65 strong'),
        (H_T_TI,'rgba(255,255,255,0.2)', f'T  {H_T_TI:.3f}'),
    ]:
        fig_radar.add_trace(go.Scatterpolar(
            r=[thr] * (len(radar_labels) + 1),
            theta=radar_labels + [radar_labels[0]],
            mode='lines', line=dict(color=col, width=1, dash='dot'),
            name=lbl, showlegend=True,
        ))
    fig_radar.update_layout(
        height=380, paper_bgcolor='rgba(3,3,14,1)',
        polar=dict(
            bgcolor='rgba(10,10,25,1)',
            radialaxis=dict(range=[0,1], tickfont=dict(color='white', size=9),
                            gridcolor='rgba(100,100,150,0.3)', linecolor='rgba(100,100,150,0.3)'),
            angularaxis=dict(tickfont=dict(color='white', size=10),
                             gridcolor='rgba(100,100,150,0.2)'),
        ),
        legend=dict(font=dict(color='white', size=10), bgcolor='rgba(0,0,0,0.4)'),
        margin=dict(l=60, r=60, t=30, b=30),
    )
    st.plotly_chart(fig_radar, use_container_width=True)

    # ── Preset chords ──────────────────────────────────────────────────────────
    st.markdown("---")
    st.markdown("### 🎼 Preset Chord Examples")
    st.caption("Click a preset to load that chord into the sliders.")

    PRESETS = {
        "G-L Bond (Abstract GILE Love)":       {'G':0.72,'I':0.30,'L':0.70,'E':0.30,'D1':0.20,'D2':0.10,'D3':0.20,'D4':0.15},
        "GILE Triad (Awakening)":               {'G':0.75,'I':0.70,'L':0.74,'E':0.30,'D1':0.20,'D2':0.10,'D3':0.20,'D4':0.15},
        "Full GILE Chord (Radiant)":            {'G':0.82,'I':0.78,'L':0.80,'E':0.76,'D1':0.30,'D2':0.10,'D3':0.30,'D4':0.20},
        "Composite Love I (GILE-L → Physical)": {'G':0.70,'I':0.30,'L':0.72,'E':0.30,'D1':0.68,'D2':0.10,'D3':0.25,'D4':0.20},
        "Composite GILE-LCC Love":              {'G':0.78,'I':0.74,'L':0.76,'E':0.30,'D1':0.70,'D2':0.10,'D3':0.72,'D4':0.25},
        "Contradiction Triad ⚠ (DT warning)":  {'G':0.25,'I':0.20,'L':0.20,'E':0.15,'D1':0.68,'D2':0.72,'D3':0.66,'D4':0.30},
        "BEC Full Chord (All 8)":               {'G':0.95,'I':0.92,'L':0.94,'E':0.91,'D1':0.90,'D2':0.18,'D3':0.93,'D4':0.88},
    }

    p_cols = st.columns(4)
    for pi, (pname, pvals) in enumerate(PRESETS.items()):
        with p_cols[pi % 4]:
            if st.button(pname, key=f"preset_{pi}", use_container_width=True):
                for k, v in pvals.items():
                    st.session_state[f"harm_{k}"] = v
                st.rerun()

    # ── Full chord reference table ─────────────────────────────────────────────
    st.markdown("---")
    with st.expander("📖 Complete Chord Dictionary — All Named BOK Chords", expanded=False):
        df_chords = pd.DataFrame(chord_reference_table())
        st.dataframe(df_chords, use_container_width=True, hide_index=True,
                     column_config={
                         'PD Score': st.column_config.NumberColumn(format="%.1f"),
                         'TI Meaning': st.column_config.TextColumn(width='large'),
                     })

    # ── BOK Dimension Note Reference ──────────────────────────────────────────
    st.markdown("---")
    with st.expander("🎵 Dimension → Note Mapping Reference", expanded=False):
        dim_rows = []
        for key in DIM_ORDER:
            d = DIM_NOTES[key]
            dim_rows.append({
                'Dim': key,
                'Layer': d.layer,
                'Label': d.label,
                'Note': d.note_name,
                'Hz': d.freq,
                'Harmonic Role': d.description,
            })
        st.dataframe(pd.DataFrame(dim_rows), use_container_width=True, hide_index=True)
        st.markdown(f"""
**Note selection rationale:**
- **C4 (G)**: Root of C major — Goodness is the foundational stability from which all others arise.
- **E4 (I)**: Major third above root — Intuition recognizes pattern; the 5/4 ratio has φ echoes.
- **G4 (L)**: Perfect fifth — Love is the purest harmonic relationship (3/2 = most consonant interval).
- **B4 (E)**: Major seventh — Aesthetics is the elevated, almost-resolving tension (the "beautiful dissonance").
- **D4 (D1)**: Major second — Physical existence, grounded just above the root.
- **F4 (D2)**: Natural fourth above C — Contradiction. The tritone relationship to B4 (E) = Tralse tension.
- **A4 (D3)**: Major sixth, A440 = universal reference — Spectral purity as the clear, agreed-upon standard.
- **C5 (D4)**: Octave above root — Velocity/rate of change ascending to the next level.

**G + I + L = C4 + E4 + G4 = C major triad** — The most fundamental chord in Western music.
This is the GILE Triad (Awakening), and it is no coincidence.
""")


# ═══════════════════════════════════════════════════════════════════════════════
# TAB 8 — 🧪 GILE-LCC GL Ratio Empirical Test Suite  (URB #649)
# ═══════════════════════════════════════════════════════════════════════════════
with tab8:
    st.subheader("🧪 GILE-LCC GL Ratio Engine — Empirical Test Suite")
    st.markdown(
        "Six tests that probe the recovery ability of the GL Ratio Engine and validate "
        "the theoretical claims of URB #649. Tests use synthetic ground-truth data "
        "(known transform + Gaussian noise) to measure how accurately the engine "
        "identifies the correct transform, ratio, and domain structure. "
        "Real-world validation replaces synthetic data with observed (LCC, GILE) pairs "
        "from scored exemplar individuals."
    )
    st.markdown("---")

    # ── Test parameters panel ──────────────────────────────────────────────────
    with st.expander("⚙️ Test Parameters", expanded=False):
        tp_c1, tp_c2, tp_c3 = st.columns(3)
        with tp_c1:
            tp_n_t1      = st.slider("T1 n_points",  10, 60, 25, 5, key="tp_n_t1")
            tp_noise_t1  = st.slider("T1/T2/T3/T5 noise σ", 0.01, 0.15, 0.05, 0.01, key="tp_noise")
        with tp_c2:
            tp_n_domain  = st.slider("T5 n per domain", 10, 40, 20, 5, key="tp_n_domain")
            tp_noise_t4  = st.slider("T4 noise σ (Radiant)", 0.01, 0.10, 0.04, 0.01, key="tp_noise_t4")
        with tp_c3:
            tp_n_cv      = st.slider("T6 n per domain (CV)", 20, 80, 50, 10, key="tp_n_cv")
            tp_k_folds   = st.slider("T6 k-folds",  3, 10, 5, 1, key="tp_k_folds")

    # ── Run button ─────────────────────────────────────────────────────────────
    run_col, status_col = st.columns([1, 3])
    with run_col:
        run_btn = st.button("▶ Run All Tests", type="primary", key="run_tests")
    with status_col:
        cached_results = st.session_state.get("test_results", None)
        if cached_results:
            smry = summarize(cached_results)
            smry_color = PASS_COLOR if smry['pass_rate'] >= 0.80 else WARN_COLOR
            st.markdown(
                f"<span style='color:{smry_color};font-size:1.1em;'>"
                f"Last run: **{smry['passed']}/{smry['total']} PASSED** — "
                f"mean score {smry['mean_score']:.2%}</span>",
                unsafe_allow_html=True,
            )

    if run_btn:
        with st.spinner("Running empirical test suite…"):
            results = run_all_tests(
                n_points_t1=tp_n_t1,
                noise_t1=tp_noise_t1,
                noise_t2=tp_noise_t1,
                noise_t3=tp_noise_t1,
                noise_t4=tp_noise_t4,
                noise_t5=tp_noise_t1,
                n_per_domain=tp_n_domain,
                n_cv=tp_n_cv,
                k_folds=tp_k_folds,
            )
        st.session_state["test_results"] = results
        st.rerun()

    results = st.session_state.get("test_results", None)
    if not results:
        st.info("Press **▶ Run All Tests** to execute the test suite.")

    if results:
        import pandas as pd
        st.markdown("---")

        # ═══ Summary scorecard ═══════════════════════════════════════════════
        smry = summarize(results)
        sc_cols = st.columns(4)
        sc_cols[0].metric("Tests Passed",  f"{smry['passed']}/{smry['total']}")
        sc_cols[1].metric("Pass Rate",     f"{smry['pass_rate']:.0%}")
        sc_cols[2].metric("Mean Score",    f"{smry['mean_score']:.3f}")
        sc_cols[3].metric("Tests Failed",  str(smry['failed']),
                          delta_color="inverse",
                          delta=f"−{smry['failed']}" if smry['failed'] else "none")
        st.markdown("---")

        for res in results:
            badge = "✅ PASS" if res.passed else "❌ FAIL"
            badge_col = PASS_COLOR if res.passed else FAIL_COLOR
            with st.expander(
                f"{badge}  **{res.test_id}: {res.name}** — score {res.score:.3f}",
                expanded=not res.passed,
            ):
                st.markdown(f"**Hypothesis:** {res.hypothesis}")
                st.markdown(
                    f"<p style='color:{badge_col};font-weight:bold;'>{res.verdict}</p>",
                    unsafe_allow_html=True,
                )
                st.markdown("**Detailed metrics:**")
                # Flatten details for table display
                flat_rows = []
                for k, v in res.details.items():
                    if isinstance(v, dict):
                        flat_rows.append({'Metric': k, 'Value': '(see sub-table below)'})
                    else:
                        flat_rows.append({'Metric': k, 'Value': str(v)})
                st.dataframe(pd.DataFrame(flat_rows), use_container_width=True,
                             hide_index=True, height=min(len(flat_rows) * 36 + 40, 360))

                # ── T1 plot: accuracy bar chart ───────────────────────────────────
                if res.test_id == 'T1' and 'per_transform' in res.details:
                    pt = res.details['per_transform']
                    fig_t1 = go.Figure(go.Bar(
                        x=list(pt.keys()),
                        y=[v['accuracy'] for v in pt.values()],
                        marker_color=[PASS_COLOR if v['accuracy'] >= 0.70
                                      else FAIL_COLOR for v in pt.values()],
                        text=[f"{v['accuracy']:.0%}" for v in pt.values()],
                        textposition='outside',
                    ))
                    fig_t1.add_hline(y=0.70, line_dash='dot', line_color=WARN_COLOR,
                                     annotation_text='70% threshold',
                                     annotation_font_color=WARN_COLOR)
                    fig_t1.update_layout(
                        height=280, yaxis=dict(range=[0, 1.05], title='Identification Accuracy'),
                        xaxis_title='Transform Type', title='T1 — Transform Identification Accuracy',
                        paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                        font=dict(color='white'), margin=dict(t=40, b=40, l=50, r=20),
                    )
                    st.plotly_chart(fig_t1, use_container_width=True)

                # ── T2 plot: bias curves ──────────────────────────────────────────
                if res.test_id == 'T2' and res.data:
                    d = res.data
                    fig_t2 = go.Figure()
                    fig_t2.add_trace(go.Scatter(
                        x=d['lcc_obs'], y=d['gile_obs'], mode='markers',
                        marker=dict(size=6, color='#00ff99',
                                    line=dict(width=0.5, color='white')),
                        name='Observed',
                    ))
                    fig_t2.add_trace(go.Scatter(
                        x=d['lcc_grid'], y=d['pred_lin'], mode='lines',
                        line=dict(color='#ff4444', width=2), name='Linear fit (biased)',
                    ))
                    fig_t2.add_trace(go.Scatter(
                        x=d['lcc_grid'], y=d['pred_pow'], mode='lines',
                        line=dict(color='#44aaff', width=2.5), name='Power fit (correct)',
                    ))
                    # Bias shading
                    lcc_g = np.array(d['lcc_grid'])
                    pred_lin_arr = np.array(d['pred_lin'])
                    pred_pow_arr = np.array(d['pred_pow'])
                    fig_t2.add_trace(go.Scatter(
                        x=np.concatenate([lcc_g, lcc_g[::-1]]),
                        y=np.concatenate([pred_lin_arr, pred_pow_arr[::-1]]),
                        fill='toself',
                        fillcolor='rgba(255,100,100,0.12)',
                        line=dict(color='rgba(0,0,0,0)'),
                        name='Linear bias region',
                    ))
                    fig_t2.update_layout(
                        height=300, title='T2 — Linear Assumption Bias (Power-Law Ground Truth)',
                        paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                        font=dict(color='white'),
                        xaxis=dict(title='LCC value', gridcolor='rgba(100,100,150,0.2)'),
                        yaxis=dict(title='GILE value', gridcolor='rgba(100,100,150,0.2)'),
                        legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
                        margin=dict(t=40, b=40, l=50, r=20),
                    )
                    st.plotly_chart(fig_t2, use_container_width=True)

                # ── T3 plot: convergence curve ────────────────────────────────────
                if res.test_id == 'T3' and res.data:
                    d = res.data
                    fig_t3 = go.Figure()
                    fig_t3.add_trace(go.Scatter(
                        x=d['n_vals'], y=d['ratio_curve'], mode='lines+markers',
                        line=dict(color='#aa44ff', width=2),
                        marker=dict(size=5), name='Fitted ratio',
                    ))
                    fig_t3.add_hline(y=d['true_ratio'], line_dash='dash', line_color='#00ff99',
                                     annotation_text=f"True ratio = {d['true_ratio']}",
                                     annotation_font_color='#00ff99')
                    fig_t3.add_hline(y=d['true_ratio'] * (1 + d['target_pct']),
                                     line_dash='dot', line_color=WARN_COLOR,
                                     annotation_text=f"+{int(d['target_pct']*100)}%",
                                     annotation_font_color=WARN_COLOR)
                    fig_t3.add_hline(y=d['true_ratio'] * (1 - d['target_pct']),
                                     line_dash='dot', line_color=WARN_COLOR,
                                     annotation_text=f"-{int(d['target_pct']*100)}%",
                                     annotation_font_color=WARN_COLOR)
                    fig_t3.update_layout(
                        height=280, title='T3 — GL Ratio Convergence Rate',
                        paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                        font=dict(color='white'),
                        xaxis=dict(title='n data points', gridcolor='rgba(100,100,150,0.2)'),
                        yaxis=dict(title='Fitted GL Ratio', gridcolor='rgba(100,100,150,0.2)'),
                        legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
                        margin=dict(t=40, b=40, l=60, r=20),
                    )
                    st.plotly_chart(fig_t3, use_container_width=True)

                    # Percentage error curve
                    fig_t3e = go.Figure()
                    fig_t3e.add_trace(go.Scatter(
                        x=d['n_vals'], y=[p * 100 for p in d['pct_err_curve']],
                        mode='lines+markers', line=dict(color='#ff9d00', width=2),
                        marker=dict(size=5), name='% error',
                    ))
                    fig_t3e.add_hline(y=d['target_pct'] * 100, line_dash='dot',
                                      line_color=PASS_COLOR,
                                      annotation_text=f"Target: {int(d['target_pct']*100)}%",
                                      annotation_font_color=PASS_COLOR)
                    fig_t3e.add_hline(y=5, line_dash='dot', line_color='#00ffff',
                                      annotation_text="5%", annotation_font_color='#00ffff')
                    fig_t3e.update_layout(
                        height=220, title='T3 — Ratio Estimation Error vs Sample Size',
                        paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                        font=dict(color='white'),
                        xaxis=dict(title='n data points', gridcolor='rgba(100,100,150,0.2)'),
                        yaxis=dict(title='% error from true ratio',
                                   gridcolor='rgba(100,100,150,0.2)'),
                        margin=dict(t=40, b=40, l=60, r=20),
                    )
                    st.plotly_chart(fig_t3e, use_container_width=True)

                # ── T4 plot: sigmoid alignment ────────────────────────────────────
                if res.test_id == 'T4' and res.data:
                    d = res.data
                    lcc_g = np.linspace(0, 1, 300)
                    from gile_lcc_ratio_engine import GLTransform as GLT, apply_transform_array as ata
                    sig_true = ata(lcc_g, d['fitted_ratio'], GLT.SIGMOID,
                                   k=10.0, mu=d['true_mu'])
                    sig_fit  = ata(lcc_g, d['fitted_ratio'], GLT.SIGMOID,
                                   k=d['recovered_k'], mu=d['recovered_mu'])
                    fig_t4 = go.Figure()
                    fig_t4.add_trace(go.Scatter(
                        x=d['lcc_obs'], y=d['gile_obs'], mode='markers',
                        marker=dict(size=6, color='#00ff99',
                                    line=dict(width=0.5, color='white')),
                        name='Observed',
                    ))
                    fig_t4.add_trace(go.Scatter(
                        x=lcc_g.tolist(), y=sig_true.tolist(), mode='lines',
                        line=dict(color='rgba(100,100,200,0.6)', width=1.5, dash='dash'),
                        name=f'True (μ = C_TI = {d["true_mu"]:.4f})',
                    ))
                    fig_t4.add_trace(go.Scatter(
                        x=lcc_g.tolist(), y=sig_fit.tolist(), mode='lines',
                        line=dict(color='#ff9d00', width=2.5),
                        name=f'Fitted (μ = {d["recovered_mu"]:.4f})',
                    ))
                    fig_t4.add_vline(x=d['true_mu'], line_dash='dot', line_color='#00ffff',
                                     annotation_text=f'C_TI={d["true_mu"]:.4f}',
                                     annotation_font_color='#00ffff')
                    fig_t4.add_vline(x=d['recovered_mu'], line_dash='dot', line_color='#ff9d00',
                                     annotation_text=f'μ̂={d["recovered_mu"]:.4f}',
                                     annotation_font_color='#ff9d00')
                    fig_t4.update_layout(
                        height=300, title='T4 — Radiant Threshold Alignment (Spiritual Domain Sigmoid)',
                        paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                        font=dict(color='white'),
                        xaxis=dict(title='LCC value', gridcolor='rgba(100,100,150,0.2)'),
                        yaxis=dict(title='GILE value', gridcolor='rgba(100,100,150,0.2)'),
                        legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
                        margin=dict(t=40, b=40, l=50, r=20),
                    )
                    st.plotly_chart(fig_t4, use_container_width=True)

                # ── T5 plot: domain discriminability bar chart ────────────────────
                if res.test_id == 'T5' and res.data:
                    d = res.data
                    fig_t5 = go.Figure()
                    fig_t5.add_trace(go.Bar(
                        name='True GL Ratio',
                        x=d['domain_names'], y=d['true_ratios'],
                        marker_color='rgba(0,200,255,0.6)',
                        text=[f"{v:.2f}" for v in d['true_ratios']],
                        textposition='outside',
                    ))
                    fig_t5.add_trace(go.Bar(
                        name='Fitted GL Ratio',
                        x=d['domain_names'], y=d['fitted_ratios'],
                        marker_color='rgba(255,150,0,0.8)',
                        text=[f"{v:.2f}" for v in d['fitted_ratios']],
                        textposition='outside',
                    ))
                    fig_t5.update_layout(
                        height=320, barmode='group',
                        title='T5 — Domain GL Ratio Discriminability (True vs Fitted)',
                        paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                        font=dict(color='white'),
                        xaxis=dict(title='Domain', tickangle=-30,
                                   gridcolor='rgba(100,100,150,0.2)'),
                        yaxis=dict(title='GL Ratio', gridcolor='rgba(100,100,150,0.2)'),
                        legend=dict(bgcolor='rgba(0,0,0,0.4)', font=dict(size=10)),
                        margin=dict(t=40, b=80, l=60, r=20),
                    )
                    st.plotly_chart(fig_t5, use_container_width=True)

                # ── T6 plot: CV RMSE by domain ────────────────────────────────────
                if res.test_id == 'T6' and res.data:
                    d = res.data
                    colors = [PASS_COLOR if p else FAIL_COLOR for p in d['pass_flags']]
                    fig_t6 = go.Figure()
                    fig_t6.add_trace(go.Bar(
                        x=d['domain_names'], y=d['mean_rmses'],
                        error_y=dict(type='data', array=d['std_rmses'], visible=True,
                                     color='rgba(255,255,255,0.5)'),
                        marker_color=colors,
                        text=[f"{v:.4f}" for v in d['mean_rmses']],
                        textposition='outside',
                    ))
                    fig_t6.add_hline(y=0.10, line_dash='dash', line_color=WARN_COLOR,
                                     annotation_text='0.10 threshold',
                                     annotation_font_color=WARN_COLOR)
                    fig_t6.update_layout(
                        height=300,
                        title=f'T6 — {tp_k_folds}-Fold CV RMSE by Domain',
                        paper_bgcolor='rgba(3,3,14,1)', plot_bgcolor='rgba(10,10,25,1)',
                        font=dict(color='white'),
                        xaxis=dict(title='Domain', tickangle=-30,
                                   gridcolor='rgba(100,100,150,0.2)'),
                        yaxis=dict(title='Mean CV RMSE', gridcolor='rgba(100,100,150,0.2)'),
                        margin=dict(t=40, b=80, l=60, r=20),
                    )
                    st.plotly_chart(fig_t6, use_container_width=True)

    # ── Real-world data collection protocol ───────────────────────────────────
    st.markdown("---")
    with st.expander("📋 Real-World Empirical Collection Protocol", expanded=False):
        st.markdown("""
### How to Replace Synthetic Data with Real Observations

To validate the GL ratio engine with real human data, you need matched (LCC, GILE) scores
from the same exemplar individual in the same domain at the same time.

**Step 1 — Recruit exemplars per domain**
- Minimum n = 10 per domain (≥ 20 for reliable transform identification — see T3)
- Exemplars should span the full range of LCC weights (0.1 to 0.95) — do not recruit only high performers

**Step 2 — Score each exemplar with TI Sigma raters**
- **LCC score**: Use the LCC loop-counting algorithm (autonomous_lcc_dashboard) on observable behavior in that domain
- **GILE score**: Use the GILE assessment protocol (G = goodness of action, I = intuitive originality, L = relational warmth, E = aesthetic coherence) — requires ≥ 2 independent raters; use mean

**Step 3 — Enter pairs into the Calibration Tool (BOK Harmonics tab, LCC mode)**
- Enter each (LCC raw, GILE value) pair
- The engine will fit the GL ratio and test linearity

**Step 4 — Interpret results**
| Conclusion | Implication |
|---|---|
| Linear, R² > 0.85 | GL ratio is domain-stable. Use as constant. |
| Power law detected (α ≠ 1) | Non-linear conversion required. Use power transform. |
| Sigmoid detected | Phase transition exists. Check if μ ≈ C_TI = 0.4370. |
| R² < 0.40 | GL ratio is not stable — i-cell moderators needed (see `ICellGLRatio`) |

**Step 5 — Feed results back into DOMAIN_REGISTRY in gile_lcc_ratio_engine.py**
- Update `gl_ratio`, `transform`, `alpha`, `k`, `mu` fields with empirically fitted values
- Mark `empirically_validated = True` in the spec

**Falsification condition (URB #649):**
If every domain produces the same fitted GL ratio (within 5%), the domain-specificity claim is falsified
and a universal GL ratio should replace the domain registry.
""")

    # ── URB #649 theoretical summary ──────────────────────────────────────────
    with st.expander("📐 URB #649 Core Claims + Test Coverage Matrix", expanded=False):
        st.markdown("""
| Claim | Test | Status after run |
|---|---|---|
| GL ratio varies by domain (domain-specificity) | T5 — Domain Discriminability | |
| Linear assumption introduces systematic directional bias | T2 — Bias Characterization | |
| Ratio converges reliably at n ≥ 8 exemplars | T3 — Convergence Rate | |
| Sigmoid inflection aligns with C_TI in Spiritual domain | T4 — Radiant Threshold Alignment | |
| best_fit_transform identifies correct transform at ≥70% accuracy | T1 — Transform Identification | |
| Fitted transform generalizes (CV-RMSE < 0.10) | T6 — Cross-Validation | |

**Key URB #649 equation:**
```
gile_val = f(lcc_val, gl_ratio, transform, α, k, μ)
```
where `f` is established empirically per domain, NOT assumed to be linear.

**Spiritual domain prediction (T4):** If the GILE-LCC relationship in the Spiritual domain
has a sigmoid inflection at μ = C_TI = 1/(φ√2) ≈ 0.4370, this supports the claim that
C_TI is the Radiant Threshold — a genuine phase transition in the GILE-Existence structure,
not an arbitrary constant.
""")
        if results:
            t4 = next((r for r in results if r.test_id == 'T4'), None)
            t5 = next((r for r in results if r.test_id == 'T5'), None)
            if t4 and t5:
                st.markdown(
                    f"**T4 last result:** Recovered μ = "
                    f"`{t4.details.get('recovered_mu', '?')}` vs "
                    f"C_TI = `{t4.details.get('C_TI', '?')}` — "
                    f"{'✅ ALIGNED' if t4.passed else '❌ NOT ALIGNED'}"
                )
                st.markdown(
                    f"**T5 last result:** Rank accuracy = "
                    f"`{t5.details.get('rank_accuracy', '?')}` — "
                    f"{'✅ DOMAIN-SPECIFIC' if t5.passed else '❌ NOT DISCRIMINABLE'}"
                )

with tab9:
    render_mood_amplifier_simulation()

with tab10:
    render_halting_experiment()

with tab11:
    render_oea_tracker()

with tab12:
    st.subheader("🎯 Spectre — TI Viral Meme Project (VMP)")
    st.caption(
        "Generator-only mode (URB #783 §6.2 directive). Predictor accuracy claim "
        "withheld until Program F validation completes (~4 weeks). "
        "Hard GILE floors enforced: G ≥ 0.50, L ≥ 0.40 (self-Love admissible)."
    )

    import spectre_engine as _spectre

    sp_left, sp_right = st.columns([1, 2])
    with sp_left:
        sp_topic = st.text_area(
            "Topic / theme",
            value="GILE-coherence as the antidote to viral cruelty",
            height=90,
            key="spectre_topic",
        )
        sp_platform = st.selectbox(
            "Platform",
            list(_spectre.PLATFORM_CARRIER.keys()),
            key="spectre_platform",
        )
        sp_audience = st.selectbox(
            "Audience profile",
            ["general", "tech/builder", "wellness/spirituality",
             "political/policy", "academic", "entertainment"],
            key="spectre_audience",
        )
        sp_n = st.slider("Candidates to generate", 5, 20, 10, key="spectre_n")
        sp_topk = st.slider("Top-K to display", 1, 5, 3, key="spectre_topk")
        sp_persist = st.checkbox("Log to spectre_memes table", value=True,
                                 key="spectre_persist")
        sp_run = st.button("Generate candidates", type="primary",
                           use_container_width=True, key="spectre_run")

        st.markdown("---")
        st.markdown("**V-formula coefficients (URB #783 §1)**")
        st.markdown(
            f"- α (CONTENT) = `{_spectre.ALPHA}`\n"
            f"- β (NETWORK) = `{_spectre.BETA}`\n"
            f"- γ (GILE) = `{_spectre.GAMMA}`\n"
            f"- δ (GILE×NETWORK) = `{_spectre.DELTA}`"
        )
        st.caption(
            "Pre-validation defaults; replaced by ridge-regression fits after Program F."
        )

    with sp_right:
        if sp_run:
            with st.spinner("Generating candidates and applying GILE floor…"):
                try:
                    result = _spectre.run_pipeline(
                        topic=sp_topic,
                        platform=sp_platform,
                        audience=sp_audience,
                        n_candidates=sp_n,
                        top_k=sp_topk,
                        persist=sp_persist,
                    )
                except Exception as e:
                    st.error(f"Generation failed: {e}")
                    result = None

            if result is not None:
                top = result["top"]
                rejected = result["rejected_count"]
                st.success(
                    f"Generated {len(result['all_candidates'])} candidates · "
                    f"rejected {rejected} on GILE floor · "
                    f"showing top {len(top)}"
                )
                if rejected:
                    with st.expander(f"Rejected ({rejected}) — gate reasons"):
                        for r in result["rejection_reasons"]:
                            st.markdown(f"- `{r}`")

                for i, c in enumerate(top, start=1):
                    st.markdown(f"### #{i} — V = {c.v_score:.3f}")
                    st.markdown(f"**{c.text}**")
                    st.caption(
                        f"Primary emotion: *{c.primary_emotion}* · "
                        f"Intended payoff: *{c.intended_payoff}*"
                    )
                    bd = c.breakdown()
                    bd_cols = st.columns(4)
                    bd_cols[0].metric("CONTENT", f"{bd['CONTENT']:.2f}")
                    bd_cols[1].metric("NETWORK", f"{bd['NETWORK']:.2f}")
                    bd_cols[2].metric("GILE", f"{bd['GILE']:.2f}")
                    bd_cols[3].metric("G×N", f"{bd['interaction']:.2f}")
                    with st.expander("Sub-scores"):
                        st.json({
                            "content": _spectre.asdict(c.content),
                            "gile": _spectre.asdict(c.gile),
                            "network": _spectre.asdict(c.network),
                        })
                    st.markdown("---")

        st.markdown("#### Recent generations")
        try:
            _spectre.init_db()
            recents = _spectre.recent_memes(limit=10)
            if recents:
                st.dataframe(recents, use_container_width=True, hide_index=True)
            else:
                st.caption("No memes generated yet.")
        except Exception as e:
            st.caption(f"(DB unavailable: {e})")

        st.markdown("---")
        st.markdown("#### URB #784 P784.5 audit (Inversion-Theorem secondary endpoint)")
        st.caption(
            "Tests V-score → engagement Spearman ρ stratified by platform-HEM proxy. "
            "Pending until Program F engagement data lands; the harness reports "
            "`insufficient_data` cleanly when no engagement is recorded yet."
        )
        if st.button("Run P784.5 audit", key="spectre_audit_p784_5"):
            try:
                report = _spectre.audit_p784_5()
                st.markdown(f"**Overall verdict:** {report['overall_verdict']}")
                st.markdown(f"**Total rows with engagement:** {report['n_total']}")
                strata_view = []
                for stratum, info in report["strata"].items():
                    strata_view.append({
                        "stratum": stratum,
                        "n": info["n"],
                        "status": info["status"],
                        "spearman_rho": info.get("spearman_rho"),
                        "verdict": info.get("verdict_vs_p784_5", "n/a"),
                    })
                st.dataframe(strata_view, use_container_width=True, hide_index=True)
                with st.expander("Platform → HEM-proxy mapping"):
                    st.json(report["platform_hem_proxy"])
            except Exception as e:
                st.error(f"P784.5 audit failed: {e}")

with tab13:
    st.subheader("🍄 Mycelial Resonance Engine — Closed-Loop Brain Entrainment")
    st.caption(
        "v1: ambient isochronic entrainment with 5.5-BPM cardiac coherence envelope. "
        "Reads your live Muse stream from `esp32_biometric_data` and drifts from your "
        "current α-peak toward the selected mood-attractor frequency. Pure Python, "
        "no external API calls."
    )

    import mycelial_resonance_engine as _mre

    mre_app_mode = st.radio(
        "Mode",
        ["Static track generator", "🎯 Live closed-loop session (biofeedback)"],
        horizontal=True, key="mre_app_mode",
        help="Static: pre-render a WAV and download/play. Live: 5-min baseline → "
             "calibrated audio + on-screen α-peak trajectory → debrief stats.",
    )

    if mre_app_mode.startswith("🎯"):
        # ============================================================
        # LIVE CLOSED-LOOP SESSION MODE
        # ============================================================
        st.markdown(
            "**How this works.** "
            "(1) **Baseline** — your live Muse stream is sampled for 5 minutes (default) "
            "to establish your resting α-peak and band-power profile. "
            "(2) **Calibration** — an audio session is generated, drifting from your "
            "actual measured baseline toward the chosen attractor. "
            "(3) **Steering** — audio plays while your α-peak is plotted live against the "
            "target. (4) **Debrief** — drift achieved, time-in-target-band, and a session "
            "log row are saved to `mre_live_sessions`."
        )

        live_left, live_right = st.columns([1, 1])
        with live_left:
            live_mood = st.selectbox(
                "Mood attractor",
                list(_mre.MOOD_ATTRACTORS.keys()),
                format_func=lambda k: f"{_mre.MOOD_ATTRACTORS[k].name} ({_mre.MOOD_ATTRACTORS[k].target_hz} Hz)",
                index=list(_mre.MOOD_ATTRACTORS.keys()).index("BLISSFUL_EMPATHIC")
                    if "BLISSFUL_EMPATHIC" in _mre.MOOD_ATTRACTORS else 0,
                key="mre_live_mood",
            )
            live_attractor = _mre.MOOD_ATTRACTORS[live_mood]
            st.caption(live_attractor.description)
            live_baseline_min = st.slider("Baseline duration (min)", 1, 10, 5,
                                          key="mre_live_baseline_min")
            live_steering_min = st.slider("Steering duration (min)", 3, 30, 15,
                                          key="mre_live_steering_min")
            live_poll_s = st.slider("Poll interval (sec)", 1, 5, 2,
                                    key="mre_live_poll_s",
                                    help="How often to read the latest Muse row.")
            live_bed = st.checkbox("L4 GILE harmonic bed", value=True,
                                   key="mre_live_bed")
            live_band_hz = st.slider("Target-band tolerance (± Hz)", 0.2, 2.0, 0.5, 0.1,
                                     key="mre_live_band_hz",
                                     help="A sample counts as 'in target band' if "
                                          "|α-peak − target| < this value.")

        with live_right:
            st.markdown("**Pre-flight check**")
            try:
                _pre_state = _mre.read_current_state()
            except Exception as _e:
                _pre_state = {}
                st.error(f"DB read failed: {_e}")
            if _pre_state:
                _pre_age = (datetime.now() - _pre_state.get('created_at')).total_seconds() \
                    if _pre_state.get('created_at') else 999
                p1, p2, p3 = st.columns(3)
                p1.metric("α", f"{(_pre_state.get('alpha') or 0):.3f}")
                p2.metric("HR", f"{(_pre_state.get('heart_rate') or 0)} bpm")
                p3.metric("Sample age", f"{_pre_age:.1f}s")
                if _pre_age > 10:
                    st.warning(f"⚠️ Latest Muse sample is {_pre_age:.0f}s old — "
                               "your bridge isn't pushing fresh data. The live "
                               "session will run on stale state until the bridge "
                               "starts streaming.")
                elif (_pre_state.get('heart_rate') or 0) == 0:
                    st.warning("⚠️ HR=0 — Polar H10 not detected. Session will run "
                               "but HRV metrics will be flat.")
                else:
                    st.success("✅ Stream looks live. Ready to start.")
            else:
                st.error("No state available — start your ESP32 bridge.")

            st.markdown("**Target attractor**")
            st.metric("Frequency", f"{live_attractor.target_hz} Hz")
            if live_attractor.overlay_hz:
                st.caption(f"+ overlay at {live_attractor.overlay_hz} Hz")

            live_start = st.button("▶ Start live closed-loop session",
                                   type="primary", use_container_width=True,
                                   key="mre_live_start")
            st.caption("To abort mid-session, refresh the browser tab.")

        if live_start:
            import time as _time
            import pandas as _pd
            import base64 as _b64

            target_hz = live_attractor.target_hz
            poll_s = live_poll_s
            baseline_dur = live_baseline_min * 60
            steering_dur = live_steering_min * 60

            st.markdown("---")
            phase_box = st.empty()
            timer_box = st.empty()
            audio_box = st.empty()
            metrics_box = st.empty()
            chart_box = st.empty()
            band_box = st.empty()

            history = {"t": [], "peak": [], "alpha": [], "beta": [],
                       "theta": [], "gamma": [], "hr": [], "rmssd": []}
            baseline_peaks = []
            steering_peaks = []
            audio_started = False
            start_t = _time.time()

            try:
                while True:
                    now = _time.time()
                    elapsed = now - start_t
                    if elapsed >= baseline_dur + steering_dur:
                        break

                    try:
                        st_row = _mre.read_current_state()
                    except Exception:
                        st_row = {}
                    peak = _mre.estimate_alpha_peak(st_row) if st_row else None

                    if peak is not None:
                        history["t"].append(elapsed)
                        history["peak"].append(peak)
                        history["alpha"].append(float(st_row.get("alpha") or 0))
                        history["beta"].append(float(st_row.get("beta") or 0))
                        history["theta"].append(float(st_row.get("theta") or 0))
                        history["gamma"].append(float(st_row.get("gamma") or 0))
                        history["hr"].append(int(st_row.get("heart_rate") or 0))
                        history["rmssd"].append(float(st_row.get("rmssd") or 0))

                    in_baseline = elapsed < baseline_dur
                    if in_baseline:
                        phase_label = "🔵 BASELINE"
                        remaining = baseline_dur - elapsed
                        if peak is not None:
                            baseline_peaks.append(peak)
                    else:
                        phase_label = "🟢 STEERING"
                        remaining = (baseline_dur + steering_dur) - elapsed
                        if peak is not None:
                            steering_peaks.append(peak)
                        if not audio_started:
                            baseline_peak = float(np.mean(baseline_peaks)) \
                                if baseline_peaks else 10.0
                            with audio_box.container():
                                with st.spinner(
                                    f"Generating {live_steering_min}-min session "
                                    f"calibrated to baseline α-peak "
                                    f"{baseline_peak:.2f} Hz → target {target_hz} Hz…"
                                ):
                                    try:
                                        gen_result = _mre.generate_for_mood(
                                            mood_key=live_mood,
                                            duration_s=int(steering_dur),
                                            use_current_state=True,
                                            mode="isochronic",
                                            harmonic_bed=live_bed,
                                        )
                                        with open(gen_result["path"], "rb") as _af:
                                            _wav_bytes = _af.read()
                                        _b64s = _b64.b64encode(_wav_bytes).decode()
                                        st.markdown(
                                            f'<audio controls autoplay '
                                            f'src="data:audio/wav;base64,{_b64s}" '
                                            f'style="width:100%"></audio>',
                                            unsafe_allow_html=True,
                                        )
                                        st.caption(
                                            f"🔊 Drift: {gen_result['start_hz']} Hz → "
                                            f"{gen_result['target_hz']} Hz over "
                                            f"{live_steering_min} min · "
                                            f"L4 bed: {'on' if live_bed else 'off'}"
                                        )
                                    except Exception as _ge:
                                        st.error(f"Audio generation failed: {_ge}")
                            audio_started = True

                    mins = int(remaining // 60)
                    secs = int(remaining % 60)
                    phase_box.markdown(
                        f"### {phase_label}  ·  remaining **{mins}:{secs:02d}**"
                    )

                    if peak is not None:
                        baseline_mean = (float(np.mean(baseline_peaks))
                                         if baseline_peaks else None)
                        distance = abs(peak - target_hz)
                        with metrics_box.container():
                            m1, m2, m3, m4, m5 = st.columns(5)
                            m1.metric("Current α-peak", f"{peak:.2f} Hz")
                            m2.metric("Baseline mean",
                                      f"{baseline_mean:.2f} Hz" if baseline_mean else "—")
                            m3.metric("Target", f"{target_hz:.2f} Hz")
                            m4.metric("Δ to target", f"{distance:.2f} Hz")
                            m5.metric("HR", f"{history['hr'][-1]} bpm"
                                            if history["hr"] else "—")

                    if len(history["t"]) >= 2:
                        df = _pd.DataFrame({
                            "t (s)": history["t"],
                            "α-peak": history["peak"],
                            "target": [target_hz] * len(history["t"]),
                        }).set_index("t (s)")
                        chart_box.line_chart(df, height=240)

                        if len(steering_peaks) > 0:
                            in_band_n = sum(1 for p in steering_peaks
                                            if abs(p - target_hz) < live_band_hz)
                            band_pct = in_band_n / len(steering_peaks)
                            band_box.progress(
                                min(1.0, band_pct),
                                text=f"Time-in-target-band (±{live_band_hz} Hz): "
                                     f"{band_pct:.0%}  ({in_band_n}/{len(steering_peaks)} samples)"
                            )

                    _time.sleep(poll_s)

            except Exception as _le:
                st.error(f"Live session loop error: {_le}")

            # Debrief
            st.markdown("---")
            st.markdown("### 📊 Session Debrief")
            if baseline_peaks and steering_peaks:
                bmean = float(np.mean(baseline_peaks))
                smean = float(np.mean(steering_peaks))
                drift = bmean - smean
                target_drift = bmean - target_hz
                in_band_final = sum(1 for p in steering_peaks
                                    if abs(p - target_hz) < live_band_hz) \
                                / max(1, len(steering_peaks))
                d1, d2, d3, d4 = st.columns(4)
                d1.metric("Baseline mean", f"{bmean:.2f} Hz")
                d2.metric("Steering mean", f"{smean:.2f} Hz",
                          delta=f"{-drift:+.2f} Hz vs baseline")
                d3.metric("Target drift", f"{target_drift:+.2f} Hz")
                d4.metric(f"Time-in-band (±{live_band_hz} Hz)",
                          f"{in_band_final:.0%}")

                # Drift efficiency: how much of the target drift was achieved
                if abs(target_drift) > 0.05:
                    efficiency = max(0.0, min(1.0, drift / target_drift)) \
                        if target_drift != 0 else 0
                    st.metric("Drift efficiency",
                              f"{efficiency:.0%}",
                              help="Fraction of intended baseline→target shift "
                                   "actually observed in α-peak.")
                try:
                    log_id = _mre.save_live_session_log(
                        mood_key=live_mood,
                        target_hz=float(target_hz),
                        baseline_peak_hz=bmean,
                        final_peak_hz=smean,
                        drift_hz=float(drift),
                        time_in_band_pct=float(in_band_final),
                        samples=len(history["t"]),
                        baseline_min=float(live_baseline_min),
                        steering_min=float(live_steering_min),
                        notes="",
                    )
                    st.success(f"✅ Session log saved to `mre_live_sessions` (id={log_id}).")
                except Exception as _se:
                    st.warning(f"(log save failed: {_se})")
            else:
                st.warning("Insufficient data to compute debrief stats — "
                           "your bridge may not have been streaming.")

        # Recent sessions table
        st.markdown("---")
        st.markdown("**Recent live sessions**")
        try:
            with psycopg2.connect(os.environ["DATABASE_URL"]) as _conn:
                _hist_df = pd.read_sql(
                    """
                    SELECT id, started_at, mood_key, target_hz,
                           ROUND(baseline_peak_hz::numeric, 2) AS baseline,
                           ROUND(final_peak_hz::numeric, 2) AS final,
                           ROUND(drift_hz::numeric, 2) AS drift,
                           ROUND((time_in_band_pct*100)::numeric, 1) AS in_band_pct,
                           samples
                    FROM mre_live_sessions
                    ORDER BY started_at DESC LIMIT 10
                    """, _conn
                )
            if not _hist_df.empty:
                st.dataframe(_hist_df, use_container_width=True, hide_index=True)
            else:
                st.caption("(no live sessions logged yet)")
        except Exception as _he:
            st.caption(f"(history unavailable: {_he})")

    else:
        # ============================================================
        # STATIC TRACK GENERATOR MODE (existing UI)
        # ============================================================
        mre_left, mre_right = st.columns([1, 1])

        with mre_left:
            st.markdown("**Live state (latest Muse sample)**")
            try:
                mre_state = _mre.read_current_state()
            except Exception as e:
                mre_state = {}
                st.caption(f"(state read failed: {e})")

            if mre_state:
                mre_alpha_peak = _mre.estimate_alpha_peak(mre_state)
                sc1, sc2, sc3 = st.columns(3)
                sc1.metric("α", f"{(mre_state.get('alpha') or 0):.3f}")
                sc2.metric("β", f"{(mre_state.get('beta') or 0):.3f}")
                sc3.metric("θ", f"{(mre_state.get('theta') or 0):.3f}")
                st.metric("Estimated α-peak (Hz)", f"{mre_alpha_peak:.2f}")
                st.caption(f"Session: `{mre_state.get('session_id', '—')}`  ·  "
                           f"updated {mre_state.get('created_at', '—')}")
            else:
                st.warning("No live Muse data — start the bridge to enable state-aware drift.")
                mre_alpha_peak = 10.0

            st.markdown("---")
            st.markdown("**Generation parameters**")
            mre_mood = st.selectbox(
                "Mood attractor",
                list(_mre.MOOD_ATTRACTORS.keys()),
                format_func=lambda k: f"{_mre.MOOD_ATTRACTORS[k].name} ({_mre.MOOD_ATTRACTORS[k].target_hz} Hz)",
                key="mre_mood",
            )
            mre_attractor = _mre.MOOD_ATTRACTORS[mre_mood]
            st.caption(mre_attractor.description)

            mre_duration = st.slider("Duration (minutes)", 1, 30, 5, key="mre_duration")
            mre_mode = st.radio("Output mode", ["isochronic", "binaural"],
                                help="isochronic = mono, speaker-safe; binaural = stereo, headphones required",
                                key="mre_mode", horizontal=True)
            mre_use_state = st.checkbox(
                "Drift from current α-peak (vs. start at target)",
                value=True, key="mre_use_state",
                help="If on, the track ramps from your estimated current peak to the target. "
                     "If off, the entire track sits at the target frequency.",
            )
            mre_bed = st.checkbox(
                "L4 — GILE-coherent harmonic bed (URB #781 §B)",
                value=False, key="mre_bed",
                help="Replaces the bare 200 Hz carrier with a sparse just-intonation chord "
                     "progression (I → IV → V → I) on a low root, with a slow breath tremolo. "
                     "Sounds less clinical, more pleasant for ambient daily use.",
            )
            mre_session_kind = st.radio(
                "Generation strategy",
                ["Single drift (v1)", "Adaptive session (v2)"],
                help="v1: one linear drift from your current α-peak to the target. "
                     "v2: anticipatory pre-adaptation — reads recent Muse history, estimates "
                     "α-velocity, builds a multi-segment WAV that meets you where you'll be.",
                key="mre_session_kind", horizontal=True,
            )
            mre_run = st.button("Generate track", type="primary",
                                use_container_width=True, key="mre_run")

        with mre_right:
            if mre_run:
                with st.spinner(f"Synthesizing {mre_duration}-minute {mre_attractor.name} track…"):
                    try:
                        if mre_session_kind.startswith("Adaptive"):
                            result = _mre.generate_adaptive_session(
                                mood_key=mre_mood,
                                duration_s=int(mre_duration * 60),
                                segment_s=30,
                                mode=mre_mode,
                                harmonic_bed=mre_bed,
                            )
                            result["start_hz"] = result["current_peak_hz"]
                        else:
                            result = _mre.generate_for_mood(
                                mood_key=mre_mood,
                                duration_s=int(mre_duration * 60),
                                use_current_state=mre_use_state,
                                mode=mre_mode,
                                harmonic_bed=mre_bed,
                            )
                    except Exception as e:
                        st.error(f"Generation failed: {e}")
                        result = None

                if result is not None:
                    st.success(
                        f"Track ready · drift {result['start_hz']} Hz → {result['target_hz']} Hz · "
                        f"{result['duration_s']}s · {result['mode']}"
                    )
                    try:
                        with open(result["path"], "rb") as f:
                            audio_bytes = f.read()
                        st.audio(audio_bytes, format="audio/wav")
                        st.download_button(
                            "Download WAV",
                            data=audio_bytes,
                            file_name=os.path.basename(result["path"]),
                            mime="audio/wav",
                            use_container_width=True,
                        )
                    except Exception as e:
                        st.warning(f"(playback unavailable: {e})")
                    with st.expander("Track metadata"):
                        st.json(result)

            st.markdown("---")
            st.markdown("**L5 — Visual SSVEP overlay (v3 preview)**")
            st.caption(
                "Soft sinusoidal flicker at the target frequency for steady-state visual "
                "evoked-potential coupling. Use in peripheral vision only — do not stare. "
                "Stop after 5–10 minutes or at any discomfort. Photosensitive-epilepsy warning applies."
            )
            ssvep_freq = st.number_input(
                "SSVEP frequency (Hz)", min_value=4.0, max_value=40.0,
                value=float(_mre.MOOD_ATTRACTORS[mre_mood].target_hz),
                step=0.1, key="mre_ssvep_freq",
            )
            if st.button("Open SSVEP overlay", use_container_width=True, key="mre_ssvep_open"):
                from streamlit.components.v1 import html as _html
                _html(_mre.ssvep_html(ssvep_freq, _mre.MOOD_ATTRACTORS[mre_mood].name),
                      height=420, scrolling=False)

            st.markdown("---")
            st.markdown("**Usage notes**")
            st.markdown(
                "- **Casual ambient use:** play at low volume in the background while you do "
                "anything — reading, eating, conversation. The entrainment works subliminally.\n"
                "- **Active session use:** play through good speakers or headphones at "
                "comfortable volume. Close eyes if you want stronger lock-in.\n"
                "- **Headphones required for binaural mode.** Isochronic works on speakers.\n"
                "- **Cardiac coupling:** every track has a 5.5-BPM amplitude envelope so "
                "HRV resonance and EEG entrainment lock simultaneously.\n"
                "- **L4 harmonic bed:** turn it on for ambient daily use; off for clinical "
                "verification (the bare 200 Hz carrier makes the modulation more measurable).\n"
                "- **L5 SSVEP overlay:** strongest entrainment when audio + visual are both on. "
                "Look slightly past the screen, not at the center fixation dot.\n"
                "- **Verification:** glance at the Muse terminal readout 3–5 minutes in. "
                "α/β should rise for CALM_FOCUS / GILE_COHERENCE; β should rise for FLOW; "
                "θ should rise for DEEP_REST / CREATIVE_IDEATION."
            )

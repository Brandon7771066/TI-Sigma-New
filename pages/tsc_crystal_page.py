"""
TI Sigma Crystal Visualizer — standalone page module for app.py
Renders the full 3D interactive TSC crystal with all three display modes.
"""

import numpy as np
import streamlit as st
import plotly.graph_objects as go

from hypercomputer import VERTICES, N_VERTICES
from hypercomputer.tsc import ADJACENCY
from hypercomputer.phases import Phase, PHASE_COLORS, PHASE_LABELS, classify_state
from hypercomputer.constants import PHI, C_TI, T_TI, ET, RING_RADII, RING_NAMES, N_RINGS, N_LAYERS

RING_PALETTE = [
    "#00e5ff",   # Ring 1  C ≈ 0.437
    "#00ff99",   # Ring 2  T ≈ 0.934
    "#e8e8ff",   # Ring 3  1.000
    "#ffd700",   # Ring 4  √2 ≈ 1.414
    "#ff9d00",   # Ring 5  φ ≈ 1.618
    "#ff5533",   # Ring 6  e ≈ 2.718
    "#cc44ff",   # Ring 7  π ≈ 3.142
]

SPACE_BG = "rgba(3,3,14,1)"


def tsc_figure(amplitudes=None, mode="ring", height=700, title=None):
    x = [v.position.real for v in VERTICES]
    y = [v.position.imag for v in VERTICES]
    z = [v.ring           for v in VERTICES]

    if mode == "bec":
        colors = ["#00ff99" if v.ring == 0 else RING_PALETTE[v.ring - 1] for v in VERTICES]
        sizes  = [22] + [16] * (N_VERTICES - 1)
        hover  = [
            f"<b>{v.label}</b><br>Ring {v.ring} — "
            f"{'Origin' if v.ring == 0 else RING_NAMES[v.ring-1]}<br>Phase: BEC (TRUE)"
            for v in VERTICES
        ]
        ec_ring, ec_rad = "rgba(0,255,160,0.28)", "rgba(100,220,255,0.18)"

    elif mode == "phase" and amplitudes is not None:
        phases = classify_state(amplitudes)
        colors = [PHASE_COLORS[p] for p in phases]
        sizes  = [20 if p == Phase.BEC else 15 if p == Phase.SUPERSOLID
                  else 11 if p == Phase.FQH else 8 if p == Phase.MOTT else 5
                  for p in phases]
        hover  = [
            f"<b>{v.label}</b><br>Ring {v.ring}: "
            f"{'O' if v.ring == 0 else RING_NAMES[v.ring-1]}<br>"
            f"|α| = {abs(amplitudes[v.index]):.4f}<br>"
            f"Phase: {PHASE_LABELS[phases[v.index]]}"
            for v in VERTICES
        ]
        ec_ring, ec_rad = "rgba(120,200,255,0.22)", "rgba(200,140,255,0.15)"

    else:
        colors = ["#ffffff"] + [RING_PALETTE[v.ring - 1] for v in VERTICES if v.ring > 0]
        sizes  = [26] + [14] * (N_VERTICES - 1)
        hover  = [
            f"<b>{v.label}</b><br>"
            f"Ring {v.ring}: {'Origin' if v.ring == 0 else RING_NAMES[v.ring-1]+' = '+f'{v.radius:.4f}'}<br>"
            f"Layer {v.layer}  θ = {v.angle:.3f} rad"
            for v in VERTICES
        ]
        ec_ring, ec_rad = "rgba(160,210,255,0.22)", "rgba(200,160,255,0.14)"

    ex_r, ey_r, ez_r = [], [], []
    ex_s, ey_s, ez_s = [], [], []
    for i in range(N_VERTICES):
        for j in range(i + 1, N_VERTICES):
            if ADJACENCY[i, j] == 0:
                continue
            if VERTICES[i].ring == VERTICES[j].ring:
                ex_r += [x[i], x[j], None]; ey_r += [y[i], y[j], None]; ez_r += [z[i], z[j], None]
            else:
                ex_s += [x[i], x[j], None]; ey_s += [y[i], y[j], None]; ez_s += [z[i], z[j], None]

    fig = go.Figure()
    fig.add_trace(go.Scatter3d(x=ex_r, y=ey_r, z=ez_r, mode='lines',
                               line=dict(color=ec_ring, width=2),
                               showlegend=False, hoverinfo='skip'))
    fig.add_trace(go.Scatter3d(x=ex_s, y=ey_s, z=ez_s, mode='lines',
                               line=dict(color=ec_rad,  width=1),
                               showlegend=False, hoverinfo='skip'))

    tc = np.linspace(0, 2 * np.pi, 128)
    for r, (radius, name) in enumerate(zip(RING_RADII, RING_NAMES), start=1):
        rc = RING_PALETTE[r-1] if mode in ("ring", "bec") else "rgba(120,120,180,0.18)"
        fig.add_trace(go.Scatter3d(x=radius*np.cos(tc), y=radius*np.sin(tc), z=[r]*128,
                                   mode='lines', line=dict(color=rc, width=1), opacity=0.28,
                                   showlegend=False, hoverinfo='skip'))
        fig.add_trace(go.Scatter3d(x=[radius*1.07], y=[0.05], z=[r], mode='text',
                                   text=[f"{name}={radius:.3f}"],
                                   textfont=dict(color=RING_PALETTE[r-1] if mode in ("ring","bec") else "#9090bb", size=9),
                                   showlegend=False, hoverinfo='skip'))

    fig.add_trace(go.Scatter3d(x=[0], y=[0], z=[0], mode='markers+text',
                               marker=dict(size=sizes[0], color=colors[0], symbol='diamond',
                                           line=dict(color='gold', width=2)),
                               text=["0"], textfont=dict(color='gold', size=11),
                               hovertext=[hover[0]], hoverinfo='text',
                               name="Origin (0 — vacuum)"))

    for ri in range(1, N_RINGS + 1):
        mask = [v.ring == ri for v in VERTICES]
        fig.add_trace(go.Scatter3d(
            x=[x[i] for i,m in enumerate(mask) if m],
            y=[y[i] for i,m in enumerate(mask) if m],
            z=[z[i] for i,m in enumerate(mask) if m],
            mode='markers',
            marker=dict(size=[sizes[i] for i,m in enumerate(mask) if m],
                        color=[colors[i] for i,m in enumerate(mask) if m],
                        opacity=0.93,
                        line=dict(color='rgba(255,255,255,0.22)', width=0.5)),
            hovertext=[hover[i] for i,m in enumerate(mask) if m],
            hoverinfo='text',
            name=f"Ring {ri}: {RING_NAMES[ri-1]} ≈ {RING_RADII[ri-1]:.3f}"
        ))

    plot_title = title or (
        "TI Sigma Crystal — Full BEC · all 57 i-cells TRUE" if mode == "bec" else
        "TI Sigma Crystal — Phase State"                    if mode == "phase" else
        "TI Sigma Crystal — 7 Rings · 8 Layers · 57 i-cells"
    )

    fig.update_layout(
        scene=dict(
            xaxis_title="Re", yaxis_title="Im", zaxis_title="Ring",
            bgcolor=SPACE_BG,
            xaxis=dict(gridcolor='rgba(60,60,100,0.22)', showbackground=True,
                       backgroundcolor=SPACE_BG, range=[-3.5, 3.8]),
            yaxis=dict(gridcolor='rgba(60,60,100,0.22)', showbackground=True,
                       backgroundcolor=SPACE_BG),
            zaxis=dict(gridcolor='rgba(60,60,100,0.22)', showbackground=True,
                       backgroundcolor=SPACE_BG, tickvals=list(range(8)),
                       ticktext=["O"]+RING_NAMES),
            camera=dict(eye=dict(x=1.55, y=1.10, z=0.75), up=dict(x=0, y=0, z=1))
        ),
        paper_bgcolor=SPACE_BG,
        font=dict(color='white', family='monospace'),
        height=height,
        margin=dict(l=0, r=0, t=44, b=0),
        legend=dict(bgcolor='rgba(8,8,22,0.85)', bordercolor='rgba(80,80,200,0.3)',
                    borderwidth=1, font=dict(size=10), x=0.01, y=0.99),
        title=dict(text=plot_title, font=dict(size=13, color='#c0c8ff'), x=0.5)
    )
    return fig


def render_tsc_crystal():
    st.subheader("🔮 TI Sigma Crystal — 7D Structure Visualizer")
    st.caption(
        "57 vertices · 7 rings at PRIMARY constant radii (C, T, 1, √2, φ, e, π) · "
        "8 golden-angle octagonal layers · ~120 lattice edges · 5 BEC truth phases"
    )

    ctrl, vis = st.columns([1, 3])

    with ctrl:
        mode = st.radio(
            "Display mode",
            ["✨ Full BEC (all TRUE)", "🌈 Ring identity", "🔬 Phase sweep"],
            index=0
        )
        if mode == "🔬 Phase sweep":
            amp_val = st.slider("|α| amplitude", 0.0, 1.0, 0.72, 0.01,
                                help="Sweep from DT → Mott → FQH → Supersolid → BEC")
            demo_amps = np.full(N_VERTICES, amp_val, dtype=complex)
        st.markdown("---")
        st.markdown("**PRIMARY constant rings:**")
        phase_map = {
            "C": "Coherence floor (FQH→Mott boundary)",
            "T": "Truth threshold (Supersolid→BEC)",
            "1": "Unity — normalization",
            "√2": "TECC error distance",
            "φ": "Golden ratio — GILE structure",
            "e": "Euler — LCC exponent",
            "π": "Pi — full rotation",
        }
        for rname, rval, rcolor in zip(RING_NAMES, RING_RADII, RING_PALETTE):
            st.markdown(
                f'<span style="color:{rcolor};font-size:16px">●</span> '
                f'**{rname}** = {rval:.4f}  \n'
                f'<small style="color:#888">{phase_map[rname]}</small>',
                unsafe_allow_html=True
            )

    with vis:
        if mode == "✨ Full BEC (all TRUE)":
            st.plotly_chart(tsc_figure(mode="bec", height=720), use_container_width=True)
        elif mode == "🔬 Phase sweep":
            st.plotly_chart(tsc_figure(amplitudes=demo_amps, mode="phase", height=720),
                            use_container_width=True)
            bec_count = sum(1 for a in demo_amps if abs(a) > T_TI)
            ss_count  = sum(1 for a in demo_amps if C_TI < abs(a) <= T_TI)
            fqh_count = sum(1 for a in demo_amps if ET < abs(a) <= C_TI)
            mott_count= sum(1 for a in demo_amps if 1e-6 < abs(a) <= ET)
            dt_count  = sum(1 for a in demo_amps if abs(a) <= 1e-6)
            mc1,mc2,mc3,mc4,mc5 = st.columns(5)
            mc1.metric("🟢 BEC/TRUE",  bec_count)
            mc2.metric("🟡 Supersolid", ss_count)
            mc3.metric("🟣 FQH",       fqh_count)
            mc4.metric("🔴 Mott/FALSE",mott_count)
            mc5.metric("⚫ DT",        dt_count)
        else:
            st.plotly_chart(tsc_figure(mode="ring", height=720), use_container_width=True)

    st.markdown("---")
    with st.expander("Crystal anatomy — what you are looking at", expanded=False):
        st.markdown(f"""
**The 57 vertices** are the i-cells of the crystal — each one is a complex number
`value = radius × e^(iθ)` where radius is a PRIMARY constant and θ is determined by
the golden-angle layer offset. Together they form a quasicrystalline state space.

**The edges (~120 total):**
- *Octagonal ring edges* (cyan/green): connect each vertex to its two neighbors within the same ring — forming 7 independent octagons
- *Radial spokes* (violet/dim): connect each vertex to the same-layer vertex in the adjacent ring — forming 8 radial "pillars" through all 7 rings

**The origin (gold diamond)** is vertex 0 — the vacuum / DT ground state. It connects to all 8 vertices in ring 1 (C-ring), making it the root of the crystal.

**The 5 BEC phases** (colors when in Phase Sweep mode):
| Color | Phase | |α| range | TI Truth value |
|-------|-------|----------|----------------|
| 🟢 Green | BEC | > T = {T_TI:.4f} | TRUE |
| 🟡 Amber | Supersolid | C – T ({C_TI:.4f}–{T_TI:.4f}) | TRALSE-INDET |
| 🟣 Purple | Frac. QH | ET – C ({ET:.4f}–{C_TI:.4f}) | TRALSE-FALSE |
| 🔴 Red | Mott | 0 – ET ({ET:.4f}) | FALSE |
| ⚫ Black | Fragmented | ≈ 0 | DOUBLE-TRALSE |

**57 in ternary:** 2·27 + 0·9 + 1·3 + 0 = **2010₃** — a ternary palindrome, encoding the 5-value architecture in base 3 (the natural base of TI Sigma logic).

Drag to rotate · Scroll to zoom · Hover any vertex for label, ring, and phase data.
        """)

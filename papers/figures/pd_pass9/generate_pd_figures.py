"""
Pass 9 PD visualization generator.
Outputs 4 figures into papers/figures/pd_pass9/:
  fig1_pd_graph_real_axis.png       — (-3, 2) Perfect-Fifth scalar with named thresholds + Indeterminate sub-range
  fig2_pd_crystal_complex_plane.png — Full complex-plane PD/DT geometry (Brandon-canonical Pass 8)
  fig3_ti_sigma_crystal.png         — 57-vertex TSC polytope (urb_645) at 7 rings
  fig4_graph_to_crystal_projection.png — Projection-arrow diagram showing how Graph is the Crystal's projection
"""
import os
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
import numpy as np

OUT = os.path.dirname(os.path.abspath(__file__))
PHI = (1 + 5**0.5) / 2
E = math.e
PI = math.pi
SQRT2 = 2**0.5

# -----------------------------------------------------------------------------
# Figure 1: PD Graph — (-3, 2) Perfect-Fifth real-axis scalar with named thresholds
# -----------------------------------------------------------------------------
fig, ax = plt.subplots(figsize=(13, 4.5))
ax.set_xlim(-3.5, 3.5)
ax.set_ylim(-1.0, 1.6)

# Indeterminate sub-range band (-2/3, +1/3) per urb_715
ax.axvspan(-2/3, 1/3, ymin=0.20, ymax=0.55, color="#FFE9A8", alpha=0.7,
           label="Indeterminate sub-range (−2/3, +1/3) — urb_715")

# Operational PD interval (-3, 2)
ax.axvspan(-3, 2, ymin=0.32, ymax=0.42, color="#BEE3F8", alpha=0.6,
           label="Operational PD scalar (−3, 2) — Perfect-Fifth 3:2")

# Zero line
ax.axhline(0.37, color="black", linewidth=2.5, zorder=2)

# Threshold ticks
thresholds = [
    (-PI,    "−π\nDT cliff (mirror)",     "#8B0000"),
    (-E,     "−e\nPre-DT (mirror)",       "#B22222"),
    (-PHI,   "−φ\nTranscendent (mirror)", "#9932CC"),
    (-1,     "−1\nStandard (mirror)",     "#1F4E79"),
    (-1/SQRT2,"−1/√2\nEmerick Crossover", "#2E8B57"),
    (1/SQRT2,"+1/√2\nEmerick Crossover",  "#2E8B57"),
    (1,      "+1\nStandard",              "#1F4E79"),
    (PHI,    "+φ\nTranscendent",          "#9932CC"),
    (E,      "+e\nPre-DT / Indet. radius","#B22222"),
    (PI,     "+π\nDT cliff",              "#8B0000"),
]
for x, label, color in thresholds:
    if -3.4 < x < 3.4:
        ax.plot([x, x], [0.27, 0.47], color=color, linewidth=2)
        # Stagger labels above/below to avoid overlap
        if x < 0:
            ax.text(x, 0.55 + 0.30 * (abs(x) % 0.6), label, ha="center", va="bottom",
                    fontsize=8, color=color, fontweight="bold")
        else:
            ax.text(x, -0.15 - 0.30 * (x % 0.6), label, ha="center", va="top",
                    fontsize=8, color=color, fontweight="bold")

# DT cliff hard boundary at -3 (urb_696)
ax.plot([-3, -3], [0.20, 0.55], color="#8B0000", linewidth=4, linestyle="--",
        label="DT cliff at −3 (urb_696)")
# Verisyn saturation cap at +2 (urb_714)
ax.plot([2, 2], [0.20, 0.55], color="#1F4E79", linewidth=4, linestyle="--",
        label="Verisyn saturation cap at +2 (urb_714)")

# Zone labels along the band
zones = [
    (-3.15, "DT", "#8B0000"),
    (-2.85, "Ultra\nterrible", "#B22222"),
    (-1.7,  "False", "#1F4E79"),
    (-1.05, "Soft\nFalse", "#4A6FA5"),
    (-0.18, "Indet.", "#B8860B"),
    (0.7,   "Soft True", "#4A6FA5"),
    (1.5,   "True", "#1F4E79"),
    (2.85,  "Ultra-great\n(Transcendent)", "#9932CC"),
]
for x, label, color in zones:
    if -3.4 < x < 3.4:
        ax.text(x, 0.91, label, ha="center", va="center", fontsize=8.5,
                color=color, fontweight="bold",
                bbox=dict(boxstyle="round,pad=0.25", facecolor="white",
                          edgecolor=color, alpha=0.85))

ax.set_yticks([])
ax.set_xticks([-3, -PI, -E, -PHI, -1, -1/SQRT2, 0, 1/SQRT2, 1, PHI, E, PI, 2])
ax.set_xticklabels(["−3", "−π", "−e", "−φ", "−1", "−1/√2", "0", "+1/√2",
                    "+1", "+φ", "+e", "+π", "+2"], fontsize=8)
ax.set_xlabel("Permissibility Distribution (real-axis scalar)", fontsize=11)
ax.set_title("Figure 1 — PD Graph (Perfect-Fifth (−3, 2) scalar): the operational projection.\n"
             "Brandon-canonical thresholds ±1, ±φ, ±e, ±π + Emerick Crossover ±1/√2 + "
             "Indeterminate sub-range (−2/3, +1/3).", fontsize=10)
ax.legend(loc="upper center", bbox_to_anchor=(0.5, -0.20), ncol=4, fontsize=8, frameon=False)
ax.spines["top"].set_visible(False); ax.spines["right"].set_visible(False)
ax.spines["left"].set_visible(False); ax.spines["bottom"].set_visible(False)
plt.tight_layout()
plt.savefig(os.path.join(OUT, "fig1_pd_graph_real_axis.png"), dpi=140, bbox_inches="tight")
plt.close()
print("✓ fig1_pd_graph_real_axis.png")

# -----------------------------------------------------------------------------
# Figure 2: PD Crystal — full complex-plane PD/DT geometry
# -----------------------------------------------------------------------------
fig, ax = plt.subplots(figsize=(10, 10))
lim = 3.6
ax.set_xlim(-lim, lim); ax.set_ylim(-lim, lim)
ax.set_aspect("equal")

# Real-axis = PD principal axis
ax.axhline(0, color="black", linewidth=1.5, zorder=2)
# Imaginary axis = DT/Tralse axis (RATIFIED Pass 8.2)
ax.axvline(0, color="#8B0000", linewidth=1.5, linestyle="-.", zorder=2)
ax.text(0.08, lim - 0.2, "DT/Tralse axis\n(imaginary)", color="#8B0000", fontsize=9,
        fontweight="bold")
ax.text(lim - 0.2, -0.18, "PD principal axis (real)", color="black", fontsize=9,
        fontweight="bold", ha="right")

# Threshold rings (centered at origin)
ring_specs = [
    (1,      "±1 Standard",         "#1F4E79", "-"),
    (PHI,    "±φ Transcendent",     "#9932CC", "-"),
    (E,      "±e Pre-DT / |PD|=e Principal Indeterminate Region radius", "#B22222", "-"),
    (PI,     "±π DT cliff",         "#8B0000", "--"),
]
theta = np.linspace(0, 2*np.pi, 400)
for r, label, color, ls in ring_specs:
    ax.plot(r*np.cos(theta), r*np.sin(theta), color=color, linewidth=1.5,
            linestyle=ls, label=label, alpha=0.85)

# Principal Indeterminate Region (RATIFIED rename) = |PD| < e disc (filled)
ax.fill(E*np.cos(theta), E*np.sin(theta), color="#FFE9A8", alpha=0.30, zorder=0)

# Transcendent Ring (RATIFIED rename) annulus φ < |PD| < e
ax.fill(np.concatenate([E*np.cos(theta), PHI*np.cos(theta[::-1])]),
        np.concatenate([E*np.sin(theta), PHI*np.sin(theta[::-1])]),
        color="#E0C3F0", alpha=0.35, zorder=0)

# Emerick Crossover ±1/√2 marker on real axis
for x in [-1/SQRT2, 1/SQRT2]:
    ax.plot(x, 0, marker="D", markersize=10, color="#2E8B57", zorder=5)
ax.text(1/SQRT2, -0.22, "Emerick Crossover\n+1/√2 ≈ 0.707", color="#2E8B57",
        fontsize=8, ha="center", fontweight="bold")
ax.text(-1/SQRT2, -0.22, "Emerick Crossover\n−1/√2", color="#2E8B57",
        fontsize=8, ha="center", fontweight="bold")

# Zone annotations on the geometry
ax.text(0, 0.45, "Principal\nIndeterminate\nRegion\n|PD| < e",
        ha="center", va="center", fontsize=10, color="#8B6914", fontweight="bold",
        bbox=dict(boxstyle="round", facecolor="#FFF8DC", alpha=0.8))
ax.text(2.15, 1.8, "Transcendent\nRing\n(φ < |PD| < e)",
        ha="center", va="center", fontsize=9, color="#6A006A", fontweight="bold",
        bbox=dict(boxstyle="round", facecolor="#F5E6FA", alpha=0.8))
ax.text(0, 3.30, "Deep DT zone\n(beyond π cliff)",
        ha="center", va="center", fontsize=9, color="#5C0000", fontweight="bold",
        bbox=dict(boxstyle="round", facecolor="#FFE5E5", alpha=0.8))

# Pure-imaginary DT marker (urb_733): DT lives on the imaginary axis
ax.plot(0, 1.5, marker="*", markersize=18, color="#8B0000", zorder=6)
ax.annotate("DT example\n(pure τ-without-δ)", xy=(0, 1.5), xytext=(1.5, 1.7),
            fontsize=8.5, color="#8B0000",
            arrowprops=dict(arrowstyle="->", color="#8B0000"))

# Brandon-canonical anchor citation
ax.text(-lim+0.1, -lim+0.1,
        "Brandon-canonical (Pass 8 RECANONIZED)\nAnchors: urb_728, urb_733, urb_734, urb_736",
        fontsize=7.5, color="gray", style="italic")

ax.set_title("Figure 2 — PD Crystal: full complex-plane PD/DT geometry.\n"
             "Real axis = PD principal axis; imaginary axis = DT/Tralse axis.\n"
             "Principal Indeterminate Region (|PD|<e disc) + Transcendent Ring (φ<|PD|<e annulus) + ±π DT cliff.",
             fontsize=11)
ax.legend(loc="upper right", fontsize=8, framealpha=0.9)
ax.grid(True, alpha=0.2)
ax.set_xlabel("Re(PD)"); ax.set_ylabel("Im(PD) — DT/Tralse axis")
plt.tight_layout()
plt.savefig(os.path.join(OUT, "fig2_pd_crystal_complex_plane.png"), dpi=140, bbox_inches="tight")
plt.close()
print("✓ fig2_pd_crystal_complex_plane.png")

# -----------------------------------------------------------------------------
# Figure 3: TI Sigma Crystal — 57-vertex polytope (urb_645)
# -----------------------------------------------------------------------------
fig, ax = plt.subplots(figsize=(11, 11))
lim2 = 3.6
ax.set_xlim(-lim2, lim2); ax.set_ylim(-lim2, lim2)
ax.set_aspect("equal")

C_const = 0.437
T_const = 0.934
ring_data = [
    (C_const, 6,  "Ring 1 — C ≈ 0.437 (Emerick Constant)",     "#1F4E79"),
    (T_const, 6,  "Ring 2 — T ≈ 0.934 (Emerick BEC threshold)", "#4A6FA5"),
    (1.0,     8,  "Ring 3 — 1 (Unit existence)",                "#2E8B57"),
    (SQRT2,   8,  "Ring 4 — √2 ≈ 1.414 (tritone, Bell max/√2)", "#B22222"),
    (PHI,     8,  "Ring 5 — φ ≈ 1.618 (golden ratio)",          "#9932CC"),
    (E,       10, "Ring 6 — e ≈ 2.718 (Euler)",                 "#FF8C00"),
    (PI,      10, "Ring 7 — π ≈ 3.142 (transcendental)",        "#8B0000"),
]
theta_ref = np.linspace(0, 2*np.pi, 400)
for r, n, label, color in ring_data:
    # Ring outline
    ax.plot(r*np.cos(theta_ref), r*np.sin(theta_ref), color=color, linewidth=1,
            alpha=0.4, linestyle=":")
    # Vertices
    angles = np.linspace(0, 2*np.pi, n, endpoint=False)
    xs = r*np.cos(angles); ys = r*np.sin(angles)
    ax.scatter(xs, ys, s=90, color=color, edgecolors="black", linewidths=0.8,
               zorder=5, label=label)
# Origin vertex
ax.scatter([0], [0], s=140, color="black", marker="*", zorder=6,
           label="Origin — vacuum / 0 (1 vertex)")

ax.set_title("Figure 3 — TI Sigma Crystal (TSC): 57-vertex polytope (urb_628 / urb_645).\n"
             "Seven rings at radii {C, T, 1, √2, φ, e, π} with vertex counts {6, 6, 8, 8, 8, 10, 10} + 1 origin = 57.\n"
             "Each ring is a TI Sigma constant; rings = phase categories (Mott / FQH / Supersolid / BEC).",
             fontsize=11)
ax.legend(loc="upper left", bbox_to_anchor=(1.02, 1), fontsize=8.5, frameon=True)
ax.grid(True, alpha=0.2)
ax.set_xlabel("Re"); ax.set_ylabel("Im")
plt.tight_layout()
plt.savefig(os.path.join(OUT, "fig3_ti_sigma_crystal.png"), dpi=140, bbox_inches="tight")
plt.close()
print("✓ fig3_ti_sigma_crystal.png")

# -----------------------------------------------------------------------------
# Figure 4: Graph ↔ Crystal projection diagram
# -----------------------------------------------------------------------------
fig, axes = plt.subplots(1, 2, figsize=(15, 6.5))

# Panel A: PD Crystal (full complex plane, schematic)
ax = axes[0]
ax.set_xlim(-3.5, 3.5); ax.set_ylim(-3.5, 3.5); ax.set_aspect("equal")
for r, color in [(1, "#1F4E79"), (PHI, "#9932CC"), (E, "#B22222"), (PI, "#8B0000")]:
    ax.plot(r*np.cos(theta_ref), r*np.sin(theta_ref), color=color, linewidth=1.2, alpha=0.7)
ax.fill(E*np.cos(theta_ref), E*np.sin(theta_ref), color="#FFE9A8", alpha=0.25)
ax.axhline(0, color="black", linewidth=1)
ax.axvline(0, color="#8B0000", linewidth=1, linestyle="-.")
# Sample points on the crystal
sample_pts = [(1.2, 0.8), (-1.5, 0.4), (0.5, -1.7), (2.3, 1.1), (-0.8, -0.3)]
for x, y in sample_pts:
    ax.scatter(x, y, s=80, color="#1F4E79", edgecolors="black", zorder=5)
    ax.plot([x, x], [y, -3.4], color="gray", linewidth=0.7, linestyle=":", alpha=0.7)
    ax.scatter(x, -3.4, s=60, color="#1F4E79", edgecolors="black", zorder=5, marker="v")
ax.set_title("PD Crystal (full complex-plane object)", fontsize=11)
ax.set_xlabel("Re(PD) = PD principal axis")
ax.set_ylabel("Im(PD) = DT/Tralse axis")
ax.grid(True, alpha=0.2)

# Panel B: PD Graph (1-D projection)
ax = axes[1]
ax.set_xlim(-3.5, 3.5); ax.set_ylim(-1, 1)
ax.axhline(0, color="black", linewidth=2)
for x, label, color in [(-3, "DT cliff", "#8B0000"), (-PI, "−π", "#8B0000"),
                        (-E, "−e", "#B22222"), (-PHI, "−φ", "#9932CC"),
                        (-1, "−1", "#1F4E79"), (1, "+1", "#1F4E79"),
                        (PHI, "+φ", "#9932CC"), (E, "+e", "#B22222"),
                        (PI, "+π", "#8B0000"), (2, "+2 cap", "#1F4E79")]:
    if -3.4 < x < 3.4:
        ax.plot([x, x], [-0.15, 0.15], color=color, linewidth=2)
for x, _ in [(p[0], None) for p in sample_pts]:
    ax.scatter(x, 0, s=80, color="#1F4E79", edgecolors="black", zorder=5, marker="v")
ax.axvspan(-2/3, 1/3, ymin=0.3, ymax=0.7, color="#FFE9A8", alpha=0.6)
ax.set_yticks([])
ax.set_title("PD Graph (1-D projection onto PD principal axis)", fontsize=11)
ax.set_xlabel("PD scalar (−3, 2) — Perfect-Fifth")
ax.text(0, -0.7, "← Loses imaginary-axis (DT/Tralse) information →",
        ha="center", fontsize=10, color="gray", style="italic")

# Big projection arrow between panels
fig.text(0.50, 0.50, "→\nProject onto\nreal axis",
         ha="center", va="center", fontsize=14, fontweight="bold",
         bbox=dict(boxstyle="round", facecolor="white", edgecolor="black"))

fig.suptitle("Figure 4 — Graph ↔ Crystal projection pattern: the PD Graph (right) is the orthogonal projection\n"
             "of the PD Crystal (left) onto the real axis. Same pattern: TI Sigma Graph projects TI Sigma Crystal.",
             fontsize=12)
plt.tight_layout(rect=[0, 0, 1, 0.94])
plt.savefig(os.path.join(OUT, "fig4_graph_to_crystal_projection.png"), dpi=140, bbox_inches="tight")
plt.close()
print("✓ fig4_graph_to_crystal_projection.png")

print("\nAll 4 figures written to", OUT)

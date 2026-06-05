"""
Pass-77 B83 — GILE +/x HEM, successor to L*+E.
ILLUSTRATIVE STRUCTURAL DIAGRAMS (no data / no simulation), per #69.
fig1: L*+E -> GILE +/x HEM lineage/generalization map.
fig2: multiplicative gate vs additive residue (illustrative curves).
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import numpy as np

OUT = os.path.dirname(os.path.abspath(__file__))

CX = "#c0392b"   # multiplicative (x) -- hyperconnection
CP = "#2471a3"   # additive (+) -- substitutable
CORE = "#7d3c98"
GREY = "#566573"


def box(ax, x, y, w, h, text, fc, ec="#1b2631", fs=10, tc="white", weight="bold"):
    ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.012,rounding_size=0.02",
                                fc=fc, ec=ec, lw=1.4))
    ax.text(x + w / 2, y + h / 2, text, ha="center", va="center",
            fontsize=fs, color=tc, weight=weight, wrap=True)


def fig1():
    fig, ax = plt.subplots(figsize=(13, 8))
    ax.set_xlim(0, 13); ax.set_ylim(0, 8); ax.axis("off")
    ax.text(6.5, 7.6, "From L*+E to GILE +/\u00d7 HEM  \u2014  one \u00d7/+ switch generalizes to four",
            ha="center", fontsize=15, weight="bold", color="#1b2631")
    ax.text(6.5, 7.18, "Illustrative structural diagram (no data / no simulation) \u2014 Pass-77 B83",
            ha="center", fontsize=9.5, style="italic", color=GREY)

    # ---- LEFT: predecessor L*/+E ----
    ax.text(2.9, 6.6, "PREDECESSOR  \u2014  L*/+E  (URB #483)", ha="center",
            fontsize=11.5, weight="bold", color="#1b2631")
    box(ax, 1.0, 4.7, 3.8, 1.4,
        "L*  =  GIL core\n(G,I,L mutually conditioning,\ntightly coupled)", CORE, fs=10)
    box(ax, 1.0, 3.2, 3.8, 1.0, "+E  appended\n(separable, off-diagonal stable)", GREY, fs=10)
    box(ax, 1.0, 1.7, 1.85, 1.0, "L\u00d7E\nHyperconnection\n(both required)", CX, fs=8.6)
    box(ax, 2.95, 1.7, 1.85, 1.0, "L+E\nExistence\n(substitutable)", CP, fs=8.6)
    ax.text(2.9, 1.25, "ONE \u00d7/+ switch on the L\u2013E pair", ha="center",
            fontsize=9, color="#1b2631", weight="bold")

    # ---- arrow ----
    ax.add_patch(FancyArrowPatch((5.05, 4.0), (6.25, 4.0), arrowstyle="-|>",
                                 mutation_scale=26, lw=2.6, color="#117a65"))
    ax.text(5.65, 4.35, "generalizes", ha="center", fontsize=9.5,
            color="#117a65", weight="bold")

    # ---- RIGHT: successor GILE +/x HEM ----
    ax.text(9.7, 6.6, "SUCCESSOR  \u2014  GILE +/\u00d7 HEM  (B82\u2192B83)", ha="center",
            fontsize=11.5, weight="bold", color="#1b2631")
    rows = [
        ("G  Goodness (Four C's)", "EF = amplitude \u00d7 frequency", "\u00d7", CX, "\u03b3\u2070"),
        ("I  Intuition (accuracy+certainty)", "precision", "+", CP, "\u03b3\u00b9"),
        ("L  Love (relational valence)", "entanglement (concurrence)", "\u00d7", CX, "\u03b3\u00b2"),
        ("E  Environment (aesthetics)", "symmetry (\u27e8SWAP\u27e9)", "+", CP, "\u03b3\u00b3"),
    ]
    y0 = 5.55
    for i, (g, h, op, col, gam) in enumerate(rows):
        y = y0 - i * 1.02
        box(ax, 6.5, y, 2.95, 0.82, g, "#34495e", fs=8.3)
        # operator badge
        ax.add_patch(plt.Circle((9.75, y + 0.41), 0.22, fc=col, ec="#1b2631", lw=1.3))
        ax.text(9.75, y + 0.41, op, ha="center", va="center", fontsize=13,
                color="white", weight="bold")
        box(ax, 10.1, y, 2.7, 0.82, h, col, fs=8.3)
        ax.text(6.35, y + 0.41, gam, ha="right", va="center", fontsize=9, color=GREY)
    ax.text(9.65, 1.32,
            "\u00d7 (G,L) = hyperconnection core  \u2502  + (I,E) = substitutable layer",
            ha="center", fontsize=9, color="#1b2631", weight="bold")
    ax.text(9.65, 0.95,
            "abstract GILE = ligand  \u00b7  physical HEM = receptor  \u00b7  virtue = bound complex",
            ha="center", fontsize=8.6, style="italic", color=GREY)

    plt.tight_layout()
    p = os.path.join(OUT, "fig1_lstar_plus_e_to_gile_hem.png")
    plt.savefig(p, dpi=145, bbox_inches="tight"); plt.close()
    print("wrote", p)


def fig2():
    fig, ax = plt.subplots(figsize=(11, 7))
    hem = np.linspace(0, 1, 200)
    g_abs = 0.9  # abstract GILE held high (imagined quality is strong)

    # multiplicative (x) coupling: virtue = g_abs * hem  -> 0 at hem=0
    mult = g_abs * hem
    # additive (+) coupling: virtue = 0.5*g_abs + 0.5*hem -> retains floor at hem=0
    add = 0.5 * g_abs + 0.5 * hem

    ax.plot(hem, mult, color=CX, lw=3.2,
            label="\u00d7 coupling  (G\u2194EF, L\u2194entanglement)")
    ax.plot(hem, add, color=CP, lw=3.2, ls="--",
            label="+ coupling  (I\u2194precision, E\u2194symmetry)")

    # pure-abstraction point HEM=0
    ax.scatter([0], [0], color=CX, s=90, zorder=5)
    ax.scatter([0], [0.5 * g_abs], color=CP, s=90, zorder=5)
    ax.annotate("HEM=0 (pure abstraction):\n\u00d7 \u2192 0  =  NO full virtue",
                xy=(0, 0), xytext=(0.16, 0.12), fontsize=10, color=CX, weight="bold",
                arrowprops=dict(arrowstyle="->", color=CX, lw=1.6))
    ax.annotate("HEM=0:  + retains floor\n= Maharishi / Metta residue\n(character-building, maybe field)",
                xy=(0, 0.5 * g_abs), xytext=(0.12, 0.62), fontsize=10, color=CP, weight="bold",
                arrowprops=dict(arrowstyle="->", color=CP, lw=1.6))

    ax.axvline(0, color=GREY, lw=0.8, ls=":")
    ax.fill_between([0, 0.06], 0, 1, color="#fdebd0", alpha=0.6, zorder=0)

    ax.text(0.5, 0.93, "imagined Love alone  =  abstract L  \u00d7  (entanglement=0)  =  0",
            ha="center", fontsize=10.5, color="#1b2631", weight="bold")
    ax.text(0.5, 0.05, "Full virtue requires all 8 GILE-HEM components engaged "
            "(einstein-monotile i-cell)", ha="center", fontsize=9.5,
            style="italic", color=GREY)

    ax.set_xlabel("HEM (physical complement) engagement  \u2014  0 = imagined only, 1 = fully enacted",
                  fontsize=11)
    ax.set_ylabel("full-virtue contribution of the dimension (illustrative)", fontsize=11)
    ax.set_title("B83: multiplicative gate vs additive residue\n"
                 "why abstract Love alone is only Maharishi-grade  "
                 "(ILLUSTRATIVE \u2014 not an empirical claim)",
                 fontsize=12.5, weight="bold")
    ax.set_xlim(-0.02, 1.0); ax.set_ylim(0, 1.0)
    ax.legend(loc="center right", fontsize=10, framealpha=0.95)
    ax.grid(alpha=0.25)
    plt.tight_layout()
    p = os.path.join(OUT, "fig2_multiplicative_gate_vs_additive_residue.png")
    plt.savefig(p, dpi=145, bbox_inches="tight"); plt.close()
    print("wrote", p)


if __name__ == "__main__":
    fig1()
    fig2()
    print("B83 figures done.")

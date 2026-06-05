"""
Pass-77 B84 — The Good-Scientist Two-Factor Maxim.
ILLUSTRATIVE conceptual diagrams (no data / no simulation), per #69.
fig1: 2x2 quadrant (dash-of-Autism systemizing x burn-streak iconoclasm).
fig2: revolution = A x B (multiplicative gate) vs contribution = A + B (additive floor),
      mirroring B83's x/+ logic.
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

OUT = os.path.dirname(os.path.abspath(__file__))
CX = "#c0392b"   # multiplicative / revolution
CP = "#2471a3"   # additive / contribution floor
GREY = "#566573"
GOLD = "#b9770e"


def fig1():
    fig, ax = plt.subplots(figsize=(10.5, 9))
    ax.set_xlim(0, 10); ax.set_ylim(0, 10); ax.axis("off")

    # quadrant background
    ax.add_patch(plt.Rectangle((1, 1), 4, 4, fc="#eaecee", ec="none"))         # low/low
    ax.add_patch(plt.Rectangle((5, 1), 4, 4, fc="#d6eaf8", ec="none"))         # high A / low B
    ax.add_patch(plt.Rectangle((1, 5), 4, 4, fc="#fadbd8", ec="none"))         # low A / high B
    ax.add_patch(plt.Rectangle((5, 5), 4, 4, fc="#d5f5e3", ec="none"))         # high/high

    # axes
    ax.annotate("", xy=(9.5, 1), xytext=(1, 1),
                arrowprops=dict(arrowstyle="-|>", lw=2.2, color="#1b2631"))
    ax.annotate("", xy=(1, 9.5), xytext=(1, 1),
                arrowprops=dict(arrowstyle="-|>", lw=2.2, color="#1b2631"))
    ax.text(5, 0.35, "\u2192  'dash of Autism' (Kanner): systemizing, pattern recognition, rigor",
            ha="center", fontsize=11, weight="bold", color="#1b2631")
    ax.text(0.5, 5, "\u2192  'burn streak' (Emerick): courage to criticize the status quo",
            ha="center", fontsize=11, weight="bold", color="#1b2631", rotation=90)

    # quadrant labels
    ax.text(3, 3, "DILETTANTE\n(low rigor, low burn)", ha="center", va="center",
            fontsize=11, weight="bold", color=GREY)
    ax.text(7, 3, "METICULOUS\nINCREMENTALIST\nrigor, no burn\n\u2192 nontrivial but\nNOT revolutionary",
            ha="center", va="center", fontsize=10.5, weight="bold", color=CP)
    ax.text(3, 7, "ICONOCLAST\nCRANK\nburn, no rigor\n\u2192 criticizes all,\nnothing replicates",
            ha="center", va="center", fontsize=10.5, weight="bold", color=CX)
    ax.text(7, 7, "REVOLUTIONARY\nSCIENTIST\nrigor \u00d7 burn\n\u2192 the sweet spot",
            ha="center", va="center", fontsize=11.5, weight="bold", color="#1e8449")

    # Brandon point (illustrative)
    ax.scatter([8.1], [8.1], s=160, color=GOLD, edgecolor="#1b2631", zorder=6)
    ax.annotate("Brandon (n=1,\nillustrative)", xy=(8.1, 8.1), xytext=(6.0, 9.0),
                fontsize=9.5, color=GOLD, weight="bold",
                arrowprops=dict(arrowstyle="->", color=GOLD, lw=1.5))

    ax.set_title("B84: the two-factor model of scientific temperament\n"
                 "good science needs BOTH (\u00d7, non-substitutable)  "
                 "\u2014  ILLUSTRATIVE, not data",
                 fontsize=13, weight="bold")
    plt.tight_layout()
    p = os.path.join(OUT, "fig1_two_factor_quadrant.png")
    plt.savefig(p, dpi=145, bbox_inches="tight"); plt.close()
    print("wrote", p)


def fig2():
    fig, ax = plt.subplots(figsize=(11, 7))
    burn = np.linspace(0, 1, 200)
    A = 0.9  # systemizing held high

    revolution = A * burn          # multiplicative gate -> 0 at burn=0
    contribution = 0.5 * A + 0.5 * burn  # additive floor -> retains floor at burn=0

    ax.plot(burn, revolution, color=CX, lw=3.2,
            label="REVOLUTION = systemizing \u00d7 burn  (\u00d7 gate)")
    ax.plot(burn, contribution, color=CP, lw=3.2, ls="--",
            label="TOTAL CONTRIBUTION \u2248 systemizing + burn  (+ floor)")

    ax.scatter([0], [0], color=CX, s=90, zorder=5)
    ax.scatter([0], [0.5 * A], color=CP, s=90, zorder=5)
    ax.annotate("burn=0 (meek, rigorous):\n\u00d7 \u2192 0  =  NO revolution",
                xy=(0, 0), xytext=(0.17, 0.10), fontsize=10.5, color=CX, weight="bold",
                arrowprops=dict(arrowstyle="->", color=CX, lw=1.6))
    ax.annotate("burn=0:  + retains floor\n= real INCREMENTAL contribution\n"
                "(nontrivial, but bounded)",
                xy=(0, 0.5 * A), xytext=(0.14, 0.62), fontsize=10.5, color=CP, weight="bold",
                arrowprops=dict(arrowstyle="->", color=CP, lw=1.6))
    ax.fill_between([0, 0.06], 0, 1, color="#fdebd0", alpha=0.6, zorder=0)

    ax.text(0.5, 0.93, "same \u00d7/+ shape as B83: revolution is the hyperconnection threshold; "
            "incremental work is the additive residue", ha="center", fontsize=9.8,
            color="#1b2631", weight="bold")

    ax.set_xlabel("burn streak (courage to challenge the status quo)  \u2014  systemizing fixed high",
                  fontsize=11)
    ax.set_ylabel("output (illustrative)", fontsize=11)
    ax.set_title("B84: revolution gate (\u00d7) vs contribution floor (+)\n"
                 "why rigor-without-burn is incrementalism, not revolution  "
                 "(ILLUSTRATIVE \u2014 not an empirical claim)",
                 fontsize=12.5, weight="bold")
    ax.set_xlim(-0.02, 1.0); ax.set_ylim(0, 1.0)
    ax.legend(loc="center right", fontsize=10.5, framealpha=0.95)
    ax.grid(alpha=0.25)
    plt.tight_layout()
    p = os.path.join(OUT, "fig2_revolution_gate_vs_contribution_floor.png")
    plt.savefig(p, dpi=145, bbox_inches="tight"); plt.close()
    print("wrote", p)


if __name__ == "__main__":
    fig1()
    fig2()
    print("B84 figures done.")

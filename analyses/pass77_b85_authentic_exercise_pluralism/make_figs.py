"""
Pass-77 B85 — Authentic-Exercise Pluralism + adaptation-usage mismatch.
ILLUSTRATIVE conceptual diagrams (no data / no simulation), per #69.
Evidence/accessibility positions are the AUTHOR'S coarse qualitative reading of
current literature (ordinal, NOT measured).
fig1: modality landscape (accessibility x evidence-strength), bubble = breadth-of-benefit.
fig2: adaptation-usage mismatch 2x2 (running, yoga, weightlifting placed).
"""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = os.path.dirname(os.path.abspath(__file__))
CONV = "#c0392b"   # conventional exercise
ALT = "#1e8449"    # alternatives
HYPE = "#b9770e"   # emerging/hyped
COMBO = "#6c3483"  # combinations


def fig1():
    # name: (accessibility 0-10, evidence 0-10, breadth(bubble), color, tier)
    mods = {
        "Brisk walking":      (9.5, 8.6, 900, ALT,  "strong"),
        "Sauna\n(dry/IR)":    (6.5, 7.8, 800, ALT,  "strong-ish"),
        "Yoga":               (8.3, 6.2, 850, ALT,  "moderate"),
        "Breathwork":         (9.2, 5.6, 700, ALT,  "moderate/understudied"),
        "Humming / OM":       (9.4, 5.2, 600, ALT,  "moderate"),
        "Ecstatic dance":     (8.0, 4.4, 650, ALT,  "weak-direct"),
        "Cold showers":       (9.0, 3.8, 520, HYPE, "emerging/hyped"),
        "Whole-body EMS":     (3.3, 4.0, 480, HYPE, "mixed (rhabdo risk)"),
        "Red / NIR light":    (3.6, 3.2, 520, HYPE, "mixed/overhyped"),
        "Conv. weights\n+ cardio": (4.2, 8.2, 1000, CONV, "strong but NARROW slice"),
    }
    fig, ax = plt.subplots(figsize=(12.5, 8.5))
    for name, (x, y, s, c, tier) in mods.items():
        ax.scatter(x, y, s=s, color=c, alpha=0.55, edgecolor="#1b2631", lw=1.3, zorder=3)
        ax.annotate(name, (x, y), ha="center", va="center", fontsize=8.6,
                    weight="bold", color="#1b2631", zorder=5)

    # combinations frontier arrow (super-additivity hypothesis, ties to B83/B84 x-logic)
    ax.annotate("COMBINATIONS\n(x super-additive?\nB83/B84 ×-logic)",
                xy=(9.0, 9.3), xytext=(5.6, 9.5),
                fontsize=10, weight="bold", color=COMBO,
                arrowprops=dict(arrowstyle="-|>", lw=2.4, color=COMBO))

    ax.axvspan(7.5, 10, color="#eafaf1", alpha=0.5, zorder=0)
    ax.text(8.75, 0.6, "high-accessibility zone\n(free / low-friction)", ha="center",
            fontsize=9, color=ALT, weight="bold")

    ax.set_xlabel("accessibility / ease  (free & low-friction \u2192)", fontsize=12)
    ax.set_ylabel("breadth + strength of healthspan benefit\n(author's coarse qualitative read \u2014 ordinal, NOT measured)",
                  fontsize=11)
    ax.set_title("B85: the authentic-exercise modality landscape\n"
                 "conventional weights+cardio = STRONG but a NARROW, low-accessibility slice; "
                 "alternatives cluster high-accessibility  (ILLUSTRATIVE)",
                 fontsize=12.5, weight="bold")
    ax.set_xlim(2, 10.6); ax.set_ylim(0, 10.4)
    ax.grid(alpha=0.25)
    # legend
    from matplotlib.lines import Line2D
    leg = [Line2D([0], [0], marker='o', color='w', markerfacecolor=CONV, markersize=13, label='conventional (glorified)'),
           Line2D([0], [0], marker='o', color='w', markerfacecolor=ALT, markersize=13, label='alternatives (strong\u2013moderate)'),
           Line2D([0], [0], marker='o', color='w', markerfacecolor=HYPE, markersize=13, label='emerging / hyped (thin evidence)')]
    ax.legend(handles=leg, loc="lower right", fontsize=9.5, framealpha=0.95)
    plt.tight_layout()
    p = os.path.join(OUT, "fig1_modality_landscape.png")
    plt.savefig(p, dpi=145, bbox_inches="tight"); plt.close()
    print("wrote", p)


def fig2():
    fig, ax = plt.subplots(figsize=(11, 9))
    ax.set_xlim(0, 10); ax.set_ylim(0, 10); ax.axis("off")

    ax.add_patch(plt.Rectangle((1, 1), 4, 4, fc="#eaecee", ec="none"))
    ax.add_patch(plt.Rectangle((5, 1), 4, 4, fc="#d6eaf8", ec="none"))
    ax.add_patch(plt.Rectangle((1, 5), 4, 4, fc="#fdebd0", ec="none"))   # the puzzle quadrant
    ax.add_patch(plt.Rectangle((5, 5), 4, 4, fc="#d5f5e3", ec="none"))

    ax.annotate("", xy=(9.5, 1), xytext=(1, 1), arrowprops=dict(arrowstyle="-|>", lw=2.2, color="#1b2631"))
    ax.annotate("", xy=(1, 9.5), xytext=(1, 1), arrowprops=dict(arrowstyle="-|>", lw=2.2, color="#1b2631"))
    ax.text(5, 0.35, "\u2192  ancestral evolutionary direct-use of the activity", ha="center",
            fontsize=11.5, weight="bold", color="#1b2631")
    ax.text(0.45, 5, "\u2192  degree of bodily adaptation / attunement", ha="center",
            fontsize=11.5, weight="bold", color="#1b2631", rotation=90)

    ax.text(7, 7, "ADAPTED & USED\n(uncontroversial:\nwalking, throwing,\ncarrying, climbing)",
            ha="center", va="center", fontsize=10.5, weight="bold", color="#1e8449")
    ax.text(3, 3, "neither adapted\nnor used", ha="center", va="center",
            fontsize=10.5, weight="bold", color="#566573")
    ax.text(7, 3, "used but low\nspecial-adaptation", ha="center", va="center",
            fontsize=10, weight="bold", color="#2471a3")
    ax.text(3, 8.4, "THE MISMATCH QUADRANT\nhigh adaptation, low (apparent) direct-use\n"
            "\u2192 resolve via: (A) deny mismatch (ERH) /\n(B) exaptation / (C) cultural post-tuning + survivorship",
            ha="center", va="center", fontsize=9.6, weight="bold", color=HYPE)

    # placed items
    ax.scatter([2.6], [7.2], s=150, color="#c0392b", edgecolor="#1b2631", zorder=6)
    ax.annotate("Endurance RUNNING\n(RUN-1) \u2014 but ERH says\nuse was HIGH \u2192 may shift right",
                xy=(2.6, 7.2), xytext=(1.3, 6.0), fontsize=8.8, weight="bold", color="#c0392b",
                arrowprops=dict(arrowstyle="->", color="#c0392b", lw=1.4))
    ax.scatter([3.7], [8.0], s=150, color="#6c3483", edgecolor="#1b2631", zorder=6)
    ax.annotate("YOGA kriyas/mudras\n(YGA-1) \u2014 cultural post-tuning\n+ survivorship (cleanest)",
                xy=(3.7, 8.0), xytext=(3.9, 6.4), fontsize=8.8, weight="bold", color="#6c3483",
                arrowprops=dict(arrowstyle="->", color="#6c3483", lw=1.4))
    ax.scatter([3.0], [5.6], s=150, color="#b9770e", edgecolor="#1b2631", zorder=6)
    ax.annotate("Barbell HYPERTROPHY\n\u2014 evolutionarily NOVEL too:\nno special claim to 'natural'",
                xy=(3.0, 5.6), xytext=(4.6, 4.9), fontsize=8.8, weight="bold", color="#b9770e",
                arrowprops=dict(arrowstyle="->", color="#b9770e", lw=1.4))

    ax.set_title("B85: the Adaptation\u2013Usage Mismatch\n"
                 "running, yoga, AND weightlifting all sit off the diagonal  "
                 "(ILLUSTRATIVE \u2014 placements are conceptual)",
                 fontsize=12.5, weight="bold")
    plt.tight_layout()
    p = os.path.join(OUT, "fig2_adaptation_usage_mismatch.png")
    plt.savefig(p, dpi=145, bbox_inches="tight"); plt.close()
    print("wrote", p)


if __name__ == "__main__":
    fig1()
    fig2()
    print("B85 figures done.")

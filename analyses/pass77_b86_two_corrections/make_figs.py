import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch

# ---------- Fig 1: persistence-hunting evidence balance (corrected) ----------
fig, ax = plt.subplots(figsize=(10.5, 6.6))
points = [
    ("Persistence hunting is\nethnographically RARE", 0.78),
    ("Occurs ONLY in flat/arid env.\n(Outback, SW US, Kalahari);\nhumans evolved in WET\nsavanna-woodlands", 0.86),
    ("Pickering & Bunn 2007\nexplicitly argue AGAINST ERH", 0.82),
    ("Requires advanced TRACKING\nearly Homo may have lacked", 0.70),
    ("Early Homo could SCAVENGE\nin wooded areas \u2014 didn't\nNEED endurance running", 0.74),
]
y = [4.6, 3.6, 2.6, 1.6, 0.6]
for (label, lean), yy in zip(points, y):
    ax.text(0.02, yy, label, va="center", ha="left", fontsize=9.5)
    ax.barh(yy, lean, left=4.3, height=0.42, color="#5B8C5A", alpha=0.85)
    ax.text(4.3 + lean + 0.03, yy, "\u2192 leans RARE/exaptation", va="center",
            ha="left", fontsize=8.5, color="#2f5e2e", style="italic")
ax.axvline(4.3, color="#888", lw=1)
ax.text(4.3, 5.25, "each cited point \u2192", ha="center", fontsize=9, color="#555")
ax.text(5.6, 5.25, "supports Brandon's read", ha="center", fontsize=9,
        color="#2f5e2e", fontweight="bold")
ax.set_xlim(0, 6.4); ax.set_ylim(0, 5.6)
ax.set_yticks([]); ax.set_xticks([])
for s in ["top", "right", "left", "bottom"]:
    ax.spines[s].set_visible(False)
ax.set_title("B86 Correction 1: the cited 'refutation' is CONSISTENT with rarity/exaptation\n"
             "ERH is CONTESTED, not settled mainstream \u2014 the evidence leans toward Brandon  (ILLUSTRATIVE)",
             fontsize=11.5, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b86_two_corrections/fig1_running_evidence_balance.png", dpi=130)
print("wrote fig1")

# ---------- Fig 2: truth-vs-existence gap applied to exercise ----------
fig, ax = plt.subplots(figsize=(10.5, 6.8))
# x = toughness / single-axis salient output (muscle aesthetics); y = all-things-considered GILE-HEM value
items = [
    ("Heavy lifting", 9.2, 6.6, "#C0392B"),
    ("Whole-body EMS", 6.3, 7.0, "#E08E0B"),
    ("Load-bearing yoga", 4.4, 7.4, "#2E7D5B"),
    ("Brisk walking", 3.0, 8.2, "#2E7D5B"),
    ("Sauna", 2.2, 7.6, "#2E7D5B"),
]
for name, x, yv, c in items:
    ax.scatter(x, yv, s=820, color=c, alpha=0.85, edgecolor="white", zorder=3)
    ax.text(x, yv, name, ha="center", va="center", fontsize=8.6,
            color="white", fontweight="bold", zorder=4)
ax.annotate("MAXIMIZES the toughness /\nsalient-output axis\n(muscle size, aesthetics)\n\u2014 but NOT the optimum",
            xy=(9.2, 6.6), xytext=(7.0, 3.2), fontsize=9, color="#C0392B",
            ha="center", arrowprops=dict(arrowstyle="->", color="#C0392B", lw=1.6))
ax.annotate("'GOOD ENOUGH' & far more\naccessible \u2192 can WIN on the\nall-things-considered axis\n(existence competes w/ toughness)",
            xy=(4.4, 7.4), xytext=(2.2, 4.4), fontsize=9, color="#2E7D5B",
            ha="center", arrowprops=dict(arrowstyle="->", color="#2E7D5B", lw=1.6))
ax.axhline(7.0, color="#999", ls="--", lw=1)
ax.text(9.6, 7.08, "GILE-HEM 'best' band", ha="right", fontsize=8.5, color="#555")
ax.set_xlabel("toughness / single salient output  (e.g. muscle hypertrophy, aesthetics)  \u2192", fontsize=10)
ax.set_ylabel("all-things-considered GILE-HEM value\n(health + accessibility + adherence + safety)  \u2192", fontsize=10)
ax.set_xlim(1, 10.2); ax.set_ylim(2.5, 9.2)
ax.grid(alpha=0.25)
ax.set_title("B86 Correction 2: GTT-1 truth-vs-existence \u2014 the BEST option is NOT the TOUGHEST\n"
             "'most studied / most salient output' \u2260 'irreplaceable'  (ILLUSTRATIVE \u2014 positions conceptual)",
             fontsize=11.5, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b86_two_corrections/fig2_truth_vs_existence_gap.png", dpi=130)
print("wrote fig2")
print("B86 figures done.")

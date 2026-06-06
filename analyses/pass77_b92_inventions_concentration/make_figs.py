import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import json

with open("analyses/pass77_b92_inventions_concentration/results.json") as f:
    R = json.load(f)
S = R["summary"]

# ---------- Fig 1: concentration (log scale) ----------
fig, ax = plt.subplots(figsize=(11.0, 5.6))
labels = ["Humans ever born\n(~117 billion)", "Currently living\n(~8.1 billion)",
          "Distinct named\nindividuals (top-90)", "Distinct catalysts\n(top-90)"]
vals = [S["humans_ever_lived"], S["currently_living"],
        S["n_distinct_named_individuals"], S["n_distinct_catalysts"]]
colors = ["#9aa7b5", "#7d8fa3", "#2E7D5B", "#1e5e40"]
y = range(len(labels))
ax.barh(list(y), vals, color=colors, edgecolor="k", lw=0.5)
ax.set_xscale("log")
ax.set_xlim(10, 5e11)
ax.set_yticks(list(y)); ax.set_yticklabels(labels, fontsize=9.5)
ax.invert_yaxis()
for i, v in enumerate(vals):
    ax.text(v * 1.4, i, f"{int(v):,}", va="center", fontsize=9, fontweight="bold")
ax.set_xlabel("number of people (log scale)", fontsize=10)
one_in = S["one_in_X_humans_ever__named"]
ax.set_title("B92 Fig 1: ~80\u2013125 people catalyzed 90 of ~100 top well-being inventions\n"
             f"\u2248 1 in {one_in/1e6:.0f} million of all humans ever born  "
             f"(~{S['pct_of_humans_ever__named']*1e7:.2f}\u00d710\u207b\u2077 %)",
             fontsize=11, fontweight="bold")
for sp in ["top", "right"]:
    ax.spines[sp].set_visible(False)
fig.tight_layout()
fig.savefig("analyses/pass77_b92_inventions_concentration/fig1_concentration.png", dpi=130)
print("wrote fig1")

# ---------- Fig 2: Fleiss kappa + hybrid Indeterminate-True ----------
fig, (axL, axR) = plt.subplots(1, 2, figsize=(13.0, 5.8))

# left: importance marginals + kappa
m = S["category_marginals_0_1_2"]
bars = axL.bar(["0\nnot top-tier", "1\nhighly signif.", "2\nworld-historic"],
               [x * 100 for x in m], color=["#c7ccd1", "#7fa8c9", "#2E7D5B"], edgecolor="k")
for b, v in zip(bars, m):
    axL.text(b.get_x() + b.get_width()/2, v*100 + 1.2, f"{v*100:.1f}%", ha="center", fontsize=9.5, fontweight="bold")
axL.set_ylabel("share of pooled rater scores (%)", fontsize=9.5)
axL.set_ylim(0, 75)
axL.set_title(f"3 raters (gpt-5, claude-opus-4-1, claude-haiku-4-5), N={S['n_inventions']}\n"
              f"Fleiss \u03ba = {S['fleiss_kappa']:.3f}  ({S['kappa_interp']} agreement)",
              fontsize=10, fontweight="bold")
axL.text(0.5, -0.235,
         "#69: \u03ba is only 'fair' \u2014 importance ranking is genuinely subjective.\n"
         "But the TOP-TIER head of the list is robust, and the concentration\n"
         "result holds across any reasonable top-90 cut.",
         transform=axL.transAxes, ha="center", fontsize=8.4, color="#444")
for sp in ["top", "right"]:
    axL.spines[sp].set_visible(False)

# right: hybrid I-True resolution
axR.axis("off"); axR.set_xlim(0, 10); axR.set_ylim(0, 10)
axR.text(5, 9.4, "The 'great man vs. followers' debate \u2014 resolved",
         ha="center", fontsize=11.5, fontweight="bold")
rows = [
    ("\u201cAt least one catalyst is causally necessary\u201d", "TRUE", "#cfe6d6", "#1e5e40",
     "counterfactual: no Jenner-class catalyst \u2192 no smallpox vaccine then (CTC-1-S)"),
    ("\u201cONLY the catalyst matters\u201d (exclusivity)", "FALSE", "#f0c9c2", "#7a1d12",
     "followers/co-developers are also necessary to realize + scale the benefit"),
    ("\u201cCatalyst + followers both necessary\u201d", "TRUE", "#cfe6d6", "#1e5e40",
     "necessity is not exclusive \u2014 multiple necessary causes coexist"),
]
yv = 7.6
for claim, label, fc, tc, note in rows:
    axR.add_patch(plt.Rectangle((0.3, yv-0.55), 9.4, 1.5, fc=fc, ec="k", lw=1.0, alpha=0.9))
    axR.text(0.6, yv+0.55, claim, fontsize=9.4, fontweight="bold", va="center")
    axR.text(9.4, yv+0.55, label, fontsize=11, fontweight="bold", color=tc, ha="right", va="center")
    axR.text(0.6, yv-0.1, note, fontsize=7.8, color="#333", va="center")
    yv -= 2.05
axR.add_patch(plt.Rectangle((0.3, 0.5), 9.4, 1.4, fc="#e8eef5", ec="#2E7D5B", lw=1.6))
axR.text(5, 1.2, "TI Sigma answer = HYBRID Indeterminate\u2013True:  BOTH the individual AND the\n"
                 "movement \u2014 and there is no contradiction in saying so.",
         ha="center", fontsize=9.2, fontweight="bold", color="#1e5e40")
axR.set_title("Hybrid I\u2013True (MR Truth Labels)", fontsize=10, fontweight="bold")

fig.tight_layout()
fig.savefig("analyses/pass77_b92_inventions_concentration/fig2_kappa_and_hybrid_truth.png", dpi=130)
print("wrote fig2"); print("B92 figures done.")

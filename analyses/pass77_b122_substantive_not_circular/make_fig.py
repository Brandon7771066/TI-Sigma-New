"""Figure for Pass-77 B122 -- contamination is universal (substantive, not circular)."""
import json
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(HERE, "contamination_results.json")))

d1, d2, d3 = d["D1_substantive_blind_predictors"], d["D2_contamination_is_universal"], d["D3_contamination_sweep"]

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4.6))

# Left: blind vs contaminated, g and GILE
g_blind = d1["auc_g_blind_like_g_predicts_income"]
gile_blind = d1["auc_GILE_blind_constituent_traits_to_truth"]
g_con = d2["auc_g_contaminated"]
gile_con = d2["auc_GILE_contaminated"]
x = np.arange(2)
w = 0.36
b1 = ax1.bar(x - w/2, [g_blind, gile_blind], w, label="BLIND (substantive)", color="#4f81bd")
b2 = ax1.bar(x + w/2, [g_con, gile_con], w, label="CONTAMINATED (hindsight)", color="#c0504d")
for bars in (b1, b2):
    for b in bars:
        ax1.text(b.get_x() + b.get_width()/2, b.get_height() + 0.012,
                 f"{b.get_height():.3f}", ha="center", fontsize=9)
ax1.axhline(0.5, ls=":", color="k", lw=1)
ax1.set_xticks(x)
ax1.set_xticklabels(["generic g\n(like g->income)", "GILE\n(trait composite)"])
ax1.set_ylabel("AUC (truth discrimination)")
ax1.set_ylim(0.4, 1.08)
ax1.set_title("Same hindsight sin inflates BOTH to ~1.0\n=> artifact is MEASUREMENT, not GILE's definition")
ax1.legend(fontsize=9, loc="lower right")

# Right: contamination sweep
cs = [s["contamination"] for s in d3["sweep"]]
ag = [s["auc_g"] for s in d3["sweep"]]
aG = [s["auc_GILE"] for s in d3["sweep"]]
ax2.plot(cs, ag, "o-", color="#c0504d", label="generic g")
ax2.plot(cs, aG, "s-", color="#4f81bd", label="GILE composite")
ax2.axhline(1.0, ls=":", color="k", lw=1)
ax2.set_xlabel("hindsight contamination strength")
ax2.set_ylabel("AUC")
ax2.set_title("Contamination response is construct-agnostic\n(both climb toward 1.0)")
ax2.legend(fontsize=9, loc="lower right")
ax2.set_ylim(0.5, 1.04)

fig.tight_layout()
fig.savefig(os.path.join(HERE, "fig_contamination_is_universal.png"), dpi=130)
plt.close(fig)
print("wrote fig_contamination_is_universal.png")

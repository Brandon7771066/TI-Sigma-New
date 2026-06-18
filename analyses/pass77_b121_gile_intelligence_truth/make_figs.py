"""Figures for Pass-77 B121 GILE-Intelligence Truth-Tracking (GIT-1)."""
import json
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(HERE, "gile_intelligence_results.json")))

base = d["meta"]["realized_base_rate"]
q1 = d["Q1_generic_g_weak"]
q2 = d["Q2_prospective_GILE_strong"]
q3a = d["Q3a_quack_paradox"]["component_means_quack_vs_sage (prospective, outcome-blind)"]
mult = d["Q3b_multiplier_GILE_lifts_resource"]
q4 = d["Q4_circularity_trap"]

# ---------------- FIG 1: g weak vs GILE strong + circularity trap ----------
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4.6))

labels = ["base\nrate", "top-Q\ngeneric g", "top-Q\nGILE", "top-decile\nGILE"]
vals = [base, q1["P_vindicated_top_quartile_g"],
        q2["P_vindicated_top_quartile_GILE"], q2["P_vindicated_top_decile_GILE"]]
colors = ["#999999", "#c0504d", "#4f81bd", "#2e5b8a"]
bars = ax1.bar(labels, vals, color=colors)
for b, v in zip(bars, vals):
    ax1.text(b.get_x() + b.get_width()/2, v + 0.006, f"{v:.3f}", ha="center", fontsize=10)
ax1.set_ylabel("P(vindicated)")
ax1.set_title("Generic g is WEAK; prospective GILE-intelligence is STRONG")
ax1.set_ylim(0, max(vals) * 1.25)

auc_lbl = ["generic g\n(IQ)", "GILE prospective\n(outcome-blind,\nFALSIFIABLE)",
           "GILE circular\n(peeks at outcome,\nUNFALSIFIABLE)"]
auc_val = [q1["auc_generic_g"], q4["auc_GILE_prospective_honest"],
           q4["auc_GILE_circular_peeks_at_outcome"]]
acolors = ["#c0504d", "#4f81bd", "#7f7f7f"]
bars = ax2.bar(auc_lbl, auc_val, color=acolors)
for b, v in zip(bars, auc_val):
    ax2.text(b.get_x() + b.get_width()/2, v + 0.01, f"{v:.3f}", ha="center", fontsize=10)
ax2.axhline(0.5, ls=":", color="k", lw=1)
ax2.set_ylabel("AUC (truth discrimination)")
ax2.set_title("The circularity trap: 'by-definition' GILE is fake 1.0")
ax2.set_ylim(0.4, 1.05)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "fig1_g_weak_gile_strong.png"), dpi=130)
plt.close(fig)

# ---------------- FIG 2: quack paradox + multiplier ------------------------
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 4.6))

comps = ["rationality_R", "creativity_C", "altruism_A", "environ_integ_E", "GILE_composite"]
short = ["Rationality", "Creativity", "Altruism", "Environ.\ninteg.", "GILE\ncomposite"]
quack = [q3a[c]["quack"] for c in comps]
sage = [q3a[c]["sage"] for c in comps]
import numpy as np
x = np.arange(len(comps))
w = 0.38
ax1.bar(x - w/2, quack, w, label="high-g QUACK (wrong)", color="#c0504d")
ax1.bar(x + w/2, sage, w, label="high-g SAGE (vindicated)", color="#4f81bd")
ax1.axhline(0, color="k", lw=0.8)
ax1.set_xticks(x)
ax1.set_xticklabels(short, fontsize=9)
ax1.set_ylabel("mean prospective score (z)")
ax1.set_title("Quack paradox: same high g, but quacks LACK GILE components")
ax1.legend(fontsize=9)

strata = ["low_GILE", "mid_GILE", "high_GILE"]
slbl = ["low GILE", "mid GILE", "high GILE"]
hi = [mult[s]["P_vindicated_high_resource"] for s in strata]
lo = [mult[s]["P_vindicated_low_resource"] for s in strata]
x = np.arange(len(strata))
ax2.bar(x - w/2, lo, w, label="low credentials+contemplation", color="#bbbbbb")
ax2.bar(x + w/2, hi, w, label="high credentials+contemplation", color="#2e5b8a")
for i, s in enumerate(strata):
    eff = mult[s]["resource_effect (hi - lo)"]
    ax2.text(i, max(hi[i], lo[i]) + 0.012, f"+{eff:.3f}", ha="center", fontsize=9)
ax2.set_xticks(x)
ax2.set_xticklabels(slbl)
ax2.set_ylabel("P(vindicated)")
ax2.set_title("Multiplier: credentials lift truth ONLY when GILE is high")
ax2.legend(fontsize=9)
fig.tight_layout()
fig.savefig(os.path.join(HERE, "fig2_quack_paradox_and_multiplier.png"), dpi=130)
plt.close(fig)

print("wrote fig1_g_weak_gile_strong.png, fig2_quack_paradox_and_multiplier.png")

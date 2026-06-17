"""B120 figures — crank-credibility conjunction. Reads the sim JSON. $0, matplotlib only."""
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = Path("analyses/pass77_b120_crank_credibility")
R = json.loads((OUT / "crank_credibility_results.json").read_text())

base = R["Q_TRUTH"]["base_rate"]
conj = R["Q_TRUTH"]["event_level_posterior_profile_rule"]
sing = R["Q_TRUTH"]["singletons_alone"]

# ---- Fig 1: two posteriors — TRUTH (weak) vs HEARING (moderate, justified) ----
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13.5, 6.0))

labels = ["base rate\n(heterodox)", "volume\nalone", "controversy\nalone",
          "credential\nalone", "intelligence\nalone", "ALL 4\ntogether"]
vals = [base,
        sing["volume"]["mean_posterior_in_profile"],
        sing["controversy"]["mean_posterior_in_profile"],
        sing["credential"]["mean_posterior_in_profile"],
        sing["intelligence"]["mean_posterior_in_profile"],
        conj]
colors = ["#888888", "#b6553f", "#b6553f", "#3b6ea5", "#3b6ea5", "#2e7d5b"]
bars = ax1.bar(labels, vals, color=colors, edgecolor="k", linewidth=0.6)
ax1.axhline(base, ls="--", color="#888", lw=1)
for b, v in zip(bars, vals):
    ax1.text(b.get_x() + b.get_width() / 2, v + 0.004, f"{v:.3f}", ha="center", fontsize=9, fontweight="bold")
ax1.set_ylabel("P(claim eventually vindicated)  —  TRUTH posterior", fontsize=10)
ax1.set_ylim(0, 0.22)
ax1.set_title("Q-TRUTH: 'is the position right?'\nWEAK→moderate — volume & controversy DON'T move it;\nonly credential+intelligence carry signal", fontsize=10.5)

# hearing panel: thresholds vs profile posterior
asy = R["Q_HEAR"]["by_asymmetry"]
ratios = list(asy.keys())
thr = [asy[r]["listen_threshold_posterior"] for r in ratios]
ax2.bar(range(len(ratios)), thr, color="#d9b310", edgecolor="k", label="listen threshold")
ax2.axhline(conj, color="#2e7d5b", lw=2.5, label=f"4-trait profile posterior = {conj:.3f}")
ax2.axhline(base, color="#888", ls="--", lw=1.5, label=f"bare base rate = {base:.3f}")
ax2.set_xticks(range(len(ratios)))
ax2.set_xticklabels([r.replace("V_to_c=", "value:cost\n") for r in ratios], fontsize=9)
ax2.set_ylabel("posterior P(vindicated) needed to justify a hearing", fontsize=10)
ax2.set_title("Q-HEAR: 'should they AT LEAST be listened to?'\nMODERATE & justified — under asymmetric payoff the profile\nclears the bar everywhere; base rate clears at ≥50:1", fontsize=10.5)
ax2.legend(fontsize=8.5, loc="upper right")
fig.suptitle("B120  CRD-1 refinement: the SAME evidence is WEAK for TRUTH but MODERATE for a HEARING (two different questions)",
             fontsize=12, fontweight="bold", y=1.00)
fig.tight_layout()
fig.savefig(OUT / "fig1_truth_weak_hearing_moderate.png", dpi=130, bbox_inches="tight")

# ---- Fig 2: survivorship / inverse-probability illusion (impressive sub-signal) ----
fig2, ax = plt.subplots(figsize=(9.2, 6.2))
b = R["Q_BIAS"]
perceived = b["illusion_perceived_P_impressive_given_celebrated_DERIVED"]
truth = b["event_level_P_vindicated_given_impressive"]
infl = b["inflation_factor_illusion_over_true"]
items = ["perceived\n(hero-only retrospective)\nP(impressive | celebrated)",
         "TRUTH\n(needs denominator)\nP(vindicated | impressive)"]
v = [perceived, truth]
bb = ax.bar(items, v, color=["#b6553f", "#2e7d5b"], edgecolor="k", linewidth=0.6)
for r, val in zip(bb, v):
    ax.text(r.get_x() + r.get_width() / 2, val + 0.02, f"{val:.3f}", ha="center", fontsize=11, fontweight="bold")
ax.set_ylim(0, 1.05)
ax.set_ylabel("apparent 'predictiveness' of the competence sub-signal", fontsize=10)
ax.set_title(f"Q-BIAS: survivorship/denominator trap (on the competence sub-signal)\nhero-only retrospective inflates the apparent effect ~{infl:.1f}x\n(derived from a disclosed fame-selection model; same trap as MEP #69 bias-sim)", fontsize=10.5)
ax.text(0.5, 0.58, "the invisible denominator =\nequally BRILLIANT, CREDENTIALED\nheterodox who were simply WRONG\n(Pauling·vit-C, Pons–Fleischmann,\nBlondlot, Montagnier, Merchants of Doubt)\n\nNB: the rare FULL 4-trait conjunction\nis NOT inflated by this mechanism",
        ha="center", va="center", fontsize=8.5, color="#8c2018",
        bbox=dict(boxstyle="round,pad=0.5", fc="#fff3f0", ec="#b6553f"))
fig2.tight_layout()
fig2.savefig(OUT / "fig2_survivorship_illusion.png", dpi=130, bbox_inches="tight")
print("wrote fig1_truth_weak_hearing_moderate.png, fig2_survivorship_illusion.png")

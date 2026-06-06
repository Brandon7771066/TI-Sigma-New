import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

# ---- Fig 1: epistemic optimum is interior (mirrors UOP/GTT-1 shape) ----
fig, ax = plt.subplots(figsize=(10.6, 6.3))
x = np.linspace(0, 1, 400)               # 0 = dismiss experts, 1 = defer fully
peak = 0.62                              # calibrated collaboration, slightly toward expertise
J = np.exp(-((x-peak)**2)/(2*0.16**2))
ax.plot(x, J, color="#2C3E70", lw=3)
ax.fill_between(x, J, color="#2C3E70", alpha=0.08)
ax.axvline(peak, color="#2E7D5B", ls="--", lw=1.6)
ax.scatter([peak],[1.0], color="#2E7D5B", zorder=5, s=70)
ax.annotate("CALIBRATED COLLABORATION\n(experts + broad literacy;\nauthority weighted, not decisive)",
            xy=(peak,1.0), xytext=(peak-0.02,0.62), ha="center", fontsize=9.2,
            color="#1e5e40", fontweight="bold")
ax.annotate("AMATEUR-SUPREMACY\n(dismiss experts)\nDunning\u2013Kruger, misinformation",
            xy=(0.04, np.exp(-((0.04-peak)**2)/(2*0.16**2))), xytext=(0.02,0.30),
            ha="left", fontsize=8.6, color="#8c2018",
            arrowprops=dict(arrowstyle="->", color="#8c2018"))
ax.annotate("HYPEREXPERTISE PARADIGM\n(defer by default;\ndon't self-educate)",
            xy=(0.97, np.exp(-((0.97-peak)**2)/(2*0.16**2))), xytext=(0.74,0.30),
            ha="left", fontsize=8.6, color="#8c2018",
            arrowprops=dict(arrowstyle="->", color="#8c2018"))
ax.text(0.5, -0.16, "Brandon's rhabdo case + Tetlock 'foxes>hedgehogs' + superforecasters all sit near the interior peak",
        ha="center", fontsize=8.4, color="#555", transform=ax.transAxes)
ax.set_xlabel("degree of deference to expert authority  \u2192", fontsize=10)
ax.set_ylabel("epistemic value  J  (accuracy of belief)", fontsize=10)
ax.set_yticks([]); ax.set_xticks([0,0.5,1.0]); ax.set_xticklabels(["dismiss","balance","defer fully"])
for s in ["top","right"]: ax.spines[s].set_visible(False)
ax.set_title("B88: the epistemic optimum is INTERIOR \u2014 both extremes lower it\n"
             "(same shape as UOP/GTT-1; authority is a real axis but never the decider)",
             fontsize=11.5, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b88_amateurism/fig1_deference_interior_optimum.png", dpi=130)
print("wrote fig1")

# ---- Fig 2: correct diagnosis needs the intersection (private info) ----
from matplotlib.patches import Circle
fig, ax = plt.subplots(figsize=(10.6, 6.3))
c1 = Circle((0.40,0.5), 0.30, color="#2C3E70", alpha=0.30)
c2 = Circle((0.66,0.5), 0.30, color="#2E7D5B", alpha=0.30)
ax.add_patch(c1); ax.add_patch(c2)
ax.text(0.24,0.83,"EXPERT knowledge\n(general / textbook)", ha="center", fontsize=10,
        fontweight="bold", color="#2C3E70")
ax.text(0.82,0.83,"PATIENT private knowledge\n(own history & behavior)", ha="center", fontsize=10,
        fontweight="bold", color="#1e5e40")
ax.text(0.27,0.5,"rhabdo physiology,\nlabs, treatment\n\n\u2717 wrong anchor:\n'54mg Concerta\ncaused it'",
        ha="center", va="center", fontsize=8.4, color="#22304f")
ax.text(0.80,0.5,"Katalyst WB-EMS\nsession +\nnext-day HIIT\n\npalpitations\nnoticed early",
        ha="center", va="center", fontsize=8.4, color="#1e5e40")
ax.text(0.53,0.5,"CORRECT\nDIAGNOSIS\n\u2713", ha="center", va="center", fontsize=11,
        fontweight="bold", color="#8c2018")
ax.annotate("self-advocacy = supplying the private datum\n+ prompting the CK test + rejecting the anchor",
            xy=(0.53,0.30), xytext=(0.53,0.05), ha="center", fontsize=9.0, color="#8c2018",
            arrowprops=dict(arrowstyle="->", color="#8c2018", lw=1.4))
ax.set_xlim(0,1.1); ax.set_ylim(0,1); ax.axis("off")
ax.set_title("B88: correct diagnosis needed the INTERSECTION \u2014 expertise alone missed it\n"
             "the patient held the decisive private information the expert could not infer",
             fontsize=11.5, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b88_amateurism/fig2_private_information.png", dpi=130)
print("wrote fig2"); print("B88 figures done.")

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

works = [
    # label, x=direction vs establishment(-1 attack .. +1 defend), y=challenges popular narrative(0..1), support(1..5)
    ("Case Against\nEducation", -0.85, 0.80, 3.0),
    ("Cracks in the\nIvory Tower", -0.75, 0.70, 3.5),
    ("Open Borders", -0.55, 0.92, 2.5),
    ("Build, Baby,\nBuild", -0.45, 0.78, 4.5),
    ("Big Business\n(defense)", +0.85, 0.88, 3.0),
]

# ---- Fig 1: contrarian empiricism, NOT anti-establishment ----
fig, ax = plt.subplots(figsize=(10.8, 6.4))
for lbl,x,y,s in works:
    col = "#8c2018" if x < 0 else "#1e5e40"
    ax.scatter(x, y, s=240, color=col, alpha=0.78, edgecolor="k", linewidth=0.6, zorder=3)
    ax.annotate(lbl, (x,y), xytext=(0,16), textcoords="offset points",
                ha="center", fontsize=8.6, fontweight="bold")
ax.axvline(0, color="#888", lw=1.2)
ax.text(-0.97, 0.02, "ATTACKS an institution / restriction", color="#8c2018", fontsize=9, fontweight="bold")
ax.text(0.97, 0.02, "DEFENDS an institution", color="#1e5e40", fontsize=9, fontweight="bold", ha="right")
ax.text(0, 1.04, "all five sit HIGH on 'challenges the popular narrative' \u2014 that, not direction, is the shared spine",
        ha="center", fontsize=8.8, color="#444")
ax.set_xlim(-1.05, 1.05); ax.set_ylim(0, 1.12)
ax.set_xlabel("direction relative to establishment  (attack \u2190 \u2192 defend)", fontsize=10)
ax.set_ylabel("degree it challenges the popular / intuitive narrative", fontsize=10)
ax.set_yticks([])
for sp in ["top","right"]: ax.spines[sp].set_visible(False)
ax.set_title("B89: the unifier is CONTRARIAN EMPIRICISM, not anti-establishment\n"
             "(Cowen DEFENDS big business \u2014 opposite direction, same evidence-over-narrative method; #69 + AA + GTT-1)",
             fontsize=11.2, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b89_heterodox_econ/fig1_contrarian_not_antiestablishment.png", dpi=130)
print("wrote fig1")

# ---- Fig 2: honest #69 calibration of empirical support ----
fig, ax = plt.subplots(figsize=(10.8, 6.0))
labels = [w[0].replace("\n"," ") for w in works]
support = [w[3] for w in works]
order = sorted(range(len(works)), key=lambda i: support[i])
labels = [labels[i] for i in order]; support=[support[i] for i in order]
colors = ["#b23a2e","#c9772b","#c9a92b","#6a9b3f","#2E7D5B"]
bars = ax.barh(labels, support, color=[colors[min(int(round(s))-1,4)] for s in support], edgecolor="k", linewidth=0.5)
for b,s in zip(bars,support):
    ax.text(s+0.06, b.get_y()+b.get_height()/2, f"{s:.1f}/5", va="center", fontsize=9, fontweight="bold")
ax.set_xlim(0,5.3); ax.set_xlabel("honest empirical support for the HEADLINE claim (agent #69 read, 1\u20135)", fontsize=10)
notes = {
 "Open Borders":"GDP-gain direction OK; 'doubling' is model-dependent",
 "Case Against Education":"signaling real; 80% magnitude contested",
 "Big Business (defense)":"careful but a deliberate defense, not neutral",
 "Cracks in the Ivory Tower":"incentive critiques strong; one-sided by design",
 "Build, Baby, Build":"closest to economist consensus (zoning\u2192price)",
}
for b,lbl in zip(bars,labels):
    ax.text(0.08, b.get_y()+b.get_height()/2, notes.get(lbl,""), va="center", fontsize=7.6, color="white", fontweight="bold")
for sp in ["top","right"]: ax.spines[sp].set_visible(False)
ax.set_title("B89: #69 calibration \u2014 endorsement \u2260 proof; the five are NOT equally settled\n"
             "(Build-Baby-Build well-supported; Open Borders' headline number is the most contested)",
             fontsize=11.2, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b89_heterodox_econ/fig2_honest_calibration.png", dpi=130)
print("wrote fig2"); print("B89 figures done.")

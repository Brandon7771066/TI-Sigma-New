import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

# ---------- Fig 1: hypertrophy bottleneck diagnosis (Oura-grounded) ----------
fig, ax = plt.subplots(figsize=(10.6, 6.2))
pillars = [
    ("Recovery / sleep",            9.0, "#2E7D5B", "Oura readiness 82.6 / sleep 82.8  \u2192  GOOD \u2014 NOT the bottleneck"),
    ("Mechanical tension /\nprogressive overload", 3.2, "#C0392B", "'easy workout, felt amazing' = sub-threshold growth stimulus  \u2192  GAP"),
    ("Caloric surplus",             2.4, "#C0392B", "TDEE ~2,525 kcal (Oura); intake UNTRACKED \u2192 likely no surplus  \u2192  GAP"),
    ("Protein intake",              4.0, "#E08E0B", "untracked; target ~1.6\u20132.2 g/kg/day  \u2192  UNKNOWN"),
]
y = list(range(len(pillars)))[::-1]
for yy, (name, val, c, note) in zip(y, pillars):
    ax.barh(yy, val, height=0.5, color=c, alpha=0.85)
    ax.text(-0.15, yy, name, ha="right", va="center", fontsize=10, fontweight="bold")
    ax.text(val+0.15, yy, note, ha="left", va="center", fontsize=8.6, color="#333")
ax.axvline(7.0, color="#888", ls="--", lw=1)
ax.text(7.0, len(pillars)-0.35, "'adequate' line", fontsize=8.5, color="#666", ha="center")
ax.set_xlim(0, 10.5); ax.set_ylim(-0.6, len(pillars)-0.2)
ax.set_yticks([]); ax.set_xticks([])
for s in ["top","right","left","bottom"]: ax.spines[s].set_visible(False)
ax.set_title("B87: Brandon's hypertrophy bottleneck diagnosis (Oura-grounded)\n"
             "recovery is FINE \u2014 the gaps are mechanical tension + caloric surplus  (ILLUSTRATIVE)",
             fontsize=11.5, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b87_gile_e_hypertrophy/fig1_bottleneck_diagnosis.png", dpi=130)
print("wrote fig1")

# ---------- Fig 2: the intake blind spot ----------
fig, ax = plt.subplots(figsize=(10.6, 6.4))
ax.axvspan(0, 5, color="#dff0e6", alpha=0.6)
ax.axvspan(5, 10, color="#fdecea", alpha=0.6)
ax.text(2.5, 9.4, "WHAT OURA MEASURES\n(expenditure + recovery)", ha="center", fontsize=11,
        fontweight="bold", color="#2E7D5B")
ax.text(7.5, 9.4, "WHAT OURA CANNOT SEE\n(where the bottleneck hides)", ha="center", fontsize=11,
        fontweight="bold", color="#C0392B")
measured = [
    ("TDEE ~2,525 kcal/day", 8.4),
    ("Active cal ~415/day (low)", 7.4),
    ("Readiness 82.6 (good)", 6.4),
    ("Sleep 82.8 (good)", 5.4),
    ("Steps ~6,588/day", 4.4),
]
unmeasured = [
    ("Calories CONSUMED", 8.4),
    ("Protein grams/day", 7.4),
    ("Bodyweight trend", 6.4),
    ("Training load / progression", 5.4),
    ("Sets-near-failure per muscle", 4.4),
]
for label, yy in measured:
    ax.text(2.5, yy, "\u2713 "+label, ha="center", fontsize=9.3, color="#1e5e40")
for label, yy in unmeasured:
    ax.text(7.5, yy, "\u2717 "+label, ha="center", fontsize=9.3, color="#8c2018")
ax.annotate("FIX: log intake + bodyweight,\nstart at TDEE +250\u2013350 kcal (~2,800\u20132,900),\nadjust by the weekly weight trend",
            xy=(7.5, 4.0), xytext=(5.0, 2.0), fontsize=9.2, color="#8c2018", ha="center",
            arrowprops=dict(arrowstyle="->", color="#8c2018", lw=1.5))
ax.set_xlim(0,10); ax.set_ylim(1.2, 10)
ax.set_xticks([]); ax.set_yticks([])
for s in ["top","right","left","bottom"]: ax.spines[s].set_visible(False)
ax.set_title("B87: the intake blind spot \u2014 Oura tracks the burn, not the build\n"
             "muscle gain needs a tracked surplus + progressive load; both are currently unmeasured  (ILLUSTRATIVE)",
             fontsize=11.5, fontweight="bold")
fig.tight_layout()
fig.savefig("analyses/pass77_b87_gile_e_hypertrophy/fig2_intake_blind_spot.png", dpi=130)
print("wrote fig2"); print("B87 figures done.")

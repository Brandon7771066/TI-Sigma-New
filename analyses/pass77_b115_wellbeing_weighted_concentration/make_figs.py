"""B115 figures: (1) wellbeing-share concentration curve; (2) domain split + hybrid range."""
import json, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

D = "analyses/pass77_b115_wellbeing_weighted_concentration"
with open(os.path.join(D, "results.json")) as f:
    R = json.load(f)
S = R["summary"]
ranked = R["ranked"]

# ---- Fig 1: cumulative wellbeing share vs cumulative distinct named contributors ----
total_W = S["total_wellbeing_weight"]
acc_w, seen = 0.0, set()
xs, ys = [0], [0.0]
for r in ranked:
    acc_w += r["weight"]
    if r["people"]:
        seen.update(r["people"])
    xs.append(len(seen))
    ys.append(acc_w / total_W * 100.0)

fig, ax = plt.subplots(figsize=(8, 5))
ax.plot(xs, ys, lw=2.2, color="#1f6feb")
ax.fill_between(xs, ys, alpha=0.12, color="#1f6feb")
for s in (50, 90, 100):
    lvl = S["wellbeing_share_levels"][f"{s}pct_wellbeing"]
    ax.scatter([lvl["named_people"]], [s], zorder=5, color="#d1242f")
    ax.annotate(f'{s}% of wellbeing\n← {lvl["named_people"]} people (1 in {lvl["one_in_X_humans_ever"]:,})',
                (lvl["named_people"], s), textcoords="offset points", xytext=(8, -22), fontsize=8)
ax.set_xlabel("Cumulative distinct named primary contributors")
ax.set_ylabel("Cumulative % of total wellbeing weight")
ax.set_title(f"B115 — Who to thank: {S['n_distinct_named_all']} people delivered ~all curated wellbeing\n"
             f"({S['n_inventions_total']} inventions, {S['n_abstract']} abstract; Fleiss κ={S['fleiss_kappa']})")
ax.grid(alpha=0.3)
fig.tight_layout()
fig.savefig(os.path.join(D, "fig1_wellbeing_share_curve.png"), dpi=130)
plt.close(fig)

# ---- Fig 2: named vs diffuse wellbeing mass + headline concentration ----
fig, (a1, a2) = plt.subplots(1, 2, figsize=(11, 4.6))
nm = S["named_wellbeing_mass_fraction"] * 100
df = S["diffuse_wellbeing_mass_fraction"] * 100
a1.bar(["Named primary\ncontributors", "Diffuse\nmovements"], [nm, df],
       color=["#1f6feb", "#8b949e"])
for i, v in enumerate([nm, df]):
    a1.text(i, v + 1, f"{v:.1f}%", ha="center", fontsize=10)
a1.set_ylabel("% of total wellbeing weight")
a1.set_title("Attributable vs diffuse wellbeing mass")
a1.set_ylim(0, 100)

# headline range bar (hybrid Indeterminate-True): catalysts -> named -> +diffuse
cats = S["n_distinct_catalysts_all"]
named = S["n_distinct_named_all"]
labels = [f"catalysts only\n{cats} (1 in {S['one_in_X_humans_ever__catalysts_all']:,})",
          f"all primary named\n{named} (1 in {S['one_in_X_humans_ever__named_all']:,})",
          f"+ {S['diffuse_items_no_single_catalyst']} diffuse\nmovements (unbounded)"]
vals = [cats, named, named]
colors = ["#2da44e", "#1f6feb", "#bf8700"]
a2.barh([0, 1, 2], vals, color=colors)
a2.set_yticks([0, 1, 2])
a2.set_yticklabels(labels, fontsize=8)
a2.invert_yaxis()
a2.set_xlabel("distinct people responsible")
a2.set_title("Hybrid Indeterminate-True RANGE\n(great-man → core-teams → movements = BOTH)")
fig.suptitle("B115 — Comprehensive, wellbeing-weighted concentration (extends KEY-PAPER B92)", fontsize=11)
fig.tight_layout(rect=[0, 0, 1, 0.95])
fig.savefig(os.path.join(D, "fig2_domain_and_hybrid_range.png"), dpi=130)
plt.close(fig)
print("figures written")

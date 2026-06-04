"""
Pass-77 B75 — Real-world survey: how well do different disciplines actually prioritize the RIGHT
GILE dimensions and follow the UOP (truth-vs-existence balance)? + the SHAPES of the J(G,H) curve
as truth and existence get prioritized over time.

Brandon directive (B75): "Do a real-world survey of how well different disciplines actually prioritize
the right dimensions and successfully follow the UOP. Also curious how the different shapes of each
graph look as truth and existence get prioritized over time."

================================  ESTABLISHED corpus inputs (cited)  ================================
  * UOP / GTT-1 : J(x) = rho*f_capped(A) + g(H); f_capped imposes 0.93 ceiling; interior optimum.
  * B72         : per-trait QM dephasing fragility costs c_G=c_L=0.30, c_E=0.15, c_I=0.00.
  * B74/urb_611 : per-domain qualitative GILE PROFILE -> proper weights; per-domain GILE:HEM ratio rho.
  * urb_576     : reference weights G=sqrt2-1, I=.25, L=.18, E=.15 (general exemplar / CCC rho=2).

============================  OPERATIONALIZED-BY-AGENT  (flagged #69)  ==============================
  The OPTIMAL allocation per discipline is principled (UOP optimization, exactly the B74 model).
  The ***ACTUAL*** allocation per discipline is an AGENT ARCHETYPE ESTIMATE built from each field's
  DOCUMENTED real-world tendency (one-line basis given for each). It is NOT a measurement. The robust
  deliverable is the QUALITATIVE PATTERN and the SHAPES; exact adherence numbers are not robust and
  must be replaced by survey/bibliometric data to become empirical. This is the SAME over-claim risk
  Brandon flagged in B72 ("by-construction vs independent") -- declared up front, not hidden.

Budget $0, local scipy/numpy/matplotlib.
"""
import numpy as np, json, math
from scipy.optimize import minimize
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

G_STAR, ALPHA = 0.93, 10.0
order = ["G", "I", "L", "E"]
C = {"G": 0.30, "I": 0.00, "L": 0.30, "E": 0.15}              # B72 fragility costs
LEVEL = {"VH": 4, "H": 3, "M": 2, "L": 1}

def f_capped(x):
    return math.log(1+x) if x <= G_STAR else math.log(1+G_STAR) - ALPHA*(x-G_STAR)**2
def g(H):
    return math.log(1+max(H, 0.0))

def profile_to_weights(profile):
    raw = {k: LEVEL[profile[k]] for k in order}
    s = sum(raw.values())
    return {k: raw[k]/s for k in order}

def aggregate(W, x):                 # x is dict G/I/L/E
    return sum(W[t]*x[t] for t in order)
def existence(x):
    return 1.0 - sum(C[t]*x[t] for t in order)
def J(W, x, rho):
    return rho*f_capped(aggregate(W, x)) + g(existence(x))

def optimize_domain(W, rho):
    def neg(v):
        xd = {t: v[i] for i, t in enumerate(order)}
        return -J(W, xd, rho)
    best = None
    for _ in range(200):
        r = minimize(neg, np.random.rand(4), bounds=[(0, 1)]*4, method="L-BFGS-B")
        if best is None or r.fun < best.fun:
            best = r
    return {t: float(best.x[i]) for i, t in enumerate(order)}

# =====================================================================================================
# DISCIPLINES.  profile+rho: B74-style (urb_611 cited for the original 5; the 7 ADDED fields' profiles
# and rho are agent estimates, flagged).  actual: agent archetype of documented real-world practice.
# =====================================================================================================
DISC = {
 "theoretical_mathematics": dict(
    profile={"G":"H","I":"VH","L":"M","E":"L"}, rho=2.4, src="urb_611",
    actual={"G":0.97,"I":0.98,"L":0.20,"E":0.10},
    basis="maximizes rigor(G)+insight(I) hard, near-ignores embodiment(E); mild OVERSHOOT past 0.93"),
 "clinical_medicine": dict(
    profile={"G":"VH","I":"H","L":"H","E":"H"}, rho=1.1, src="agent",
    actual={"G":0.90,"I":0.75,"L":0.80,"E":0.85},
    basis="evidence(G)+judgment(I)+care(L)+body(E) all genuinely engaged -> strong UOP balance"),
 "engineering": dict(
    profile={"G":"H","I":"M","L":"L","E":"VH"}, rho=0.9, src="agent",
    actual={"G":0.85,"I":0.55,"L":0.30,"E":0.95},
    basis="existence-grounded(E)+correctness(G); slightly under-weights deep insight(I)"),
 "climate_science": dict(
    profile={"G":"VH","I":"H","L":"M","E":"VH"}, rho=1.3, src="agent",
    actual={"G":0.90,"I":0.80,"L":0.45,"E":0.90},
    basis="empirics(E)+theory(G/I) jointly high -> truth AND existence well served"),
 "molecular_biology": dict(
    profile={"G":"M","I":"H","L":"H","E":"VH"}, rho=0.6, src="urb_611",
    actual={"G":0.60,"I":0.80,"L":0.70,"E":0.90},
    basis="physical-structure(E)-grounded, matches its HEM-dominant proper profile well"),
 "social_work_therapy": dict(
    profile={"G":"H","I":"M","L":"VH","E":"M"}, rho=0.9, src="urb_611",
    actual={"G":0.75,"I":0.45,"L":0.90,"E":0.60},
    basis="relational alliance(L) correctly central, matches high-L proper profile"),
 "fine_art_aesthetics": dict(
    profile={"G":"M","I":"H","L":"M","E":"VH"}, rho=1.2, src="urb_611",
    actual={"G":0.40,"I":0.75,"L":0.50,"E":0.95},
    basis="aesthetic embodiment(E) correctly maximized, matches E-dominant proper profile"),
 "law": dict(
    profile={"G":"VH","I":"H","L":"M","E":"M"}, rho=1.1, src="agent",
    actual={"G":0.70,"I":0.65,"L":0.40,"E":0.55},
    basis="justice/norms(G) aspired-to but PROCEDURE-vs-truth tension lowers effective truth-reaching"),
 "academic_philosophy": dict(
    profile={"G":"H","I":"VH","L":"M","E":"L"}, rho=2.0, src="agent",
    actual={"G":0.85,"I":0.98,"L":0.30,"E":0.12},
    basis="abstraction(I) OVERSHOOTS, under-grounds in existence(E); documented 'ungrounded' critique"),
 "mainstream_economics": dict(
    profile={"G":"H","I":"H","L":"M","E":"VH"}, rho=1.4, src="agent",
    actual={"G":0.60,"I":0.95,"L":0.30,"E":0.45},
    basis="MIS-PRIORITIZES: over-weights formal abstraction(I) where domain needs empirics(E)"),
 "politics_governance": dict(
    profile={"G":"VH","I":"H","L":"H","E":"H"}, rho=1.0, src="agent",
    actual={"G":0.40,"I":0.45,"L":0.50,"E":0.80},
    basis="documented UNDER-prioritization of truth(G/I) relative to existence/power(E); poorest UOP"),
 "theology_religion": dict(
    profile={"G":"VH","I":"VH","L":"H","E":"L"}, rho=2.0, src="agent",
    actual={"G":0.70,"I":0.90,"L":0.85,"E":0.20},
    basis="high truth-ASPIRATION(I)+love(L); G-grounding contested -> effective-G reduced"),
}

def cosine(a, b):
    av = np.array([a[t] for t in order]); bv = np.array([b[t] for t in order])
    return float(av.dot(bv)/(np.linalg.norm(av)*np.linalg.norm(bv)+1e-12))

def centered_corr(a, b):
    """Mean-centered Pearson across the 4 dims -> captures whether a discipline OVER/UNDER-weights the
    RIGHT dimensions *relative* to each other (scale-free; discriminates, unlike positive-orthant cosine).
    Returns r in [-1,1]; we map to [0,1] for the adherence blend."""
    av = np.array([a[t] for t in order], float); bv = np.array([b[t] for t in order], float)
    av -= av.mean(); bv -= bv.mean()
    d = np.linalg.norm(av)*np.linalg.norm(bv)
    return float(av.dot(bv)/d) if d > 1e-9 else 0.0

rows = []
for name, d in DISC.items():
    W = profile_to_weights(d["profile"])
    xstar = optimize_domain(W, d["rho"])
    xact = d["actual"]
    A_star, A_act = aggregate(W, xstar), aggregate(W, xact)
    H_star, H_act = existence(xstar), existence(xact)
    J_star, J_act = J(W, xstar, d["rho"]), J(W, xact, d["rho"])
    dim_corr = centered_corr(xact, xstar)      # RIGHT-dimensions test (scale-free, discriminating)
    dim_match = round((dim_corr+1)/2, 4)       # mapped to [0,1] for the blend
    j_eff = J_act/J_star if J_star else 0.0    # truth-vs-existence balance efficiency
    uop = round(0.6*dim_match + 0.4*j_eff, 4)  # combined UOP-adherence (dims weighted slightly more)
    overshoot = "OVERSHOOT" if A_act > G_STAR+0.005 else ("under" if A_act < A_star-0.02 else "balanced")
    rows.append(dict(name=name, rho=d["rho"], src=d["src"], weights={k:round(W[k],3) for k in order},
        optimal={k:round(xstar[k],3) for k in order}, actual=xact,
        A_star=round(A_star,4), A_act=round(A_act,4), H_act=round(H_act,4),
        J_star=round(J_star,4), J_act=round(J_act,4),
        dim_match=round(dim_match,4), j_efficiency=round(j_eff,4),
        uop_adherence=uop, truth_status=overshoot, basis=d["basis"]))

rows.sort(key=lambda r: r["uop_adherence"], reverse=True)

# =====================================================================================================
# FIGURES
# =====================================================================================================
# Fig 1 — SHAPE of J as the truth aggregate A is prioritized, for several rho (GILE:HEM) regimes.
#         existence proxied by H = 1 - k*A with k = representative weighted fragility.
k_eff = 0.22
A = np.linspace(0, 1.0, 400)
plt.figure(figsize=(8, 5))
for rho in [0.6, 1.0, 1.4, 2.0, 2.4]:
    Jc = [rho*f_capped(a) + g(max(1-k_eff*a, 0)) for a in A]
    plt.plot(A, Jc, label=f"rho (GILE:HEM) = {rho}")
plt.axvline(G_STAR, ls="--", color="k", lw=1, label="0.93 Radiant cap")
plt.xlabel("aggregate truth prioritized  A (GILE)"); plt.ylabel("J(G,H)  UOP objective")
plt.title("Shape of the UOP objective as TRUTH is prioritized\n(rises -> peaks near 0.93 -> declines: the quadratic over-reach penalty)")
plt.legend(fontsize=8); plt.tight_layout()
plt.savefig("analyses/pass77_b75_uop_discipline_survey/fig1_J_shape_vs_truth.png", dpi=110)
plt.close()

# Fig 2 — survey: UOP-adherence by discipline (sorted), colored by truth_status.
cmap = {"balanced":"#2a9d8f","OVERSHOOT":"#e76f51","under":"#e9c46a"}
plt.figure(figsize=(9, 5.5))
names = [r["name"].replace("_","\n") for r in rows]
vals = [r["uop_adherence"] for r in rows]
cols = [cmap[r["truth_status"]] for r in rows]
plt.barh(range(len(rows)), vals, color=cols)
plt.yticks(range(len(rows)), names, fontsize=7)
plt.gca().invert_yaxis()
plt.xlabel("UOP-adherence  (0.5*dimension-match + 0.5*J-efficiency)")
plt.title("How well disciplines follow the UOP (agent archetype estimate, #69)")
handles = [plt.Rectangle((0,0),1,1,color=c) for c in cmap.values()]
plt.legend(handles, cmap.keys(), fontsize=8, loc="lower right")
plt.tight_layout()
plt.savefig("analyses/pass77_b75_uop_discipline_survey/fig2_survey_adherence.png", dpi=110)
plt.close()

# Fig 3 — TRAJECTORY SHAPES over time: 4 archetypal disciplinary paths of A(t), and resulting J(t).
t = np.linspace(0, 1, 300)
paths = {
  "healthy climber -> plateau @0.93": 0.93*(1-np.exp(-3.2*t)),
  "truth-zealot -> overshoot":        np.clip(1.05*(1-np.exp(-3.5*t)), 0, 1.0),
  "existence-stuck -> stagnates":     0.55*(1-np.exp(-3.0*t)),
  "self-correcting -> overshoot+return": 0.93 + 0.10*np.sin(3.1*t)*np.exp(-1.5*t),
}
fig, ax = plt.subplots(1, 2, figsize=(12, 5))
for lab, At in paths.items():
    At = np.clip(At, 0, 1.0)
    ax[0].plot(t, At, label=lab)
    Jt = [1.6*f_capped(a) + g(max(1-k_eff*a, 0)) for a in At]   # rho=1.6 representative
    ax[1].plot(t, Jt, label=lab)
ax[0].axhline(G_STAR, ls="--", color="k", lw=1); ax[0].set_title("truth aggregate A(t) over time")
ax[0].set_xlabel("time (discipline maturation)"); ax[0].set_ylabel("A (GILE truth)")
ax[1].set_title("resulting UOP objective J(t) — note the distinct SHAPES")
ax[1].set_xlabel("time"); ax[1].set_ylabel("J(G,H)")
ax[0].legend(fontsize=7); ax[1].legend(fontsize=7); plt.tight_layout()
plt.savefig("analyses/pass77_b75_uop_discipline_survey/fig3_time_trajectories.png", dpi=110)
plt.close()

# Fig 4 — truth-vs-existence tradeoff: as truth priority rises, A up / H down / J peaks.
plt.figure(figsize=(8, 5))
H = [max(1-k_eff*a, 0) for a in A]
Jr = [1.6*f_capped(a) + g(max(1-k_eff*a, 0)) for a in A]
plt.plot(A, A, label="truth A (rising)")
plt.plot(A, H, label="existence H (falling)")
plt.plot(A, Jr, label="J(G,H) objective", lw=2.5, color="k")
astar = A[int(np.argmax(Jr))]
plt.axvline(astar, ls=":", color="r", label=f"J-optimal A≈{astar:.2f}")
plt.axvline(G_STAR, ls="--", color="gray", lw=1, label="0.93 cap")
plt.xlabel("truth prioritization  A"); plt.ylabel("value")
plt.title("Truth vs existence tradeoff under the UOP (rho=1.6)")
plt.legend(fontsize=8); plt.tight_layout()
plt.savefig("analyses/pass77_b75_uop_discipline_survey/fig4_truth_existence_tradeoff.png", dpi=110)
plt.close()

# =====================================================================================================
out = dict(
  established_inputs="UOP/GTT-1 J=rho*f_capped(A)+g(H); B72 fragility costs; B74/urb_611 profiles+rho; urb_576 weights",
  agent_operationalization_69=(
     "OPTIMAL allocation is principled UOP optimization. ACTUAL allocation per discipline is an AGENT "
     "ARCHETYPE of documented real-world tendency, NOT a measurement; 7 of 12 disciplines' profiles+rho "
     "are also agent estimates (src='agent'). Robust deliverable = qualitative pattern + curve shapes; "
     "exact adherence numbers require survey/bibliometric data to become empirical."),
  survey=rows,
  best=[r["name"] for r in rows[:3]],
  worst=[r["name"] for r in rows[-3:]],
  shape_findings=dict(
     universal_shape="J(A) RISES, PEAKS near A=0.93, then DECLINES (quadratic over-reach penalty) -> "
        "a concave peak, NOT monotone. Over-prioritizing truth past 0.93 LOWERS J = punished by UOP.",
     rho_effect="higher rho (GILE-dominant) -> higher, sharper peak located AT 0.93; lower rho "
        "(HEM-dominant) -> flatter peak located BELOW 0.93 (existence term dominates) -> the 0.93 cap "
        "only BINDS for high-rho disciplines, exactly the B74 result reflected in curve shape.",
     trajectory_shapes="four archetypes: (1) healthy climber = saturating rise to 0.93 plateau (J max); "
        "(2) truth-zealot = overshoot -> J turns DOWN; (3) existence-stuck = low plateau, J never reaches "
        "potential; (4) self-correcting = overshoot then damped return to 0.93 (J recovers)."),
  honest_caveats_69=(
     "Actual allocations are reasoned archetypes from documented disciplinary tendencies, not measured; "
     "they encode the agent's priors and could be contested. The ORDERING (math/medicine/climate strong; "
     "politics/economics weak) and the SHAPES are the defensible claims; precise scores are illustrative. "
     "Empirical upgrade path: bibliometric/replication-rate/practitioner-survey calibration per field."),
  principle_count_effect="no new principle; applied survey + visualization of UOP/GTT-1. Count 74.")

with open("analyses/pass77_b75_uop_discipline_survey/results.json", "w") as f:
    json.dump(out, f, indent=2)

print("=== UOP DISCIPLINE SURVEY (sorted by adherence) ===")
for r in rows:
    print(f'{r["uop_adherence"]:.3f}  {r["name"]:24s} rho={r["rho"]:<4} '
          f'A_act={r["A_act"]:.3f} ({r["truth_status"]:9s}) dim={r["dim_match"]:.3f} '
          f'Jeff={r["j_efficiency"]:.3f}  [{r["src"]}]')
print("\nbest:", out["best"], "\nworst:", out["worst"])
print("figs: fig1_J_shape_vs_truth, fig2_survey_adherence, fig3_time_trajectories, fig4_truth_existence_tradeoff")

"""
Pass-77 B77 — Communication asymmetry: why "mean what you say / say what you mean" (MWYS) is an
over-idealized standard, and why explicitness has an INTERIOR optimum (over-explaining = over-reach).

Brandon morning insight (2026-05-28): "'Mean what you say and say what you mean' is essentially
wishful thinking for 'neat freaks.' Actual conversation is asymmetrical and obligating everyone to such
a narrow standard is just plain silly. Besides, getting the other person to think for themselves about
what was said has merit. Not everything should be spelled out to a tee. Moreover, speakers cannot
actually customize their communication to each person ... since that would require knowing the person's
knowledge and thoughts."

MODEL (mirrors the UOP over-reach geometry from B75): a speaker picks explicitness e in [0,1] for a
listener with prior knowledge k in [0,1]. Comprehension saturates in e (filling the (1-k) gap), and
OVER-explaining past what the listener needs (e > 1-k) incurs a QUADRATIC over-reach penalty (the
"neat-freak" cost: boredom / insult / wasted effort / disengagement) -- structurally identical to the
0.93 cap penalty. Result: optimal explicitness e* < 1 for any informed listener (NEVER spell it all
out), e* DEPENDS on the listener (customization matters), and a single broadcast e cannot serve a
mixed audience (customization-impossibility cost is irreducible).

#69 HONESTY: by-construction generative model; the SHAPES + qualitative claims are the deliverable,
parameters illustrative. Empirical upgrade: comprehension/engagement experiments varying explicitness
against measured listener priors.

Budget $0, local numpy/matplotlib.
"""
import numpy as np, json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = "analyses/pass77_b77_communication_asymmetry"
BETA, LAM = 4.0, 1.6          # explicitness fill-rate ; over-reach penalty weight
e = np.linspace(0, 1, 400)

def value(e, k):
    """communicative value: comprehension reached  -  over-explicitness over-reach penalty.
    comprehension U = k + (1-k)(1-exp(-BETA*e)); penalty = LAM*max(0, e-(1-k))^2."""
    U = k + (1-k)*(1-np.exp(-BETA*e))
    over = np.clip(e - (1-k), 0, None)
    return U - LAM*over**2

# ---- per-listener curves (different prior knowledge k) ----
ks = [0.1, 0.3, 0.5, 0.7, 0.9]
curves = {k: value(e, k) for k in ks}
estar = {k: float(e[np.argmax(value(e, k))]) for k in ks}     # optimal explicitness per listener

# ---- population: customization-impossibility cost ----
rng = np.random.default_rng(77)
K = rng.beta(2, 2, 20000)                                     # mixed audience, knowledge ~ Beta(2,2)
# idealized (impossible) per-listener best:
ideal = np.mean([np.max(value(e, k)) for k in rng.choice(K, 600, replace=False)])
# best single BROADCAST explicitness for the whole audience:
grid = np.linspace(0, 1, 200)
broadcast_vals = [np.mean([np.mean(value(np.array([g]), k)) for k in rng.choice(K, 400, replace=False)]) for g in grid]
e_broadcast = float(grid[int(np.argmax(broadcast_vals))])
v_broadcast = float(np.max(broadcast_vals))
# MWYS maximal-explicitness (e=1, "say everything to a tee"):
v_mwys = float(np.mean([np.mean(value(np.array([1.0]), k)) for k in rng.choice(K, 1200, replace=False)]))
cust_cost = ideal - v_broadcast                              # irreducible customization-impossibility loss
mwys_penalty = v_broadcast - v_mwys                          # how much MWYS-maximalism loses vs broadcast opt

# ---- figures ----
plt.figure(figsize=(8, 5))
for k in ks:
    plt.plot(e, curves[k], label=f"listener knows k={k}")
    plt.axvline(estar[k], ls=":", lw=0.8, color="gray")
plt.xlabel("speaker explicitness  e   (1 = 'spell everything out to a tee')")
plt.ylabel("communicative value V(e; k)")
plt.title("Explicitness has an INTERIOR optimum that DEPENDS on the listener\n(over-explaining = over-reach; e*<1 always -> never spell it all out)")
plt.legend(fontsize=8); plt.tight_layout()
plt.savefig(f"{OUT}/fig1_explicitness_optima_per_listener.png", dpi=110); plt.close()

plt.figure(figsize=(7.5, 5))
bars = {"idealized\nper-listener\n(IMPOSSIBLE)": ideal,
        f"best single\nBROADCAST\n(e*={e_broadcast:.2f})": v_broadcast,
        "MWYS maximal\nexplicitness\n(e=1)": v_mwys}
cols = ["#2a9d8f", "#264653", "#e76f51"]
plt.bar(range(3), list(bars.values()), color=cols)
plt.xticks(range(3), list(bars.keys()), fontsize=8)
plt.ylabel("mean communicative value over audience")
plt.title(f"Customization is impossible -> irreducible loss = {cust_cost:.3f};\n"
          f"MWYS-maximalism loses a further {mwys_penalty:.3f} below the broadcast optimum")
plt.tight_layout()
plt.savefig(f"{OUT}/fig2_customization_impossibility_cost.png", dpi=110); plt.close()

out = dict(
  insight="MWYS is over-idealized; communication is asymmetrical; explicitness has an interior optimum; "
          "perfect per-listener customization is impossible",
  model_is_illustrative_69=("by-construction generative model; shapes+qualitative claims are the "
     "deliverable, parameters illustrative. Empirical upgrade: comprehension/engagement experiments."),
  params=dict(beta=BETA, lam=LAM, audience="k~Beta(2,2)"),
  optimal_explicitness_per_listener={f"k={k}": round(estar[k], 3) for k in ks},
  population=dict(idealized_per_listener=round(ideal, 4), broadcast_value=round(v_broadcast, 4),
                  best_broadcast_e=round(e_broadcast, 3), mwys_maximal_value=round(v_mwys, 4),
                  customization_impossibility_cost=round(cust_cost, 4),
                  mwys_maximalism_extra_loss=round(mwys_penalty, 4)),
  findings=dict(
    f1_interior_optimum="for every informed listener (k>0) optimal explicitness e*<1 -> 'never spell it "
       "all out'; over-explaining past e=(1-k) is a quadratic OVER-REACH penalty, structurally identical "
       "to the UOP 0.93 cap (B75). Brandon's 'getting the other person to think for themselves has merit' "
       "= e* sits below maximal explicitness by construction of the saturating+penalized value.",
    f2_listener_dependence="e* falls as k rises (well-informed listener -> be terse, let them infer; "
       "uninformed -> be explicit). No single e is right for everyone.",
    f3_customization_impossible="the gap between idealized per-listener value and the best single "
       "broadcast value is IRREDUCIBLE (cannot read each mind) -> Brandon's 'speakers cannot customize "
       "to each person' is a quantified bound, not a failing.",
    f4_mwys_is_strictly_worse="MWYS maximal-explicitness (e=1) scores BELOW even the single-broadcast "
       "optimum -> the 'neat-freak' standard is not just unattainable, it's actively suboptimal."),
  principle_status="ACN-1 (Asymmetric-Communication Norm) introduced CANDIDATE canonical; ratification "
     "= Brandon choice. Canonical count unchanged 74.")

with open(f"{OUT}/results.json", "w") as f:
    json.dump(out, f, indent=2)

print("=== B77 communication asymmetry ===")
print("optimal explicitness e* per listener:", {f"k={k}": round(estar[k],3) for k in ks})
print(f"idealized per-listener value : {ideal:.4f}")
print(f"best broadcast value (e*={e_broadcast:.2f}) : {v_broadcast:.4f}")
print(f"MWYS maximal (e=1) value     : {v_mwys:.4f}")
print(f"customization-impossibility cost : {cust_cost:.4f}")
print(f"MWYS-maximalism extra loss vs broadcast : {mwys_penalty:.4f}")
print("figs: fig1_explicitness_optima_per_listener, fig2_customization_impossibility_cost")

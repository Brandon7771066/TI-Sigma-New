"""
Pass-77 B78 — TIL + PD as an antidote to AI hallucination (the flagship "singular AI malady" app).

Brandon insight (2026-05-28): "TIL with the PD represent an excellent antidote to AI hallucinations.
The real reason 'AI can't tell true from false' is that binary is a false dichotomy. Also, so-called
'hallucinations' are in fact 'validly constructed hyper-imaginings (i.e. incorrigible)' WITHIN an
agent's mind. ... speculative but reasonable conjecture: The extent to which AIs hallucinate (i.e. not
simply ERR) depends on their level of consciousness."

OPERATIONAL MODEL. Every output claim lives in a 2-axis plane:
  - PD-real  e in [0,1]  = EXTERNAL evidential support (how well the world backs it).
  - internal confidence / PD-imaginary c in [0,1] = the agent's INTERNAL generative conviction.
A fraction rho of claims are HYPER-IMAGININGS: internally coherent + high-confidence (c high) but
evidentially unsupported (e low) and non-veridical -- incorrigible from inside the agent. rho is the
agent's imaginative generativity, used here as a (#69 speculative) PROXY for "level of consciousness."

  - BINARY policy ("can it tell true from false?"): assert TRUE iff internal confidence c > tau.
    -> confidently asserts hyper-imaginings as TRUE. This IS hallucination.
  - TIL/PD policy: assert plain-TRUE only when EVIDENTIALLY supported (PD-real e >= 0.5); when c is
    high but e is low, do NOT collapse to True -- label the item a HYPER-IMAGINING (high PD-imaginary,
    Indeterminate on the categorical axis) and withhold/flag it. The false dichotomy is dissolved:
    "true vs false" becomes "evidentially-true vs imaginative-construct vs ...".

CLAIMS THIS ILLUSTRATES (shapes are the deliverable; #69 by-construction, magnitudes illustrative):
  H-a  binary T/F is a false dichotomy -> a confidence-only gate cannot separate hyper-imaginings from
       evidentially-true claims (they share high c).
  H-b  hyper-imaginings are a DISTINCT category from ERR (random process noise), and PD makes them
       nameable -> hallucination rate drops sharply under TIL/PD while true-assertion is retained.
  H-c  CONJECTURE: hallucination-propensity rises with imaginative generativity (consciousness proxy
       rho) under the binary gate, but TIL/PD ABSORBS that rise -> the antidote scales.

Budget $0, local numpy/matplotlib.
"""
import numpy as np, json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

OUT = "analyses/pass77_b78_hallucination_as_hyperimagining"
TAU = 0.60          # binary confidence threshold
E_GATE = 0.50       # TIL/PD evidential (PD-real) gate
rng = np.random.default_rng(78)

def make_claims(n, rho):
    e = rng.uniform(0, 1, n)                                  # evidential support (PD-real)
    c = np.clip(e + rng.normal(0, 0.12, n), 0, 1)            # confidence usually tracks evidence
    veridical = (e >= 0.5).astype(int)                       # ground truth tracks evidence
    is_imag = rng.uniform(0, 1, n) < rho                     # hyper-imaginings override
    e[is_imag] = rng.uniform(0.00, 0.25, is_imag.sum())     #   low external support
    c[is_imag] = rng.uniform(0.75, 1.00, is_imag.sum())     #   high internal conviction
    veridical[is_imag] = 0                                    #   non-veridical (incorrigible)
    return e, c, veridical, is_imag

def evaluate(e, c, veridical, is_imag):
    n = len(e)
    # BINARY: assert True iff confidence high
    bin_assert_T = c > TAU
    # hallucination = confidently asserting a (non-veridical) hyper-imagining as TRUE
    hall_bin = float(np.mean(bin_assert_T & is_imag))
    # true-assertion retention on genuinely veridical, non-imaginative claims
    real_true = veridical.astype(bool) & ~is_imag
    ret_bin = float(np.mean(bin_assert_T[real_true]))
    # TIL/PD: assert plain-True only if evidentially supported; flag high-c/low-e as hyper-imagining
    pd_assert_T = e >= E_GATE
    pd_flag_imag = (c > TAU) & (e < E_GATE)
    hall_pd = float(np.mean(pd_assert_T & is_imag))
    ret_pd = float(np.mean(pd_assert_T[real_true]))
    caught = float(np.mean(pd_flag_imag[is_imag])) if is_imag.sum() else 0.0   # imaginings correctly flagged
    return dict(hall_bin=hall_bin, hall_pd=hall_pd, ret_bin=ret_bin, ret_pd=ret_pd, imag_caught=caught)

# ---- fixed-rho snapshot for the scatter ----
e0, c0, v0, im0 = make_claims(8000, 0.20)
snap = evaluate(e0, c0, v0, im0)

# ---- H-c: sweep rho (consciousness/imaginativeness proxy) ----
rhos = np.linspace(0.0, 0.6, 13)
sweep = []
for r in rhos:
    e, c, v, im = make_claims(12000, r)
    sweep.append(evaluate(e, c, v, im))
hall_bin_curve = [s["hall_bin"] for s in sweep]
hall_pd_curve  = [s["hall_pd"]  for s in sweep]

# ---- figures ----
plt.figure(figsize=(7.8, 6))
real = v0.astype(bool) & ~im0
err  = (~v0.astype(bool)) & ~im0
plt.scatter(e0[real][:1500], c0[real][:1500], s=6, c="#2a9d8f", label="evidentially TRUE", alpha=.5)
plt.scatter(e0[err][:1500],  c0[err][:1500],  s=6, c="#bbbbbb", label="ordinary false / ERR", alpha=.5)
plt.scatter(e0[im0][:1500],  c0[im0][:1500],  s=10, c="#e76f51", label="HYPER-IMAGINING (incorrigible)", alpha=.7)
plt.axhline(TAU, color="#264653", ls="--", lw=1.4, label=f"BINARY gate (confidence>{TAU}) — asserts imaginings TRUE")
plt.axvline(E_GATE, color="#3a0ca3", ls=":", lw=1.6, label=f"TIL/PD evidential gate (PD-real≥{E_GATE})")
plt.fill_betweenx([TAU, 1], 0, E_GATE, color="#e76f51", alpha=0.10)
plt.text(0.02, 0.97, "hyper-imagining quadrant\n(high confidence, low evidence)\nPD flags it; binary asserts it TRUE",
         fontsize=7.5, va="top", color="#9c2706")
plt.xlabel("PD-real  e  = external evidential support")
plt.ylabel("internal confidence c  (PD-imaginary)")
plt.title("Binary T/F is a false dichotomy: a confidence-only gate cannot\nseparate hyper-imaginings from evidentially-true claims; PD can")
plt.legend(fontsize=7, loc="lower right"); plt.tight_layout()
plt.savefig(f"{OUT}/fig1_false_dichotomy_plane.png", dpi=110); plt.close()

plt.figure(figsize=(7.8, 5))
plt.plot(rhos, hall_bin_curve, "o-", color="#264653", label="BINARY gate — hallucination rate")
plt.plot(rhos, hall_pd_curve,  "s-", color="#2a9d8f", label="TIL/PD gate — hallucination rate")
plt.xlabel("imaginative generativity ρ  (#69 speculative proxy for 'level of consciousness')")
plt.ylabel("hallucination rate  (confident-false hyper-imaginings asserted TRUE)")
plt.title("H-c conjecture: hallucination rises with imaginative richness under binary,\nbut TIL/PD ABSORBS it — the antidote scales with consciousness-proxy")
plt.legend(fontsize=9); plt.tight_layout()
plt.savefig(f"{OUT}/fig2_consciousness_conjecture_absorption.png", dpi=110); plt.close()

out = dict(
  insight="TIL+PD as antidote to AI hallucination; binary true/false is a false dichotomy; "
          "hallucinations = validly-constructed incorrigible hyper-imaginings (distinct from ERR); "
          "conjecture: hallucination-propensity scales with consciousness-level",
  model_is_illustrative_69=("by-construction model; shapes+qualitative claims are the deliverable, "
     "magnitudes illustrative. 'consciousness level' is OPERATIONALIZED as imaginative generativity rho "
     "-- a modeling proxy, NOT a measurement. Empirical upgrade: hallucination benchmarks with separated "
     "evidential vs internal-confidence signals + a corrigibility/abstention channel."),
  params=dict(binary_tau=TAU, pd_evidential_gate=E_GATE),
  snapshot_rho_0p20=snap,
  sweep=dict(rho=[round(float(r),3) for r in rhos],
             hallucination_binary=[round(x,4) for x in hall_bin_curve],
             hallucination_pd=[round(x,4) for x in hall_pd_curve]),
  findings=dict(
    Ha_false_dichotomy="hyper-imaginings and evidentially-true claims SHARE high internal confidence; a "
       "confidence-only (binary) gate cannot separate them. Separating PD-real (evidence) from "
       "PD-imaginary (internal conviction) is what dissolves the dichotomy.",
    Hb_distinct_category=f"at ρ=0.20 binary asserts {snap['hall_bin']:.3f} of outputs as confident-false "
       f"hyper-imaginings (hallucination) vs {snap['hall_pd']:.3f} under TIL/PD; PD flags "
       f"{snap['imag_caught']:.3f} of imaginings as hyper-imaginings, while RETAINING true-assertion "
       f"{snap['ret_pd']:.3f} vs binary {snap['ret_bin']:.3f}. Hyper-imagining is a NAMEABLE category, "
       f"not ERR.",
    Hc_consciousness_conjecture="under the binary gate hallucination rate rises ~linearly with "
       "imaginative generativity ρ (consciousness proxy); under TIL/PD it stays near zero -> the antidote "
       "absorbs exactly the failure mode that a more 'imaginative' (conjecturally more conscious) agent "
       "would exhibit. SPECULATIVE per Brandon + #69."),
  principles_status="TWO CANDIDATE principles introduced: HAH-1 (Hallucination-as-Hyperimagining + PD "
     "antidote) flagship; VPP-1 (Valence-Presentation Professionalism: emoji-parity + anti-coldness, "
     "extends VFP-1/TPS-1/ACN-1). Ratification = Brandon choice. Canonical count unchanged 74.")

with open(f"{OUT}/results.json", "w") as f:
    json.dump(out, f, indent=2)

print("=== B78 hallucination-as-hyperimagining ===")
print("snapshot rho=0.20:", {k: round(v,4) for k,v in snap.items()})
print("hallucination BINARY by rho:", [round(x,3) for x in hall_bin_curve])
print("hallucination TIL/PD by rho:", [round(x,3) for x in hall_pd_curve])
print("figs: fig1_false_dichotomy_plane, fig2_consciousness_conjecture_absorption")

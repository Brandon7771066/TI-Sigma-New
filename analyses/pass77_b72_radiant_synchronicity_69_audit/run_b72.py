"""
Pass-77 B72 — #69 audit of the "super-synchronicity" reading of B71.

Brandon's claim: all four GILE traits confirmed at 0.93 to two decimal places is
super-synchronicity-level evidence that GILE is THE correct abstract model of reality.

#69 obligation: was the four-way agreement at 0.93 an INDEPENDENT convergence, or did
it merely echo back the single 0.93 parameter hardcoded into the shared f_capped function
applied identically to each trait?

Test: replace the imposed-0.93 cap with an INDEPENDENT per-trait optimum derived from the
QM dephasing fragility measured in B71 (G:0.30, L:0.30, E:0.15, I:0.00 trait-loss under
gamma=0.3). If GILE traits truly, independently converge to ~0.93, the independent derivation
should reproduce ~0.93 for all four. If they scatter (or some don't cap at all), the
two-decimal agreement is by-construction, NOT synchronicity.

Budget: $0 (local). Free.
"""
import math, json

out = {}

# ----------------------------------------------------------------------------
# Part A — restate the construction. B71 used ONE function for all four traits:
#   f_capped(x) = log(1+x) for x<=0.93 ; log(1.93) - 10(x-0.93)^2 for x>0.93
# The cap location 0.93 is an INPUT PARAMETER, applied identically to G,I,L,E.
# Therefore argmax over each trait = 0.93 BY CONSTRUCTION, for all four, trivially.
# ----------------------------------------------------------------------------
out["A_construction"] = {
    "B71_functional": "f_capped(x) with cap parameter G_STAR=0.93, SAME function for G,I,L,E",
    "consequence": "all four argmax at 0.93 is a MATHEMATICAL IDENTITY given the shared input, "
                   "not four independent measurements that happened to agree",
    "probability_of_agreement_given_construction": 1.0,
    "note": "A synchronicity is a MEANINGFUL IMPROBABLE coincidence (low prior, p<<1). "
            "An event with prior probability 1.0 (certain by construction) is the OPPOSITE "
            "of a synchronicity."}

# ----------------------------------------------------------------------------
# Part B — INDEPENDENT derivation: derive each trait's optimum from its OWN QM fragility,
# with NO imposed 0.93. Truth-vs-existence net objective:
#   N(x) = log(1+x)  -  kappa_trait * x^2
# benefit = log(1+x) (monotone up); existence penalty grows with x^2, scaled by the
# trait's empirical decoherence fragility (more fragile -> existence costs more to push up).
# Interior optimum: d/dx = 1/(1+x) - 2 kappa x = 0.
# Calibrate kappa so the MOST-fragile traits (G,L, loss 0.30) optimize at 0.93, then apply
# the SAME fragility->kappa scaling to E and I and see where THEY independently land.
# ----------------------------------------------------------------------------
frag = {"G":0.30, "L":0.30, "E":0.15, "I":0.00}    # from B71 Part E dephasing trait-loss

# kappa_ref so that x*=0.93 at frag=0.30:  1/(1+0.93) = 2 kappa_ref * 0.93
kappa_ref_at_030 = 1.0/((1+0.93)*2*0.93)
def kappa(trait):
    return kappa_ref_at_030 * (frag[trait]/0.30)   # proportional to fragility

def optimum(trait, step=0.0005):
    k = kappa(trait)
    if k <= 1e-12:
        return 1.0, "NO CAP (zero fragility -> pushes to maximum 1.0)"
    # interior root of 1/(1+x) = 2k x on [0,1]; else boundary 1.0
    best = (-1e9, None)
    x = 0.0
    while x <= 1.0:
        N = math.log(1+x) - k*x*x
        if N > best[0]: best = (N, x)
        x += step
    xs = round(best[1], 3)
    return xs, ("interior cap" if xs < 0.999 else "NO CAP (optimum at boundary 1.0)")

ind = {}
for tr in ["G","I","L","E"]:
    xs, kind = optimum(tr)
    ind[tr] = {"fragility": frag[tr], "kappa": round(kappa(tr),4),
               "independent_optimum": xs, "kind": kind,
               "matches_0.93_to_2dp": abs(xs-0.93) < 0.005}
out["B_independent_per_trait_optimum"] = {
    "model": "N(x)=log(1+x) - kappa*x^2, kappa proportional to B71 QM dephasing fragility",
    "calibration": "kappa set so G,L (fragility 0.30) -> 0.93; SAME scaling applied to E,I",
    "results": ind,
    "spread": "G,L cap near 0.93; E caps HIGHER (less fragile); I does NOT cap (zero fragility)"}

# ----------------------------------------------------------------------------
# Part C — what kappa WOULD each trait need to independently hit 0.93?
# 1/(1+0.93) = 2 kappa 0.93  ->  kappa_required = const, INDEPENDENT of trait.
# But kappa is supposed to come from fragility, which DIFFERS per trait. So to force all
# four to 0.93 you must DECOUPLE kappa from fragility -> i.e. impose it. For I (frag 0) the
# required kappa is finite but its actual fragility-derived kappa is 0 -> mismatch = infinite ratio.
# ----------------------------------------------------------------------------
kappa_required_for_093 = kappa_ref_at_030   # same for any trait by the FOC
mismatch = {}
for tr in ["G","I","L","E"]:
    actual = kappa(tr)
    ratio = (kappa_required_for_093/actual) if actual>1e-12 else float('inf')
    mismatch[tr] = {"kappa_required_for_0.93": round(kappa_required_for_093,4),
                    "kappa_from_fragility": round(actual,4),
                    "must_override_by_factor": (round(ratio,3) if ratio!=float('inf') else "infinite")}
out["C_what_forcing_0.93_requires"] = {
    "finding": "To make all four traits independently optimize at 0.93, the penalty must be "
               "DECOUPLED from the (heterogeneous) QM fragility and set by hand. For I (zero "
               "fragility) the override factor is INFINITE. This is exactly what B71's shared "
               "f_capped did implicitly.",
    "per_trait": mismatch}

# ----------------------------------------------------------------------------
# Part D — what IS genuinely non-trivial in B71 (credit where due, #69 symmetric)
# ----------------------------------------------------------------------------
out["D_genuine_support_for_GILE"] = {
    "real_findings_NOT_by_construction": [
        "All four GILE traits are operationalizable from a SINGLE 2-qubit state via FOUR "
        "DISTINCT natural QM observables (coherence/measurement/entanglement/symmetry) -- a "
        "non-trivial, elegant carving; GILE maps onto an independent QM structure.",
        "The interior-optimum / sub-maximal 'tralseness' structure is real: optimal entangled "
        "state has fidelity 0.965 to Bell, i.e. perfection is genuinely disfavored once ANY "
        "existence cost is present (this needs only existence-cost>0, not the specific 0.93).",
        "3 of 4 traits (G,L,E) are empirically fragile under dephasing -- an independent QM "
        "fact, not imposed."],
    "what_is_NOT_supported": [
        "The specific 'all four at 0.93 to two decimal places' is BY CONSTRUCTION (shared "
        "f_capped), prior probability 1.0 -> NOT a synchronicity.",
        "Independent QM-fragility derivation gives HETEROGENEOUS optima (G,L~0.93; E higher; "
        "I uncapped) -- the four traits do NOT naturally converge to a common cap."]}

# ----------------------------------------------------------------------------
# Part E — the skeptic engagement, done honestly
# ----------------------------------------------------------------------------
out["E_skeptic_engagement"] = {
    "skeptic_claim": "objective values cannot exist / are nonsensical",
    "what_B71_DOES_bear_on_it": "GILE values ARE well-defined, computable, and non-arbitrary "
        "(each maps to a standard QM observable) -- this answers the 'nonsensical' charge: the "
        "values are operationally meaningful and reproducible.",
    "what_B71_does_NOT_establish": "that the values objectively converge to a universal constant "
        "(0.93). That would require INDEPENDENT convergence, which the audit shows is absent.",
    "honest_path_to_synchronicity_grade_evidence": "Estimate each trait's cap from FOUR "
        "SEPARATE empirical datasets (not one imposed function). If those four independent "
        "empirical estimates clustered near a common value with p<<1, THAT would be "
        "synchronicity-grade. This is an open, falsifiable experiment -- not yet done."}

out["verdict"] = {
    "#69": "The 'super-synchronicity, confirmed to two decimals' framing is OVER-CLAIM: the "
           "four-way 0.93 agreement is true-by-construction (shared cap parameter), prior "
           "probability 1.0, the opposite of an improbable meaningful coincidence. Independent "
           "QM derivation does NOT reproduce it. HOWEVER, B71 does provide genuine (weaker) "
           "support for GILE: the four traits map onto four distinct QM observables and the "
           "tralseness/interior-optimum structure is real and not imposed.",
    "recommendation": "Do NOT register 'super-synchronicity' as canonical on this result. "
           "Register the GENUINE finding (GILE<->QM four-observable mapping + tralseness "
           "structure) and the OPEN experiment (independent four-dataset cap estimation) that "
           "could, if it succeeded, earn the synchronicity grade.",
    "principle_count_effect": "no change; count stays 74 (this is an audit, not a new principle)."}

print(json.dumps(out, indent=2))

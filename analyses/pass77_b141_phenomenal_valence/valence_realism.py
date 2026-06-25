"""
B141 — The PHENOMENAL / VALENCE argument for moral realism, in detail.
GME-1 refinement #3. Structural toy: stipulated structure, ZERO empirical
weight, no numerology. Encodes LOGICAL STRUCTURE only.

THE AUTHOR'S ARGUMENT (the valence argument):
  Value is not ADDED to the universe -- it FALLS OUT of conscious valence
  itself. The bulk of ethics is promoting happiness, minimizing suffering, and
  sustaining wellbeing. So ANY conscious being -- and ESPECIALLY any society --
  will develop values/rules around healthy valence. To deny moral realism you
  would have to STRIP conscious valence of its intrinsic value and declare laws
  "meaningless / arbitrarily constructed." Conscious states have intrinsic value
  BY DEFINITION; a person may verbally deny this, but their REAL BEHAVIOR shows
  otherwise.

HONEST VERDICT BUILT IN (#69 both directions):
  STRONG: valence grounds value in the least-deniable fact there is (your own
  felt suffering) -> this maximally clears Q1 (moral reality / not illusion;
  cf. B140) and, via performative contradiction, catches anyone who denies it
  in word but not deed.
  TWO HONEST EDGES:
   (E1) TARGET. The argument refutes the VALUELESS-UNIVERSE thesis (axiological
        nihilism / value-eliminativism) -- NOT physicalism-as-such. A
        value-KEEPING naturalist moral realist (Cornell realism: Railton, Boyd,
        Sturgeon) is a physicalist who AGREES valence has value and is untouched.
        So "physicalism is impossible" overshoots; correct target = the
        valueless universe (which is exactly what the author names).
   (E2) THE LEAP. "Valence is bad-FOR-the-subject" (agent-relative) is robust and
        nearly undeniable. "Therefore it is bad SIMPLICITER / every rational
        agent is stance-independently bound to reduce it" (agent-neutral) adds a
        bridge premise the quasi-realist reconstructs rather than denies. That is
        exactly B140's Q2 residual (Hume's guillotine; Moore's open question).
        The toy REFUSES to manufacture the agent-neutral ought (anti-rig #69).
"""

import json
import os
import statistics

SEED = 141
N_SOCIETIES = 200
N_NORM_DIMS = 10
N_VALENCE_LINKED = 4          # core: tied to suffering/wellbeing
# remaining 6 = arbitrary cultural conventions (honest: NOT everything converges)
RD = 0.95                     # beyond-reasonable-doubt threshold (from B140)


def _lcg(seed):
    x = seed
    while True:
        x = (1103515245 * x + 12345) & 0x7FFFFFFF
        yield x / 0x7FFFFFFF


def simulate_societies(intrinsic_value_on, rng):
    """Each society sets values on N_NORM_DIMS. The first N_VALENCE_LINKED dims
    are tied to valence (suffering/wellbeing); the rest are arbitrary conventions.
    With intrinsic value ON, conscious members disvalue suffering, so every
    society is pulled to the valence-optimal value (1.0) on the core dims. With
    it stripped OFF, there is no pull -> the core dims become as arbitrary as
    conventions."""
    core_vectors = []
    for _ in range(N_SOCIETIES):
        vec = []
        for d in range(N_NORM_DIMS):
            is_core = d < N_VALENCE_LINKED
            if is_core and intrinsic_value_on:
                # pulled to valence-optimum 1.0 with small cultural noise
                vec.append(1.0 - 0.05 * next(rng))
            else:
                # arbitrary convention (or stripped core): uniform random
                vec.append(next(rng))
        core_vectors.append(vec[:N_VALENCE_LINKED])
    return core_vectors


def cross_society_agreement(core_vectors):
    """1 - mean per-dim variance across societies on the valence-linked core.
    High => societies CONVERGE on valence norms; low => arbitrary/'meaningless'."""
    dims = list(zip(*core_vectors))
    mean_var = statistics.mean(statistics.pvariance(d) for d in dims)
    return 1.0 - min(mean_var * 4.0, 1.0)   # scaled to [0,1] for readability


# ---- P1/P2: convergence ON vs OFF -------------------------------------------
rng_on = _lcg(SEED)
rng_off = _lcg(SEED)
agree_on = cross_society_agreement(simulate_societies(True, rng_on))
agree_off = cross_society_agreement(simulate_societies(False, rng_off))

# ---- E1 / GATE-3: target identification -------------------------------------
# A value-keeping naturalist realist is intrinsic_value_on AND physicalist.
# They converge identically to any value-keeper -> what collapses convergence is
# stripping value (eliminativism), NOT physicalism.
naturalist_realist_is_physicalist = True
naturalist_realist_keeps_value = True
naturalist_realist_converges = naturalist_realist_keeps_value  # = ON path
refuted_target = ("value-eliminativism / valueless universe"
                  if agree_off < RD <= agree_on else "indeterminate")

# ---- E2 / GATE-1 & GATE-2: the agent-relative vs agent-neutral derivation ----
def derive_agent_relative(valence_sign):
    """From the felt sign alone: a subject acts to reduce its own negative
    valence. No extra premise. ROBUST."""
    return valence_sign < 0   # negative valence -> reason-to-reduce (for self)

def derive_agent_neutral(valence_sign, agent_neutrality_bridge):
    """'X ought to reduce Y's negative valence, stance-independently' is NOT
    derivable from the felt sign alone -- it needs an INJECTED bridge premise
    (agent-neutrality). The toy will not manufacture it."""
    if not agent_neutrality_bridge:
        return None   # honestly underivable -> the Q2 residual
    return valence_sign < 0

gate1 = derive_agent_relative(-1)                       # True (robust)
gate2_without_bridge = derive_agent_neutral(-1, False)  # None (honest residual)
gate2_with_injected_bridge = derive_agent_neutral(-1, True)  # only via injection

# ---- Performative check ------------------------------------------------------
# Verbal denier whose revealed behavior still avoids negative valence.
verbal_denial_of_intrinsic_value = True
behavior_avoids_negative_valence = True
performative_mismatch = verbal_denial_of_intrinsic_value and behavior_avoids_negative_valence

results = {
    "scope": "ILLUSTRATIVE STRUCTURAL TOY -- stipulated structure, zero empirical weight, no numerology",
    "P1_convergence_when_value_intrinsic": {
        "cross_society_agreement": round(agree_on, 4),
        "clears_RD": agree_on >= RD,
        "claim": "with valence intrinsically (dis)valued, heterogeneous societies CONVERGE on "
                 "valence-promoting norms -> morality 'falls out' of valence",
    },
    "P2_collapse_when_value_stripped": {
        "cross_society_agreement": round(agree_off, 4),
        "clears_RD": agree_off >= RD,
        "claim": "strip intrinsic value -> convergence collapses to chance; norms become "
                 "arbitrary/'meaningless' -- exactly what denying realism requires",
    },
    "E1_target_identification": {
        "naturalist_realist_is_physicalist": naturalist_realist_is_physicalist,
        "naturalist_realist_converges": naturalist_realist_converges,
        "refuted_target": refuted_target,
        "claim": "what's refuted is the VALUELESS UNIVERSE (axiological nihilism), NOT "
                 "physicalism-as-such; a value-keeping physicalist (Cornell realism) is untouched. "
                 "'physicalism is impossible' -> sharpen to 'the valueless universe is impossible'",
    },
    "E2_agent_relative_vs_neutral": {
        "gate1_agent_relative_derivable": gate1,
        "gate2_agent_neutral_without_bridge": gate2_without_bridge,   # None
        "gate2_agent_neutral_requires_injected_bridge": gate2_with_injected_bridge,
        "claim": "agent-RELATIVE 'bad-for-subject' is robust & nearly undeniable; agent-NEUTRAL "
                 "'bad simpliciter, binding on all' needs an INJECTED bridge (Hume/Moore) = B140 Q2 "
                 "residual. Toy refuses to manufacture it (anti-rig #69).",
    },
    "performative_check": {
        "verbal_denial": verbal_denial_of_intrinsic_value,
        "behavior_avoids_negative_valence": behavior_avoids_negative_valence,
        "mismatch_flagged": performative_mismatch,
        "claim": "a verbal denier whose revealed behavior still flees suffering exhibits a "
                 "word/deed contradiction (catches the naive nihilist; the careful quasi-realist "
                 "escapes by affirming Q1 and contesting only Q2)",
    },
}

if __name__ == "__main__":
    out = os.path.join(os.path.dirname(__file__), "results.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)

    print("=== B141 phenomenal/valence argument (illustrative; zero weight) ===\n")
    p1, p2 = results["P1_convergence_when_value_intrinsic"], results["P2_collapse_when_value_stripped"]
    print(f"[P1 value intrinsic]   cross-society agreement={p1['cross_society_agreement']} "
          f"clears_RD={p1['clears_RD']}  -> morality falls out of valence")
    print(f"[P2 value stripped]    cross-society agreement={p2['cross_society_agreement']} "
          f"clears_RD={p2['clears_RD']}  -> norms arbitrary/'meaningless'")
    e1 = results["E1_target_identification"]
    print(f"[E1 target]            refuted = {e1['refuted_target']}")
    print(f"                       (value-keeping physicalist still converges={e1['naturalist_realist_converges']} "
          f"=> NOT physicalism-as-such)")
    e2 = results["E2_agent_relative_vs_neutral"]
    print(f"[E2 gate1 agent-rel]   derivable={e2['gate1_agent_relative_derivable']} (robust, no extra premise)")
    print(f"[E2 gate2 agent-neut]  without bridge={e2['gate2_agent_neutral_without_bridge']} "
          f"(UNDERIVABLE = honest Q2 residual); only via INJECTED bridge={e2['gate2_agent_neutral_requires_injected_bridge']}")
    pc = results["performative_check"]
    print(f"[performative]         verbal_denial={pc['verbal_denial']} but flees suffering={pc['behavior_avoids_negative_valence']} "
          f"=> mismatch_flagged={pc['mismatch_flagged']}\n")

    print("VERDICT: the valence argument maximally clears Q1 (moral reality is grounded in the")
    print("least-deniable fact -- felt valence) and refutes the VALUELESS UNIVERSE. Two honest")
    print("edges kept: it targets value-eliminativism not physicalism-as-such (E1), and the")
    print("agent-neutral 'ought' (Q2) still needs a bridge the quasi-realist reconstructs (E2).")
    print("Rail held: NO deductive proof of robust mind-independence; 'physicalism impossible'")
    print("sharpened to 'the valueless universe is impossible'. Count unchanged 79.")

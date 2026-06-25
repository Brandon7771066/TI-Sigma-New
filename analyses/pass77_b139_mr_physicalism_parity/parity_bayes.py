"""
B139 — Moral-Realism / Physicalism Parity, illustrative Bayesian structure.

PURPOSE (honest scope): this is a STRUCTURAL toy, not an empirical measurement.
The likelihood ratios below are STIPULATED to expose the *logical shape* of the
parity argument the author raised:

  "Moral realism is no less unprovable than physicalism; both rest primarily on
   experiential + inductive evidence; and there is a BETTER case for ethics than
   for its non-existence."

It carries ZERO evidential weight (anti-numerology rail). It demonstrates three
pre-registered claims and nothing more.

Each domain compares REALISM against a *non-denying, data-respecting competitor*
(the thing the author says nonrealists lack — but which actually exists):
  - physical domain : PH (physical realism) vs IDEAL (structural/empirical
                      anti-realism that predicts the SAME observations)
  - moral   domain : MR (moral realism) vs QR (Blackburn quasi-realism, which
                      accepts every first-order datum -- it too condemns atrocity)

We accumulate evidence as log-likelihood-ratios (LLR = log P(data|realism) -
log P(data|competitor)) over four shared channels, starting from 1:1 prior odds.

PRE-REGISTERED PREDICTIONS (written before reading the output):
  P1 (parity is valid): if the two domains are given IDENTICAL channel LLRs,
     posterior(MR) == posterior(PH) exactly. Same evidence-type => same status.
  P2 (neither is "decisively closed"): whenever a competitor matches the
     first-order data (LLR ~ 0 on the channels it can mimic), the realist
     posterior is bounded strictly BELOW 1. Proof would require a channel the
     competitor cannot touch (residual -> the GME-1-F1 strengthening condition).
  P3 (the strengths trade, honestly): ethics leads on the
     livability/performative channel (you cannot LIVE as a moral nihilist),
     physics leads on indispensability/novel-prediction. Net is a WASH
     (near-parity); WHICH one edges ahead is an artifact of a CONTESTED
     weighting (the live Harman/Sturgeon dispute over moral explanations), so
     the only robust claims are P1 (parity) and P2 (neither closes). We do NOT
     assert ethics is strictly superior -- only that it is NOT inferior, which
     is itself the under-appreciated result.
"""

import json
import math
import os

CHANNELS = ["experiential", "inductive_convergence", "indispensability", "livability"]


def posterior_from_llrs(llrs, prior_odds=1.0):
    """Combine independent channel LLRs into a posterior P(realism|data)."""
    log_odds = math.log(prior_odds) + sum(llrs[c] for c in CHANNELS)
    odds = math.exp(log_odds)
    return odds / (1.0 + odds)


def residual_to_proof(p):
    return 1.0 - p


# ---------------------------------------------------------------------------
# Scenario A — STRICT PARITY (sanity): identical evidence vectors per domain.
# Demonstrates the logical core: same evidence-type => identical epistemic status.
# ---------------------------------------------------------------------------
parity_vec = {
    "experiential": 0.80,
    "inductive_convergence": 0.10,   # competitor mimics convergence => small
    "indispensability": 0.60,
    "livability": 0.70,
}
A_phys = posterior_from_llrs(parity_vec)
A_moral = posterior_from_llrs(parity_vec)

# ---------------------------------------------------------------------------
# Scenario B — CHANNEL-REALISTIC: the two domains trade their strongest channels.
#   physics  : strongest on indispensability (predicts the unobserved; the
#              idealist must mimic post hoc) -- Sturgeon/Harman-style edge.
#   ethics   : strongest on livability (the performative point) -- but the
#              quasi-realist ALSO condemns atrocity, so its edge is real but
#              not total.
# Convergence channel is ~0 for BOTH: each competitor predicts the same
# cross-cultural / inductive regularities (Curry 60 societies <-> physical law).
# ---------------------------------------------------------------------------
phys_vec = {
    "experiential": 0.80,
    "inductive_convergence": 0.05,
    "indispensability": 0.95,        # physics' strongest, hardest-to-mimic edge
    "livability": 0.55,
}
moral_vec = {
    "experiential": 0.80,
    "inductive_convergence": 0.05,
    "indispensability": 0.45,        # moral explanations contested (Harman/Sturgeon)
    "livability": 1.00,              # nihilism is the least livable stance
}
B_phys = posterior_from_llrs(phys_vec)
B_moral = posterior_from_llrs(moral_vec)

# ---------------------------------------------------------------------------
# Scenario C — SENSITIVITY: posterior(MR) -> 1 ONLY as the quasi-realist's
# match on the first-order channels degrades. We sweep a "competitor mismatch"
# bonus added to the channels QR currently mimics (convergence + livability):
# this models discovering a datum the anti-realist canNOT reconstruct
# (= the GME-1-F1 strengthening condition). Closure is approached but the
# point is WHAT it would take, not that it has happened.
# ---------------------------------------------------------------------------
sweep = []
for mismatch in [0.0, 0.5, 1.0, 2.0, 4.0, 8.0]:
    v = dict(moral_vec)
    v["inductive_convergence"] += mismatch
    v["livability"] += mismatch
    sweep.append({"competitor_mismatch": mismatch,
                  "posterior_MR": round(posterior_from_llrs(v), 6)})

results = {
    "scope": "ILLUSTRATIVE STRUCTURAL TOY — stipulated likelihoods, zero empirical weight, no numerology",
    "scenario_A_strict_parity": {
        "channel_LLRs": parity_vec,
        "posterior_physicalism": round(A_phys, 6),
        "posterior_moral_realism": round(A_moral, 6),
        "equal": abs(A_phys - A_moral) < 1e-12,
        "claim": "P1 parity is VALID: identical evidence-type => identical posterior",
    },
    "scenario_B_channel_realistic": {
        "phys_LLRs": phys_vec,
        "moral_LLRs": moral_vec,
        "posterior_physicalism": round(B_phys, 6),
        "posterior_moral_realism": round(B_moral, 6),
        "moral_minus_phys": round(B_moral - B_phys, 6),
        "residual_to_proof_phys": round(residual_to_proof(B_phys), 6),
        "residual_to_proof_moral": round(residual_to_proof(B_moral), 6),
        "claim": "P2/P3: near-parity WASH (domains trade strengths); the tiny ordering is an "
                 "artifact of a contested weighting, NOT a ranking; ethics is NOT inferior; "
                 "BOTH bounded < 1 (neither closed)",
    },
    "scenario_C_closure_requires_unmatched_datum": {
        "sweep": sweep,
        "claim": "P2: posterior -> 1 ONLY as the data-respecting competitor stops matching "
                 "(= a realist-only residual datum, the GME-1-F1 strengthening condition). "
                 "It has NOT happened; this shows what closure would REQUIRE.",
    },
}

if __name__ == "__main__":
    out = os.path.join(os.path.dirname(__file__), "results.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)

    print("=== B139 parity (illustrative structural toy; zero empirical weight) ===\n")
    print("PRE-REGISTERED: P1 strict-parity equal posteriors; P2 competitor-match caps posterior<1;")
    print("                P3 ethics leads livability, physics leads indispensability, net ~ parity.\n")

    a = results["scenario_A_strict_parity"]
    print(f"[A strict parity] P(physicalism)={a['posterior_physicalism']}  "
          f"P(moral realism)={a['posterior_moral_realism']}  equal={a['equal']}")

    b = results["scenario_B_channel_realistic"]
    print(f"[B realistic]     P(physicalism)={b['posterior_physicalism']}  "
          f"P(moral realism)={b['posterior_moral_realism']}  "
          f"(MR - PH = {b['moral_minus_phys']}; a WASH -- ordering is contested-weighting noise)")
    print(f"                  residual-to-proof: phys={b['residual_to_proof_phys']}  "
          f"moral={b['residual_to_proof_moral']}  -> NEITHER reaches 0\n")

    print("[C closure sweep] posterior_MR as the quasi-realist stops matching the data:")
    for row in sweep:
        print(f"    competitor_mismatch={row['competitor_mismatch']:>4}  "
              f"posterior_MR={row['posterior_MR']}")
    print("\nVERDICT: parity HOLDS (P1); ethics is NOT inferior -- the domains trade strengths,")
    print("net is a wash (P3); but 'decisively closed' overstates for BOTH equally (P2) -- closure")
    print("needs a realist-only residual the non-denying competitor cannot reconstruct. Honest")
    print("landing: moral facts are tralse-real -- the SAME status TRG-1 assigns physical reality.")

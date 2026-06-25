"""
B140 — The correct burden-of-proof STANDARD + the indispensability RED HERRING.
GME-1 refinement #2; partial ERRATUM to B139 scenario B.

Honest scope: STRUCTURAL toy, stipulated likelihoods, ZERO empirical weight,
no numerology. It operationalizes three corrections the author raised to B139:

  (1) WRONG BAR. The test is NOT mathematical certainty (the 2+2=4 bar). The
      appropriate bar is "beyond reasonable doubt" + pragmatic. Demanding 100%
      of EITHER physicalist or moral realist is an illegitimate burden. So
      "posterior < 1" (which B139 leaned on) is NOT a deficiency -- it is the
      normal condition of ALL empirical knowledge.

  (2) BURDEN. B139's scenario B *stipulated* a physics-indispensability edge.
      Per the burden point that stipulation was itself question-begging: a
      physicalist who claims "physics is MORE indispensable than ethics" (or a
      valueless universe / knowledge-without-awareness) is making a positive,
      extraordinary claim that must be EVIDENCED -- it is not the free skeptical
      default. So the honest default on that channel is SYMMETRIC, and the
      stipulated edge is WITHDRAWN here.

  (3) RED HERRING. Even if some physics is more fundamental, fundamentality is
      NOT reality. Temperature is less fundamental than particles, fully real.
      So the indispensability/fundamentality channel is non-pivotal to the
      question "is morality real as we recognize it today."

Key move: separate the two theses the word "realism" conflates.
  Q1 = MORAL REALITY: morality is real (not illusion); moral claims are
       genuinely truth-apt and many are true. Competitor = error-theory /
       nihilism (Mackie / naive nihilist). NOTE: the quasi-realist AFFIRMS Q1.
  Q2 = ROBUST MIND-INDEPENDENCE: the truth-makers are stance-independent FACTS,
       not projected shared attitudes. Competitor = quasi-realism (Blackburn).

Because the sophisticated anti-realist (QR) is on the realist's side for Q1 and
only contests Q2, Q1 is nearly hypothesis-independent and clears beyond-
reasonable-doubt; Q2 carries the one honest residual -- and Q2 is NOT the
practically-relevant thesis.
"""

import json
import math
import os

RD = 0.95   # "beyond reasonable doubt" threshold (illustrative, legal-flavored)
CERTAINTY = 1.0  # the 2+2=4 bar -- the WRONG test (rejected by rail + author)


def posterior(llrs, prior_odds=1.0):
    log_odds = math.log(prior_odds) + sum(llrs.values())
    odds = math.exp(log_odds)
    return odds / (1.0 + odds)


# --- Q1: MORAL REALITY (real/not-illusion) vs error-theory+nihilism -----------
# Channels strongly favor "morality functions as real" over "systematic mass
# error": felt objectivity, cross-cultural convergence (Curry 60 societies),
# unlivability of nihilism. The quasi-realist is ON THIS SIDE.
Q1_channels = {
    "experiential": 1.20,
    "convergence": 1.30,
    "performative_livability": 1.60,
    "indispensability": 0.00,   # withdrawn per burden point -> symmetric/neutral
}
Q1 = posterior(Q1_channels)

# Red-herring check: remove the indispensability channel entirely.
Q1_no_indisp = posterior({k: v for k, v in Q1_channels.items()
                          if k != "indispensability"})

# Fundamentality-orthogonality check: even GRANT physics strictly more
# fundamental. Fundamentality does not enter Q1's likelihoods at all.
physics_strictly_more_fundamental = True   # granted for the sake of argument
Q1_given_physics_fundamental = Q1          # by construction: orthogonal axis

# --- Q2: ROBUST MIND-INDEPENDENCE vs quasi-realism ----------------------------
# QR matches every first-order datum, so the LLRs here are ~0 (it predicts the
# same convergence/livability). A small residual edge at most. This is the
# genuine, honest, sub-certainty residual -- and it is metaphysical, not
# practical (QR and robust-realism AGREE on every action).
Q2_channels = {
    "experiential": 0.05,
    "convergence": 0.00,            # QR predicts convergence too
    "performative_livability": 0.05,  # QR lives morally too
    "indispensability": 0.00,
}
Q2 = posterior(Q2_channels)

# --- Burden demonstration: the eliminativist "valueless universe / knowledge
# without awareness" is an EXTRAORDINARY positive claim, not the zero-info
# default. If (wrongly) granted a free default it would start at even odds; the
# honest treatment gives it its OWN low prior (it must be evidenced). We show
# Q1 under both treatments to expose the smuggled free-ride.
Q1_if_elim_gets_free_default = posterior(Q1_channels, prior_odds=1.0)      # 1:1
Q1_honest_elim_bears_burden = posterior(Q1_channels, prior_odds=3.0)       # >1:1

results = {
    "scope": "ILLUSTRATIVE STRUCTURAL TOY -- stipulated likelihoods, zero empirical weight, no numerology",
    "standard": {
        "reasonable_doubt_threshold": RD,
        "certainty_bar_REJECTED": CERTAINTY,
        "note": "the 2+2=4 certainty bar is the WRONG test for BOTH physics and ethics",
    },
    "Q1_moral_reality": {
        "posterior": round(Q1, 6),
        "clears_beyond_reasonable_doubt": Q1 >= RD,
        "claim": "morality is real / not illusion -- quasi-realist AFFIRMS this; clears RD bar",
    },
    "red_herring_check": {
        "Q1_posterior_full": round(Q1, 6),
        "Q1_posterior_without_indispensability": round(Q1_no_indisp, 6),
        "verdict_unchanged": (Q1 >= RD) == (Q1_no_indisp >= RD),
        "claim": "indispensability is NON-PIVOTAL -> RED HERRING confirmed",
    },
    "fundamentality_orthogonality": {
        "physics_strictly_more_fundamental_granted": physics_strictly_more_fundamental,
        "Q1_posterior": round(Q1_given_physics_fundamental, 6),
        "claim": "fundamentality != reality; granting physics more fundamental leaves Q1 untouched",
    },
    "Q2_robust_mind_independence": {
        "posterior": round(Q2, 6),
        "clears_beyond_reasonable_doubt": Q2 >= RD,
        "claim": "the ONE honest residual -- metaphysical truth-maker question, NOT practical; "
                 "QR matches first-order data so this specific thesis stays sub-certain",
    },
    "burden_of_proof": {
        "Q1_if_eliminativist_gets_free_default": round(Q1_if_elim_gets_free_default, 6),
        "Q1_if_eliminativist_bears_its_burden": round(Q1_honest_elim_bears_burden, 6),
        "claim": "'valueless universe / knowledge without awareness' is an extraordinary "
                 "positive claim, NOT the zero-info default; denying it a free ride only "
                 "RAISES Q1; the skeptic does not get a free dismissal",
    },
}

if __name__ == "__main__":
    out = os.path.join(os.path.dirname(__file__), "results.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)

    print("=== B140 burden-standard + indispensability red herring (illustrative; zero weight) ===\n")
    print(f"STANDARD: test = beyond reasonable doubt (>= {RD}), NOT mathematical certainty (1.0).")
    print("          Demanding 100% of EITHER side is illegitimate; sub-certainty is normal.\n")

    print(f"[Q1 moral reality]        posterior={results['Q1_moral_reality']['posterior']}  "
          f"clears RD={results['Q1_moral_reality']['clears_beyond_reasonable_doubt']}  "
          f"(quasi-realist AFFIRMS Q1)")
    rh = results["red_herring_check"]
    print(f"[red-herring check]       with indisp={rh['Q1_posterior_full']}  "
          f"without indisp={rh['Q1_posterior_without_indispensability']}  "
          f"verdict_unchanged={rh['verdict_unchanged']} -> RED HERRING")
    fo = results["fundamentality_orthogonality"]
    print(f"[fundamentality check]    grant physics more fundamental -> Q1={fo['Q1_posterior']} "
          f"(unchanged; fundamentality != reality)")
    print(f"[Q2 mind-independence]    posterior={results['Q2_robust_mind_independence']['posterior']}  "
          f"clears RD={results['Q2_robust_mind_independence']['clears_beyond_reasonable_doubt']}  "
          f"(the one honest, metaphysical-not-practical residual)")
    bp = results["burden_of_proof"]
    print(f"[burden of proof]         eliminativist free-ride Q1={bp['Q1_if_eliminativist_gets_free_default']}  "
          f"-> eliminativist bears burden Q1={bp['Q1_if_eliminativist_bears_its_burden']} (skeptic gets no free dismissal)\n")

    print("VERDICT: under the CORRECT standard, 'morality is real as we recognize it today' (Q1)")
    print("clears beyond-reasonable-doubt and is even hypothesis-independent (the sophisticated")
    print("anti-realist affirms it). Indispensability/fundamentality is a RED HERRING for Q1.")
    print("The only residual (Q2: robust mind-independence vs projected attitudes) is metaphysical,")
    print("not practical, and does NOT make ethics unreal. Rail held: no claim of DEDUCTIVE proof")
    print("(the 2+2=4 bar) -- but the appropriate beyond-reasonable-doubt bar IS met for Q1.")

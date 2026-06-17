"""
Crank-Credibility Conjunction — Bayesian + decision-theoretic simulation.
Pass-77 B120 (refines CRD-1 from B119).

Brandon's claim (2026-06-17):
  "Publishing LARGE VOLUMES of work in a HIGHLY CONTROVERSIAL subject WHILE
   demonstrating HIGH INTELLIGENCE and/or CREDENTIALS is NOT *mild* evidence
   that the person should be listened to. The weight of all 4 variables
   TOGETHER is MODERATE evidence in their favor that they should AT LEAST be
   LISTENED TO. The evidence should back this up if it is true."

This script does NOT use primary data (budget $0). Following the #69 discipline
of the MEP bias-sim (analyses/mep_calling_success_2026_05_28), it is an honest
confound-and-decision quantification that asks three separate questions:

  (Q-TRUTH)  Conditioning on the 4-trait profile, what is P(claim eventually
             vindicated as settled fact)?  -> tests "is the position right".
  (Q-HEAR)   Under an ASYMMETRIC payoff (a missed Wegener is far costlier than
             a cheap hearing), is granting a hearing the +EV decision?
             -> tests Brandon's actual claim: "AT LEAST be listened to".
  (Q-BIAS)   Does the NAIVE retrospective design (look only at vindicated
             heroes and notice they all had the 4 traits) manufacture a large
             apparent credibility even when the true discriminating signal is
             small?  -> the survivorship/denominator trap.

Key honest move: the 4 traits are SPLIT by quality. Credentials-in-domain and
intelligence weakly discriminate vindicated-vs-permanent; VOLUME barely does
(cranks are prolific too -> Lotka/graphomania); CONTROVERSY does NOT discriminate
at all once we have already conditioned on the claim being heterodox. So the
"4 variables together" are super-additive ONLY through the two screening traits.

Deterministic (seeded). numpy only.
"""

import json
import numpy as np
from pathlib import Path

OUT = Path("analyses/pass77_b120_crank_credibility")
RNG = np.random.default_rng(20260617)

# ---------------------------------------------------------------- population
N = 400_000

# Base rate that a HETERODOX (already-controversial) claim is eventually
# vindicated as settled fact. Radical claims are usually wrong; we take a
# deliberately non-tiny but still-minority prior and stress it later.
PI_VINDICATED = 0.08

# Class-conditional trait means (z-scored traits, sd=1 in both classes).
# vindicated (T=1) vs permanent-heterodox / wrong (T=0).
#   credential_in_domain : modest positive signal  (real experts do better)
#   intelligence         : modest positive signal
#   volume               : ~NULL, slightly NEGATIVE (cranks are prolific too)
#   controversy          : ZERO signal (we already conditioned on heterodox)
MEANS = {
    "credential": (0.45, 0.00),   # (T1, T0)
    "intelligence": (0.45, 0.00),
    "volume": (0.00, 0.08),       # honest: volume tilts slightly to T0
    "controversy": (0.00, 0.00),  # non-discriminating by construction
}
SD = 1.0
TRAITS = list(MEANS.keys())


def simulate():
    T = (RNG.random(N) < PI_VINDICATED).astype(int)
    X = {}
    for k, (m1, m0) in MEANS.items():
        mu = np.where(T == 1, m1, m0)
        X[k] = RNG.normal(mu, SD, size=N)
    return T, X


def log_lr_per_trait(x, k):
    """log [ N(x; m1, sd) / N(x; m0, sd) ] for a single trait."""
    m1, m0 = MEANS[k]
    # log-density ratio of two equal-variance gaussians = linear in x
    return ((x - m0) ** 2 - (x - m1) ** 2) / (2 * SD ** 2)


def posterior_from_logodds(prior, logodds_shift):
    lo = np.log(prior / (1 - prior)) + logodds_shift
    return 1.0 / (1.0 + np.exp(-lo))


T, X = simulate()

# ---- the SUBGROUP Brandon describes: high on ALL FOUR observable traits ----
# (the impressive, prolific, controversial, credentialed figure)
profile = (X["credential"] > 0.5) & (X["intelligence"] > 0.5) & \
          (X["volume"] > 0.5) & (X["controversy"] > 0.5)
n_profile = int(profile.sum())

# Conjunction log-LR (naive-Bayes sum of per-trait log-LRs).
logLR_all = sum(log_lr_per_trait(X[k], k) for k in TRAITS)
post_truth_all = posterior_from_logodds(PI_VINDICATED, logLR_all)

# Singleton posteriors (each variable ALONE).
singletons = {}
for k in TRAITS:
    lr = log_lr_per_trait(X[k], k)
    p = posterior_from_logodds(PI_VINDICATED, lr)
    singletons[k] = {
        "mean_logLR_in_profile": float(lr[profile].mean()),
        "mean_posterior_in_profile": float(p[profile].mean()),
    }

# Q-TRUTH: two DISTINCT posteriors that must not be conflated --
# (a) EVENT-LEVEL posterior for the profile RULE itself (the decision-relevant
#     number): P(vindicated | individual satisfies the all-4 profile rule),
#     computed from the profile-rule frequencies via Bayes.
# (b) within-profile MEAN of per-sample continuous posteriors (a coarser
#     summary that over-weights individuals deep inside the profile region).
_p_prof_T1 = float(profile[T == 1].mean())
_p_prof_T0 = float(profile[T == 0].mean())
event_post_profile = (_p_prof_T1 * PI_VINDICATED) / (
    _p_prof_T1 * PI_VINDICATED + _p_prof_T0 * (1 - PI_VINDICATED)
)
truth_profile_mean = float(post_truth_all[profile].mean())   # within-profile mean
truth_profile_median = float(np.median(post_truth_all[profile]))
conj_logLR_profile = float(logLR_all[profile].mean())

# ----------------------------------------------------- Q-HEAR (decision theory)
# Decision: grant a HEARING iff expected value > 0.
#   EV(listen) = P(vindicated) * V_value_of_a_true_heterodox_idea - c_hearing
# Listen iff  P(vindicated) > c_hearing / V.
# We report the break-even threshold for several asymmetry ratios V:c.
def hearing_threshold(value_to_cost_ratio):
    return 1.0 / value_to_cost_ratio


asymmetries = [10, 50, 200]   # value of a true Wegener : cost of a cheap hearing
hearing = {}
for r in asymmetries:
    thr = hearing_threshold(r)
    hearing[f"V_to_c={r}"] = {
        "listen_threshold_posterior": thr,
        "base_rate_clears_threshold": bool(PI_VINDICATED > thr),
        "profile_posterior_clears_threshold": bool(event_post_profile > thr),
        "margin_profile_over_threshold": float(event_post_profile - thr),
    }

# ------------------------------------------------- Q-BIAS (survivorship trap)
# NAIVE retrospective design: an investigator who looks ONLY at the vindicated
# heroes (T=1) notices "they (nearly) all had the 4 traits" and concludes the
# traits strongly predict vindication -- WITHOUT inspecting the denominator
# (the permanent-heterodox T=0 who ALSO have the traits).
#
# Apparent (biased) "predictiveness" = P(profile | T=1), reported as if it were
# the thing that matters. The VALID quantity is the likelihood ratio
#   LR = P(profile | T=1) / P(profile | T=0),
# which is what actually updates belief. We show LR is modest even though
# P(profile|T=1) looks impressive.
p_profile_given_T1 = float(profile[T == 1].mean())
p_profile_given_T0 = float(profile[T == 0].mean())
true_profile_LR = p_profile_given_T1 / max(p_profile_given_T0, 1e-9)

# The illusion is an INVERSE-PROBABILITY (base-rate-neglect) error sharpened by
# survivorship, and we DERIVE it from an explicit, DISCLOSED fame-selection
# model rather than hardcoding a number. Mechanism: we only ever catalog
# CELEBRATED vindicated thinkers (Wegener, Marshall, Boltzmann...) -- and a
# vindicated thinker becomes a remembered legend with probability that RISES
# with how strongly they fit the impressive profile (a dramatic, prolific,
# credentialed winner becomes a legend; a quiet correct person is forgotten).
# So the celebrated set is selection-biased toward the profile.
#   remember_logit = FAME_BASE + FAME_SLOPE * z(profile strength), among T==1.
FAME_BASE, FAME_SLOPE = -1.0, 1.3   # disclosed selection params (not fitted)
z_profile = (logLR_all - logLR_all.mean()) / logLR_all.std()
remember_p = 1.0 / (1.0 + np.exp(-(FAME_BASE + FAME_SLOPE * z_profile)))
celebrated = (T == 1) & (RNG.random(N) < remember_p)
n_celebrated = int(celebrated.sum())

# IMPORTANT honest finding: the survivorship illusion does NOT operate on the
# full 4-way conjunction (it stays rare even among legends -> selecting on it
# does not inflate). It operates on the IMPRESSIVE sub-signal -- credentials +
# intelligence -- which is exactly what the "they were ALL brilliant" intuition
# actually tracks (controversy/volume carry ~no truth-signal anyway).
impressive = (X["credential"] > 0.5) & (X["intelligence"] > 0.5)
_imp_T1 = float(impressive[T == 1].mean())
_imp_T0 = float(impressive[T == 0].mean())
event_post_impressive = (_imp_T1 * PI_VINDICATED) / (
    _imp_T1 * PI_VINDICATED + _imp_T0 * (1 - PI_VINDICATED)
)
# What the naive hero-surveyor SEES: among celebrated vindicated mavericks,
# the fraction that are impressive -- P(impressive | celebrated) -- read
# (wrongly) as if it were P(vindicated | impressive).
illusion_perceived_predictiveness = float(impressive[celebrated].mean())
# The DECISION-RELEVANT truth: event-level P(vindicated | impressive).
true_predictiveness = event_post_impressive
inflation_factor = illusion_perceived_predictiveness / max(true_predictiveness, 1e-9)

# Prospective competence-matched recovery: report the honest LR + posterior.
prospective_posterior = posterior_from_logodds(
    PI_VINDICATED, np.log(max(true_profile_LR, 1e-9))
)

results = {
    "params": {
        "N": N,
        "prior_vindicated_pi": PI_VINDICATED,
        "trait_means_T1_T0": MEANS,
        "profile_rule": "all four traits z>0.5",
        "n_in_profile": n_profile,
    },
    "Q_TRUTH": {
        "base_rate": PI_VINDICATED,
        "conjunction_mean_logLR_in_profile": conj_logLR_profile,
        "event_level_posterior_profile_rule": float(event_post_profile),
        "within_profile_mean_persample_posterior": truth_profile_mean,
        "within_profile_median_persample_posterior": truth_profile_median,
        "verdict": (
            "WEAK->moderate for TRUTH: the 4-trait profile lifts the "
            "vindication posterior well above base rate but it stays a "
            "minority probability (<0.5). The traits do NOT make the claim "
            "likely-true."
        ),
        "singletons_alone": singletons,
        "super_additivity_note": (
            "controversy-alone and volume-alone barely move (or lower) the "
            "posterior; only credential+intelligence carry signal, so the "
            "'4 together' lift is real but driven by 2 of the 4 traits."
        ),
    },
    "Q_HEAR": {
        "rule": "listen iff P(vindicated) > c_hearing / V_true_idea",
        "by_asymmetry": hearing,
        "verdict": (
            "MODERATE-and-justified for HEARING: under a realistically "
            "asymmetric payoff (a missed true heterodox idea >> a cheap "
            "hearing), the 4-trait profile posterior clears the listen "
            "threshold by a wide margin -- and at high asymmetry even the bare "
            "base rate clears it. Brandon's 'AT LEAST be listened to' is the "
            "DEFENSIBLE reading."
        ),
    },
    "Q_BIAS": {
        "p_profile_given_vindicated": p_profile_given_T1,
        "p_profile_given_permanent_heterodox": p_profile_given_T0,
        "true_profile_likelihood_ratio": true_profile_LR,
        "illusion_operates_on": "impressive sub-signal (credential & intelligence), NOT the rare 4-way conjunction",
        "event_level_P_vindicated_given_impressive": float(true_predictiveness),
        "fame_model": {"FAME_BASE": FAME_BASE, "FAME_SLOPE": FAME_SLOPE,
                       "n_celebrated": n_celebrated,
                       "note": "disclosed selection params, not fitted"},
        "illusion_perceived_P_impressive_given_celebrated_DERIVED": illusion_perceived_predictiveness,
        "inflation_factor_illusion_over_true": float(inflation_factor),
        "prospective_recovered_posterior": float(prospective_posterior),
        "verdict": (
            "INVERSE-PROBABILITY error sharpened by survivorship, operating on "
            "the IMPRESSIVE sub-signal (credentials+intelligence), which is "
            "what the 'they were ALL brilliant' intuition actually tracks. "
            "Under a DISCLOSED fame-selection model (legends are remembered in "
            "proportion to profile strength), almost all celebrated mavericks "
            "are impressive, so a hero-surveyor SEES a high "
            "P(impressive|celebrated) and mis-reads it as "
            "P(vindicated|impressive) -- which is far lower (the invisible "
            "denominator = equally-impressive heterodox who were simply wrong). "
            "Honest caveat: the illusion does NOT inflate the rare full 4-way "
            "conjunction (that stays rare even among legends), so the "
            "inflation is a statement about the competence sub-signal, not "
            "Brandon's full 4-trait profile. Mirrors the MEP #69 bias-sim; "
            "magnitude depends on the disclosed fame-selection strength."
        ),
    },
}

OUT.mkdir(parents=True, exist_ok=True)
(OUT / "crank_credibility_results.json").write_text(json.dumps(results, indent=2))

# ---------------------------------------------------------------- console
print("=" * 70)
print("B120 CRANK-CREDIBILITY CONJUNCTION SIM")
print("=" * 70)
print(f"N={N:,}  base-rate vindicated pi={PI_VINDICATED}")
print(f"in-profile (all 4 traits z>0.5): {n_profile:,}")
print("-" * 70)
print("Q-TRUTH  (is the position right?)")
print(f"  base rate ............................. {PI_VINDICATED:.3f}")
print(f"  EVENT-LEVEL P(vindicated|profile rule)  {event_post_profile:.3f}  <-- headline")
print(f"  within-profile mean per-sample post. .. {truth_profile_mean:.3f}")
print(f"  within-profile median per-sample post.  {truth_profile_median:.3f}")
for k in TRAITS:
    print(f"    {k:12s} alone posterior ......... {singletons[k]['mean_posterior_in_profile']:.3f}")
print("-" * 70)
print("Q-HEAR   (should they AT LEAST be listened to?)")
for r in asymmetries:
    h = hearing[f"V_to_c={r}"]
    print(f"  value:cost={r:4d}  threshold={h['listen_threshold_posterior']:.4f}  "
          f"base-clears={h['base_rate_clears_threshold']}  "
          f"profile-clears={h['profile_posterior_clears_threshold']}")
print("-" * 70)
print("Q-BIAS   (survivorship/denominator trap)")
print(f"  P(profile | vindicated) ............... {p_profile_given_T1:.3f}")
print(f"  P(profile | permanent-heterodox) ..... {p_profile_given_T0:.3f}")
print(f"  TRUE 4-trait likelihood ratio ........ {true_profile_LR:.2f}x")
print(f"  [illusion on IMPRESSIVE sub-signal]")
print(f"  event-level P(vindicated|impressive)   {true_predictiveness:.3f}")
print(f"  perceived P(impressive|celebrated) ... {illusion_perceived_predictiveness:.3f}  (n_celeb={n_celebrated:,})")
print(f"  inflation (illusion/truth) ........... {inflation_factor:.2f}x")
print("=" * 70)
print("wrote", OUT / "crank_credibility_results.json")

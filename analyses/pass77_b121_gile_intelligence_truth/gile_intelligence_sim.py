"""
Pass-77 B121 -- GILE-Intelligence Truth-Tracking (GIT-1) simulation.

Brandon's challenge (2026-06-17): CRD-1b's "truth prior = WEAK" used GENERIC
problem-solving intelligence (g / IQ). But GILE defines intelligence as a
four-faced construct -- Rationality, Creativity, Altruism (loving orientation),
Environmental integration -- and BY DEFINITION GILE-intelligence is a strong
orientation toward truth. Prediction: GILE-intelligence is the "one redeeming
factor" that LIFTS credentials + contemplation-time into truth; "true quacks"
are high in raw cognition but LACK >=1 GILE component.

This sim does four honest jobs (#69 -- no fabricated effect size, $0 data):

  (Q1) Reproduce that GENERIC g is a WEAK truth predictor (the Nobel-disease
       fact CRD-1b correctly captured).
  (Q2) Show that GILE-intelligence -- when measured PROSPECTIVELY and
       OUTCOME-BLIND -- predicts truth FAR more strongly.
  (Q3) Resolve the quack paradox: high-g quacks score LOW on >=1 GILE component;
       and show the MULTIPLIER (GILE lifts credentials/contemplation -- "the
       redeeming factor that lifts the others").
  (Q4) Demarcate the HONEST claim (GIT-1) from the CIRCULAR one: if the
       definition peeks at the outcome ("GILE-intelligence == truth-orientation"),
       you manufacture a fake ~1.0 predictor that is UNFALSIFIABLE
       (No-True-Scotsman). The honest, outcome-blind version is bounded.

IMPORTANT LIMITATION (stated up front, not buried): with no primary data this
sim BUILDS IN the partial GILE->truth correlation. It therefore CANNOT prove
GILE-intelligence predicts truth in the real world. What it CAN do is (a) show
the structure is internally coherent and resolves the quack paradox, (b) show
the multiplier ("lifts the others") is identifiable, and (c) quantify the gap
between the falsifiable prospective definition and the unfalsifiable circular
one. Real test = falsifier GIT-1-F1 (prospective GILE ratings on a labeled
cohort). Same discipline as the MEP #69 calling-success bias-sim.

Deterministic: numpy default_rng(seed=20260617).
"""

import json
import os
import numpy as np

SEED = 20260617
rng = np.random.default_rng(SEED)
N = 400_000
HERE = os.path.dirname(os.path.abspath(__file__))


def sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))


def z(x):
    return (x - x.mean()) / x.std()


def auc(scores, labels):
    """Mann-Whitney AUC, ties handled via rank averaging."""
    order = np.argsort(scores, kind="mergesort")
    ranks = np.empty(len(scores), dtype=float)
    s = scores[order]
    r = np.arange(1, len(scores) + 1, dtype=float)
    i = 0
    while i < len(s):
        j = i
        while j + 1 < len(s) and s[j + 1] == s[i]:
            j += 1
        ranks[order[i:j + 1]] = r[i:j + 1].mean()
        i = j + 1
    pos = labels == 1
    n_pos = pos.sum()
    n_neg = len(labels) - n_pos
    if n_pos == 0 or n_neg == 0:
        return float("nan")
    return float((ranks[pos].sum() - n_pos * (n_pos + 1) / 2) / (n_pos * n_neg))


def event_posterior(profile_mask, vindicated):
    """Event-level P(vindicated | profile rule) -- the decision-relevant
    quantity (B120 lesson: use event-level, NOT within-profile mean)."""
    if profile_mask.sum() == 0:
        return float("nan")
    return float(vindicated[profile_mask].mean())


# ==========================================================================
# DISCLOSED PARAMETERS (all hand-set; this is a STRUCTURE model, not a fit)
# ==========================================================================
PI_BASE = 0.08            # base rate of eventual vindication (matches B120/CRD-1)

# GILE-intelligence component weights (latent composite). Rationality and
# Environmental-integration dominate -- the literature's verdict (Stanovich:
# rationality-disposition, not IQ, resists myside bias; Tetlock: integrating/
# updating foxes beat hedgehogs). Altruism = epistemic good-faith (Galef
# scout-mindset); Creativity generates hypotheses but does not calibrate.
W_R, W_C, W_A, W_E = 0.35, 0.15, 0.15, 0.35

B_GILE  = 2.30            # strong main effect of latent GILE-intelligence
B_G     = 0.18            # generic problem-solving g: near-null (Nobel disease)
B_INTER = 1.20            # GILE x (credentials+contemplation) MULTIPLIER term
B_CRED_ALONE = 0.05       # credentials with ZERO GILE: almost nothing
B_CONTRO = 0.0            # controversy: zero truth-signal (carried from CRD-1)

# RTI-1 / TRG-1 ceiling: even perfect GILE-intelligence only LEANS toward truth
# -- residual tralseness floor forbids certainty. Disclosed cap < 1.0.
RTI_CEILING = 0.85

# Prospective measurement noise: an outcome-blind rater scores each GILE
# component with error. This is what makes the honest version falsifiable
# (and < perfect). Disclosed sd.
MEAS_SD = 0.55

# ==========================================================================
# 1. LATENT TRAITS
# ==========================================================================
g = rng.standard_normal(N)
R = 0.30 * g + np.sqrt(1 - 0.30**2) * rng.standard_normal(N)   # rationality-disposition (AOT)
C = 0.30 * g + np.sqrt(1 - 0.30**2) * rng.standard_normal(N)   # creativity
A = rng.standard_normal(N)                                     # altruism / epistemic good-faith
E = rng.standard_normal(N)                                     # environmental integration (openness/updating)

credentials   = 0.55 * g + np.sqrt(1 - 0.55**2) * rng.standard_normal(N)
contemplation = 0.20 * A + np.sqrt(1 - 0.20**2) * rng.standard_normal(N)
controversy   = rng.standard_normal(N)

GILE_latent   = W_R * R + W_C * C + W_A * A + W_E * E
GILE_latent_z = z(GILE_latent)
resource      = z(credentials + contemplation)   # "the others" the multiplier acts on

# ==========================================================================
# 2. TRUE VINDICATION MODEL (with RTI-1 ceiling)
# ==========================================================================
lin = (B_GILE * GILE_latent_z
       + B_G * z(g)
       + B_CRED_ALONE * resource
       + B_INTER * (GILE_latent_z * resource)
       + B_CONTRO * z(controversy))

# calibrate intercept so mean(P) ~ PI_BASE under the ceiling.
b0 = -2.30
for _ in range(80):
    p = RTI_CEILING * sigmoid(b0 + lin)
    b0 += 0.5 * (np.log(PI_BASE) - np.log(p.mean()))
p_true = RTI_CEILING * sigmoid(b0 + lin)
vindicated = (rng.random(N) < p_true).astype(int)
realized_base = float(vindicated.mean())

# ==========================================================================
# 3. MEASUREMENTS
# ==========================================================================
# (a) PROSPECTIVE, OUTCOME-BLIND GILE: latent components + rater noise. The
#     rater never sees whether the person turned out right.
R_obs = R + MEAS_SD * rng.standard_normal(N)
C_obs = C + MEAS_SD * rng.standard_normal(N)
A_obs = A + MEAS_SD * rng.standard_normal(N)
E_obs = E + MEAS_SD * rng.standard_normal(N)
GILE_obs = z(W_R * R_obs + W_C * C_obs + W_A * A_obs + W_E * E_obs)

# (b) CIRCULAR "definitional" GILE: the rater is allowed to peek at the outcome
#     ("GILE-intelligence just IS orientation-to-truth"). We model this as
#     scoring that loads heavily on the realized outcome itself. This is the
#     No-True-Scotsman trap: it predicts ~perfectly BY CONSTRUCTION and is
#     therefore unfalsifiable, not evidence.
GILE_circular = z(3.0 * (vindicated - vindicated.mean()) + 0.3 * rng.standard_normal(N))

# ==========================================================================
# Q1 -- generic g is a WEAK truth predictor
# ==========================================================================
g_top = z(g) > np.quantile(z(g), 0.75)
q1 = {
    "auc_generic_g": auc(z(g), vindicated),
    "P_vindicated_top_quartile_g": event_posterior(g_top, vindicated),
    "base_rate": realized_base,
}

# ==========================================================================
# Q2 -- prospective GILE-intelligence is a STRONG truth predictor
# ==========================================================================
gile_top = GILE_obs > np.quantile(GILE_obs, 0.75)
gile_topdecile = GILE_obs > np.quantile(GILE_obs, 0.90)
q2 = {
    "auc_GILE_prospective": auc(GILE_obs, vindicated),
    "P_vindicated_top_quartile_GILE": event_posterior(gile_top, vindicated),
    "P_vindicated_top_decile_GILE": event_posterior(gile_topdecile, vindicated),
    "lift_over_base_top_quartile": event_posterior(gile_top, vindicated) / realized_base,
}

# ==========================================================================
# Q3a -- QUACK PARADOX: among high-g people, compare the WRONG (quacks) vs the
#         RIGHT on each prospectively-measured GILE component.
# ==========================================================================
high_g = z(g) > np.quantile(z(g), 0.75)
quack = high_g & (vindicated == 0)      # high cognition, still wrong
sage  = high_g & (vindicated == 1)      # high cognition, vindicated
def m(mask, arr):
    return float(arr[mask].mean())
q3_quack = {
    "n_high_g": int(high_g.sum()),
    "n_quack_high_g_wrong": int(quack.sum()),
    "n_sage_high_g_right": int(sage.sum()),
    "component_means_quack_vs_sage (prospective, outcome-blind)": {
        "rationality_R":   {"quack": m(quack, R_obs), "sage": m(sage, R_obs)},
        "creativity_C":    {"quack": m(quack, C_obs), "sage": m(sage, C_obs)},
        "altruism_A":      {"quack": m(quack, A_obs), "sage": m(sage, A_obs)},
        "environ_integ_E": {"quack": m(quack, E_obs), "sage": m(sage, E_obs)},
        "GILE_composite":  {"quack": m(quack, GILE_obs), "sage": m(sage, GILE_obs)},
    },
}

# ==========================================================================
# Q3b -- MULTIPLIER: credentials+contemplation lift truth ONLY when GILE high.
#         Stratify by GILE tercile, measure effect of top- vs bottom-half
#         resource within each stratum.
# ==========================================================================
ter = np.quantile(GILE_obs, [1/3, 2/3])
strata = {
    "low_GILE":  GILE_obs <= ter[0],
    "mid_GILE":  (GILE_obs > ter[0]) & (GILE_obs <= ter[1]),
    "high_GILE": GILE_obs > ter[1],
}
res_hi = resource > np.median(resource)
multiplier = {}
for name, smask in strata.items():
    hi = smask & res_hi
    lo = smask & (~res_hi)
    multiplier[name] = {
        "P_vindicated_high_resource": event_posterior(hi, vindicated),
        "P_vindicated_low_resource":  event_posterior(lo, vindicated),
        "resource_effect (hi - lo)":  event_posterior(hi, vindicated) - event_posterior(lo, vindicated),
    }

# ==========================================================================
# Q4 -- CIRCULARITY TRAP: honest prospective vs unfalsifiable circular GILE
# ==========================================================================
q4 = {
    "auc_GILE_prospective_honest": auc(GILE_obs, vindicated),
    "auc_GILE_circular_peeks_at_outcome": auc(GILE_circular, vindicated),
    "note": ("The circular definition predicts near-perfectly BY CONSTRUCTION "
             "(it is scored from the outcome). It is UNFALSIFIABLE -- every "
             "wrong person is relabelled 'not truly GILE-intelligent' "
             "(No-True-Scotsman). GIT-1 uses ONLY the prospective, outcome-blind "
             "score, whose signal is strong but bounded and therefore TESTABLE."),
}

# ==========================================================================
# RTI-1 CEILING CHECK
# ==========================================================================
rti = {
    "RTI_ceiling_param": RTI_CEILING,
    "max_realized_true_probability": float(p_true.max()),
    "note": ("Even the most GILE-intelligent agent never reaches certainty: "
             "RTI-1 residual tralseness / TRG-1 (reality is tralse, not true) "
             "cap the truth-lean below 1.0. 'High likelihood', not 'must'."),
}

# ==========================================================================
# WRITE + PRINT
# ==========================================================================
results = {
    "meta": {
        "seed": SEED, "N": N, "pi_base_target": PI_BASE,
        "realized_base_rate": realized_base,
        "weights": {"R": W_R, "C": W_C, "A": W_A, "E": W_E},
        "coeffs": {"B_GILE": B_GILE, "B_g": B_G, "B_inter": B_INTER,
                   "B_cred_alone": B_CRED_ALONE, "B_controversy": B_CONTRO},
        "RTI_ceiling": RTI_CEILING, "meas_sd": MEAS_SD,
    },
    "Q1_generic_g_weak": q1,
    "Q2_prospective_GILE_strong": q2,
    "Q3a_quack_paradox": q3_quack,
    "Q3b_multiplier_GILE_lifts_resource": multiplier,
    "Q4_circularity_trap": q4,
    "RTI1_ceiling": rti,
}
out = os.path.join(HERE, "gile_intelligence_results.json")
with open(out, "w") as f:
    json.dump(results, f, indent=2)

print("=" * 72)
print("B121 GILE-INTELLIGENCE TRUTH-TRACKING (GIT-1) SIM")
print("=" * 72)
print(f"N={N:,}  realized base rate vindicated = {realized_base:.3f}")
print("-" * 72)
print("Q1  GENERIC g (problem-solving / IQ) -- expect WEAK")
print(f"  AUC(g) ............................. {q1['auc_generic_g']:.3f}")
print(f"  P(vindicated | top-quartile g) ..... {q1['P_vindicated_top_quartile_g']:.3f}  (base {realized_base:.3f})")
print("-" * 72)
print("Q2  PROSPECTIVE GILE-intelligence (outcome-blind) -- expect STRONG")
print(f"  AUC(GILE_prospective) .............. {q2['auc_GILE_prospective']:.3f}")
print(f"  P(vindicated | top-quartile GILE) .. {q2['P_vindicated_top_quartile_GILE']:.3f}  "
      f"(lift x{q2['lift_over_base_top_quartile']:.1f})")
print(f"  P(vindicated | top-decile GILE) .... {q2['P_vindicated_top_decile_GILE']:.3f}")
print("-" * 72)
print("Q3a QUACK PARADOX (high-g WRONG vs high-g RIGHT, prospective GILE)")
cm = q3_quack["component_means_quack_vs_sage (prospective, outcome-blind)"]
for k, v in cm.items():
    print(f"  {k:18s} quack={v['quack']:+.3f}  sage={v['sage']:+.3f}  gap={v['sage']-v['quack']:+.3f}")
print("-" * 72)
print("Q3b MULTIPLIER (effect of credentials+contemplation by GILE stratum)")
for name, v in multiplier.items():
    print(f"  {name:10s} resource-effect (hi-lo) = {v['resource_effect (hi - lo)']:+.3f}  "
          f"[hi={v['P_vindicated_high_resource']:.3f} lo={v['P_vindicated_low_resource']:.3f}]")
print("-" * 72)
print("Q4  CIRCULARITY TRAP")
print(f"  AUC honest prospective GILE ........ {q4['auc_GILE_prospective_honest']:.3f}  (falsifiable)")
print(f"  AUC circular (peeks at outcome) .... {q4['auc_GILE_circular_peeks_at_outcome']:.3f}  (UNFALSIFIABLE -- not evidence)")
print("-" * 72)
print("RTI-1 CEILING")
print(f"  max realized P(vindicated) ......... {rti['max_realized_true_probability']:.3f}  (cap {RTI_CEILING}; never 1.0)")
print("=" * 72)
print(f"wrote {out}")

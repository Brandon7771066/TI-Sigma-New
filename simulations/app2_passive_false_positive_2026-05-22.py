"""F-APP-2-Passive-2 — false-positive rate under pure null distributions.

Pass-61 closure. APP-2-Passive principle (Pass-58): for physiology-only-engagement
paradigms (e.g., presentiment), relax APP-1's >=2-of-3 active-engagement gate to
>=1-of-3 with compensatory effect-strength gate raised to T_BORDER=0.13534.

Falsifier F-APP-2-Passive-2: under a pure null (no signal, engagement randomly
present), APP-2-Passive must show false-positive rate <= 0.05 at large N to be
ratifiable. If FPR > 0.05, the relaxation introduces inferential leakage.
"""
import numpy as np

RNG = np.random.default_rng(20260522)
T_BORDER = 0.13534
N_SIMS = 2000
N_PER_SIM = 500
P_ENGAGEMENT = 0.5  # null: engagement uncorrelated with outcome

def app2_passive_gate(engagement_flags, observed_effect):
    """Return True iff APP-2-Passive fires CONFIRM."""
    return (sum(engagement_flags) >= 1) and (observed_effect >= T_BORDER)

def run_null_trial(n=N_PER_SIM):
    # Pure null: outcomes are random; observed "effect" is sampling noise around 0.
    outcomes = RNG.standard_normal(n)
    effect = abs(outcomes.mean())  # absolute effect (one-sided)
    engagement = [int(RNG.random() < P_ENGAGEMENT) for _ in range(3)]
    return app2_passive_gate(engagement, effect)

false_positives = sum(run_null_trial() for _ in range(N_SIMS))
fpr = false_positives / N_SIMS

# Counterfactual: pure-N-driven NHST analog
def nhst_gate(n=N_PER_SIM):
    outcomes = RNG.standard_normal(n)
    t = abs(outcomes.mean()) / (outcomes.std() / np.sqrt(n))
    return t > 1.96

nhst_fpr = sum(nhst_gate() for _ in range(N_SIMS)) / N_SIMS

print(f"APP-2-Passive false-positive rate: {fpr:.4f} (target <= 0.05)")
print(f"NHST p<0.05 false-positive rate:   {nhst_fpr:.4f} (calibration check)")
print(f"T_BORDER threshold: {T_BORDER}")
print(f"N per sim: {N_PER_SIM}, N sims: {N_SIMS}")

verdict = "F-APP-2-Passive-2 NOT REFUTED (FPR within bound)" if fpr <= 0.05 \
    else "F-APP-2-Passive-2 REFUTED (FPR exceeds 0.05 — principle leaks)"
print(f"\nVerdict: {verdict}")

# #69 honesty: pure null with absolute-mean effect-size is a STRONG test because
# T_BORDER=0.13534 was calibrated against signal-bearing distributions; on pure
# noise with n=500 the standard error is ~0.045, so observing |mean| >= 0.135
# requires ~3-sigma deviation -- expected FPR ~ 0.003. If observed FPR is far
# below 0.05, the principle passes BY CONSTRUCTION rather than by empirical
# discrimination, and ratification should NOT use this as the sole basis.
print("\n#69 note: T_BORDER on absolute-mean of n=500 N(0,1) noise expects FPR ~0.003")
print("by SE arithmetic. Pass-62 must add signal-bearing alternative-hypothesis")
print("sensitivity test before APP-2-Passive can be ratified to CANONICAL.")

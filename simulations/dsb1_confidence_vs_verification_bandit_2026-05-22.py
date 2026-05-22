"""
F-DSB-1-1 and F-DSB-1-2 simulation.

Tests the Default-Success-Belief (DSB-1) candidate canonical principle.

DSB-1 agent:  commits to highest-prior arm when prior confidence c >= tau_c.
Verify-first: requires k = 20 samples per arm before any commitment.

Signal regime  (F-DSB-1-1): prior is informative (correlated with true reward).
Noise regime   (F-DSB-1-2): prior is uniform (uninformative).

Falsifier:
  F-DSB-1-1: DSB-1 cumulative-regret ratio vs verify-first must be < 0.85
             in signal regime, else REFUTED.
  F-DSB-1-2: DSB-1 must NOT win in noise regime, else scope condition
             REFUTED (would mean DSB-1 generates signal from noise).

Pass-62 batch-1 · 2026-05-22 · #69 honest sim.
"""

import numpy as np

SEED = 20260522
RNG = np.random.default_rng(SEED)

N_ARMS = 10
T_PULLS = 1000
N_SIMS = 500
TAU_C = 0.60
VERIFY_K = 20


def simulate_one(informative_prior: bool) -> tuple[float, float]:
    """Returns (dsb1_regret, verify_first_regret) for one simulation run."""
    true_means = RNG.uniform(0.1, 0.9, size=N_ARMS)
    best = true_means.max()

    if informative_prior:
        prior = true_means + RNG.normal(0, 0.15, size=N_ARMS)
        prior = np.clip(prior, 0, 1)
    else:
        prior = RNG.uniform(0, 1, size=N_ARMS)

    # DSB-1: commit to highest-prior arm if max prior >= TAU_C.
    dsb1_regret = 0.0
    if prior.max() >= TAU_C:
        chosen = int(np.argmax(prior))
        for _ in range(T_PULLS):
            r = RNG.normal(true_means[chosen], 0.1)
            dsb1_regret += best - r
    else:
        # Fall back to random arm if no confident prior.
        chosen = int(RNG.integers(N_ARMS))
        for _ in range(T_PULLS):
            r = RNG.normal(true_means[chosen], 0.1)
            dsb1_regret += best - r

    # Verify-first: sample VERIFY_K per arm, then commit to empirical best.
    vf_regret = 0.0
    sample_means = np.zeros(N_ARMS)
    pulls_used = 0
    for arm in range(N_ARMS):
        rewards = RNG.normal(true_means[arm], 0.1, size=VERIFY_K)
        sample_means[arm] = rewards.mean()
        vf_regret += (best * VERIFY_K) - rewards.sum()
        pulls_used += VERIFY_K
    chosen = int(np.argmax(sample_means))
    remaining = T_PULLS - pulls_used
    if remaining > 0:
        rewards = RNG.normal(true_means[chosen], 0.1, size=remaining)
        vf_regret += (best * remaining) - rewards.sum()

    return dsb1_regret, vf_regret


def run_regime(label: str, informative: bool, falsifier_rule: str) -> dict:
    dsb1s = np.zeros(N_SIMS)
    vfs = np.zeros(N_SIMS)
    for s in range(N_SIMS):
        d, v = simulate_one(informative)
        dsb1s[s] = d
        vfs[s] = v
    ratio = dsb1s.mean() / vfs.mean()
    print(f"\n== {label} ==")
    print(f"  DSB-1 mean cumulative regret:        {dsb1s.mean():.3f}")
    print(f"  Verify-first mean cumulative regret: {vfs.mean():.3f}")
    print(f"  Ratio DSB-1 / verify-first:          {ratio:.4f}")
    print(f"  Falsifier rule: {falsifier_rule}")
    return {"label": label, "ratio": ratio, "dsb1": dsb1s.mean(), "vf": vfs.mean()}


def main() -> None:
    print("DSB-1 falsifier simulation")
    print(f"N_SIMS={N_SIMS}, N_ARMS={N_ARMS}, T_PULLS={T_PULLS}, "
          f"TAU_C={TAU_C}, VERIFY_K={VERIFY_K}, seed={SEED}")

    sig = run_regime(
        "F-DSB-1-1 SIGNAL regime (informative prior)",
        informative=True,
        falsifier_rule="REFUTED if ratio >= 0.85",
    )
    noi = run_regime(
        "F-DSB-1-2 NOISE regime (uninformative prior)",
        informative=False,
        falsifier_rule="scope-condition REFUTED if ratio < 0.85",
    )

    print("\n== Verdict ==")
    if sig["ratio"] < 0.85:
        print(f"  F-DSB-1-1: NOT REFUTED (ratio {sig['ratio']:.4f} < 0.85). "
              "DSB-1 holds in signal regime, pass 1 of >=2 needed for ratification.")
    else:
        print(f"  F-DSB-1-1: REFUTED (ratio {sig['ratio']:.4f} >= 0.85). "
              "DSB-1 candidate FAILS first falsifier round.")

    if noi["ratio"] >= 0.85:
        print(f"  F-DSB-1-2: scope-condition CONFIRMED "
              f"(ratio {noi['ratio']:.4f} >= 0.85, DSB-1 does NOT beat verify-first "
              "in noise regime as predicted).")
    else:
        print(f"  F-DSB-1-2: scope-condition REFUTED "
              f"(ratio {noi['ratio']:.4f} < 0.85, DSB-1 wins in pure noise "
              "which contradicts the informative-intuition scope clause).")

    print("\n#69 honesty: this is a synthetic bandit. Real-world ratification "
          "requires F-DSB-1-3 on human-task data (Klein expert-intuition corpora) "
          "before DSB-1 can be promoted to CANONICAL.")


if __name__ == "__main__":
    main()

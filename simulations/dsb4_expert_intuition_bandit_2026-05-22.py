"""
F-DSB-2-EXPERT simulation: 70%-accurate-intuition prior (Klein RPD regime).

Per Brandon (Pass-62 batch-4): prior batches drew intuition as Gaussian
noise around true means, which is NOT the regime the principle targets.
The target regime is a domain-expert agent whose intuitions are RIGHT
about 70% of the time (matches Klein RPD expert calibration AND Brandon's
own stated operating condition — established expertise, not novice guess).

Operationalization: with probability 0.70 the prior correctly ranks the
best arm at top (plus small noise on values); with probability 0.30 the
prior is misranked (random permutation). Net: argmax(prior) == argmax(true)
approximately 70% of the time, matching the stated calibration.

This re-tests all four policies (W, B, M_linear, M_strength) under the
expert regime. Hypothesis: under expert calibration, M_strength should
now help (strong intuitions are usually right), reversing the DSB-3 result.

Pass-62 batch-4 · 2026-05-22 · #69 honest sim.
"""

import numpy as np

SEED = 20260522
RNG = np.random.default_rng(SEED + 3)

N_ARMS = 10
T_PULLS = 1000
N_SIMS = 500
VERIFY_K_W = 50
VERIFY_K_M = 5
EXPERT_ACCURACY = 0.70


def make_expert_prior(true_means: np.ndarray) -> np.ndarray:
    """Prior that correctly ranks best arm ~EXPERT_ACCURACY of the time."""
    if RNG.random() < EXPERT_ACCURACY:
        # Informed prior: noise around true_means, then ensure top is preserved
        prior = true_means + RNG.normal(0, 0.10, size=N_ARMS)
        prior = np.clip(prior, 0, 1)
        # Force argmax to match true argmax (lock in the "right" intuition)
        true_best = int(np.argmax(true_means))
        if int(np.argmax(prior)) != true_best:
            prior[true_best] = prior.max() + 0.05
            prior = np.clip(prior, 0, 1)
    else:
        # Misranked prior: random permutation of plausible values
        prior = RNG.uniform(0.2, 0.9, size=N_ARMS)
    return prior


def simulate_one():
    true_means = RNG.uniform(0.1, 0.9, size=N_ARMS)
    prior = make_expert_prior(true_means)

    # Policy W
    w_reward = 0.0
    w_means = np.zeros(N_ARMS)
    for arm in range(N_ARMS):
        r = RNG.normal(true_means[arm], 0.1, size=VERIFY_K_W)
        w_means[arm] = r.mean()
        w_reward += r.sum()
    w_chosen = int(np.argmax(w_means))
    rem = T_PULLS - N_ARMS * VERIFY_K_W
    if rem > 0:
        w_reward += RNG.normal(true_means[w_chosen], 0.1, size=rem).sum()

    # Policy B
    b_chosen = int(np.argmax(prior))
    b_reward = RNG.normal(true_means[b_chosen], 0.1, size=T_PULLS).sum()

    # Shared M examination
    m_means = np.zeros(N_ARMS)
    shared_reward = 0.0
    for arm in range(N_ARMS):
        r = RNG.normal(true_means[arm], 0.1, size=VERIFY_K_M)
        m_means[arm] = r.mean()
        shared_reward += r.sum()
    rem_m = T_PULLS - N_ARMS * VERIFY_K_M

    # M_linear
    m_lin_chosen = int(np.argmax(0.5 * prior + 0.5 * m_means))
    m_lin_reward = shared_reward
    if rem_m > 0:
        m_lin_reward += RNG.normal(true_means[m_lin_chosen], 0.1, size=rem_m).sum()

    # M_strength (per-arm)
    s = 2 * np.abs(prior - 0.5)
    m_str_chosen = int(np.argmax(s * prior + (1 - s) * m_means))
    m_str_reward = shared_reward
    if rem_m > 0:
        m_str_reward += RNG.normal(true_means[m_str_chosen], 0.1, size=rem_m).sum()

    # Track: did prior get the best arm right?
    intuition_correct = int(np.argmax(prior)) == int(np.argmax(true_means))

    return w_reward, b_reward, m_lin_reward, m_str_reward, intuition_correct


def main():
    print("DSB-EXPERT simulation: 70%-accurate intuition prior (Klein RPD regime)")
    print(f"N_SIMS={N_SIMS}, N_ARMS={N_ARMS}, T_PULLS={T_PULLS}, "
          f"EXPERT_ACCURACY={EXPERT_ACCURACY}, "
          f"VERIFY_K_W={VERIFY_K_W}, VERIFY_K_M={VERIFY_K_M}, seed={SEED+3}")

    ws, bs, mls, mss = (np.zeros(N_SIMS) for _ in range(4))
    correct = 0
    for i in range(N_SIMS):
        w, b, ml, ms_, c = simulate_one()
        ws[i], bs[i], mls[i], mss[i] = w, b, ml, ms_
        correct += c

    realized_acc = correct / N_SIMS
    print(f"\n  Realized intuition accuracy: {realized_acc:.3f} "
          f"(target {EXPERT_ACCURACY:.2f})")
    print(f"\n  Policy W (Wait-and-See):           {ws.mean():.2f}")
    print(f"  Policy B (Blind-Faith on expert prior):   {bs.mean():.2f}")
    print(f"  Policy M_linear (equal weight):    {mls.mean():.2f}")
    print(f"  Policy M_strength (strength-weighted): {mss.mean():.2f}")

    def m(a, b):
        return (a / b - 1) * 100
    print(f"\n  B vs W: {m(bs.mean(), ws.mean()):+.2f}%")
    print(f"  M_linear vs W: {m(mls.mean(), ws.mean()):+.2f}%")
    print(f"  M_linear vs B: {m(mls.mean(), bs.mean()):+.2f}%")
    print(f"  M_strength vs M_linear: {m(mss.mean(), mls.mean()):+.2f}%")
    print(f"  M_strength vs B: {m(mss.mean(), bs.mean()):+.2f}%")
    print(f"  M_strength vs W: {m(mss.mean(), ws.mean()):+.2f}%")

    print("\n== Verdict (expert regime) ==")
    winner = max(("W", ws.mean()), ("B", bs.mean()),
                 ("M_linear", mls.mean()), ("M_strength", mss.mean()),
                 key=lambda x: x[1])
    print(f"  Best policy: {winner[0]} with mean reward {winner[1]:.2f}")
    if mss.mean() > mls.mean():
        print("  Strength-weighting HELPS under expert calibration "
              f"(M_strength beats M_linear by {m(mss.mean(), mls.mean()):+.2f}%). "
              "DSB-3 finding inverted in expert regime as predicted.")
    else:
        print(f"  Strength-weighting still does not help "
              f"(M_strength vs M_linear: {m(mss.mean(), mls.mean()):+.2f}%); "
              "expert calibration alone insufficient to flip the result.")
    if bs.mean() > mls.mean():
        print(f"  B (Blind-Faith on expert prior) beats M_linear by "
              f"{m(bs.mean(), mls.mean()):+.2f}% — when intuition is 70%+ accurate, "
              "even pure intuition beats examined-and-weighted intuition.")

    print("\n#69 honesty: this regime is closer to Brandon's stated condition "
          "(established expertise, calibrated intuition). It is NOT a test of "
          "the generic DSB-2 principle — it is a test of the principle WITHIN "
          "the expert-calibrated subdomain. Generalization to novice agents or "
          "uncalibrated domains requires the prior batches (DSB-2 and DSB-3).")


if __name__ == "__main__":
    main()

"""
F-O4 falsifier (companion to steelman objections doc, Pass-62 batch-6):
test Tralse-middle vs wait-and-see under HARDER conditions:

  - NON-STATIONARY reward distribution (arm means drift over time)
  - OPPORTUNITY-COST: each tick incurs a small holding cost while sampling
  - SPARSE REWARD: rewards come in occasional bursts, not uniform stream

Pre-registered prediction: under hard conditions Policy W's deficit vs
Policy M GROWS, not shrinks (per O4 structural response). If Policy W
ties or wins under hard conditions, O4's bandit-toy objection holds and
the principle's bandit-derived evidence is structurally weakened.

Pass-62 batch-6 · 2026-05-22 · #69 honest sim.
"""

import numpy as np

SEED = 20260522
RNG = np.random.default_rng(SEED + 5)

N_ARMS = 10
T_PULLS = 1000
N_SIMS = 500
VERIFY_K_W = 50
VERIFY_K_M = 5
DRIFT_STD = 0.005           # per-tick arm-mean drift (non-stationary)
HOLDING_COST = 0.05         # opportunity cost per pull (constant drain)
SPARSITY = 0.30             # probability that any given pull yields reward


def simulate_one():
    true_means = RNG.uniform(0.1, 0.9, size=N_ARMS)
    prior = true_means + RNG.normal(0, 0.15, size=N_ARMS)
    prior = np.clip(prior, 0, 1)

    def reward_draw(arm_mean: float) -> float:
        if RNG.random() < SPARSITY:
            return RNG.normal(arm_mean / SPARSITY, 0.1) - HOLDING_COST
        return -HOLDING_COST

    def drift():
        nonlocal true_means
        true_means = np.clip(true_means + RNG.normal(0, DRIFT_STD,
                                                    size=N_ARMS), 0.05, 0.95)

    # ---- Policy W: heavy verify, then commit ----
    w_reward = 0.0
    w_means = np.zeros(N_ARMS)
    w_counts = np.zeros(N_ARMS)
    for arm in range(N_ARMS):
        for _ in range(VERIFY_K_W):
            r = reward_draw(true_means[arm])
            w_reward += r
            w_means[arm] = (w_means[arm] * w_counts[arm] + r) / (w_counts[arm] + 1)
            w_counts[arm] += 1
            drift()
    w_chosen = int(np.argmax(w_means))
    remaining = T_PULLS - int(w_counts.sum())
    for _ in range(remaining):
        w_reward += reward_draw(true_means[w_chosen])
        drift()

    # ---- Reset domain for next agent (independent comparison) ----
    true_means = RNG.uniform(0.1, 0.9, size=N_ARMS)
    prior_b = true_means + RNG.normal(0, 0.15, size=N_ARMS)
    prior_b = np.clip(prior_b, 0, 1)

    # ---- Policy B: commit on prior ----
    b_chosen = int(np.argmax(prior_b))
    b_reward = 0.0
    for _ in range(T_PULLS):
        b_reward += reward_draw(true_means[b_chosen])
        drift()

    # ---- Reset for M ----
    true_means = RNG.uniform(0.1, 0.9, size=N_ARMS)
    prior_m = true_means + RNG.normal(0, 0.15, size=N_ARMS)
    prior_m = np.clip(prior_m, 0, 1)

    # ---- Policy M: light verify + prior + forward commit ----
    m_reward = 0.0
    m_means = np.zeros(N_ARMS)
    for arm in range(N_ARMS):
        rsum = 0.0
        for _ in range(VERIFY_K_M):
            r = reward_draw(true_means[arm])
            m_reward += r
            rsum += r
            drift()
        m_means[arm] = rsum / VERIFY_K_M
    score = 0.5 * prior_m + 0.5 * m_means
    m_chosen = int(np.argmax(score))
    pulls_used_m = N_ARMS * VERIFY_K_M
    for _ in range(T_PULLS - pulls_used_m):
        m_reward += reward_draw(true_means[m_chosen])
        drift()

    return w_reward, b_reward, m_reward


def main():
    print("DSB-6 adversarial-robustness simulation")
    print(f"N_SIMS={N_SIMS}, N_ARMS={N_ARMS}, T_PULLS={T_PULLS}, "
          f"VERIFY_K_W={VERIFY_K_W}, VERIFY_K_M={VERIFY_K_M}")
    print(f"Adversarial conditions: DRIFT_STD={DRIFT_STD} (non-stationary), "
          f"HOLDING_COST={HOLDING_COST} (opportunity cost), "
          f"SPARSITY={SPARSITY} (sparse reward), seed={SEED+5}")

    ws = np.zeros(N_SIMS)
    bs = np.zeros(N_SIMS)
    ms = np.zeros(N_SIMS)
    for i in range(N_SIMS):
        w, b, m = simulate_one()
        ws[i], bs[i], ms[i] = w, b, m

    print(f"\n  Policy W (Wait-and-See) mean reward:   {ws.mean():.2f}")
    print(f"  Policy B (Blind-Faith) mean reward:    {bs.mean():.2f}")
    print(f"  Policy M (Tralse-Middle) mean reward:  {ms.mean():.2f}")

    def margin(a, b):
        return (a / b - 1) * 100 if b != 0 else float('inf')

    print(f"\n  M vs W margin: {margin(ms.mean(), ws.mean()):+.2f}% "
          "(prediction: GROWS vs DSB-2's +19.8% under stationary conditions)")
    print(f"  M vs B margin: {margin(ms.mean(), bs.mean()):+.2f}%")
    print(f"  B vs W margin: {margin(bs.mean(), ws.mean()):+.2f}%")

    print("\n== Verdict on F-O4 (bandit-toy objection) ==")
    dsb2_margin = 19.84
    this_margin = margin(ms.mean(), ws.mean())
    if this_margin >= dsb2_margin:
        print(f"  F-O4 STRUCTURALLY INVERTED: M's advantage over W under "
              f"hard conditions ({this_margin:+.2f}%) >= advantage under "
              f"stationary conditions ({dsb2_margin:+.2f}%). The bandit-toy "
              "objection's structural premise (hard conditions favor W) is "
              "refuted on this test.")
    elif this_margin > 0:
        print(f"  F-O4 PARTIALLY HOLDS: M still beats W under hard conditions "
              f"({this_margin:+.2f}%) but by smaller margin than stationary "
              f"({dsb2_margin:+.2f}%). Hard conditions reduce but do not "
              "eliminate Tralse-middle advantage.")
    else:
        print(f"  F-O4 OBJECTION HOLDS: M loses to W under hard conditions "
              f"({this_margin:+.2f}%). The principle's bandit evidence does "
              "not generalize to adversarial regimes.")

    print("\n#69 honesty: this is still a synthetic bandit. The adversarial "
          "extensions (drift + holding-cost + sparsity) cover three of the "
          "five conditions O4 named (non-stationary, opportunity-cost, sparse "
          "reward). Multi-agent and irreversible-decision regimes remain "
          "untested. The principle's advantage in those regimes is a Pass-63+ "
          "open question.")


if __name__ == "__main__":
    main()

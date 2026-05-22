"""
F-DSB-2-1-EXT and F-DSB-2-2-EXT simulation: strength-weighted Tralse-middle.

Per Brandon (Pass-62 batch-3): same conditions as DSB-2 sim, but additionally
accept strong intuitions over weaker intuitions, ceteris paribus.

Operationalization: prior strength s = 2 * |prior - 0.5| in [0, 1].
  s = 0 -> prior is maximally uncertain (around 0.5), defer to empirical
  s = 1 -> prior is maximally confident (near 0 or 1), weight prior heavily

Policy M_linear:  score = 0.5*prior + 0.5*empirical          (from DSB-2 sim)
Policy M_strength: score = s*prior + (1-s)*empirical          (NEW)

Pre-registered prediction: M_strength >= M_linear in signal regime by >=1%,
and M_strength <= M_linear in noise regime by no more than 2% (the strength
heuristic should help when priors are informative and hurt only slightly when
priors are noise — the asymmetry is the test).

Pass-62 batch-3 · 2026-05-22 · #69 honest sim.
"""

import numpy as np

SEED = 20260522
RNG = np.random.default_rng(SEED + 2)

N_ARMS = 10
T_PULLS = 1000
N_SIMS = 500
VERIFY_K_W = 50
VERIFY_K_M = 5


def simulate_one(informative_prior: bool):
    true_means = RNG.uniform(0.1, 0.9, size=N_ARMS)

    if informative_prior:
        prior = true_means + RNG.normal(0, 0.15, size=N_ARMS)
        prior = np.clip(prior, 0, 1)
    else:
        prior = RNG.uniform(0, 1, size=N_ARMS)

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

    # Policy M_linear and M_strength share the examination phase
    m_means = np.zeros(N_ARMS)
    shared_reward = 0.0
    for arm in range(N_ARMS):
        r = RNG.normal(true_means[arm], 0.1, size=VERIFY_K_M)
        m_means[arm] = r.mean()
        shared_reward += r.sum()
    rem_m = T_PULLS - N_ARMS * VERIFY_K_M

    # M_linear: equal weighting
    m_lin_score = 0.5 * prior + 0.5 * m_means
    m_lin_chosen = int(np.argmax(m_lin_score))
    m_lin_reward = shared_reward
    if rem_m > 0:
        m_lin_reward += RNG.normal(true_means[m_lin_chosen], 0.1, size=rem_m).sum()

    # M_strength: per-arm strength weighting
    s = 2 * np.abs(prior - 0.5)             # in [0, 1]
    m_str_score = s * prior + (1 - s) * m_means
    m_str_chosen = int(np.argmax(m_str_score))
    m_str_reward = shared_reward
    if rem_m > 0:
        m_str_reward += RNG.normal(true_means[m_str_chosen], 0.1, size=rem_m).sum()

    return w_reward, b_reward, m_lin_reward, m_str_reward


def run_regime(label: str, informative: bool):
    ws, bs, mls, mss = (np.zeros(N_SIMS) for _ in range(4))
    for i in range(N_SIMS):
        w, b, ml, ms_ = simulate_one(informative)
        ws[i], bs[i], mls[i], mss[i] = w, b, ml, ms_
    print(f"\n== {label} ==")
    print(f"  Policy W (Wait-and-See):           {ws.mean():.2f}")
    print(f"  Policy B (Blind-Faith):            {bs.mean():.2f}")
    print(f"  Policy M_linear (equal weight):    {mls.mean():.2f}")
    print(f"  Policy M_strength (ceteris-paribus prior-strength): {mss.mean():.2f}")
    print(f"  M_strength vs M_linear margin:     "
          f"{(mss.mean()/mls.mean() - 1)*100:+.3f}%")
    print(f"  M_strength vs W margin:            "
          f"{(mss.mean()/ws.mean() - 1)*100:+.3f}%")
    print(f"  M_strength vs B margin:            "
          f"{(mss.mean()/bs.mean() - 1)*100:+.3f}%")
    return {"W": ws.mean(), "B": bs.mean(),
            "M_lin": mls.mean(), "M_str": mss.mean()}


def main():
    print("DSB-2-EXT strength-weighted Tralse-middle simulation")
    print(f"N_SIMS={N_SIMS}, N_ARMS={N_ARMS}, T_PULLS={T_PULLS}, "
          f"VERIFY_K_W={VERIFY_K_W}, VERIFY_K_M={VERIFY_K_M}, seed={SEED+2}")

    sig = run_regime("SIGNAL regime (informative prior)", informative=True)
    noi = run_regime("NOISE regime (uninformative prior)", informative=False)

    print("\n== Verdict ==")
    sig_delta = sig["M_str"] / sig["M_lin"] - 1
    noi_delta = noi["M_str"] / noi["M_lin"] - 1
    if sig_delta >= 0.01:
        print(f"  Signal regime: STRENGTH-WEIGHTING HELPS "
              f"(M_strength beats M_linear by {sig_delta*100:+.3f}% >= 1%).")
    elif sig_delta <= -0.01:
        print(f"  Signal regime: STRENGTH-WEIGHTING HURTS "
              f"(M_strength loses to M_linear by {sig_delta*100:+.3f}%).")
    else:
        print(f"  Signal regime: STRENGTH-WEIGHTING NEUTRAL "
              f"({sig_delta*100:+.3f}%, within +/-1%).")

    if noi_delta >= -0.02:
        print(f"  Noise regime: strength-weighting cost within bound "
              f"({noi_delta*100:+.3f}% >= -2%); asymmetry confirmed if signal was positive.")
    else:
        print(f"  Noise regime: STRENGTH-WEIGHTING HURTS TOO MUCH "
              f"({noi_delta*100:+.3f}% < -2%); ceteris-paribus refinement REFUTED "
              "on cost-side.")

    print("\n#69 honesty: this refines DSB-2 within the Tralse-middle family. "
          "It does not retest the W/B/M comparison (those margins already logged "
          "in dsb2_three_agent_bandit_2026-05-22.py). The strength heuristic is "
          "a known classical Bayesian-shrinkage analog; the TI Sigma framing is "
          "that 'strong intuitions deserve more weight' is the corresponding "
          "decision-policy heuristic at the agent level.")


if __name__ == "__main__":
    main()

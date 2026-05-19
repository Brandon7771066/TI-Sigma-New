"""
Pass-58 batch-1 TSS-MATH-4: TSIS Lindley-paradox immunity check.

Fix tiny effect δ=0.001 (well below T_RAND=0.0660); vary N.
Conventional NHT (M-A) expected to show Lindley behavior (FPR rises with N).
TSIS / MFD-1 (M-C) expected to be Lindley-immune (FPR stable).
"""
import json
import math
import os
import random
from statistics import mean

random.seed(20260521)
CHANCE = 0.25
N_VALUES = [100, 1000, 10000, 100000]
N_MC = 300
DELTA_TINY = 0.001  # well below T_RAND=0.0660
P_ENG = 0.5
T_RAND = 0.0660
C_LCC = 0.4370


def gen(n, delta):
    out = []
    for _ in range(n):
        eng = random.random() < P_ENG
        p = CHANCE + (delta if eng else 0)
        hit = random.random() < p
        out.append({"engaged": eng, "hit": hit})
    return out


def m_a_p_value(trials):
    n = len(trials)
    h = sum(t["hit"] for t in trials)
    se = math.sqrt(CHANCE * (1 - CHANCE) / n)
    z = (h / n - CHANCE) / se
    # one-sided p-value
    return 1 - 0.5 * (1 + math.erf(z / math.sqrt(2)))


def m_c_tsis_decision(trials):
    """TSIS four-gate (simplified)."""
    eng = [t for t in trials if t["engaged"]]
    if len(eng) < 10:
        return False
    n_eng = len(eng)
    # Gate 1: TSD-A per-event mean TIU above threshold (use hit rate excess as proxy)
    hit_rate_eng = sum(t["hit"] for t in eng) / n_eng
    effect = hit_rate_eng - CHANCE
    # Gate 2 (absolute): effect ≥ T_RAND
    if effect < T_RAND:
        return False
    # Gate 3 (absolute): "LCC" proxy via engagement-vs-outcome correlation strength
    # Compute phi correlation between engaged-status and hit
    a = sum(1 for t in trials if t["engaged"] and t["hit"])
    b = sum(1 for t in trials if t["engaged"] and not t["hit"])
    c = sum(1 for t in trials if not t["engaged"] and t["hit"])
    d = sum(1 for t in trials if not t["engaged"] and not t["hit"])
    denom = math.sqrt((a + b) * (c + d) * (a + c) * (b + d))
    if denom == 0:
        return False
    phi = (a * d - b * c) / denom
    if abs(phi) < C_LCC:
        return False
    # Gate 4: Bayesian posterior monotone/coherent — use posterior odds proxy
    p0, p1 = CHANCE, CHANCE + 0.05
    ll0 = sum(math.log(p0) if t["hit"] else math.log(1 - p0) for t in eng)
    ll1 = sum(math.log(p1) if t["hit"] else math.log(1 - p1) for t in eng)
    if ll1 <= ll0:
        return False
    return True


def run():
    print(f"TSS-MATH-4 Lindley immunity: δ_tiny={DELTA_TINY}, N_MC={N_MC}")
    results = []
    for n in N_VALUES:
        # Under tiny effect (the Lindley regime)
        m_a_rejects = 0
        m_c_confirms = 0
        for _ in range(N_MC):
            trials = gen(n, DELTA_TINY)
            if m_a_p_value(trials) < 0.05:
                m_a_rejects += 1
            if m_c_tsis_decision(trials):
                m_c_confirms += 1
        fpr_a = m_a_rejects / N_MC
        fpr_c = m_c_confirms / N_MC
        results.append({"N": n, "m_a_reject_rate_at_tiny_effect": round(fpr_a, 4),
                        "m_c_confirm_rate_at_tiny_effect": round(fpr_c, 4)})
        print(f"  N={n:7d} | M-A reject rate={fpr_a:.4f} | M-C confirm rate={fpr_c:.4f}")
    # Lindley signature: M-A FPR rises monotonically with N
    m_a_rates = [r["m_a_reject_rate_at_tiny_effect"] for r in results]
    m_c_rates = [r["m_c_confirm_rate_at_tiny_effect"] for r in results]
    m_a_lindley = m_a_rates[-1] > m_a_rates[0] + 0.10
    m_c_lindley = m_c_rates[-1] > m_c_rates[0] + 0.10
    summary = {
        "m_a_lindley_behavior_observed": m_a_lindley,
        "m_c_lindley_behavior_observed": m_c_lindley,
        "F_TSS_MATH_4_1": (
            f"REFUTED if M-C shows Lindley behavior like M-A. "
            f"M-A rates {m_a_rates}; M-C rates {m_c_rates}. "
            f"{'REFUTED' if m_c_lindley else 'NOT REFUTED (M-C Lindley-immune)'}."
        ),
    }
    print("\n=== Summary ===")
    for k, v in summary.items():
        print(f"  {k}: {v}")
    output = {"pass": "58-batch-1-TSS-MATH-4", "date": "2026-05-17",
              "config": {"CHANCE": CHANCE, "N_VALUES": N_VALUES, "N_MC": N_MC,
                         "DELTA_TINY": DELTA_TINY, "P_ENG": P_ENG,
                         "T_RAND": T_RAND, "C_LCC": C_LCC, "seed": 20260521},
              "results": results, "summary": summary}
    os.makedirs("simulations", exist_ok=True)
    out = "simulations/tss_math_4_lindley_immunity_results_2026-05-17.json"
    with open(out, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nWritten: {out}")
    return output


if __name__ == "__main__":
    run()

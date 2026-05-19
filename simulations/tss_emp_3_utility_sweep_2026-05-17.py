"""
Pass-58 batch-1 TSS-EMP-3: asymmetric-utility sensitivity sweep.

Vary utility ratio (cost-of-false-positive-celebrate / cost-of-false-negative-celebrate)
across {1.0, 2.0, 5.0, 10.0}. Measure how each method's decision boundary moves.

Hypothesis: MFD-1 dual (M-C) should respond correctly to utility changes;
APP-1 strict (M-B) is utility-insensitive by construction.

Pre-reg falsifier F-TSS-EMP-3-1: REFUTED if M-C decision rate is invariant
across utility ratios (i.e., MFD-1 is not actually utility-aware).
"""
import json
import math
import os
import random
from statistics import mean

random.seed(20260519)
CHANCE = 0.25
N_TRIALS = 1000
N_MC = 300
DELTA = 0.05
P_ENG = 0.5
UTILITY_RATIOS = [1.0, 2.0, 5.0, 10.0]


def gen(n, p_eng, delta):
    out = []
    for _ in range(n):
        eng = random.random() < p_eng
        p = CHANCE + (delta if eng else 0)
        hit = random.random() < p
        out.append({"engaged": eng, "hit": hit,
                    "tiu": max(0.1, random.gammavariate(2, 1)) if hit else 0.0})
    return out


def m_a(trials):
    n = len(trials)
    h = sum(t["hit"] for t in trials)
    se = math.sqrt(CHANCE * (1 - CHANCE) / n)
    return (h / n - CHANCE) / se


def m_b(trials):
    eng = [t for t in trials if t["engaged"]]
    if len(eng) < 10:
        return 0
    hits = [t["tiu"] for t in eng if t["hit"]]
    mt = mean(hits) if hits else 1.0
    pen = mt * CHANCE / (1 - CHANCE)
    pts = [t["tiu"] if t["hit"] else -pen for t in eng]
    from statistics import stdev
    sd = stdev(pts) if len(pts) > 1 else 1
    return sum(pts) / (sd * math.sqrt(len(eng))) if sd > 0 else 0


def m_c(trials, utility_ratio):
    eng = [t for t in trials if t["engaged"]]
    if len(eng) < 10:
        return 0
    # Bayesian posterior P(H1=signal | data) with flat prior
    p0, p1 = CHANCE, CHANCE + 0.05
    ll0 = sum(math.log(p0) if t["hit"] else math.log(1 - p0) for t in eng)
    ll1 = sum(math.log(p1) if t["hit"] else math.log(1 - p1) for t in eng)
    diff = ll1 - ll0
    post = 1 / (1 + math.exp(-diff)) if -700 < diff < 700 else (1.0 if diff > 0 else 0.0)
    # Decision threshold from utility ratio
    threshold = 1.0 / (1.0 + utility_ratio)
    return post - threshold  # positive = celebrate


def run():
    results = []
    print(f"TSS-EMP-3 utility sweep: δ={DELTA}, p_eng={P_ENG}, N={N_TRIALS}, N_MC={N_MC}")
    for u in UTILITY_RATIOS:
        # Null and signal under this utility
        null_a, null_b, null_c = [], [], []
        sig_a, sig_b, sig_c = [], [], []
        for _ in range(N_MC):
            t_null = gen(N_TRIALS, P_ENG, 0.0)
            t_sig = gen(N_TRIALS, P_ENG, DELTA)
            null_a.append(m_a(t_null)); sig_a.append(m_a(t_sig))
            null_b.append(m_b(t_null)); sig_b.append(m_b(t_sig))
            null_c.append(m_c(t_null, u)); sig_c.append(m_c(t_sig, u))
        # Decision rate under signal (TPR at method's own α=0.05 critical)
        def crit(xs, alpha=0.05):
            s = sorted(xs); idx = max(0, min(len(s) - 1, int((1 - alpha) * len(s)) - 1))
            return s[idx]
        ca, cb, cc = crit(null_a), crit(null_b), crit(null_c)
        tpr_a = sum(1 for x in sig_a if x > ca) / N_MC
        tpr_b = sum(1 for x in sig_b if x > cb) / N_MC
        tpr_c = sum(1 for x in sig_c if x > cc) / N_MC
        # Celebration rate (decision_score > 0, M-C only)
        celeb_c_signal = sum(1 for x in sig_c if x > 0) / N_MC
        celeb_c_null = sum(1 for x in null_c if x > 0) / N_MC
        results.append({"utility_ratio": u, "tpr_A": round(tpr_a, 3),
                        "tpr_B": round(tpr_b, 3), "tpr_C": round(tpr_c, 3),
                        "celebrate_rate_C_under_signal": round(celeb_c_signal, 3),
                        "celebrate_rate_C_under_null": round(celeb_c_null, 3)})
        print(f"  U={u:4.1f} | TPR A={tpr_a:.3f} B={tpr_b:.3f} C={tpr_c:.3f} | "
              f"M-C celeb signal={celeb_c_signal:.3f} null={celeb_c_null:.3f}")
    # Falsifier check: M-C celebrate_rate should DECREASE as utility ratio rises
    # (higher penalty for FP-celebrate → more conservative)
    celeb_rates_signal = [r["celebrate_rate_C_under_signal"] for r in results]
    celeb_rates_null = [r["celebrate_rate_C_under_null"] for r in results]
    monotone = all(celeb_rates_signal[i] >= celeb_rates_signal[i + 1]
                   for i in range(len(celeb_rates_signal) - 1))
    null_monotone = all(celeb_rates_null[i] >= celeb_rates_null[i + 1]
                        for i in range(len(celeb_rates_null) - 1))
    summary = {
        "celeb_rate_C_signal_range": [min(celeb_rates_signal), max(celeb_rates_signal)],
        "celeb_rate_C_signal_monotone_decreasing": monotone,
        "celeb_rate_C_null_monotone_decreasing": null_monotone,
        "F_TSS_EMP_3_1": (
            f"REFUTED if M-C celebrate rate invariant across utility ratios. "
            f"Observed signal range: [{min(celeb_rates_signal):.3f}, {max(celeb_rates_signal):.3f}], "
            f"monotone-decreasing: {monotone}. "
            f"{'REFUTED (invariant)' if max(celeb_rates_signal) - min(celeb_rates_signal) < 0.05 else 'NOT REFUTED'}."
        ),
    }
    print("\n=== Summary ===")
    for k, v in summary.items():
        print(f"  {k}: {v}")
    output = {"pass": "58-batch-1-TSS-EMP-3", "date": "2026-05-17",
              "config": {"DELTA": DELTA, "P_ENG": P_ENG, "N_TRIALS": N_TRIALS,
                         "N_MC": N_MC, "UTILITY_RATIOS": UTILITY_RATIOS, "seed": 20260519},
              "results": results, "summary": summary}
    os.makedirs("simulations", exist_ok=True)
    out = "simulations/tss_emp_3_utility_sweep_results_2026-05-17.json"
    with open(out, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nWritten: {out}")
    return output


if __name__ == "__main__":
    run()

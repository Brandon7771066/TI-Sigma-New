"""
Pass-58 batch-1 TSS-EMP-5: cross-domain negative control (F-PASS-57-2).

Medical-RCT-like domain where engagement-status is STRUCTURALLY ABSENT
(double-blind randomized treatment, patient is passive recipient).

Predicted result: M-A ≈ M-B ≈ M-C (all equivalent) because there's
no engagement-stratified signal to exploit.

F-PASS-57-2 REFUTED if M-C wins anyway (indicating MFD-1 is over-broad
and the four-pronged ESP critique would apply outside its intended domain).
"""
import json
import math
import os
import random
from statistics import mean, stdev

random.seed(20260520)
CHANCE = 0.50  # 50/50 outcome (e.g., binary cure rate)
N_TRIALS = 1000
N_MC = 500
DELTAS = [0.00, 0.05, 0.10]
ALPHA = 0.05


def gen_medical(n, delta):
    """All trials are randomized; 'engagement' label is meaningless noise."""
    trials = []
    for _ in range(n):
        # 'engaged' is random noise (no actual stratification of effect)
        engaged_label = random.random() < 0.5
        p_hit = CHANCE + delta  # uniform across all trials, no stratification
        hit = random.random() < p_hit
        trials.append({"engaged": engaged_label, "hit": hit,
                       "tiu": max(0.1, random.gammavariate(2, 1)) if hit else 0.0})
    return trials


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
    sd = stdev(pts) if len(pts) > 1 else 1
    return sum(pts) / (sd * math.sqrt(len(eng))) if sd > 0 else 0


def m_c(trials):
    eng = [t for t in trials if t["engaged"]]
    if len(eng) < 10:
        return 0
    p0, p1 = CHANCE, CHANCE + 0.05
    ll0 = sum(math.log(p0) if t["hit"] else math.log(1 - p0) for t in eng)
    ll1 = sum(math.log(p1) if t["hit"] else math.log(1 - p1) for t in eng)
    diff = ll1 - ll0
    post = 1 / (1 + math.exp(-diff)) if -700 < diff < 700 else (1.0 if diff > 0 else 0.0)
    return post - 1.0 / 6.0  # decision threshold under utility 5:1


def auc(null, sig):
    if not null or not sig:
        return 0.5
    wins = ties = 0
    for s in sig:
        for n_ in null:
            if s > n_: wins += 1
            elif s == n_: ties += 1
    return (wins + 0.5 * ties) / (len(null) * len(sig))


def run():
    results = []
    print(f"TSS-EMP-5 negative control (medical-RCT-like, engagement-status absent)")
    null_a, null_b, null_c = [], [], []
    for _ in range(N_MC):
        t = gen_medical(N_TRIALS, 0.0)
        null_a.append(m_a(t))
        null_b.append(m_b(t))
        null_c.append(m_c(t))
    for delta in DELTAS:
        sig_a, sig_b, sig_c = [], [], []
        for _ in range(N_MC):
            t = gen_medical(N_TRIALS, delta)
            sig_a.append(m_a(t))
            sig_b.append(m_b(t))
            sig_c.append(m_c(t))
        auc_a = auc(null_a, sig_a)
        auc_b = auc(null_b, sig_b)
        auc_c = auc(null_c, sig_c)
        results.append({"delta": delta, "auc_A": round(auc_a, 4),
                        "auc_B": round(auc_b, 4), "auc_C": round(auc_c, 4),
                        "C_minus_A": round(auc_c - auc_a, 4),
                        "C_minus_B": round(auc_c - auc_b, 4)})
        print(f"  δ={delta:.2f} | AUC A={auc_a:.3f} B={auc_b:.3f} C={auc_c:.3f} | "
              f"C-A={auc_c - auc_a:+.4f}  C-B={auc_c - auc_b:+.4f}")
    # F-PASS-57-2 evaluation: should NOT see M-C dominate
    max_c_advantage = max(max(r["C_minus_A"] for r in results if r["delta"] > 0),
                          max(r["C_minus_B"] for r in results if r["delta"] > 0))
    refuted = max_c_advantage > 0.05  # generous threshold
    summary = {
        "max_C_advantage_over_others": round(max_c_advantage, 4),
        "F_PASS_57_2_falsifier": (
            f"MFD-1 OVER-BROAD if M-C dominates A and B in this negative-control domain. "
            f"Max C-advantage over A or B: {max_c_advantage:+.4f}. "
            f"{'OVER-BROAD (refuted)' if refuted else 'NOT OVER-BROAD (passes negative control)'}."
        ),
    }
    print("\n=== Summary ===")
    for k, v in summary.items():
        print(f"  {k}: {v}")
    output = {"pass": "58-batch-1-TSS-EMP-5", "date": "2026-05-17",
              "config": {"CHANCE": CHANCE, "N_TRIALS": N_TRIALS, "N_MC": N_MC,
                         "DELTAS": DELTAS, "ALPHA": ALPHA, "seed": 20260520},
              "results": results, "summary": summary}
    os.makedirs("simulations", exist_ok=True)
    out = "simulations/tss_emp_5_negative_control_results_2026-05-17.json"
    with open(out, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nWritten: {out}")
    return output


if __name__ == "__main__":
    run()

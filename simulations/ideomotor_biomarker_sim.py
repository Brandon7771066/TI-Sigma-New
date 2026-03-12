"""
TI Sigma — Ideomotor Biomarker Simulation
Paper #399: Biomarkers of Ideomotor Accuracy
Author: Brandon Charles Emerick | March 12, 2026

Models ideomotor accuracy as a sigmoid function of normalized LCC,
calibrated to HRV RMSSD reference ranges. Integrates actual session data
and published neural LCC results. Runs Monte Carlo simulation across 100,000
trials and produces power analysis + polarity calibration requirements.
"""

import numpy as np
import math
import os
from scipy import stats

np.random.seed(42)

PHI    = (1 + math.sqrt(5)) / 2
C_EM   = 1 / (PHI * math.sqrt(2))
P_CHANCE = 0.50
P_MAX    = 0.30
K        = 10.0

def sigmoid(x):
    return 1 / (1 + math.exp(-x))

def accuracy(lcc):
    return P_CHANCE + P_MAX * sigmoid(K * (lcc - C_EM))

def rmssd_to_lcc(rmssd):
    return rmssd / (rmssd + 50)

def lcc_to_rmssd(lcc):
    if lcc >= 1.0:
        return float("inf")
    return 50 * lcc / (1 - lcc)

def power_for_n(n, p, alpha=0.05):
    crit = stats.binom.ppf(1 - alpha, n, 0.5)
    return 1 - stats.binom.cdf(int(crit), n, p)

def min_n_for_power(p, target_power=0.80, alpha=0.05, max_n=10000):
    for n in range(5, max_n):
        if power_for_n(n, p, alpha) >= target_power:
            return n
    return max_n

def run_simulation(verbose=True):
    def pr(s=""):
        if verbose:
            print(s)

    rmssd_thresh = lcc_to_rmssd(C_EM)

    pr("=" * 65)
    pr("TI SIGMA — IDEOMOTOR BIOMARKER SIMULATION")
    pr("=" * 65)
    pr(f"\nC_EMERICK   = {C_EM:.6f}   (1 / (phi * sqrt(2)))")
    pr(f"phi         = {PHI:.6f}")
    pr(f"RMSSD threshold (C_EMERICK crossing) = {rmssd_thresh:.2f} ms")

    pr("\n--- ACCURACY vs LCC (theoretical) ---")
    pr(f"{'LCC':>8}  {'RMSSD (ms)':>12}  {'Acc (%)':>9}  {'Position':>10}")
    key_lccs = [0.20, 0.30, 0.35, 0.389, C_EM, 0.465, 0.55, 0.65, 0.80, 1.00]
    for lcc in key_lccs:
        r = lcc_to_rmssd(lcc)
        a = accuracy(lcc)
        pos = "AT C_EM" if abs(lcc - C_EM) < 0.002 else ("ABOVE" if lcc > C_EM else "below")
        rstr = f"{r:.1f}" if r < 900 else "inf"
        pr(f"{lcc:>8.4f}  {rstr:>12}  {a*100:>9.2f}%  {pos:>10}")

    sessions = [
        ("Relaxed Metta Bliss",    31.886, 4.515),
        ("ACTIVE Heart Coherence", 43.475, 19.300),
    ]
    pr("\n--- ACTUAL SESSION DATA vs SIMULATION PREDICTION ---")
    pr(f"{'Session':>28}  {'RMSSD':>6}  {'LCC_n':>6}  {'Pred Acc':>9}  {'CCI Shift':>10}  {'Status':>12}")
    for name, rmssd, shift in sessions:
        lcc_n = rmssd_to_lcc(rmssd)
        pred  = accuracy(lcc_n)
        flag  = "ABOVE C_EM" if lcc_n > C_EM else "below C_EM"
        pr(f"{name:>28}  {rmssd:>6.1f}  {lcc_n:>6.4f}  {pred*100:>9.2f}%  {shift:>10.2f}  {flag:>12}")

    s1_acc = accuracy(rmssd_to_lcc(31.886))
    s2_acc = accuracy(rmssd_to_lcc(43.475))
    pr(f"\n  Predicted accuracy ratio S2/S1 : {s2_acc/s1_acc:.3f}x")
    pr(f"  Observed CCI shift ratio  S2/S1 : {19.300/4.515:.3f}x")

    datasets = [
        ("DANDI:000552",      0.4349, 0.000, 6.011, "HIGHLY SIGNIFICANT"),
        ("ALLEN:000039",      0.3451, 0.059, 1.794, "NOT SIGNIFICANT"),
        ("DANDI:000582_MEC",  0.1329, 0.001, 0.134, "WEAK SIGNIFICANT"),
    ]
    pr("\n--- NEURAL LCC vs C_EMERICK ---")
    pr(f"{'Dataset':>20}  {'LCC':>7}  {'p-val':>7}  {'d':>6}  {'delta':>8}  Status")
    for ds, lcc, p, d, status in datasets:
        delta = lcc - C_EM
        pr(f"{ds:>20}  {lcc:>7.4f}  {p:>7.4f}  {d:>6.3f}  {delta:>+8.4f}  {status}")
    pr(f"\n  DANDI:000552 vs C_EMERICK: {abs(0.4349-C_EM):.4f} = {abs(0.4349-C_EM)/C_EM*100:.2f}%")

    N_PER_LEVEL = 1000
    lcc_vals = np.linspace(0.0, 1.0, 100)
    sim_acc = []
    for lcc in lcc_vals:
        p = accuracy(float(lcc))
        hits = np.random.binomial(N_PER_LEVEL, p)
        sim_acc.append(hits / N_PER_LEVEL)
    sim_acc = np.array(sim_acc)
    grad = np.gradient(sim_acc, lcc_vals)
    peak_idx = np.argmax(grad)
    total_trials = N_PER_LEVEL * len(lcc_vals)
    pr(f"\n--- MONTE CARLO: {total_trials:,} TRIALS across {len(lcc_vals)} LCC levels ---")
    pr(f"Steepest accuracy gain at LCC = {lcc_vals[peak_idx]:.3f} (gradient = {grad[peak_idx]:.4f})")

    pr("\n--- MINIMUM TRIALS FOR 80% POWER (one-sided, alpha=0.05) ---")
    pr(f"{'LCC':>8}  {'RMSSD':>8}  {'Accuracy':>10}  {'N_min':>8}  Label")
    for lcc in [C_EM, 0.55, 0.65, 0.39, 0.35]:
        p = accuracy(lcc)
        rmssd = lcc_to_rmssd(lcc)
        n = min_n_for_power(p)
        label = "C_EMERICK" if abs(lcc - C_EM) < 0.002 else ""
        pr(f"{lcc:>8.4f}  {rmssd:>7.1f}ms  {p*100:>10.2f}%  {n:>8}  {label}")

    pr("\n--- POLARITY CALIBRATION: Trials for 90% classification confidence ---")
    pr(f"{'True Acc':>10}  {'N for 90% conf':>16}")
    for p_true in [0.65, 0.70, 0.75, 0.55]:
        n = min_n_for_power(p_true, target_power=0.90, alpha=0.10)
        pr(f"{p_true*100:>10.1f}%  {n:>16}")

    pr("\n--- RMSSD PRACTICAL GUIDE ---")
    pr(f"{'RMSSD':>8}  {'LCC_n':>7}  {'Pred Acc':>10}  Recommendation")
    for r in [15, 25, 32, 35, 38.8, 43.5, 50, 60, 80, 100]:
        lcc_n = rmssd_to_lcc(r)
        acc   = accuracy(lcc_n)
        rec = (
            "PROCEED — high coherence" if r >= 50 else
            "PROCEED — above C_EMERICK" if r >= 38.8 else
            "Marginal — extend breathing" if r >= 35 else
            "Do NOT proceed — PSI Tune first"
        )
        pr(f"{r:>8.1f}  {lcc_n:>7.4f}  {acc*100:>10.2f}%  {rec}")

    pr("\n" + "="*65)
    pr("SIMULATION COMPLETE")
    pr("="*65)

    return {
        "C_EMERICK": C_EM,
        "rmssd_threshold_ms": rmssd_thresh,
        "session_1_pred_accuracy": accuracy(rmssd_to_lcc(31.886)),
        "session_2_pred_accuracy": accuracy(rmssd_to_lcc(43.475)),
        "n_min_at_C_EMERICK_80pwr": min_n_for_power(accuracy(C_EM)),
        "dandi_delta_from_C_EM": abs(0.4349 - C_EM),
        "total_simulated_trials": total_trials,
    }

if __name__ == "__main__":
    results = run_simulation(verbose=True)

"""
Pass-57 batch-3: MFD-1 Moot-Failure Duality simulation (TSS-EMP-1).

Compares three failure-treatment methods on engagement-stratified ESP-like data:
  M-A: conventional all-trials z-test (failures fully counted).
  M-B: APP-1 strict (engaged-only, ±TIU asymmetric penalty).
  M-C: MFD-1 dual-output (pragmatic = TSD-A success-only;
       epistemic = MBE-Acc over all engaged;
       decision = Bayes-risk under 5:1 success-emphasis utility).

Metrics: AUC, TPR at α=0.05, Brier score, ECE.
Pre-reg falsifiers F-MFD-1, F-MFD-2 evaluated.

#69 honest scope: synthetic data, perfect engagement coding assumed.
"""

import json
import math
import os
import random
from statistics import mean, stdev

random.seed(20260518)

CHANCE_BASELINE = 0.25
N_TRIALS = 1000
N_MC = 500
DELTAS = [0.00, 0.02, 0.05, 0.10, 0.20]
P_ENGAGED_LIST = [0.3, 0.5, 0.7]
ALPHA = 0.05
UTILITY_RATIO = 5.0  # cost(FP-celebrate) / cost(FN-celebrate) — success-emphasizing


def generate_trials(n, p_engaged, delta_signal):
    trials = []
    for _ in range(n):
        engaged = random.random() < p_engaged
        p_hit = CHANCE_BASELINE + (delta_signal if engaged else 0.0)
        hit = random.random() < p_hit
        tiu = max(0.1, random.gammavariate(2.0, 1.0)) if hit else 0.0
        trials.append({"engaged": engaged, "hit": hit, "tiu": tiu, "p_hit_true": p_hit})
    return trials


def method_a_conventional(trials):
    n = len(trials)
    hits = sum(1 for t in trials if t["hit"])
    p_hat = hits / n
    se = math.sqrt(CHANCE_BASELINE * (1 - CHANCE_BASELINE) / n)
    z = (p_hat - CHANCE_BASELINE) / se if se > 0 else 0.0
    return {"z": z, "p_hat": p_hat, "n_eff": n}


def method_b_app1_strict(trials):
    engaged = [t for t in trials if t["engaged"]]
    if len(engaged) < 10:
        return {"z": 0.0, "p_hat": CHANCE_BASELINE, "n_eff": len(engaged)}
    hits_tiu = [t["tiu"] for t in engaged if t["hit"]]
    mean_hit_tiu = mean(hits_tiu) if hits_tiu else 1.0
    penalty = mean_hit_tiu * CHANCE_BASELINE / (1 - CHANCE_BASELINE)
    per_trial = [t["tiu"] if t["hit"] else -penalty for t in engaged]
    score = sum(per_trial)
    sd = stdev(per_trial) if len(per_trial) > 1 else 1.0
    z = score / (sd * math.sqrt(len(engaged))) if sd > 0 else 0.0
    p_hat = sum(1 for t in engaged if t["hit"]) / len(engaged)
    return {"z": z, "p_hat": p_hat, "n_eff": len(engaged)}


def method_c_mfd1_dual(trials):
    """MFD-1: pragmatic success-only TSD-A + epistemic Bayes posterior + utility-weighted decision."""
    engaged = [t for t in trials if t["engaged"]]
    if len(engaged) < 10:
        return {"z": 0.0, "p_hat": CHANCE_BASELINE, "posterior_p_signal": 0.5,
                "decision_score": 0.0, "n_eff": len(engaged)}
    # Pragmatic: TSD-A weighted score (success-only)
    success_tiu = sum(t["tiu"] for t in engaged if t["hit"])
    n_eng = len(engaged)
    # Expected TSD-A under null: n_eng * chance * E[tiu | hit]
    # Use empirical mean tiu from observed hits as estimator
    hits = [t for t in engaged if t["hit"]]
    mean_tiu = mean([t["tiu"] for t in hits]) if hits else 2.0
    expected_null = n_eng * CHANCE_BASELINE * mean_tiu
    sd_null = math.sqrt(n_eng * CHANCE_BASELINE * (1 - CHANCE_BASELINE)) * mean_tiu
    tsd_a_z = (success_tiu - expected_null) / sd_null if sd_null > 0 else 0.0
    # Epistemic: MBE-Acc posterior P(signal | E_engaged) via Bayes against two hypotheses
    # H0: hit-rate = chance; H1: hit-rate = chance + δ_prior (use δ=0.05 as moderate prior)
    delta_prior = 0.05
    p0 = CHANCE_BASELINE
    p1 = CHANCE_BASELINE + delta_prior
    log_lik_h0 = sum(math.log(p0) if t["hit"] else math.log(1 - p0) for t in engaged)
    log_lik_h1 = sum(math.log(p1) if t["hit"] else math.log(1 - p1) for t in engaged)
    # Flat prior P(H0) = P(H1) = 0.5
    log_post_h1 = log_lik_h1 - math.log(math.exp(log_lik_h0) + math.exp(log_lik_h1)) \
        if max(log_lik_h0, log_lik_h1) - min(log_lik_h0, log_lik_h1) < 700 \
        else (0.0 if log_lik_h1 > log_lik_h0 else -700.0)
    posterior_p_signal = math.exp(log_post_h1) if log_post_h1 > -700 else 0.0
    # Decision: Bayes risk under utility ratio
    # Threshold to celebrate: posterior_p_signal > 1 / (1 + UTILITY_RATIO)
    decision_threshold = 1.0 / (1.0 + UTILITY_RATIO)
    decision_score = posterior_p_signal - decision_threshold  # > 0 → celebrate
    # Composite z = tsd_a_z combined with decision_score (use tsd_a_z as primary discriminative stat,
    # but the test stat for our discrimination is the decision_score itself)
    p_hat = sum(1 for t in engaged if t["hit"]) / n_eng
    return {"z": tsd_a_z, "p_hat": p_hat, "posterior_p_signal": posterior_p_signal,
            "decision_score": decision_score, "n_eff": n_eng}


def auc(null_scores, signal_scores):
    if not null_scores or not signal_scores:
        return 0.5
    wins = 0
    ties = 0
    for s in signal_scores:
        for n_ in null_scores:
            if s > n_:
                wins += 1
            elif s == n_:
                ties += 1
    return (wins + 0.5 * ties) / (len(null_scores) * len(signal_scores))


def empirical_crit(null_scores, alpha):
    s = sorted(null_scores)
    idx = max(0, min(len(s) - 1, int(math.ceil((1 - alpha) * len(s))) - 1))
    return s[idx]


def brier(prob_signal_per_rep, true_label_per_rep):
    """Brier score: mean (predicted_prob - true_label)²."""
    return mean((p - y) ** 2 for p, y in zip(prob_signal_per_rep, true_label_per_rep))


def ece(prob_signal_per_rep, true_label_per_rep, n_bins=10):
    """Expected Calibration Error: mean |bin_mean_prob - bin_mean_truth| weighted by bin size."""
    bins = [[] for _ in range(n_bins)]
    for p, y in zip(prob_signal_per_rep, true_label_per_rep):
        b = min(n_bins - 1, int(p * n_bins))
        bins[b].append((p, y))
    total = len(prob_signal_per_rep)
    err = 0.0
    for b in bins:
        if not b:
            continue
        avg_p = mean(p for p, _ in b)
        avg_y = mean(y for _, y in b)
        err += (len(b) / total) * abs(avg_p - avg_y)
    return err


def z_to_prob(z):
    """Approximate P(signal) from z-score via logistic mapping (calibrated against null/signal mix)."""
    return 1.0 / (1.0 + math.exp(-z))


def run():
    results = []
    # Collect probability estimates + true labels for Brier/ECE across full design
    pred_a, pred_b, pred_c = [], [], []
    truth = []
    print(f"Running {N_MC} MC × {len(DELTAS)} δ × {len(P_ENGAGED_LIST)} p_eng × 3 methods...")

    for p_eng in P_ENGAGED_LIST:
        # Build null distribution
        null_a_z, null_b_z, null_c_dec = [], [], []
        for _ in range(N_MC):
            trials = generate_trials(N_TRIALS, p_eng, 0.0)
            null_a_z.append(method_a_conventional(trials)["z"])
            null_b_z.append(method_b_app1_strict(trials)["z"])
            null_c_dec.append(method_c_mfd1_dual(trials)["decision_score"])
        crit_a = empirical_crit(null_a_z, ALPHA)
        crit_b = empirical_crit(null_b_z, ALPHA)
        crit_c = empirical_crit(null_c_dec, ALPHA)
        # Add null reps to Brier/ECE pool with label 0
        for z in null_a_z:
            pred_a.append(z_to_prob(z))
            truth.append(0)
        for z in null_b_z:
            pred_b.append(z_to_prob(z))
        for d in null_c_dec:
            # MFD-1 dual: pred = posterior probability (use sigmoid of decision_score for symmetry)
            pred_c.append(z_to_prob(d * 5))
        # signal cells
        for delta in DELTAS:
            sig_a_z, sig_b_z, sig_c_dec = [], [], []
            for _ in range(N_MC):
                trials = generate_trials(N_TRIALS, p_eng, delta)
                sig_a_z.append(method_a_conventional(trials)["z"])
                sig_b_z.append(method_b_app1_strict(trials)["z"])
                sig_c_dec.append(method_c_mfd1_dual(trials)["decision_score"])
            auc_a = auc(null_a_z, sig_a_z)
            auc_b = auc(null_b_z, sig_b_z)
            auc_c = auc(null_c_dec, sig_c_dec)
            tpr_a = sum(1 for s in sig_a_z if s > crit_a) / N_MC
            tpr_b = sum(1 for s in sig_b_z if s > crit_b) / N_MC
            tpr_c = sum(1 for s in sig_c_dec if s > crit_c) / N_MC
            results.append({
                "p_engaged": p_eng, "delta_signal": delta,
                "auc_A": round(auc_a, 4), "auc_B": round(auc_b, 4), "auc_C": round(auc_c, 4),
                "tpr_A": round(tpr_a, 4), "tpr_B": round(tpr_b, 4), "tpr_C": round(tpr_c, 4),
                "C_vs_A_auc": round(auc_c - auc_a, 4),
                "C_vs_B_auc": round(auc_c - auc_b, 4),
                "C_vs_A_tpr": round(tpr_c - tpr_a, 4),
                "C_vs_B_tpr": round(tpr_c - tpr_b, 4),
            })
            if delta > 0:
                for z in sig_a_z:
                    pred_a.append(z_to_prob(z))
                    truth.append(1)
                for z in sig_b_z:
                    pred_b.append(z_to_prob(z))
                for d in sig_c_dec:
                    pred_c.append(z_to_prob(d * 5))
            print(f"  p_eng={p_eng} δ={delta:.2f} | AUC A={auc_a:.3f} B={auc_b:.3f} C={auc_c:.3f} "
                  f"| TPR A={tpr_a:.3f} B={tpr_b:.3f} C={tpr_c:.3f}")

    # truth list is aligned with pred_a (and pred_b, pred_c are same length by construction)
    brier_a = brier(pred_a, truth)
    brier_b = brier(pred_b, truth)
    brier_c = brier(pred_c, truth)
    ece_a = ece(pred_a, truth)
    ece_b = ece(pred_b, truth)
    ece_c = ece(pred_c, truth)

    auc_advantages_c_over_a = [r["C_vs_A_auc"] for r in results if r["delta_signal"] > 0]
    auc_advantages_c_over_b = [r["C_vs_B_auc"] for r in results if r["delta_signal"] > 0]
    tpr_advantages_c_over_a = [r["C_vs_A_tpr"] for r in results if r["delta_signal"] > 0]
    tpr_advantages_c_over_b = [r["C_vs_B_tpr"] for r in results if r["delta_signal"] > 0]

    summary = {
        "n_signal_cells": len(auc_advantages_c_over_a),
        "auc_C_over_A_mean": round(mean(auc_advantages_c_over_a), 4),
        "auc_C_over_B_mean": round(mean(auc_advantages_c_over_b), 4),
        "auc_C_beats_A_count": sum(1 for x in auc_advantages_c_over_a if x > 0),
        "auc_C_beats_B_count": sum(1 for x in auc_advantages_c_over_b if x > 0),
        "tpr_C_over_A_mean": round(mean(tpr_advantages_c_over_a), 4),
        "tpr_C_over_B_mean": round(mean(tpr_advantages_c_over_b), 4),
        "tpr_C_beats_A_count": sum(1 for x in tpr_advantages_c_over_a if x > 0),
        "tpr_C_beats_B_count": sum(1 for x in tpr_advantages_c_over_b if x > 0),
        "brier_A": round(brier_a, 4),
        "brier_B": round(brier_b, 4),
        "brier_C": round(brier_c, 4),
        "ece_A": round(ece_a, 4),
        "ece_B": round(ece_b, 4),
        "ece_C": round(ece_c, 4),
        "F_MFD_1_brier_falsifier": (
            f"REFUTED if brier_C > brier_A AND brier_C > brier_B. "
            f"Observed: brier_C={brier_c:.4f}, brier_A={brier_a:.4f}, brier_B={brier_b:.4f}. "
            f"{'REFUTED' if (brier_c > brier_a and brier_c > brier_b) else 'NOT REFUTED'}."
        ),
        "F_MFD_2_auc_falsifier": (
            f"REFUTED if max(ΔAUC C-vs-A) ≤ 0.01 AND max(ΔAUC C-vs-B) ≤ 0.01. "
            f"Observed: max C-A={max(auc_advantages_c_over_a):.4f}, "
            f"max C-B={max(auc_advantages_c_over_b):.4f}. "
            f"{'REFUTED' if (max(auc_advantages_c_over_a) <= 0.01 and max(auc_advantages_c_over_b) <= 0.01) else 'NOT REFUTED'}."
        ),
    }
    print("\n=== Summary ===")
    for k, v in summary.items():
        print(f"  {k}: {v}")

    output = {
        "pass": "57-batch-3", "date": "2026-05-17",
        "config": {"N_TRIALS": N_TRIALS, "N_MC": N_MC, "DELTAS": DELTAS,
                   "P_ENGAGED_LIST": P_ENGAGED_LIST, "CHANCE_BASELINE": CHANCE_BASELINE,
                   "ALPHA": ALPHA, "UTILITY_RATIO": UTILITY_RATIO, "seed": 20260518},
        "results": results, "summary": summary,
    }
    os.makedirs("simulations", exist_ok=True)
    out = "simulations/moot_failure_duality_results_2026-05-17.json"
    with open(out, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults written to {out}")
    return output


if __name__ == "__main__":
    run()

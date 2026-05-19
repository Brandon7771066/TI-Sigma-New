"""
Pass-57 batch-2 simulation: Active-Pragmatism (APP-1) vs conventional counting.

Compares two analyzers on engagement-stratified synthetic ESP-like data:
  Method A: count all trials, z-test vs chance baseline.
  Method B: APP-1 filter to engaged trials only, TSD-A weighted score.

Outputs: AUC + FPR + TPR table to JSON, summary printed.

#69 honest scope: synthetic data; real Ganzfeld/PEAR validation is Pass-58 F-SM-2.
"""

import json
import math
import os
import random
from statistics import mean, stdev

random.seed(20260517)

CHANCE_BASELINE = 0.25  # 1-of-4 Ganzfeld-style forced choice
N_TRIALS = 1000
N_MC = 1000  # Monte Carlo replications per cell
DELTAS = [0.00, 0.02, 0.05, 0.10, 0.20]
P_ENGAGED_LIST = [0.3, 0.5, 0.7]
ALPHA = 0.05


def generate_trials(n, p_engaged, delta_signal):
    """Generate n trials. Engaged trials hit with prob chance+delta; drifted with prob chance."""
    trials = []
    for _ in range(n):
        engaged = random.random() < p_engaged
        p_hit = CHANCE_BASELINE + (delta_signal if engaged else 0.0)
        hit = random.random() < p_hit
        # TIU weight: striking-ness of match. For hits, draw from gamma-ish distribution
        # representing per-event evidentiary weight; for misses, zero contribution
        # under TSD-A (TSD-A counts successes only with per-event magnitude).
        # Negative contribution comes from engaged-failures in APP-1 below.
        if hit:
            tiu = max(0.1, random.gammavariate(2.0, 1.0))
        else:
            tiu = 0.0
        trials.append({"engaged": engaged, "hit": hit, "tiu": tiu})
    return trials


def method_a_conventional(trials):
    """Conventional z-test against chance baseline on ALL trials."""
    n = len(trials)
    hits = sum(1 for t in trials if t["hit"])
    p_hat = hits / n
    se = math.sqrt(CHANCE_BASELINE * (1 - CHANCE_BASELINE) / n)
    z = (p_hat - CHANCE_BASELINE) / se if se > 0 else 0.0
    return z


def method_b_app1(trials):
    """APP-1: engaged-only filter + TSD-A weighted z."""
    engaged = [t for t in trials if t["engaged"]]
    if len(engaged) < 10:
        return 0.0
    n = len(engaged)
    # TSD-A: sum of per-event TIU over engaged successes minus engaged failures penalty.
    # We use a TIU-weighted hit-rate test: each hit contributes +tiu, each failure
    # contributes -mean_tiu (asymmetric penalty per APP-1 §1.4).
    hits_tiu = [t["tiu"] for t in engaged if t["hit"]]
    mean_hit_tiu = mean(hits_tiu) if hits_tiu else 1.0
    score = sum(t["tiu"] if t["hit"] else -mean_hit_tiu * CHANCE_BASELINE / (1 - CHANCE_BASELINE)
                for t in engaged)
    # Normalize: expected score under null (engagement filter independent of outcome)
    # is approximately zero by construction of the penalty term.
    # Standardize by sqrt(n) * sd of per-trial score under null.
    per_trial = [t["tiu"] if t["hit"]
                 else -mean_hit_tiu * CHANCE_BASELINE / (1 - CHANCE_BASELINE)
                 for t in engaged]
    if len(per_trial) < 2:
        return 0.0
    sd = stdev(per_trial)
    z = score / (sd * math.sqrt(n)) if sd > 0 else 0.0
    return z


def auc_from_scores(null_scores, signal_scores):
    """Mann-Whitney U / AUC of signal vs null score distributions."""
    n_null = len(null_scores)
    n_signal = len(signal_scores)
    if n_null == 0 or n_signal == 0:
        return 0.5
    wins = 0
    ties = 0
    for s in signal_scores:
        for n_ in null_scores:
            if s > n_:
                wins += 1
            elif s == n_:
                ties += 1
    return (wins + 0.5 * ties) / (n_null * n_signal)


def critical_z_for_alpha(null_scores, alpha):
    """Empirical critical value: 1-alpha quantile of null distribution."""
    sorted_null = sorted(null_scores)
    idx = int(math.ceil((1 - alpha) * len(sorted_null))) - 1
    idx = max(0, min(len(sorted_null) - 1, idx))
    return sorted_null[idx]


def run():
    results = []
    print(f"Running {N_MC} MC reps × {len(DELTAS)} deltas × {len(P_ENGAGED_LIST)} p_engaged...")
    for p_eng in P_ENGAGED_LIST:
        # First, build null distribution (delta=0) for this p_engaged
        null_a = []
        null_b = []
        for _ in range(N_MC):
            trials = generate_trials(N_TRIALS, p_eng, 0.0)
            null_a.append(method_a_conventional(trials))
            null_b.append(method_b_app1(trials))
        crit_a = critical_z_for_alpha(null_a, ALPHA)
        crit_b = critical_z_for_alpha(null_b, ALPHA)
        # FPR is alpha by construction of empirical crit
        for delta in DELTAS:
            sig_a = []
            sig_b = []
            for _ in range(N_MC):
                trials = generate_trials(N_TRIALS, p_eng, delta)
                sig_a.append(method_a_conventional(trials))
                sig_b.append(method_b_app1(trials))
            auc_a = auc_from_scores(null_a, sig_a)
            auc_b = auc_from_scores(null_b, sig_b)
            tpr_a = sum(1 for s in sig_a if s > crit_a) / N_MC
            tpr_b = sum(1 for s in sig_b if s > crit_b) / N_MC
            results.append({
                "p_engaged": p_eng,
                "delta_signal": delta,
                "auc_method_a": round(auc_a, 4),
                "auc_method_b": round(auc_b, 4),
                "auc_advantage_b_minus_a": round(auc_b - auc_a, 4),
                "tpr_method_a": round(tpr_a, 4),
                "tpr_method_b": round(tpr_b, 4),
                "tpr_advantage_b_minus_a": round(tpr_b - tpr_a, 4),
                "n_trials": N_TRIALS,
                "n_mc": N_MC,
            })
            print(f"  p_eng={p_eng} δ={delta:.2f} | AUC_A={auc_a:.3f} AUC_B={auc_b:.3f} "
                  f"ΔAUC={auc_b - auc_a:+.3f} | TPR_A={tpr_a:.3f} TPR_B={tpr_b:.3f} "
                  f"ΔTPR={tpr_b - tpr_a:+.3f}")

    # Summary metrics
    auc_advantages = [r["auc_advantage_b_minus_a"] for r in results if r["delta_signal"] > 0]
    tpr_advantages = [r["tpr_advantage_b_minus_a"] for r in results if r["delta_signal"] > 0]
    summary = {
        "n_cells_signal": len(auc_advantages),
        "auc_advantage_mean": round(mean(auc_advantages), 4),
        "auc_advantage_min": round(min(auc_advantages), 4),
        "auc_advantage_max": round(max(auc_advantages), 4),
        "n_cells_where_B_beats_A_auc": sum(1 for x in auc_advantages if x > 0),
        "tpr_advantage_mean": round(mean(tpr_advantages), 4),
        "n_cells_where_B_beats_A_tpr": sum(1 for x in tpr_advantages if x > 0),
        "fpr_method_a_target": ALPHA,
        "fpr_method_b_target": ALPHA,
        "pre_reg_falsifier_F_PASS_57_1": (
            "REFUTED if B's AUC ≤ A's AUC in ALL cells. "
            f"Observed: B>A in {sum(1 for x in auc_advantages if x > 0)}/{len(auc_advantages)} cells "
            f"→ {'NOT REFUTED' if any(x > 0 for x in auc_advantages) else 'REFUTED'}."
        ),
    }
    print("\n=== Summary ===")
    for k, v in summary.items():
        print(f"  {k}: {v}")

    output = {
        "pass": "57-batch-2",
        "date": "2026-05-17",
        "config": {
            "N_TRIALS": N_TRIALS,
            "N_MC": N_MC,
            "DELTAS": DELTAS,
            "P_ENGAGED_LIST": P_ENGAGED_LIST,
            "CHANCE_BASELINE": CHANCE_BASELINE,
            "ALPHA": ALPHA,
            "seed": 20260517,
        },
        "results": results,
        "summary": summary,
    }
    os.makedirs("simulations", exist_ok=True)
    out_path = "simulations/active_pragmatism_results_2026-05-17.json"
    with open(out_path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults written to {out_path}")
    return output


if __name__ == "__main__":
    run()

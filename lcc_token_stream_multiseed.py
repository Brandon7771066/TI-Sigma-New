"""URB #807 — LCC token-stream pilot (URB #803), multi-seed Monte Carlo.

Architect-recommended robustness check. Reruns the URB #803 protocol
with seeds 2026..2035, collects per-seed AUC and per-seed
fraction-above-C_EMERICK at each alpha, reports mean +/- 95% CI.
"""

import json
import math
import time

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

PHI = (1.0 + 5.0**0.5) / 2.0
C_EMERICK = 1.0 / (PHI * 2.0**0.5)
T = 300
K_STATES = 16
N_PER_COND = 100
SIGMA = 5.0
MAX_LAG = 15
ALPHAS = [0.0, 0.1, 0.2, 0.4, 0.6, 0.8]
SEEDS = list(range(2026, 2036))


_TAU = np.arange(-MAX_LAG, MAX_LAG + 1)
_W = np.exp(-(_TAU.astype(np.float64) ** 2) / (2.0 * SIGMA * SIGMA))


def lcc_resonance_form_b(a, b, sigma=SIGMA, max_lag=MAX_LAG):
    """Vectorized Form B LCC (peak-Gaussian-damped, sign-preserving)."""
    a = (a - a.mean()) / (a.std() + 1e-12)
    b = (b - b.mean()) / (b.std() + 1e-12)
    n = len(a)
    rhos = np.empty(2 * max_lag + 1, dtype=np.float64)
    for k, tau in enumerate(_TAU):
        if tau >= 0:
            x, y = a[: n - tau], b[tau:]
        else:
            x, y = a[-tau:], b[: n + tau]
        if len(x) < 2:
            rhos[k] = 0.0
        else:
            rhos[k] = np.dot(x, y) / len(x)
    vals = rhos * _W
    idx = int(np.argmax(np.abs(vals)))
    return float(vals[idx])


def make_transition(rng, k=K_STATES):
    M = rng.dirichlet(alpha=np.ones(k), size=k)
    return M


def sample_chain(M, t, rng, x0=None):
    k = M.shape[0]
    out = np.zeros(t, dtype=np.int64)
    out[0] = rng.integers(k) if x0 is None else x0
    for i in range(1, t):
        out[i] = rng.choice(k, p=M[out[i - 1]])
    return out


def sample_independent_pair(MX, MY, t, rng):
    return sample_chain(MX, t, rng), sample_chain(MY, t, rng)


def sample_coupled_pair(MX, MY, t, alpha, rng):
    k = MX.shape[0]
    X = np.zeros(t, dtype=np.int64)
    Y = np.zeros(t, dtype=np.int64)
    X[0] = rng.integers(k)
    Y[0] = rng.integers(k)
    for i in range(1, t):
        X[i] = rng.choice(k, p=MX[X[i - 1]])
        if rng.random() < alpha:
            Y[i] = X[i - 1]
        else:
            Y[i] = rng.choice(k, p=MY[Y[i - 1]])
    return X, Y


def roc_auc_one_sided(scores_pos, scores_neg):
    n_pos, n_neg = len(scores_pos), len(scores_neg)
    all_scores = np.concatenate([scores_pos, scores_neg])
    all_labels = np.concatenate([np.ones(n_pos), np.zeros(n_neg)])
    order = np.argsort(-all_scores, kind="mergesort")
    sorted_labels = all_labels[order]
    tp_cum = np.cumsum(sorted_labels)
    fp_cum = np.cumsum(1 - sorted_labels)
    tpr = np.concatenate([[0.0], tp_cum / n_pos])
    fpr = np.concatenate([[0.0], fp_cum / n_neg])
    return float(np.trapz(tpr, fpr))


def run_one_seed(seed):
    rng = np.random.default_rng(seed)
    MX = make_transition(rng)
    MY = make_transition(rng)
    out = []
    for alpha in ALPHAS:
        coupled_lccs = []
        indep_lccs = []
        for _ in range(N_PER_COND):
            xc, yc = sample_coupled_pair(MX, MY, T, alpha, rng)
            xi, yi = sample_independent_pair(MX, MY, T, rng)
            coupled_lccs.append(lcc_resonance_form_b(xc.astype(float), yc.astype(float)))
            indep_lccs.append(lcc_resonance_form_b(xi.astype(float), yi.astype(float)))
        c = np.array(coupled_lccs)
        i = np.array(indep_lccs)
        out.append({
            "alpha": alpha,
            "auc": roc_auc_one_sided(c, i),
            "frac_coupled_above_C_EMERICK": float((c >= C_EMERICK).mean()),
            "frac_indep_above_C_EMERICK": float((i >= C_EMERICK).mean()),
            "mean_coupled": float(c.mean()),
            "mean_indep": float(i.mean()),
        })
    return out


def main():
    t0 = time.time()
    print(f"Multi-seed Monte Carlo: {len(SEEDS)} seeds x {len(ALPHAS)} alphas x {N_PER_COND} pairs/cond")
    per_seed = []
    for s in SEEDS:
        print(f"  seed={s} ...", flush=True)
        per_seed.append(run_one_seed(s))
    by_alpha = {a: {"auc": [], "frac_c": [], "frac_i": [], "mean_c": [], "mean_i": []} for a in ALPHAS}
    for seed_results in per_seed:
        for r in seed_results:
            by_alpha[r["alpha"]]["auc"].append(r["auc"])
            by_alpha[r["alpha"]]["frac_c"].append(r["frac_coupled_above_C_EMERICK"])
            by_alpha[r["alpha"]]["frac_i"].append(r["frac_indep_above_C_EMERICK"])
            by_alpha[r["alpha"]]["mean_c"].append(r["mean_coupled"])
            by_alpha[r["alpha"]]["mean_i"].append(r["mean_indep"])

    summary = []
    for a in ALPHAS:
        d = by_alpha[a]
        auc = np.array(d["auc"])
        fc = np.array(d["frac_c"])
        fi = np.array(d["frac_i"])
        mc = np.array(d["mean_c"])
        mi = np.array(d["mean_i"])

        def ci(x):
            return float(1.96 * x.std(ddof=1) / np.sqrt(len(x)))

        summary.append({
            "alpha": a,
            "auc_mean": float(auc.mean()),
            "auc_ci95": ci(auc),
            "auc_min": float(auc.min()),
            "auc_max": float(auc.max()),
            "frac_coupled_mean": float(fc.mean()),
            "frac_coupled_ci95": ci(fc),
            "frac_indep_mean": float(fi.mean()),
            "frac_indep_ci95": ci(fi),
            "mean_coupled": float(mc.mean()),
            "mean_indep": float(mi.mean()),
        })

    print(f"\n=== Multi-seed Summary (n={len(SEEDS)} seeds) ===")
    print(f"alpha |  AUC mean +- 95% CI       | frac_c mean +- CI | mean_c | mean_i")
    for s in summary:
        print(
            f"{s['alpha']:.2f}  | {s['auc_mean']:.3f} +- {s['auc_ci95']:.3f}  "
            f"({s['auc_min']:.3f}-{s['auc_max']:.3f}) | "
            f"{s['frac_coupled_mean']*100:5.1f}% +- {s['frac_coupled_ci95']*100:.1f}%   | "
            f"{s['mean_coupled']:+.4f} | {s['mean_indep']:+.4f}"
        )

    report = {
        "C_EMERICK": C_EMERICK,
        "n_seeds": len(SEEDS),
        "n_per_cond": N_PER_COND,
        "T": T,
        "K_states": K_STATES,
        "sigma": SIGMA,
        "max_lag": MAX_LAG,
        "alphas": ALPHAS,
        "summary": summary,
        "per_seed_results": per_seed,
        "wall_time_s": float(time.time() - t0),
    }
    with open("lcc_token_stream_multiseed_report.json", "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    fig, axes = plt.subplots(1, 2, figsize=(13, 5))
    aucs_mean = [s["auc_mean"] for s in summary]
    aucs_ci = [s["auc_ci95"] for s in summary]
    axes[0].errorbar(ALPHAS, aucs_mean, yerr=aucs_ci, marker="o", capsize=4, color="tab:blue")
    axes[0].axhline(0.9, color="red", linestyle="--", label="H2 threshold (0.9)")
    axes[0].axhline(0.5, color="gray", linestyle=":", label="chance (0.5)")
    axes[0].set_xlabel("coupling alpha")
    axes[0].set_ylabel("ROC-AUC (mean +/- 95% CI)")
    axes[0].set_title(f"H2 multi-seed AUC (n={len(SEEDS)} seeds)")
    axes[0].set_ylim(0.4, 1.05)
    axes[0].legend()

    fc_mean = [s["frac_coupled_mean"] * 100 for s in summary]
    fc_ci = [s["frac_coupled_ci95"] * 100 for s in summary]
    fi_mean = [s["frac_indep_mean"] * 100 for s in summary]
    fi_ci = [s["frac_indep_ci95"] * 100 for s in summary]
    axes[1].errorbar(ALPHAS, fc_mean, yerr=fc_ci, marker="o", capsize=4, label="coupled", color="tab:blue")
    axes[1].errorbar(ALPHAS, fi_mean, yerr=fi_ci, marker="s", capsize=4, label="independent", color="tab:gray")
    axes[1].set_xlabel("coupling alpha")
    axes[1].set_ylabel("% pairs >= C_EMERICK (mean +/- 95% CI)")
    axes[1].set_title(f"Fraction above C_EMERICK (n={len(SEEDS)} seeds)")
    axes[1].legend()

    plt.tight_layout()
    plt.savefig("lcc_token_stream_multiseed.png", dpi=120)
    plt.close()
    print(f"\n[{time.time()-t0:.1f}s] wrote lcc_token_stream_multiseed_report.json + .png")


if __name__ == "__main__":
    main()

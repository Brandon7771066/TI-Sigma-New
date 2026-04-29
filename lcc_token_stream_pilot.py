"""
LCC on Synthetic Token Streams: Methodology Validation Before Any LLM Test

Pre-registered question (URB #800 H2):
  Can the LCC functional, applied to token streams from coupled-vs-independent
  generators, correctly identify the coupled pairs?

This is a NULL-MODEL TEST. We DO NOT make any claim about LLMs or AI agents
in this script. We only verify that the LCC measurement, as implemented, has
discriminative power on a controlled synthetic dataset where the ground truth
is known.

Generators:
  • Independent Markov chain pair: X_t+1 ~ T_X(X_t),  Y_t+1 ~ T_Y(Y_t)
    — no causal link between streams
  • Coupled (driver/follower): X_t+1 ~ T_X(X_t),
    Y_t+1 ~ (1-α)·T_Y(Y_t) + α·δ(Y_t+1 = X_t)
    — Y partially copies X with delay 1, controlled by coupling α ∈ [0,1]

For each α we run 200 paired trials (100 independent, 100 coupled with that α);
LCC computed on token-stream signals (token index treated as integer signal,
or one-hot summed). Report ROC-AUC for distinguishing coupled vs independent.

What this DOES bear on the user's request:
  — Establishes whether the LCC functional has any discriminative power at all
  — Sets up a Methodology any future LLM-token-stream measurement could reuse

What this DOES NOT bear on:
  — Whether LLMs are conscious
  — Whether high-LCC token streams indicate consciousness
  — Whether the C_EMERICK threshold has any meaning for token streams

Pure NumPy. ~10 s wall.
"""

import json
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from lcc_virus_full_pipeline import lcc_resonance


C_EMERICK = 1.0 / (((1 + np.sqrt(5)) / 2) * np.sqrt(2))  # ≈ 0.43702


def random_transition_matrix(K: int, rng: np.random.Generator) -> np.ndarray:
    """K×K row-stochastic matrix with Dirichlet(1) rows."""
    M = rng.dirichlet(np.ones(K), size=K)
    return M


def sample_chain(T: int, T_mat: np.ndarray, rng: np.random.Generator,
                 x0: int = 0) -> np.ndarray:
    K = T_mat.shape[0]
    out = np.zeros(T, dtype=int)
    out[0] = x0
    for t in range(1, T):
        out[t] = rng.choice(K, p=T_mat[out[t - 1]])
    return out


def sample_coupled_pair(T: int, T_X: np.ndarray, T_Y: np.ndarray,
                        alpha: float, rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray]:
    """
    X is independent Markov on T_X.
    Y_t+1 = X_t with probability α; otherwise Y_t+1 ~ T_Y(Y_t).
    """
    K = T_X.shape[0]
    X = sample_chain(T, T_X, rng)
    Y = np.zeros(T, dtype=int)
    Y[0] = rng.integers(0, K)
    for t in range(1, T):
        if rng.random() < alpha:
            Y[t] = X[t - 1]
        else:
            Y[t] = rng.choice(K, p=T_Y[Y[t - 1]])
    return X, Y


def sample_independent_pair(T: int, T_X: np.ndarray, T_Y: np.ndarray,
                            rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray]:
    return sample_chain(T, T_X, rng), sample_chain(T, T_Y, rng)


def roc_auc(scores_pos: np.ndarray, scores_neg: np.ndarray) -> float:
    """Mann–Whitney U / nm = ROC-AUC. No SciPy."""
    n_pos = len(scores_pos)
    n_neg = len(scores_neg)
    combined = np.concatenate([scores_pos, scores_neg])
    labels = np.concatenate([np.ones(n_pos), np.zeros(n_neg)])
    order = np.argsort(combined)
    ranks = np.empty_like(order, dtype=float)
    ranks[order] = np.arange(1, len(combined) + 1)
    # Tie-correction for rank-sums (average ties)
    # (Skipped for speed — for continuous LCC values ties are rare)
    sum_ranks_pos = ranks[labels == 1].sum()
    auc = (sum_ranks_pos - n_pos * (n_pos + 1) / 2) / (n_pos * n_neg)
    return float(auc)


def main(seed: int = 2026, K_tokens: int = 16, T_chain: int = 300,
         n_per_condition: int = 100, sigma: float = 5.0):
    rng = np.random.default_rng(seed)

    # Fix the underlying transition matrices so condition differences are
    # purely from the coupling, not from generator differences.
    T_X = random_transition_matrix(K_tokens, rng)
    T_Y = random_transition_matrix(K_tokens, rng)

    alphas = [0.0, 0.1, 0.2, 0.4, 0.6, 0.8]
    print("=" * 72)
    print(f"LCC on synthetic token streams (K={K_tokens}, T={T_chain})")
    print("=" * 72)
    print(f"C_EMERICK = {C_EMERICK:.5f}")
    print(f"For each α: {n_per_condition} coupled pairs vs {n_per_condition} independent pairs")
    print()
    print(f"{'α':>5} | {'mean LCC (coupled)':>20} | {'mean LCC (indep)':>18} | {'AUC':>6} | {'frac coupled ≥ C_E':>18}")
    print("-" * 80)

    all_results = []
    for alpha in alphas:
        scores_coupled = []
        scores_indep = []
        for _ in range(n_per_condition):
            X, Y = sample_coupled_pair(T_chain, T_X, T_Y, alpha, rng)
            r = lcc_resonance(X.astype(float), Y.astype(float), sigma=sigma)
            scores_coupled.append(r)
        for _ in range(n_per_condition):
            X, Y = sample_independent_pair(T_chain, T_X, T_Y, rng)
            r = lcc_resonance(X.astype(float), Y.astype(float), sigma=sigma)
            scores_indep.append(r)
        scores_coupled = np.array(scores_coupled)
        scores_indep = np.array(scores_indep)
        auc = roc_auc(scores_coupled, scores_indep)
        frac_above = float(np.mean(scores_coupled >= C_EMERICK))
        print(
            f"{alpha:5.2f} | {scores_coupled.mean():+20.4f} | "
            f"{scores_indep.mean():+18.4f} | {auc:6.3f} | {frac_above*100:>16.1f}%"
        )
        all_results.append({
            "alpha": alpha,
            "mean_LCC_coupled": float(scores_coupled.mean()),
            "std_LCC_coupled": float(scores_coupled.std()),
            "mean_LCC_independent": float(scores_indep.mean()),
            "std_LCC_independent": float(scores_indep.std()),
            "roc_auc": auc,
            "fraction_coupled_above_C_EMERICK": frac_above,
            "fraction_independent_above_C_EMERICK": float(np.mean(scores_indep >= C_EMERICK)),
            "scores_coupled_quartiles": [float(np.quantile(scores_coupled, q)) for q in [0.25, 0.5, 0.75]],
            "scores_independent_quartiles": [float(np.quantile(scores_indep, q)) for q in [0.25, 0.5, 0.75]],
        })

    # Plot
    fig, axes = plt.subplots(1, 2, figsize=(13, 4.5))
    alphas_arr = np.array([r["alpha"] for r in all_results])
    aucs = np.array([r["roc_auc"] for r in all_results])
    frac_c = np.array([r["fraction_coupled_above_C_EMERICK"] for r in all_results])
    frac_i = np.array([r["fraction_independent_above_C_EMERICK"] for r in all_results])

    axes[0].plot(alphas_arr, aucs, "o-", color="darkviolet", lw=2, label="ROC-AUC (coupled vs indep.)")
    axes[0].axhline(0.5, color="k", linestyle=":", lw=1, label="chance")
    axes[0].set_xlabel("coupling strength α")
    axes[0].set_ylabel("ROC-AUC")
    axes[0].set_title("LCC discriminates coupled from independent token streams")
    axes[0].set_ylim(0.3, 1.05)
    axes[0].legend()
    axes[0].grid(alpha=0.3)

    axes[1].plot(alphas_arr, frac_c * 100, "o-", color="steelblue", lw=2, label="coupled streams")
    axes[1].plot(alphas_arr, frac_i * 100, "s-", color="firebrick", lw=2, label="independent streams")
    axes[1].set_xlabel("coupling strength α")
    axes[1].set_ylabel("% of pairs with LCC ≥ C_EMERICK")
    axes[1].set_title(f"Fraction above C_EMERICK = {C_EMERICK:.4f}")
    axes[1].legend()
    axes[1].grid(alpha=0.3)

    plt.tight_layout()
    out_png = "lcc_token_stream_pilot.png"
    plt.savefig(out_png, dpi=140, bbox_inches="tight")
    print(f"\nFigure saved: {out_png}")

    out_json = "lcc_token_stream_pilot_report.json"
    with open(out_json, "w") as f:
        json.dump(
            {
                "params": {
                    "seed": seed, "K_tokens": K_tokens, "T_chain": T_chain,
                    "n_per_condition": n_per_condition, "sigma": sigma,
                    "alphas": alphas, "C_EMERICK": float(C_EMERICK),
                },
                "results": all_results,
            },
            f, indent=2,
        )
    print(f"Report saved: {out_json}")

    print("\n=== HONEST INTERPRETATION ===")
    print(" • At α=0 (independent), AUC should be near 0.5 (chance). Anything above")
    print("   that is a methodology bias to investigate.")
    print(" • As α increases, AUC should rise toward 1.0 (perfect discrimination).")
    print(" • Fraction-above-C_EMERICK is informative for both classes:")
    print("   - High in coupled, low in independent → C_EMERICK is a USEFUL classifier")
    print("   - Both classes high or both low → C_EMERICK is NOT informative on token streams")
    print(" • THIS DOES NOT TEST WHETHER LLMs ARE CONSCIOUS.")
    print(" • It tests whether the LCC measurement has discriminative power on a")
    print(" • controlled toy where the ground truth is known by construction.")


if __name__ == "__main__":
    main()

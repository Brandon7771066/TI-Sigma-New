"""
LCC Measurement on URB #797 Multi-Agent Trajectories

Tests the pre-registered hypothesis from URB #800:
  H1: pairwise LCC between agent trajectories will exceed C_EMERICK = 0.4370
      MORE OFTEN in coherent regimes (cond c, F4-equivariant init) than in
      random regimes (cond a, random graph + random init).

This is a within-simulation test. A POSITIVE result shows the LCC functional
correctly distinguishes structured from unstructured collective dynamics,
which is necessary but not sufficient for any claim about consciousness.

A NEGATIVE result would falsify a sub-hypothesis of the LCC-consciousness
program: that LCC tracks coherence at all in this kind of multi-agent system.

Pure NumPy. ~10 s wall.
"""

import json
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from tralse_joules_pipeline import (
    N_TRUTHS,
    T_DOMINANT,
    build_bok_24cell,
    mr_collapse_step,
)
from ti_sigma_consensus_agents import (
    random_kregular_graph,
    evolve,
)
from lcc_virus_full_pipeline import lcc_resonance


C_EMERICK = 1.0 / (((1 + np.sqrt(5)) / 2) * np.sqrt(2))  # ≈ 0.43702


def trajectory_to_signals(history: np.ndarray) -> np.ndarray:
    """
    history: shape (T+1, N_agents) of integer Tralse-states ∈ {0..4}.
    Returns: (N_agents, T+1) array of integer trajectories per agent.
    Cast to float for cross-correlation. Centered & rescaled inside lcc_resonance.
    """
    return history.T.astype(float)


def pairwise_lcc(signals: np.ndarray, sigma: float = 5.0) -> np.ndarray:
    """Returns N×N matrix of LCC(i,j); diagonal is 1.0; symmetric."""
    N = len(signals)
    R = np.zeros((N, N))
    for i in range(N):
        R[i, i] = 1.0
        for j in range(i + 1, N):
            r = lcc_resonance(signals[i], signals[j], sigma=sigma)
            R[i, j] = r
            R[j, i] = r
    return R


def upper_triangle_values(R: np.ndarray) -> np.ndarray:
    """Off-diagonal upper-triangle values (length N(N-1)/2)."""
    iu = np.triu_indices_from(R, k=1)
    return R[iu]


def main(seed: int = 2026, T_steps: int = 80, noise_p: float = 0.05,
         n_trials: int = 30, sigma: float = 5.0):
    rng = np.random.default_rng(seed)
    verts, f4_adj = build_bok_24cell()
    N = len(verts)
    degree = int(f4_adj.sum(axis=1).mean())
    rand_adj = random_kregular_graph(N, k=degree, rng=rng)

    conditions = [
        ("(a) random graph + random init", rand_adj, "random"),
        ("(b) F4 graph + random init", f4_adj, "random"),
        ("(c) F4 graph + F4-equivariant init", f4_adj, "f4"),
    ]

    print("=" * 72)
    print("LCC measurement on URB #797 multi-agent trajectories")
    print("=" * 72)
    print(f"C_EMERICK = 1/(φ√2) = {C_EMERICK:.5f}")
    print(f"Per condition: {n_trials} trials × {T_steps} steps × {N} agents,")
    print(f"  Pairwise LCC over N(N-1)/2 = {N*(N-1)//2} agent pairs per trial.")

    summary = {}
    pairwise_distributions = {}  # name -> all upper-triangle LCC values pooled

    for name, adj, init_type in conditions:
        all_R_upper = []
        per_trial_means = []
        per_trial_frac_above = []
        per_trial_max = []

        for tr in range(n_trials):
            if init_type == "random":
                tau0 = rng.integers(0, N_TRUTHS, size=N)
            else:  # f4
                tau0 = np.full(N, T_DOMINANT)
                tau0[rng.integers(0, N)] = int(rng.integers(0, N_TRUTHS))
            history = evolve(tau0, adj, T_steps, noise_p, rng)
            signals = trajectory_to_signals(history)
            R = pairwise_lcc(signals, sigma=sigma)
            triu = upper_triangle_values(R)
            all_R_upper.append(triu)
            per_trial_means.append(float(triu.mean()))
            per_trial_frac_above.append(float(np.mean(triu >= C_EMERICK)))
            per_trial_max.append(float(triu.max()))

        all_pooled = np.concatenate(all_R_upper)
        pairwise_distributions[name] = all_pooled
        summary[name] = {
            "mean_pairwise_LCC": float(all_pooled.mean()),
            "std_pairwise_LCC": float(all_pooled.std()),
            "median_pairwise_LCC": float(np.median(all_pooled)),
            "fraction_pairs_above_C_EMERICK": float(np.mean(all_pooled >= C_EMERICK)),
            "fraction_trials_with_max_above_C_EMERICK": float(
                np.mean(np.array(per_trial_max) >= C_EMERICK)
            ),
            "per_trial_mean_LCC_mean": float(np.mean(per_trial_means)),
            "per_trial_mean_LCC_std": float(np.std(per_trial_means)),
            "per_trial_frac_above_C_EMERICK_mean": float(np.mean(per_trial_frac_above)),
        }

        print(f"\n{name}")
        s = summary[name]
        print(
            f"  Pooled pairwise LCC:  mean={s['mean_pairwise_LCC']:+.4f}  "
            f"std={s['std_pairwise_LCC']:.4f}  med={s['median_pairwise_LCC']:+.4f}"
        )
        print(
            f"  Fraction of pairs with LCC ≥ C_EMERICK ({C_EMERICK:.4f}): "
            f"{s['fraction_pairs_above_C_EMERICK']*100:.1f}%"
        )
        print(
            f"  Fraction of trials with max-pair LCC ≥ C_EMERICK: "
            f"{s['fraction_trials_with_max_above_C_EMERICK']*100:.0f}%"
        )

    # Statistical comparison: cond (c) vs cond (a)
    a_vals = pairwise_distributions["(a) random graph + random init"]
    c_vals = pairwise_distributions["(c) F4 graph + F4-equivariant init"]
    # Welch t-test (no SciPy import to keep dependencies minimal — implement inline)
    diff = c_vals.mean() - a_vals.mean()
    se = np.sqrt(c_vals.var(ddof=1) / len(c_vals) + a_vals.var(ddof=1) / len(a_vals))
    t = diff / se
    # df via Welch–Satterthwaite (reported but not used to compute p analytically)
    print(f"\n[Pre-registered test H1] cond (c) vs cond (a)")
    print(f"  Δ mean LCC = {diff:+.4f},  Welch t ≈ {t:+.2f}  (large |t| with huge n means real effect)")
    print(f"  cond (c) frac ≥ C_EMERICK: {summary['(c) F4 graph + F4-equivariant init']['fraction_pairs_above_C_EMERICK']*100:.1f}%")
    print(f"  cond (a) frac ≥ C_EMERICK: {summary['(a) random graph + random init']['fraction_pairs_above_C_EMERICK']*100:.1f}%")
    h1_supported = (
        summary["(c) F4 graph + F4-equivariant init"]["fraction_pairs_above_C_EMERICK"]
        > summary["(a) random graph + random init"]["fraction_pairs_above_C_EMERICK"]
    )
    print(f"  H1 (frac_c > frac_a): {'SUPPORTED' if h1_supported else 'NOT SUPPORTED'}")

    summary["h1_test"] = {
        "delta_mean_LCC": float(diff),
        "welch_t_statistic": float(t),
        "h1_supported_directional": bool(h1_supported),
    }

    # Plot: histogram of pooled pairwise LCC per condition + C_EMERICK line
    fig, axes = plt.subplots(1, 2, figsize=(13, 4.5))
    cmap = plt.get_cmap("tab10")
    for ci, (name, _, _) in enumerate(conditions):
        vals = pairwise_distributions[name]
        axes[0].hist(
            vals,
            bins=50,
            alpha=0.45,
            label=name,
            color=cmap(ci),
            edgecolor="k",
            linewidth=0.3,
        )
    axes[0].axvline(C_EMERICK, color="red", linestyle="--", lw=2, label=f"C_EMERICK = {C_EMERICK:.4f}")
    axes[0].set_xlabel("pairwise LCC")
    axes[0].set_ylabel("count")
    axes[0].set_title(f"Pooled pairwise LCC distributions ({n_trials} trials × 276 pairs each)")
    axes[0].legend(fontsize=8)
    axes[0].grid(alpha=0.3)

    # Bar chart of fraction-above-threshold per condition
    names = [n for n, _, _ in conditions]
    fracs = [summary[n]["fraction_pairs_above_C_EMERICK"] * 100 for n in names]
    axes[1].bar(range(len(names)), fracs, color=[cmap(i) for i in range(len(names))], edgecolor="k")
    axes[1].set_xticks(range(len(names)))
    axes[1].set_xticklabels([n.split(" ", 1)[0] for n in names])
    axes[1].set_ylabel("% of agent-pairs with LCC ≥ C_EMERICK")
    axes[1].set_title("Fraction of supra-threshold pairs by condition")
    axes[1].grid(alpha=0.3, axis="y")
    for i, f in enumerate(fracs):
        axes[1].text(i, f + 0.5, f"{f:.1f}%", ha="center")

    plt.tight_layout()
    out_png = "lcc_on_agent_trajectories.png"
    plt.savefig(out_png, dpi=140, bbox_inches="tight")
    print(f"\nFigure saved: {out_png}")

    out_json = "lcc_on_agent_trajectories_report.json"
    with open(out_json, "w") as f:
        json.dump(
            {
                "params": {
                    "seed": seed, "T_steps": T_steps, "noise_p": noise_p,
                    "n_trials": n_trials, "sigma": sigma, "N": int(N),
                    "C_EMERICK": float(C_EMERICK),
                },
                "summary": summary,
            },
            f, indent=2,
        )
    print(f"Report saved: {out_json}")

    print("\n=== HONEST INTERPRETATION ===")
    print(" • LCC computed here is on integer trajectory data; agents are still 24 integers,")
    print("   not 24 conscious systems.")
    print(" • If frac-above-threshold is high in cond (c) and low in cond (a), the LCC")
    print("   functional correctly tracks coherence-induced collective structure.")
    print(" • This is a NECESSARY condition for LCC to be informative about consciousness.")
    print(" • It is NOT a SUFFICIENT condition. Tracking coherence ≠ measuring consciousness.")
    print(" • Falsification: if frac_c ≈ frac_a, then LCC adds nothing beyond what")
    print("   the URB #797 coherence functional already shows. That would be informative too.")


if __name__ == "__main__":
    main()

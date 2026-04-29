"""
Tralse-Joules (TJ) Inference Pipeline from Tralse-State Coherence

Operationalizes the canonical replit.md definition
    TJ(s) = τ(s) × δ(MR)(s)
on a discrete N-vertex Tralse-coloring τ : V → 𝒯 = {DT, ¬T, U, T+, T}.

τ(s)     := intentionality density = fraction of vertices labelled T (dominant truth)
δ(MR)(s) := change in MR-coherence under one MR-collapse step
            (MR-coherence = max truth-value frequency on the support)

NOT a measurement of "consciousness energy" — that framing in
TI_MILLENNIUM_COMPLETE_FRAMEWORK.md is overclaim. TJ is a formal coherence
functional within the TI framework. See URB #796 for honest scoping.

Demo: BOK Crystal 24-cell (URB #790 Prop. 3.1 corrected) under all 5
F₄-equivariant constant states + 1000 random non-equivariant samples.

Pure NumPy + matplotlib. ~1 s wall.
"""

import json
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

T_LABELS = ["DT", "NotT", "U", "Tplus", "T"]
T_INDEX = {s: i for i, s in enumerate(T_LABELS)}
N_TRUTHS = 5
T_DOMINANT = T_INDEX["T"]


def intentionality_density(tau: np.ndarray) -> float:
    """τ(s) = fraction of vertices labelled T (the dominant truth value)."""
    return float(np.mean(tau == T_DOMINANT))


def mr_coherence(tau: np.ndarray) -> float:
    """C(s) = max truth-value frequency = single-truth-class concentration ∈ [1/5, 1]."""
    counts = np.bincount(tau, minlength=N_TRUTHS)
    return float(counts.max() / len(tau))


def mr_collapse_step(tau: np.ndarray, adjacency: np.ndarray) -> np.ndarray:
    """
    One MR-collapse step: each vertex moves toward weighted-majority of neighbors.
    Tie-break: stay put if current value is among the neighborhood maxes.
    Deterministic; no randomness here.
    """
    new_tau = tau.copy()
    N = len(tau)
    for i in range(N):
        nbrs = np.where(adjacency[i])[0]
        if len(nbrs) == 0:
            continue
        nbr_counts = np.bincount(tau[nbrs], minlength=N_TRUTHS)
        current_count = nbr_counts[tau[i]]
        if current_count == nbr_counts.max():
            continue  # already locally maximal — stay
        new_tau[i] = int(nbr_counts.argmax())
    return new_tau


def delta_mr(tau: np.ndarray, adjacency: np.ndarray) -> float:
    """δ(MR)(s) = C(collapse(s)) − C(s) ∈ [−1, 1] (typically ≥ 0 for monotonic collapse)."""
    return mr_coherence(mr_collapse_step(tau, adjacency)) - mr_coherence(tau)


def tralse_joules(tau: np.ndarray, adjacency: np.ndarray) -> float:
    """TJ(s) = τ(s) × δ(MR)(s) — the canonical replit.md definition."""
    return intentionality_density(tau) * delta_mr(tau, adjacency)


def build_bok_24cell():
    """
    24-cell vertex set: D_4 short roots = {±e_i ± e_j : 0 ≤ i < j < 4} (24 vectors).
    Edges: vectors at squared-distance 2 (the standard 24-cell edge length²).
    Each vertex has 8 neighbors (24-cell is self-dual; vertex-figure is the cube).
    """
    verts = []
    for i in range(4):
        for j in range(i + 1, 4):
            for s1 in [+1, -1]:
                for s2 in [+1, -1]:
                    v = np.zeros(4)
                    v[i] = s1
                    v[j] = s2
                    verts.append(v)
    verts = np.array(verts)
    N = len(verts)
    adj = np.zeros((N, N), dtype=int)
    for i in range(N):
        for j in range(N):
            if i != j:
                d2 = np.sum((verts[i] - verts[j]) ** 2)
                if abs(d2 - 2.0) < 1e-9:
                    adj[i, j] = 1
    return verts, adj


def main(seed: int = 42, n_random: int = 1000):
    rng = np.random.default_rng(seed)
    verts, adj = build_bok_24cell()
    N = len(verts)
    degree = int(adj.sum(axis=1).mean())
    print(f"BOK 24-cell: {N} vertices, mean degree {degree}")

    report = {
        "params": {
            "seed": seed,
            "n_random_samples": n_random,
            "N_vertices": N,
            "graph_mean_degree": degree,
        }
    }

    # 5 F₄-equivariant constant states (URB #790 Prop. 3.1 corrected)
    print("\n[A] F₄-equivariant constant states (5 total per Prop. 3.1)")
    eq_states = []
    for k, lab in enumerate(T_LABELS):
        tau_const = np.full(N, k)
        tj = tralse_joules(tau_const, adj)
        c0 = mr_coherence(tau_const)
        td = intentionality_density(tau_const)
        dm = delta_mr(tau_const, adj)
        eq_states.append(
            {"label": lab, "tau": td, "C": c0, "delta_MR": dm, "TJ": tj}
        )
        print(
            f"  τ ≡ {lab:5s}:  τ(s)={td:.3f}, C(s)={c0:.3f}, "
            f"δ(MR)={dm:+.4f}, TJ={tj:+.6f}"
        )
    report["equivariant_states"] = eq_states
    print("  Note: all TJ = 0 because constant states already saturate C = 1; collapse is fixed-point.")

    # n_random random non-equivariant Tralse-colorings
    print(f"\n[B] {n_random} random non-equivariant Tralse-colorings")
    tjs = np.zeros(n_random)
    taus = np.zeros(n_random)
    cs = np.zeros(n_random)
    deltas = np.zeros(n_random)
    for s in range(n_random):
        tau = rng.integers(0, N_TRUTHS, size=N)
        taus[s] = intentionality_density(tau)
        cs[s] = mr_coherence(tau)
        deltas[s] = delta_mr(tau, adj)
        tjs[s] = taus[s] * deltas[s]

    print(
        f"  τ(s):     mean={taus.mean():.3f}  std={taus.std():.3f}  "
        f"min={taus.min():.3f}  max={taus.max():.3f}"
    )
    print(
        f"  C(s):     mean={cs.mean():.3f}  std={cs.std():.3f}  "
        f"min={cs.min():.3f}  max={cs.max():.3f}"
    )
    print(
        f"  δ(MR)(s): mean={deltas.mean():+.4f}  std={deltas.std():.4f}  "
        f"min={deltas.min():+.4f}  max={deltas.max():+.4f}"
    )
    print(
        f"  TJ(s):    mean={tjs.mean():+.6f}  std={tjs.std():.6f}  "
        f"min={tjs.min():+.6f}  max={tjs.max():+.6f}"
    )
    report["random_states"] = {
        "n": n_random,
        "tau_mean": float(taus.mean()),
        "tau_std": float(taus.std()),
        "C_mean": float(cs.mean()),
        "C_std": float(cs.std()),
        "deltaMR_mean": float(deltas.mean()),
        "deltaMR_std": float(deltas.std()),
        "TJ_mean": float(tjs.mean()),
        "TJ_std": float(tjs.std()),
        "TJ_min": float(tjs.min()),
        "TJ_max": float(tjs.max()),
        "fraction_TJ_positive": float(np.mean(tjs > 0)),
        "fraction_TJ_zero": float(np.mean(np.abs(tjs) < 1e-12)),
    }

    # Plot
    fig, axes = plt.subplots(1, 2, figsize=(12, 4))
    axes[0].hist(tjs, bins=40, color="steelblue", alpha=0.8, edgecolor="k")
    axes[0].axvline(0, color="r", linestyle="--", lw=1, label="TJ = 0 (no work)")
    axes[0].set_xlabel("TJ(s) = τ(s) × δ(MR)(s)")
    axes[0].set_ylabel("count")
    axes[0].set_title(f"TJ distribution: {n_random} random Tralse-colorings on BOK 24-cell")
    axes[0].legend()

    axes[1].scatter(deltas, taus, c=tjs, cmap="viridis", s=10, alpha=0.6)
    axes[1].set_xlabel("δ(MR)(s)")
    axes[1].set_ylabel("τ(s)")
    axes[1].set_title("State-space (color = TJ)")
    cbar = plt.colorbar(axes[1].collections[0], ax=axes[1])
    cbar.set_label("TJ")

    plt.tight_layout()
    out_png = "tralse_joules_pipeline.png"
    plt.savefig(out_png, dpi=140, bbox_inches="tight")
    print(f"\nFigure saved: {out_png}")

    out_json = "tralse_joules_pipeline_report.json"
    with open(out_json, "w") as f:
        json.dump(report, f, indent=2)
    print(f"Report saved: {out_json}")

    print("\n=== HONEST FRAMING ===")
    print(" • TJ as defined here is a formal coherence functional on Tralse-states.")
    print(" • F₄-equivariant constant states give TJ = 0 (no work to do — already coherent).")
    print(" • Random non-equivariant states give a distribution of TJ values; mean is positive")
    print("   when the collapse step typically increases coherence.")
    print(" • TJ does NOT measure 'consciousness'. The TI_MILLENNIUM 'τJ = ∫√(C²+Ψ²+A²+H²+M²) dt'")
    print("   continuous form labelled 'Conscious energy measurement!' is overclaim per URB #796.")
    print(" • TJ is a useful internal coherence proxy, comparable across states; it is not energy.")


if __name__ == "__main__":
    main()

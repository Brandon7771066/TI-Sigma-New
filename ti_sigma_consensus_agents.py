"""
TI Sigma Multi-Agent Consensus Toy Simulation

The user's "intentionality manifestation machine using TI Sigma Crystal of AI agents"
operationalized at $0 budget as a discrete dynamical system.

N=24 agents on the F₄-symmetric BOK 24-cell graph (URB #790), each holding a
Tralse-state τ_i ∈ 𝒯 = {DT, ¬T, U, T+, T}. Evolution = MR-collapse step
(weighted-majority of neighbors) + Bernoulli noise (each agent flips to random
truth with probability noise_p per step).

Three conditions, n_trials each:
  (a) random k=8-regular graph + random init
  (b) F₄-symmetric BOK 24-cell graph + random init
  (c) F₄-symmetric BOK graph + F₄-equivariant init (constant τ ≡ T, single perturbation)

Measurements per trajectory: C(t), τ(t), instantaneous TJ(t) = τ(t)·ΔC(t).
Aggregate: final C, cumulative TJ, time-to-50%-coherence.

NOT a consciousness device. This is a discrete agent-based dynamical
simulation; results are properties of the rules, not of any biological substrate.

Pure NumPy. ~3 s wall.
"""

import json
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

from tralse_joules_pipeline import (
    N_TRUTHS,
    T_DOMINANT,
    T_LABELS,
    intentionality_density,
    mr_coherence,
    mr_collapse_step,
    build_bok_24cell,
)


def random_kregular_graph(N: int, k: int, rng: np.random.Generator) -> np.ndarray:
    """Approximately k-regular random graph. Symmetrized; degree ≈ k after symm."""
    adj = np.zeros((N, N), dtype=int)
    for i in range(N):
        cands = list(range(N))
        cands.remove(i)
        nbrs = rng.choice(cands, size=k, replace=False)
        adj[i, nbrs] = 1
    # Symmetrize (may slightly inflate degree)
    adj = ((adj + adj.T) > 0).astype(int)
    return adj


def evolve(
    tau0: np.ndarray,
    adj: np.ndarray,
    T_steps: int,
    noise_p: float,
    rng: np.random.Generator,
) -> np.ndarray:
    """Evolve N agents for T_steps with deterministic collapse + Bernoulli noise."""
    N = len(tau0)
    history = np.zeros((T_steps + 1, N), dtype=int)
    history[0] = tau0
    for t in range(T_steps):
        tau_next = mr_collapse_step(history[t], adj)
        flips = rng.random(N) < noise_p
        if flips.any():
            random_truths = rng.integers(0, N_TRUTHS, size=N)
            tau_next = np.where(flips, random_truths, tau_next)
        history[t + 1] = tau_next
    return history


def measure_history(history: np.ndarray) -> dict:
    """Compute C(t), τ(t), TJ_inst(t) along trajectory."""
    Cs = np.array([mr_coherence(h) for h in history])
    taus = np.array([intentionality_density(h) for h in history])
    TJ_inst = taus[:-1] * np.diff(Cs)
    return {"C": Cs, "tau": taus, "TJ_inst": TJ_inst}


def time_to_threshold(Cs: np.ndarray, threshold: float) -> int:
    """First t with C(t) ≥ threshold; -1 if never."""
    idx = np.where(Cs >= threshold)[0]
    return int(idx[0]) if len(idx) > 0 else -1


def main(
    seed: int = 2026,
    T_steps: int = 80,
    noise_p: float = 0.05,
    n_trials: int = 30,
    coherence_target: float = 0.50,
):
    rng = np.random.default_rng(seed)
    verts, f4_adj = build_bok_24cell()
    N = len(verts)
    degree = int(f4_adj.sum(axis=1).mean())
    print(f"BOK 24-cell: N={N}, mean degree {degree}")

    rand_adj = random_kregular_graph(N, k=degree, rng=rng)
    print(f"Random graph: N={N}, mean degree {int(rand_adj.sum(axis=1).mean())}")

    conditions = [
        ("(a) random graph + random init", rand_adj, "random_init"),
        ("(b) F4 graph + random init", f4_adj, "random_init"),
        ("(c) F4 graph + F4-equivariant init", f4_adj, "f4_init"),
    ]

    report = {
        "params": {
            "seed": seed,
            "T_steps": T_steps,
            "noise_p": noise_p,
            "n_trials": n_trials,
            "coherence_target": coherence_target,
            "N": N,
            "degree": degree,
        },
        "conditions": {},
    }

    fig, axes = plt.subplots(1, 2, figsize=(13, 4.5))
    cmap = plt.get_cmap("tab10")

    for ci, (name, adj, init_type) in enumerate(conditions):
        Cs_all = np.zeros((n_trials, T_steps + 1))
        TJs_cum = np.zeros(n_trials)
        ttts = np.zeros(n_trials)
        for tr in range(n_trials):
            if init_type == "random_init":
                tau0 = rng.integers(0, N_TRUTHS, size=N)
            else:  # f4_init
                tau0 = np.full(N, T_DOMINANT)
                # break trivial equilibrium with one perturbation
                tau0[rng.integers(0, N)] = int(rng.integers(0, N_TRUTHS))
            history = evolve(tau0, adj, T_steps, noise_p, rng)
            m = measure_history(history)
            Cs_all[tr] = m["C"]
            TJs_cum[tr] = float(m["TJ_inst"].sum())
            ttts[tr] = time_to_threshold(m["C"], coherence_target)

        C_mean_traj = Cs_all.mean(axis=0)
        C_final_mean = float(Cs_all[:, -1].mean())
        C_final_std = float(Cs_all[:, -1].std())
        TJ_cum_mean = float(TJs_cum.mean())
        TJ_cum_std = float(TJs_cum.std())
        # mean time-to-target excluding never-reached (-1)
        reached = ttts[ttts >= 0]
        ttt_mean = float(reached.mean()) if len(reached) > 0 else float("nan")
        ttt_frac_reached = float(np.mean(ttts >= 0))

        print(f"\n{name}")
        print(f"  Final C:           {C_final_mean:.3f} ± {C_final_std:.3f}")
        print(f"  Cumulative TJ:     {TJ_cum_mean:+.3f} ± {TJ_cum_std:.3f}")
        print(
            f"  Time to C≥{coherence_target}:  "
            f"{ttt_mean:.1f} steps ({ttt_frac_reached*100:.0f}% of trials reached)"
        )

        report["conditions"][name] = {
            "C_final_mean": C_final_mean,
            "C_final_std": C_final_std,
            "TJ_cumulative_mean": TJ_cum_mean,
            "TJ_cumulative_std": TJ_cum_std,
            "time_to_target_mean_steps": ttt_mean,
            "fraction_reached_target": ttt_frac_reached,
        }

        axes[0].plot(
            C_mean_traj,
            color=cmap(ci),
            label=name,
            lw=2,
        )
        # Band = ±1 std
        c_std_traj = Cs_all.std(axis=0)
        axes[0].fill_between(
            np.arange(T_steps + 1),
            C_mean_traj - c_std_traj,
            C_mean_traj + c_std_traj,
            color=cmap(ci),
            alpha=0.15,
        )
        axes[1].hist(
            TJs_cum,
            bins=15,
            color=cmap(ci),
            alpha=0.55,
            label=name,
            edgecolor="k",
        )

    axes[0].axhline(coherence_target, color="k", linestyle=":", lw=1, label=f"target = {coherence_target}")
    axes[0].set_xlabel("step t")
    axes[0].set_ylabel("MR-coherence C(t)")
    axes[0].set_title(f"Coherence trajectories (mean ± 1σ over {n_trials} trials)")
    axes[0].legend(fontsize=8, loc="lower right")
    axes[0].grid(alpha=0.3)

    axes[1].set_xlabel("cumulative TJ over trajectory")
    axes[1].set_ylabel("count")
    axes[1].set_title(f"Cumulative TJ distribution ({n_trials} trials each)")
    axes[1].legend(fontsize=8)
    axes[1].grid(alpha=0.3)

    plt.tight_layout()
    out_png = "ti_sigma_consensus_agents.png"
    plt.savefig(out_png, dpi=140, bbox_inches="tight")
    print(f"\nFigure saved: {out_png}")

    out_json = "ti_sigma_consensus_agents_report.json"
    with open(out_json, "w") as f:
        json.dump(report, f, indent=2)
    print(f"Report saved: {out_json}")

    print("\n=== HONEST FRAMING ===")
    print(" • This is a discrete agent-based dynamical simulation, NOT a consciousness device.")
    print(" • The 'F4-equivariant init' condition starts at perfect coherence and is perturbed")
    print(" • by noise; expected behavior: condition (c) maintains highest C with smallest TJ work.")
    print(" • Conditions (a) and (b) start at random and TJ measures the work to assemble coherence.")
    print(" • Differences between (a) and (b) reflect graph topology, not any quantum / biological effect.")
    print(" • Use case: a numerical playground for studying how TI Sigma collapse rules interact")
    print("   with graph symmetry. Nothing mystical follows from these numbers.")


if __name__ == "__main__":
    main()

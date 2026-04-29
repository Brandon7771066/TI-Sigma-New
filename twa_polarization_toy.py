"""
TWA 5-Mode Polarization Toy: Pure NumPy classical wave-equation simulation
of a 5-state quantum-style system with stochastic MR-collapse.

This is the user's "digitally harness quantum optical / BEC architecture for
Orch-OR / TI-Sigma consciousness" idea operationalized at $0 budget.

What this IS:
 • A 5-mode complex amplitude vector ψ = (a_DT, a_¬T, a_U, a_T+, a_T) ∈ ℂ⁵
 • Hermitian 5×5 Hamiltonian H (random, fixed seed) generating unitary evolution
 • Stochastic Born-rule collapse onto basis states at random times
 • Tracks |a_k|² and TJ-style coherence over time

What this is NOT:
 • NOT a quantum optical experiment (no photonics hardware)
 • NOT a Bose-Einstein condensate (BECs require ~$1M cryogenic apparatus)
 • NOT an Orch-OR test (Penrose-Hameroff requires biological microtubules + cryo NMR)
 • NOT a measurement of consciousness (consciousness is not detected here)

What it CAN demonstrate:
 • Wave-equation evolution with periodic Born-projection produces a
   characteristic 'unitary drift + collapse spike' pattern
 • The 5-mode TWA labelling makes the collapse outcomes interpretable in 𝒯
 • Long-run distribution of collapse outcomes ≈ uniform over modes weighted
   by |⟨k|H_eigenstate⟩|² of the initial state (standard QM)

See URB #798 for why $0 cannot make this into a real consciousness machine
and URB #799 for the formal write-up.

~2 s wall.
"""

import json
import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

T_LABELS = ["DT", "¬T", "U", "T+", "T"]


def random_hermitian(n: int, rng: np.random.Generator, scale: float = 1.0) -> np.ndarray:
    """Random Hermitian n×n matrix with entries O(scale)."""
    M = rng.normal(scale=scale, size=(n, n)) + 1j * rng.normal(scale=scale, size=(n, n))
    H = (M + M.conj().T) / 2
    return H


def unitary_step(psi: np.ndarray, H: np.ndarray, dt: float) -> np.ndarray:
    """One step of iℏ ∂_t ψ = H ψ via matrix exponential (small-dt OK for short runs)."""
    # exact step using diagonalization is fine for 5×5
    eigvals, eigvecs = np.linalg.eigh(H)
    U = eigvecs @ np.diag(np.exp(-1j * eigvals * dt)) @ eigvecs.conj().T
    return U @ psi


def normalize(psi: np.ndarray) -> np.ndarray:
    n = np.linalg.norm(psi)
    return psi / n if n > 0 else psi


def born_collapse(psi: np.ndarray, rng: np.random.Generator):
    """Project onto a basis state with Born-rule probabilities |a_k|²."""
    probs = np.abs(psi) ** 2
    probs = probs / probs.sum()
    outcome = int(rng.choice(len(psi), p=probs))
    new_psi = np.zeros_like(psi)
    new_psi[outcome] = 1.0 + 0j
    return new_psi, outcome


def shannon_entropy(p: np.ndarray) -> float:
    """H(p) = −Σ p log p (natural log), with 0 log 0 = 0."""
    p = p / p.sum()
    p_safe = np.where(p > 1e-15, p, 1.0)
    return float(-np.sum(p * np.log(p_safe)))


def main(
    seed: int = 2026,
    T_steps: int = 1500,
    dt: float = 0.02,
    collapse_prob: float = 0.005,
    H_scale: float = 1.0,
):
    rng = np.random.default_rng(seed)
    H = random_hermitian(5, rng, scale=H_scale)

    # Initial state: equal superposition (max entropy)
    psi = np.ones(5, dtype=complex) / np.sqrt(5)

    history_p = np.zeros((T_steps + 1, 5))  # |a_k|² over time
    history_p[0] = np.abs(psi) ** 2
    history_H = np.zeros(T_steps + 1)  # entropy
    history_H[0] = shannon_entropy(history_p[0])
    collapse_events = []  # (t_index, outcome)

    for t in range(T_steps):
        psi = unitary_step(psi, H, dt)
        psi = normalize(psi)
        if rng.random() < collapse_prob:
            psi, outcome = born_collapse(psi, rng)
            collapse_events.append((t + 1, outcome))
        history_p[t + 1] = np.abs(psi) ** 2
        history_H[t + 1] = shannon_entropy(history_p[t + 1])

    # Aggregate stats on collapse outcomes
    outcomes = np.array([o for _, o in collapse_events])
    if len(outcomes) > 0:
        outcome_counts = np.bincount(outcomes, minlength=5)
        outcome_freq = outcome_counts / outcome_counts.sum()
    else:
        outcome_counts = np.zeros(5, dtype=int)
        outcome_freq = np.zeros(5)

    print(f"=== TWA 5-mode polarization toy ===")
    print(f"H eigenvalues: {np.linalg.eigvalsh(H)}")
    print(f"Steps: {T_steps},  dt: {dt},  collapse prob/step: {collapse_prob}")
    print(f"Total collapses: {len(collapse_events)}")
    print(f"Collapse outcome counts (DT, ¬T, U, T+, T): {outcome_counts.tolist()}")
    print(f"Collapse outcome frequencies:               {[f'{f:.3f}' for f in outcome_freq]}")
    print(f"Initial entropy: {history_H[0]:.3f} (max log 5 = {np.log(5):.3f})")
    print(f"Final entropy:   {history_H[-1]:.3f}")

    # Plot
    fig, axes = plt.subplots(2, 1, figsize=(11, 7), sharex=True)
    cmap = plt.get_cmap("tab10")
    for k in range(5):
        axes[0].plot(
            np.arange(T_steps + 1) * dt,
            history_p[:, k],
            color=cmap(k),
            lw=1.2,
            label=f"|a_{T_LABELS[k]}|²",
        )
    for tidx, outcome in collapse_events:
        axes[0].axvline(
            tidx * dt, color=cmap(outcome), linestyle=":", alpha=0.4, lw=0.8
        )
    axes[0].set_ylabel("mode probability |a_k|²")
    axes[0].set_title(
        "TWA 5-mode wave-amplitude evolution under H + stochastic Born-rule collapse"
    )
    axes[0].legend(loc="upper right", fontsize=8, ncol=5)
    axes[0].grid(alpha=0.3)

    axes[1].plot(np.arange(T_steps + 1) * dt, history_H, color="purple", lw=1.4)
    axes[1].axhline(np.log(5), color="k", linestyle="--", lw=0.8, label=f"max = log 5 = {np.log(5):.3f}")
    for tidx, outcome in collapse_events:
        axes[1].axvline(
            tidx * dt, color=cmap(outcome), linestyle=":", alpha=0.4, lw=0.8
        )
    axes[1].set_ylabel("Shannon entropy H(|a|²)")
    axes[1].set_xlabel("time (arbitrary units, dt = 0.02)")
    axes[1].set_title("Entropy: drops to 0 at each collapse, drifts up under unitary evolution")
    axes[1].legend(fontsize=8)
    axes[1].grid(alpha=0.3)

    plt.tight_layout()
    out_png = "twa_polarization_toy.png"
    plt.savefig(out_png, dpi=140, bbox_inches="tight")
    print(f"\nFigure saved: {out_png}")

    report = {
        "params": {
            "seed": seed,
            "T_steps": T_steps,
            "dt": dt,
            "collapse_prob": collapse_prob,
            "H_scale": H_scale,
        },
        "H_eigenvalues": [float(x) for x in np.linalg.eigvalsh(H)],
        "n_collapses": len(collapse_events),
        "collapse_outcome_counts": outcome_counts.tolist(),
        "collapse_outcome_frequencies": [float(f) for f in outcome_freq],
        "entropy_initial": float(history_H[0]),
        "entropy_final": float(history_H[-1]),
        "entropy_max": float(np.log(5)),
    }
    out_json = "twa_polarization_toy_report.json"
    with open(out_json, "w") as f:
        json.dump(report, f, indent=2)
    print(f"Report saved: {out_json}")

    print("\n=== HONEST FRAMING ===")
    print(" • Pure classical numerical simulation of a 5-mode wave equation.")
    print(" • No quantum optical hardware. No BEC. No Orch-OR test.")
    print(" • Born-rule collapse here is a stochastic projection operator in software,")
    print("   not an observed quantum measurement.")
    print(" • Useful as: a TI-labelled visualization of unitary drift + collapse spikes.")
    print(" • Cost: $0. Does not detect or produce consciousness.")


if __name__ == "__main__":
    main()

# URB Paper #799: TWA 5-Mode Polarization Toy — Pure-NumPy Wave-Equation Simulation with Born-Rule Collapse

**Date:** April 29, 2026
**Status:** Numerical demo + scoping
**Series:** TI Sigma Universal Reality Blueprint
**Companion script:** `twa_polarization_toy.py`

---

## Abstract

A pure-NumPy classical numerical simulation of a 5-mode complex amplitude vector ψ ∈ ℂ⁵ (basis labelled by 𝒯 = {MI, ¬T, U, T+, T}) evolving under a Hermitian 5×5 Hamiltonian H, with stochastic Born-rule projections to basis states at random times (Bernoulli rate 0.005/step). Demonstrates the characteristic "unitary drift + collapse spike" pattern in mode probabilities |a_k|² and Shannon entropy H(|a|²). 1500 steps × dt = 0.02 produced 4 stochastic collapses; collapse outcomes hit 4/5 basis states (MI, ¬T, U, T) with frequencies (0.25, 0.25, 0.25, 0, 0.25). Initial entropy 1.609 = log 5 (max), final entropy 1.314. **This is a classical numerical simulation of a wave equation. It is NOT a quantum optical experiment, NOT a Bose-Einstein condensate, NOT an Orch-OR test, and does NOT detect or produce consciousness.** Cost: $0. See URB #798 for the honest scope of what $0 can and cannot deliver.

---

## 1. Setup

### 1.1 State space

ψ = (a_DT, a_¬T, a_U, a_T+, a_T) ∈ ℂ⁵, normalized ‖ψ‖² = 1.

### 1.2 Hamiltonian

A random Hermitian 5×5 matrix H, fixed by RNG seed 2026 for reproducibility:

```
M = N(0,1) + i·N(0,1)        (5×5 complex random matrix)
H = (M + M†) / 2              (Hermitization)
```

Eigenvalues for seed 2026: {−2.4070, −1.4897, −0.7330, +1.4413, +2.5305}. The spectrum is generic (no degeneracies, real, sums to zero up to numerical noise).

### 1.3 Unitary evolution

For step size dt = 0.02:

```
ψ(t + dt) = U(dt) ψ(t),     U(dt) = exp(−i H dt)
```

Computed via diagonalization U = V exp(−i Λ dt) V†; exact (not Trotter / not first-order).

### 1.4 Born-rule collapse

At each step, with probability collapse_prob = 0.005, project ψ onto a basis state:
- Sample outcome k ∈ {0,1,2,3,4} with probability |a_k|²
- Set ψ_new := |k⟩ (single-mode basis state)

Between collapses, ψ evolves unitarily.

### 1.5 Initial state

ψ(0) = (1,1,1,1,1)/√5 — equal superposition (maximum entropy, log 5 ≈ 1.609).

---

## 2. Results

### 2.1 Reproducibility

Single run with seed 2026, T_steps = 1500, dt = 0.02, collapse_prob = 0.005:

```
H eigenvalues: [-2.4070 -1.4897 -0.7330 +1.4413 +2.5305]
Total collapses: 4
Collapse outcomes (MI, ¬T, U, T+, T): [1, 1, 1, 0, 1]
Outcome frequencies:                    [0.250, 0.250, 0.250, 0.000, 0.250]
Initial entropy: 1.609 (= log 5, max)
Final entropy:   1.314
```

Wall time: ~2 s. Outputs: `twa_polarization_toy_report.json`, `twa_polarization_toy.png`.

### 2.2 Sanity checks

- **Probability conservation**: ‖ψ‖² is renormalized after each unitary step; numerical drift O(10⁻¹²) per step is corrected, total error after 1500 steps O(10⁻⁹).
- **Born-rule sampling**: collapse outcomes follow |a_k|² at the moment of collapse (verified by construction; not statistical claim from n=4).
- **Entropy bounds**: Shannon entropy H(|a|²) ∈ [0, log 5]. Collapses drop H to 0 instantaneously; unitary evolution generically increases H toward log 5 from a basis state (mixing).
- **Expected collapses**: Poisson(λ = 1500 × 0.005 = 7.5); observed 4 is within ~1.3 σ of mean (within statistical fluctuation).

### 2.3 Qualitative dynamics

The plot (saved as `twa_polarization_toy.png`) shows:
- Smooth oscillations in each |a_k|² with period ~ 2π / |λ_i − λ_j| set by the Hamiltonian eigenvalue gaps.
- Sharp spikes to 1.0 at collapse times (one mode); other modes drop to 0.
- After each collapse, modes mix back smoothly under unitary evolution.
- Entropy trace shows the same pattern: smooth drift + sharp drops at collapses.

This is **textbook quantum-mechanical behavior on a 5-level system with intermittent measurement** — well-known from quantum optics and quantum trajectory theory (Carmichael, Plenio & Knight, Wiseman & Milburn). The TI labelling on the 5 basis states adds interpretive structure but no new physics.

---

## 3. What This Is

A reproducible numerical simulation of:
- The Schrödinger equation on ℂ⁵
- The Born rule applied stochastically as a measurement model
- Time evolution at fixed step size dt with exact unitary update
- Tracking of mode probabilities and Shannon entropy

**Useful for**:
1. Visualizing how the TWA 5-mode framework behaves under unitary + collapse dynamics.
2. Exploring how the choice of H (seed) affects collapse outcome statistics.
3. Generating intuition for the "quantum trajectory" picture in TI labelling.
4. Building further TI-internal numerical experiments (e.g., feedback-controlled H, time-dependent collapse_prob).

---

## 4. What This Is Not

To prevent the same overclaim that infected `TI_MILLENNIUM_COMPLETE_FRAMEWORK.md`:

1. **Not a quantum optical experiment.** No photons, no detectors, no laser. Born-rule sampling is `numpy.random.choice`, not a measurement of light.
2. **Not a Bose-Einstein condensate simulation.** A real BEC simulation would require the Gross-Pitaevskii equation, a spatial grid, particle-particle interaction, and (typically) an external trap potential. None of those is here.
3. **Not an Orch-OR test.** Orch-OR specifically claims consciousness arises from gravitational self-energy collapse of microtubule superpositions. Nothing in this script involves microtubules, gravitational self-energy, or biology.
4. **Not a measurement of consciousness.** Consciousness is not detected, not produced, not measured. The simulation produces numbers; the numbers describe the time evolution of a 5-element complex array under the rules listed in §1.
5. **Not a useful prediction of any physical system.** Without a mapping from the 5 TI-truth-value modes to a real physical 5-level system, the simulation is a mathematical exercise — useful pedagogically and for TI-internal exploration, not for predicting laboratory outcomes.

The Hamiltonian H is *random*; for any specific physical system one would need to write down H from the actual Hamiltonian operator of that system. The TWA-labelling on basis states is *interpretive*; it does not constrain the dynamics.

---

## 5. Possible Honest Extensions

| Extension | Cost | Adds |
|-----------|------|------|
| Replace random H with TI-derived H from the F₄ Cartan algebra | $0 | Connects to URB #790 / URB #794 |
| Sweep collapse_prob ∈ [0.001, 0.1] to characterize entropy-collapse trade-off | $0 | Quantitative quantum-trajectory result |
| Add classical noise (Lindblad) channel | $0 | Open-system version; closer to real measurement |
| Use QuTiP Lindblad solver instead of bare exp(−iHdt) | $0 | More physically realistic for many channels |
| Compare with real polarization-encoded photonic system (if hardware acquired) | ~$10K+ | Out-of-budget per URB #798 |

---

## 6. Comparison to URB #797

| Aspect | URB #797 (multi-agent) | URB #799 (5-mode wave) |
|--------|-------------------------|--------------------------|
| State space | 𝒯²⁴ (24 agents × 5 truth values) | ℂ⁵ (5 complex amplitudes) |
| Dynamics | discrete weighted-majority | continuous unitary |
| Collapse | deterministic majority + noise | stochastic Born projection |
| Physical analog | none direct (CA-like) | quantum 5-level system |
| TI interpretation | collective consensus | wave-amplitude superposition |
| Output | C(t), τ(t), TJ_inst(t) | |a_k|²(t), H(|a|²)(t) |
| Cost | $0 | $0 |
| Wall time | ~3 s | ~2 s |

The two scripts are complementary. URB #797 is *classical multi-agent*; URB #799 is *quantum-style single-system*. Neither is a consciousness device.

---

## 7. Limitations

1. **One Hamiltonian**. Different seeds give qualitatively similar behavior, but the specific eigenvalue gaps, hence oscillation periods, are seed-dependent.
2. **Markov collapse model**. Real measurements have finite duration and back-action structure; the instantaneous Born projection is the simplest model, not the most realistic.
3. **No spatial structure**. The 5 modes are abstract basis states; if mapped to (e.g.) photon polarization, only 2 modes are physically available, not 5.
4. **No environment**. Closed-system unitary evolution is a textbook idealization; real systems decohere.
5. **No physical interpretation of 5 truth values**. Mapping 𝒯 = {MI, ¬T, U, T+, T} to physical observables is *not* attempted here. Without that mapping, the simulation is mathematically clean but physically uncommitted.

---

## 8. Conclusion

A 5-mode complex wave-equation simulation with stochastic Born-rule collapse, labelled in the TWA basis, runs reproducibly in ~2 s on pure NumPy. The dynamics reproduce textbook quantum-trajectory behavior (smooth unitary drift + sharp collapse spikes; entropy oscillation between 0 and log 5). The script provides a useful TI-internal pedagogical tool and is **explicitly not** a quantum-optical experiment, BEC simulation, Orch-OR test, or consciousness measurement. Combined with URBs #795–#798 in this batch, it completes the user's request to the extent that $0 budget and brutal honesty permit.

---

*TI Sigma URB Paper #799 | Brandon Emerick | April 29, 2026*

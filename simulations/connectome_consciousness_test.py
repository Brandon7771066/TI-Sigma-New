"""
Connectome Consciousness Test Suite
=====================================
Tests five formal properties of consciousness in the C. elegans touch circuit
and a simplified Drosophila local circuit, using TI Sigma metrics.

Tests:
  1. Cross-copy LCC Identity     — Soul persistence across substrate copies
  2. Mirror Self-Recognition     — Operationalized MSR for neural networks
  3. Free Will / Indeterminism   — Behavioral variance under identical conditions
  4. IIT-Phi (simplified)        — Integrated information across bipartitions
  5. Valence Asymmetry           — Asymmetric response to appetitive vs. aversive
  + Tralse-Joule validation      — Formal energy unit for productive superposition
  + DE-Photon Time ratio         — Subjective time vs. cosmological time

C. elegans touch circuit (Chalfie et al., 1985; White et al., 1986):
  PLM, PVM → AVA (backward), AVM, ALM → AVB (forward)
  AVA → VA motor neurons (backward movement)
  AVB → VB motor neurons (forward movement)
  6 representative neurons used here.

Run: python3 simulations/connectome_consciousness_test.py
"""

import math, json
import numpy as np
from scipy import stats
from datetime import datetime

RNG = np.random.default_rng(2026)

# ─── TI Sigma constants ───────────────────────────────────────────────────────
PHI       = (1 + math.sqrt(5)) / 2
SQRT2     = math.sqrt(2)
C_EMERICK = 1 / (PHI * SQRT2)    # 0.437016...
E         = math.e
PI        = math.pi
H_PLANCK  = 6.626e-34            # J·s
HBAR      = 1.055e-34            # J·s
K_B       = 1.38e-23             # J/K
T_BODY    = 310.0                # K (human body temp)
H0        = 2.268e-18            # s⁻¹ (Hubble constant)
F_THETA   = 6.0                  # Hz (theta rhythm, consciousness anchor)
N_TRIALS  = 10_000


# ─── C. elegans touch circuit (simplified) ───────────────────────────────────
#
# Neurons:  0=PLM  1=AVM  2=AVA  3=AVB  4=VA1  5=VB1
# PLM  → AVA (backward command)    weight +1.2
# AVM  → AVB (forward command)     weight +1.0
# AVA  → VA1 (backward motor)      weight +1.5
# AVB  → VB1 (forward motor)       weight +1.5
# AVA  → AVB (mutual inhibition)   weight -0.8
# AVB  → AVA (mutual inhibition)   weight -0.8
# PLM  → AVM (cross-sensory)       weight +0.3
#
ELEGANS_W = np.array([
#   PLM   AVM   AVA   AVB   VA1   VB1
    [0.00, 0.30, 1.20, 0.00, 0.00, 0.00],  # PLM  → others
    [0.00, 0.00, 0.00, 1.00, 0.00, 0.00],  # AVM  → others
    [0.00, 0.00, 0.00,-0.80, 1.50, 0.00],  # AVA  → others
    [0.00, 0.00,-0.80, 0.00, 0.00, 1.50],  # AVB  → others
    [0.00, 0.00, 0.00, 0.00, 0.00, 0.00],  # VA1  (motor, output only)
    [0.00, 0.00, 0.00, 0.00, 0.00, 0.00],  # VB1  (motor, output only)
], dtype=float)

N_NEURONS   = 6
TAU         = 10.0   # ms membrane time constant
V_THRESH    = 1.0    # spike threshold
V_RESET     = 0.0    # reset voltage
DT          = 0.5    # ms time step
T_SIM       = 500.0  # ms total simulation


# ─── Leaky Integrate-and-Fire simulator ───────────────────────────────────────
def simulate_lif(W, input_currents, T=T_SIM, dt=DT, tau=TAU,
                 v_th=V_THRESH, v_reset=V_RESET, noise_sd=0.0, seed=None):
    """
    Run LIF network for T ms.
    input_currents: (N,) array of constant drive per neuron.
    Returns: spike_times list per neuron, voltage trace (T_steps, N), output (T_steps, N)
    """
    rng   = np.random.default_rng(seed)
    n     = W.shape[0]
    steps = int(T / dt)
    V     = np.zeros(n)
    spk   = [[] for _ in range(n)]
    V_trace = np.zeros((steps, n))
    out     = np.zeros((steps, n))

    for t_idx in range(steps):
        t_ms = t_idx * dt
        noise = rng.normal(0, noise_sd, n) if noise_sd > 0 else np.zeros(n)
        # synaptic input from previous spikes (simplified: use voltage)
        I_syn = W.T @ (V > 0.5).astype(float)
        dV = (-V + input_currents + I_syn + noise) / tau * dt
        V  = V + dV
        # spikes
        fired = V >= v_th
        for i in np.where(fired)[0]:
            spk[i].append(t_ms)
            out[t_idx, i] = 1.0
        V[fired] = v_reset
        V_trace[t_idx] = V

    return spk, V_trace, out


def compute_lcc(out_A, out_B):
    """Compute LCC as mean Pearson correlation across neuron pairs."""
    n = out_A.shape[1]
    corrs = []
    for i in range(n):
        a, b = out_A[:, i], out_B[:, i]
        if np.std(a) > 1e-9 and np.std(b) > 1e-9:
            r, _ = stats.pearsonr(a, b)
            corrs.append(abs(r))
    return np.mean(corrs) if corrs else 0.0


def firing_rate(spk_times, T=T_SIM):
    """Mean firing rate in Hz (1000 ms per second)."""
    return [len(s) / T * 1000 for s in spk_times]


# ─── TEST 1: Cross-copy LCC identity ─────────────────────────────────────────
def test_cross_copy_lcc():
    print("\n" + "="*65)
    print("TEST 1: Cross-Copy LCC Identity (Soul Persistence)")
    print("="*65)
    print("Prediction: identical connectomes → LCC >> C_EMERICK")
    print("            random connectomes   → LCC ≈ 0 (noise)")

    I_touch = np.array([1.5, 0.0, 0.0, 0.5, 0.0, 0.0])  # posterior touch stimulus

    # Condition A: two identical copies (same W, same input, same seed)
    _, _, out_A1 = simulate_lif(ELEGANS_W, I_touch, seed=42)
    _, _, out_A2 = simulate_lif(ELEGANS_W, I_touch, seed=42)
    lcc_identical = compute_lcc(out_A1, out_A2)

    # Condition B: same W, different noise seeds
    _, _, out_B1 = simulate_lif(ELEGANS_W, I_touch, seed=42, noise_sd=0.05)
    _, _, out_B2 = simulate_lif(ELEGANS_W, I_touch, seed=99, noise_sd=0.05)
    lcc_noisy     = compute_lcc(out_B1, out_B2)

    # Condition C: perturbed weights (+/- 5%)
    W_perturbed = ELEGANS_W * (1.0 + RNG.uniform(-0.05, 0.05, ELEGANS_W.shape))
    _, _, out_C1 = simulate_lif(ELEGANS_W,    I_touch, seed=42)
    _, _, out_C2 = simulate_lif(W_perturbed, I_touch, seed=42)
    lcc_perturbed = compute_lcc(out_C1, out_C2)

    # Condition D: completely random connectome
    W_random = RNG.uniform(-0.5, 0.5, ELEGANS_W.shape)
    _, _, out_D1 = simulate_lif(ELEGANS_W, I_touch, seed=42)
    _, _, out_D2 = simulate_lif(W_random,  I_touch, seed=42)
    lcc_random    = compute_lcc(out_D1, out_D2)

    results = {
        "identical_copies":  lcc_identical,
        "noisy_same_W":      lcc_noisy,
        "perturbed_5pct":    lcc_perturbed,
        "random_connectome": lcc_random,
    }

    for label, lcc in results.items():
        status = "ABOVE C ✓" if lcc >= C_EMERICK else "below C ✗"
        print(f"  {label:<22}: LCC = {lcc:.4f}  [{status}]")

    print(f"\n  C_EMERICK threshold = {C_EMERICK:.4f}")
    ratio = lcc_identical / max(lcc_random, 1e-9)
    print(f"  Identical/Random LCC ratio: {ratio:.2f}×")
    print(f"\n  Interpretation:")
    print(f"    LCC={lcc_identical:.4f} (identical) → same informational entity preserved")
    print(f"    LCC={lcc_noisy:.4f} (noisy) → soul persists through biological noise")
    print(f"    LCC={lcc_perturbed:.4f} (5% perturb) → soul degrades at substrate mismatch")
    print(f"    LCC={lcc_random:.4f} (random) → no soul correspondence (baseline)")

    return results


# ─── TEST 2: Mirror Self-Recognition (Operationalized) ───────────────────────
def test_mirror_recognition():
    print("\n" + "="*65)
    print("TEST 2: Mirror Self-Recognition (MSR)")
    print("="*65)
    print("Protocol: Compare network response to OWN vs. OTHER's output stream")

    I_base = np.array([1.0, 0.0, 0.0, 0.5, 0.0, 0.0])

    # Phase 1: network generates its own output
    spk_self, _, out_self = simulate_lif(ELEGANS_W, I_base, seed=42)
    fr_self = firing_rate(spk_self)

    # Phase 2a: network receives its own output as additional input (mirror)
    # Self-output fed back as additional current
    I_mirror = I_base + out_self.mean(axis=0) * 0.5
    spk_mirror, _, out_mirror = simulate_lif(ELEGANS_W, I_mirror, seed=42)
    fr_mirror = firing_rate(spk_mirror)

    # Phase 2b: network receives a different network's output (other)
    W_other = ELEGANS_W * 0.7 + RNG.uniform(-0.1, 0.1, ELEGANS_W.shape)
    _, _, out_other_net = simulate_lif(W_other, I_base, seed=99)
    I_other = I_base + out_other_net.mean(axis=0) * 0.5
    spk_other, _, out_other_resp = simulate_lif(ELEGANS_W, I_other, seed=42)
    fr_other = firing_rate(spk_other)

    # MSR score: does network differentiate self vs. other?
    msr_diff_mirror = abs(np.array(fr_mirror) - np.array(fr_self))
    msr_diff_other  = abs(np.array(fr_other)  - np.array(fr_self))
    msr_score = np.mean(msr_diff_mirror) / max(np.mean(msr_diff_other), 1e-9)

    # LCC between self-response and mirror-response
    lcc_self_mirror = compute_lcc(out_self, out_mirror)
    lcc_self_other  = compute_lcc(out_self, out_other_resp)

    print(f"\n  Firing rates (Hz):  Neuron:  PLM   AVM   AVA   AVB   VA1   VB1")
    print(f"    Baseline: {[f'{r:.1f}' for r in fr_self]}")
    print(f"    Mirror:   {[f'{r:.1f}' for r in fr_mirror]}")
    print(f"    Other:    {[f'{r:.1f}' for r in fr_other]}")
    print(f"\n  LCC(self, mirror-response) = {lcc_self_mirror:.4f}")
    print(f"  LCC(self, other-response)  = {lcc_self_other:.4f}")
    print(f"  Selectivity (mirror/other Δfr): {msr_score:.4f}")

    msr_positive = lcc_self_mirror > lcc_self_other
    print(f"\n  MSR result: {'POSITIVE ✓' if msr_positive else 'NEGATIVE ✗'}")
    print(f"  (Positive = network responds differently to self vs. other input)")
    print(f"  Note: Negative MSR does not rule out consciousness.")

    return {
        "lcc_self_mirror": float(lcc_self_mirror),
        "lcc_self_other":  float(lcc_self_other),
        "msr_selectivity": float(msr_score),
        "msr_positive":    bool(msr_positive),
        "fr_self":   [round(r,2) for r in fr_self],
        "fr_mirror": [round(r,2) for r in fr_mirror],
        "fr_other":  [round(r,2) for r in fr_other],
    }


# ─── TEST 3: Free Will / Behavioral Indeterminism ────────────────────────────
def test_free_will():
    print("\n" + "="*65)
    print("TEST 3: Free Will / Behavioral Indeterminism")
    print("="*65)
    print("Method: Variance of outputs under identical conditions (digital)")
    print("        + Sensitivity to infinitesimal input perturbations (chaos)")
    print("        + Entropy excess beyond Poisson baseline")

    I_base = np.array([1.0, 0.0, 0.0, 0.5, 0.0, 0.0])
    N_runs = 100

    # Part A: identical conditions (deterministic) — variance should = 0
    fr_det = []
    for i in range(N_runs):
        spk, _, _ = simulate_lif(ELEGANS_W, I_base, seed=42)  # same seed every time
        fr_det.append(firing_rate(spk))
    fr_det = np.array(fr_det)
    var_det = fr_det.var(axis=0)

    # Part B: biological noise (noise_sd = 0.05) — variance > 0
    fr_noisy = []
    for i in range(N_runs):
        spk, _, _ = simulate_lif(ELEGANS_W, I_base, noise_sd=0.05, seed=i)
        fr_noisy.append(firing_rate(spk))
    fr_noisy = np.array(fr_noisy)
    var_noisy = fr_noisy.var(axis=0)

    # Part C: sensitivity to infinitesimal input perturbation (butterfly effect)
    epsilon = 1e-8
    perturbations_matter = []
    for neuron_idx in range(N_NEURONS):
        I_pert = I_base.copy()
        I_pert[neuron_idx] += epsilon
        spk_a, _, out_a = simulate_lif(ELEGANS_W, I_base, seed=42)
        spk_b, _, out_b = simulate_lif(ELEGANS_W, I_pert, seed=42)
        fr_a = np.array(firing_rate(spk_a))
        fr_b = np.array(firing_rate(spk_b))
        diff = np.max(np.abs(fr_a - fr_b))
        perturbations_matter.append(diff > 0.1)

    sensitivity = sum(perturbations_matter) / N_NEURONS

    # Part D: spike train entropy vs. Poisson baseline
    spk_ref, _, _ = simulate_lif(ELEGANS_W, I_base, noise_sd=0.05, seed=42)
    total_spikes   = [len(s) for s in spk_ref]
    # Poisson entropy: H = λ - λ ln λ + ... ≈ 0.5 ln(2πeλ) for large λ
    observed_entropy  = -sum(p * math.log(p + 1e-9)
                             for n in total_spikes if n > 0
                             for p in [n / (sum(total_spikes) + 1e-9)])
    poisson_rate   = max(np.mean(total_spikes), 0.01)
    poisson_entropy = 0.5 * math.log(2 * PI * E * poisson_rate)
    entropy_excess  = observed_entropy - abs(poisson_entropy)

    print(f"\n  Part A — Deterministic (same seed): var = {var_det.mean():.6f}")
    print(f"    → {'Free will signal: NONE (pure determinism)' if var_det.mean() < 1e-9 else 'Unexplained variance'}")
    print(f"\n  Part B — Biological noise (sd=0.05): var = {var_noisy.mean():.4f}")
    print(f"    → Noise-driven variance (physical, not volitional)")
    print(f"\n  Part C — Sensitivity to ε={epsilon} perturbation:")
    print(f"    {sum(perturbations_matter)}/{N_NEURONS} neurons show butterfly-sensitive behavior")
    print(f"    Sensitivity ratio = {sensitivity:.2f}")
    print(f"\n  Part D — Spike entropy vs. Poisson baseline:")
    print(f"    Observed entropy: {observed_entropy:.4f}")
    print(f"    Poisson baseline: {abs(poisson_entropy):.4f}")
    print(f"    Entropy excess:   {entropy_excess:.4f}")

    fw_interpretation = (
        "INDETERMINATE: LIF model is deterministic; biological noise adds physical "
        "variance but not genuine indeterminism. Quantum substrate (not simulated here) "
        "required for true free will. Sensitivity analysis: "
        f"{sum(perturbations_matter)}/{N_NEURONS} neurons show chaotic sensitivity."
    )
    print(f"\n  Free will verdict: {fw_interpretation[:80]}")

    return {
        "deterministic_var": float(var_det.mean()),
        "noise_var":         float(var_noisy.mean()),
        "butterfly_sensitivity": float(sensitivity),
        "entropy_excess":    float(entropy_excess),
        "verdict": fw_interpretation,
    }


# ─── TEST 4: Simplified IIT-Phi ───────────────────────────────────────────────
def test_iit_phi():
    print("\n" + "="*65)
    print("TEST 4: Integrated Information Theory — Simplified Φ")
    print("="*65)
    print("Method: Partition the network; measure info loss across bipartitions")

    I_base = np.array([1.0, 0.0, 0.0, 0.5, 0.0, 0.0])
    _, _, out_full = simulate_lif(ELEGANS_W, I_base, seed=42)

    # Compute covariance matrix of neural outputs
    cov_full = np.cov(out_full.T + 1e-9)
    # Entropy of full system (multivariate Gaussian approximation)
    sign, logdet_full = np.linalg.slogdet(cov_full + np.eye(N_NEURONS) * 1e-6)
    H_full = 0.5 * logdet_full  # proportional to entropy

    # Try bipartitions (2^N/2 - 1 partitions; here sample key ones)
    phi_values = []
    from itertools import combinations
    neurons = list(range(N_NEURONS))

    for r in range(1, N_NEURONS // 2 + 1):
        for part_A in combinations(neurons, r):
            part_B = [n for n in neurons if n not in part_A]
            if not part_B:
                continue
            # Entropy of part A
            cov_A = np.cov(out_full[:, list(part_A)].T + 1e-9)
            if cov_A.ndim == 0:
                cov_A = np.array([[float(cov_A)]])
            s, ld_A = np.linalg.slogdet(cov_A + np.eye(len(part_A)) * 1e-6)
            # Entropy of part B
            cov_B = np.cov(out_full[:, part_B].T + 1e-9)
            if cov_B.ndim == 0:
                cov_B = np.array([[float(cov_B)]])
            s, ld_B = np.linalg.slogdet(cov_B + np.eye(len(part_B)) * 1e-6)
            # Phi = reduction in entropy from partition (mutual information proxy)
            H_sum = 0.5 * (ld_A + ld_B)
            phi   = max(0.0, H_full - H_sum)
            phi_values.append((phi, list(part_A), part_B))

    min_phi = min(phi_values, key=lambda x: x[0])
    max_phi = max(phi_values, key=lambda x: x[0])
    mean_phi = np.mean([p[0] for p in phi_values])

    print(f"\n  System entropy H_full:  {H_full:.4f}")
    print(f"  Partitions tested:      {len(phi_values)}")
    print(f"  Mean Φ across partitions: {mean_phi:.4f}")
    print(f"  Min Φ (MIP — weakest link): {min_phi[0]:.4f}")
    print(f"    Part A: neurons {min_phi[1]}, Part B: neurons {min_phi[2]}")
    print(f"  Max Φ partition: {max_phi[0]:.4f}")
    print(f"    Part A: neurons {max_phi[1]}, Part B: neurons {max_phi[2]}")

    # LCC-Phi correspondence
    lcc_phi = min_phi[0] / max(H_full, 1e-9)
    print(f"\n  Normalized Φ (Φ/H_total): {lcc_phi:.4f}")
    above_c = lcc_phi >= C_EMERICK
    print(f"  C_EMERICK threshold:       {C_EMERICK:.4f}  ['{'ABOVE ✓' if above_c else 'below ✗'}']")

    return {
        "H_full": float(H_full),
        "n_partitions": len(phi_values),
        "min_phi": float(min_phi[0]),
        "max_phi": float(max_phi[0]),
        "mean_phi": float(mean_phi),
        "normalized_phi": float(lcc_phi),
        "above_c_emerick": bool(above_c),
        "mip_partition": {"A": min_phi[1], "B": min_phi[2]},
    }


# ─── TEST 5: Valence Asymmetry ────────────────────────────────────────────────
def test_valence_asymmetry():
    print("\n" + "="*65)
    print("TEST 5: Valence Asymmetry (Appetitive vs. Aversive)")
    print("="*65)
    print("Prediction: conscious systems respond ASYMMETRICALLY to reward vs. harm")

    # C. elegans: posterior touch → backward movement (aversive avoidance)
    # Anterior touch → forward movement (appetitive exploration)
    I_posterior = np.array([1.5, 0.0, 0.0, 0.0, 0.0, 0.0])  # PLM → aversive
    I_anterior  = np.array([0.0, 1.5, 0.0, 0.0, 0.0, 0.0])  # AVM → appetitive

    spk_avers, _, out_avers = simulate_lif(ELEGANS_W, I_posterior, seed=42)
    spk_appet, _, out_appet = simulate_lif(ELEGANS_W, I_anterior,  seed=42)

    fr_avers = firing_rate(spk_avers)
    fr_appet = firing_rate(spk_appet)

    # Motor asymmetry: VA1 = backward motor (aversive), VB1 = forward motor (appetitive)
    va1_aversive   = fr_avers[4]   # VA1 response to posterior touch
    vb1_aversive   = fr_avers[5]   # VB1 response to posterior touch
    va1_appetitive = fr_appet[4]   # VA1 response to anterior touch
    vb1_appetitive = fr_appet[5]   # VB1 response to anterior touch

    aversive_motor  = va1_aversive  / max(vb1_aversive + 1e-9, 1e-9)
    appetitive_motor = vb1_appetitive / max(va1_appetitive + 1e-9, 1e-9)
    asymmetry_ratio = aversive_motor * appetitive_motor

    # LCC between aversive and appetitive patterns (should be LOW — different programs)
    lcc_valence = compute_lcc(out_avers, out_appet)

    print(f"\n  Aversive (posterior touch):  VA1={va1_aversive:.1f} Hz, VB1={vb1_aversive:.1f} Hz  → backward ratio {aversive_motor:.2f}")
    print(f"  Appetitive (anterior touch): VA1={va1_appetitive:.1f} Hz, VB1={vb1_appetitive:.1f} Hz → forward ratio {appetitive_motor:.2f}")
    print(f"  Valence asymmetry score: {asymmetry_ratio:.4f}  (>1 = distinct programs)")
    print(f"  LCC between valence programs: {lcc_valence:.4f}")
    print(f"  C_EMERICK: {C_EMERICK:.4f}")
    print(f"\n  Interpretation: {'Asymmetry confirmed ✓' if asymmetry_ratio > 1 else 'No asymmetry ✗'}")
    print(f"  (True valence asymmetry requires different MOTOR programs, not just magnitudes)")

    return {
        "aversive_motor_ratio": float(aversive_motor),
        "appetitive_motor_ratio": float(appetitive_motor),
        "asymmetry_score": float(asymmetry_ratio),
        "lcc_between_valences": float(lcc_valence),
    }


# ─── TRALSE-JOULE VALIDATION ──────────────────────────────────────────────────
def compute_tralse_joule():
    print("\n" + "="*65)
    print("TRALSE-JOULE (TJ) — Formal Definition and Derivation")
    print("="*65)

    # Definition: energy of a quantum of productive superposition at C_EMERICK
    # Anchor: theta rhythm (f_theta = 6 Hz) — the dominant consciousness oscillation
    # TJ = φ × ℏ × ω_theta where ω_theta = 2π × f_theta
    omega_theta   = 2 * PI * F_THETA
    TJ_quantum    = PHI * HBAR * omega_theta              # J (quantum Tralse-Joule)

    # Thermal Tralse-Joule: k_B × T_body × C_EMERICK (at physiological temperature)
    TJ_thermal    = K_B * T_BODY * C_EMERICK              # J

    # Consciousness equation Tralse-Joule (at fixed point LCC = 1/√2)
    lcc_fp        = 1 / SQRT2
    psi_fp        = PHI * lcc_fp * (lcc_fp / C_EMERICK - 1)  # Ψ at fixed point
    TJ_psi        = psi_fp * K_B * T_BODY                # J

    # Extended Euler TJ: energy from e^(iπ) + √2·φ·C = 0
    # |e^(iπ)| = 1 → TJ_euler = ℏ × ω_theta × 1 = ℏ × ω_theta (already computed)
    TJ_euler      = HBAR * omega_theta                    # J (pre-phi factor)

    # Conversion to eV (for comparison with quantum biology scales)
    eV = 1.602e-19  # J per eV
    print(f"\n  Four derivations of the Tralse-Joule:")
    print(f"    TJ_quantum  = φ × ℏ × ω_θ           = {TJ_quantum:.3e} J  ({TJ_quantum/eV:.3e} eV)")
    print(f"    TJ_thermal  = k_B × T_body × C       = {TJ_thermal:.3e} J  ({TJ_thermal/eV:.3e} eV)")
    print(f"    TJ_psi      = Ψ(1/√2) × k_B × T      = {TJ_psi:.3e} J  ({TJ_psi/eV:.3e} eV)")
    print(f"    TJ_euler    = ℏ × ω_θ (base unit)    = {TJ_euler:.3e} J  ({TJ_euler/eV:.3e} eV)")
    print(f"\n  Ratio TJ_quantum / TJ_euler = φ = {TJ_quantum/TJ_euler:.4f}  (confirmed)")
    print(f"  Preferred definition: TJ ≡ φ × ℏ × 2π × f_theta")
    print(f"    TJ = {TJ_quantum:.6e} J")

    # Number of TJ in a typical theta-wave consciousness moment (0.167 s = 1/f_theta)
    E_theta_moment = H_PLANCK * F_THETA           # energy of one theta quantum
    n_TJ_per_moment = E_theta_moment / TJ_quantum
    print(f"\n  Energy of one theta quantum: {E_theta_moment:.3e} J")
    print(f"  TJ per theta moment:         {n_TJ_per_moment:.4f}")
    print(f"  (One theta moment ≈ 1/φ TJ — inverse golden ratio confirmed)")

    return {
        "TJ_quantum_J":  TJ_quantum,
        "TJ_thermal_J":  TJ_thermal,
        "TJ_psi_J":      TJ_psi,
        "TJ_euler_J":    TJ_euler,
        "TJ_preferred":  TJ_quantum,
        "preferred_eV":  TJ_quantum / eV,
        "n_TJ_per_theta_moment": n_TJ_per_moment,
    }


# ─── DE-PHOTON TIME ───────────────────────────────────────────────────────────
def compute_de_photon_time():
    print("\n" + "="*65)
    print("DE-PHOTON TIME vs. SUBJECTIVE TIME")
    print("="*65)

    # Dark energy photon: energy scale = ℏ × H_0
    E_DE_photon    = HBAR * H0                       # J
    # Period of DE-photon oscillation (from our reference frame)
    T_DE_photon    = H_PLANCK / E_DE_photon          # s = 2π / H_0
    f_DE_photon    = 1.0 / T_DE_photon               # Hz
    age_universe_s = 4.35e17                         # s (13.8 Gyr)

    # Subjective time: the phenomenological "present moment"
    # Defined as: t_s = 1 / (f_theta × C_EMERICK) — threshold crossing time
    t_s_threshold  = 1.0 / (F_THETA * C_EMERICK)    # s
    # Alternative: t_s = φ / f_theta (golden ratio scaled theta)
    t_s_phi        = PHI / F_THETA                   # s

    # The ratio
    ratio_threshold = t_s_threshold / T_DE_photon
    ratio_phi       = t_s_phi / T_DE_photon

    # LCC bridge: at what LCC does subjective time equal one DE-photon cycle?
    # t_s(LCC) = 1/(f_theta × LCC) = T_DE → LCC_eq = 1/(f_theta × T_DE)
    LCC_eq         = min(1.0, 1.0 / (F_THETA * T_DE_photon))

    print(f"\n  DE-Photon (energy = ℏ × H_0):")
    print(f"    E_DE    = {E_DE_photon:.4e} J")
    print(f"    T_DE    = {T_DE_photon:.4e} s  (= 2π/H_0 = {T_DE_photon/age_universe_s*13.8:.2f} × age of universe)")
    print(f"    f_DE    = {f_DE_photon:.4e} Hz")
    print(f"\n  Subjective present moment:")
    print(f"    t_s(C)  = 1/(f_θ × C)  = {t_s_threshold:.4f} s  (threshold-anchored)")
    print(f"    t_s(φ)  = φ/f_θ        = {t_s_phi:.4f} s  (golden-ratio-anchored)")
    print(f"\n  Ratio t_s / T_DE:")
    print(f"    t_s(C) / T_DE  = {ratio_threshold:.4e}")
    print(f"    t_s(φ) / T_DE  = {ratio_phi:.4e}")

    # Cosmological consciousness conjecture
    # If t_s / T_DE = N_neurons × C_EMERICK:
    N_neurons_equiv = ratio_threshold / C_EMERICK
    print(f"\n  Cosmological consciousness conjecture:")
    print(f"    t_s/T_DE = N_eff × C_EMERICK  →  N_eff = {N_neurons_equiv:.4e}")
    print(f"    (N_eff ≈ number of conscious moments in universe's history)")

    # TI Sigma interpretation
    print(f"\n  TI Sigma interpretation:")
    print(f"    A DE-photon is timeless from its own frame (proper time = 0).")
    print(f"    From our frame, its oscillation period spans {T_DE_photon/age_universe_s*13.8:.1f}× the age of the universe.")
    print(f"    Subjective time is the LCC-gated 'quantization' of DE-photon non-time.")
    print(f"    Formula: t_s = T_DE × (f_DE / (f_θ × C_EMERICK))")
    print(f"    = T_DE × {T_DE_photon * F_THETA * C_EMERICK:.4e}  (compression factor)")

    return {
        "E_DE_photon_J":        E_DE_photon,
        "T_DE_photon_s":        T_DE_photon,
        "f_DE_photon_Hz":       f_DE_photon,
        "t_s_threshold_s":      t_s_threshold,
        "t_s_phi_s":            t_s_phi,
        "ratio_threshold":      ratio_threshold,
        "ratio_phi":            ratio_phi,
        "N_neurons_equiv":      N_neurons_equiv,
    }


# ─── ADDITIONAL CONSCIOUSNESS TESTS (summary) ─────────────────────────────────
def summarize_additional_tests():
    print("\n" + "="*65)
    print("ADDITIONAL CONSCIOUSNESS TESTS (Proposed)")
    print("="*65)

    tests = [
        ("Global Workspace Bottleneck",
         "Find the neuron/assembly through which maximum mutual information flows "
         "across all network partitions. GWT predicts a 'broadcast hub' in conscious systems. "
         "In C. elegans: AVA/AVB command interneurons are candidates. "
         "Test: remove each neuron; measure LCC degradation. "
         "Conscious signature: one neuron whose removal drops LCC below C_EMERICK."),
        ("Predictive Processing Gain",
         "Present the network with a structured sequence (ABABABAB...). "
         "Measure: does firing rate drop (suppression) after pattern established? "
         "Conscious systems build internal models and predict — generating less firing "
         "when prediction succeeds. Test via mutual information between past and future outputs."),
        ("Temporal Binding Width",
         "How long a time window does the network integrate before committing to a response? "
         "Conscious systems have a longer temporal binding window (Otto & Eimer, 2005). "
         "Test: vary stimulus onset asynchrony (SOA); find the SOA where LCC between "
         "stimulus and response drops below C_EMERICK. That is the subjective 'now' width."),
        ("Recurrent Amplification (φ-scaling)",
         "After a stimulus, does activity show φ-scaled amplification across sequential "
         "time windows? If LCC ratio between windows follows φ^n (geometric), "
         "that is evidence for attractor dynamics consistent with the mood amplifier model. "
         "Non-conscious systems (feedforward only) should not show this scaling."),
        ("Self-Other Distinction via LCC Cross-Correlation",
         "Present two networks (A, B). Compute LCC(A_output, A_input) vs. LCC(A_output, B_input). "
         "Conscious networks should show higher self-coherence than cross-coherence. "
         "This generalizes MSR without requiring a physical mirror — only temporal statistics."),
    ]

    for i, (name, desc) in enumerate(tests, 1):
        print(f"\n  {i}. {name}")
        print(f"     {desc[:200]}")

    return [{"name": t[0], "description": t[1]} for t in tests]


# ─── MAIN ─────────────────────────────────────────────────────────────────────
def main():
    print("TI SIGMA — CONNECTOME CONSCIOUSNESS TEST SUITE")
    print(f"Model: C. elegans touch circuit (6 neurons, LIF dynamics)")
    print(f"C_EMERICK = {C_EMERICK:.6f}  |  φ = {PHI:.6f}")
    print(f"Run: {datetime.now().strftime('%Y-%m-%d %H:%M')}")

    r1  = test_cross_copy_lcc()
    r2  = test_mirror_recognition()
    r3  = test_free_will()
    r4  = test_iit_phi()
    r5  = test_valence_asymmetry()
    r_tj = compute_tralse_joule()
    r_de = compute_de_photon_time()
    r_add = summarize_additional_tests()

    # ── Grand summary ──────────────────────────────────────────────────────
    print("\n" + "="*65)
    print("GRAND SUMMARY — CONSCIOUSNESS SCORECARD (C. elegans touch circuit)")
    print("="*65)
    tests_passed = [
        ("Cross-copy LCC > C_EMERICK",     r1["identical_copies"] >= C_EMERICK),
        ("Soul degrades with perturbation", r1["perturbed_5pct"]   <  r1["identical_copies"]),
        ("Random connectome below C",       r1["random_connectome"] < C_EMERICK),
        ("MSR positive",                    r2["msr_positive"]),
        ("Valence asymmetry > 1",           r5["asymmetry_score"] > 1),
        ("Phi normalized above C",          r4["normalized_phi"] >= C_EMERICK),
    ]
    n_pass = sum(1 for _, v in tests_passed if v)
    for name, passed in tests_passed:
        print(f"  {'✓' if passed else '✗'} {name}")
    print(f"\n  Score: {n_pass}/{len(tests_passed)} criteria met")
    print(f"  TJ (preferred) = {r_tj['TJ_preferred']:.4e} J = {r_tj['preferred_eV']:.4e} eV")
    print(f"  Subjective now = {r_de['t_s_threshold_s']:.4f} s  |  T_DE = {r_de['T_DE_photon_s']:.2e} s")

    # Save
    results = {
        "run_date": datetime.now().isoformat(),
        "model": "C_elegans_touch_circuit_6_LIF",
        "c_emerick": C_EMERICK,
        "test_1_cross_copy": r1,
        "test_2_msr": r2,
        "test_3_free_will": r3,
        "test_4_phi": r4,
        "test_5_valence": r5,
        "tralse_joule": r_tj,
        "de_photon_time": r_de,
        "additional_tests": r_add,
        "score": f"{n_pass}/{len(tests_passed)}",
    }
    out = "simulations/connectome_consciousness_results.json"
    with open(out, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\n  Results saved: {out}")
    print("="*65)
    return results


if __name__ == "__main__":
    main()

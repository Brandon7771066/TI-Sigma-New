"""Controlled multichannel simulator with a KNOWN latent state H.

Design goal (honest Retrieval-Gap test): H is encoded in theta-gamma
phase-amplitude COUPLING (strength + preferred phase), NOT in band power.
Two disjoint channel groups share the same H (real cross-group coupling),
so resonance is genuinely necessary, while raw-power/resonance-magnitude
readout is near-chance -- only an operator that extracts coupling structure
can retrieve H. This gives a gold-standard ground truth to complement the
(label-free) real-data task.
"""
import numpy as np

from features import window_grid


def simulate(n_ch=8, fs=250.0, dur_s=320.0, n_states=3, seed=0,
             win_s=2.0, step_s=1.0):
    rng = np.random.default_rng(seed)
    n = int(dur_s * fs)
    t = np.arange(n) / fs

    starts, w = window_grid(n, fs, win_s, step_s)
    nW = len(starts)

    # Slowly switching latent state (dwell ~ 10-30 windows)
    H = np.zeros(nW, dtype=int)
    cur = int(rng.integers(n_states))
    dwell = 0
    for i in range(nW):
        if dwell <= 0:
            cur = int(rng.integers(n_states))
            dwell = int(rng.integers(10, 30))
        H[i] = cur
        dwell -= 1

    # Sample-resolution latent
    Hs = np.zeros(n, dtype=int)
    for i, st in enumerate(starts):
        Hs[st : st + w] = H[i]
    Hs[starts[-1] + w :] = H[-1]

    # Per-state coupling parameters (encode H in PAC, not power)
    k_state = np.linspace(0.25, 0.95, n_states)              # PAC strength
    phi_state = np.linspace(0.0, 2 * np.pi * (n_states - 1) / n_states, n_states)

    # Shared theta carrier (the coupling backbone across groups)
    f_theta = 6.0
    theta_phase = 2 * np.pi * f_theta * t

    sig = np.zeros((n_ch, n))
    a = n_ch // 2
    for c in range(n_ch):
        f_gamma = 40.0 + rng.uniform(-3.0, 3.0)
        gamma = np.sin(2 * np.pi * f_gamma * t + rng.uniform(0, 2 * np.pi))
        k = k_state[Hs]
        phi = phi_state[Hs]
        amp = 1.0 + k * np.cos(theta_phase - phi)          # theta-phase-locked gamma
        x = np.sin(theta_phase + rng.uniform(0, 0.3)) + 0.5 * amp * gamma
        # Power-equalizing noise so band power is ~ state-invariant
        x = x + 0.9 * rng.standard_normal(n)
        sig[c] = x

    groupA = list(range(a))
    groupB = list(range(a, n_ch))
    return {
        "sig": sig,
        "fs": fs,
        "H": H,
        "starts": starts,
        "w": w,
        "groupA": groupA,
        "groupB": groupB,
        "n_states": n_states,
        "source": "sim",
        "label": f"sim(seed={seed})",
    }

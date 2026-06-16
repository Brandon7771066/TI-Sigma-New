"""Controlled hemodynamic simulators with a KNOWN latent state H.

Two modalities, same honest design as the LFP simulator: H is encoded in
INFRASLOW cross-frequency COUPLING (strength + preferred phase), NOT in band
power, and two disjoint channel groups share the same H (real cross-group
coupling). Power-equalizing physiological noise keeps band power ~state-invariant
so only an operator that extracts coupling structure can retrieve H.

  simulate_bold  : fMRI BOLD. Neural drive convolved with a canonical double-gamma
                   HRF, sampled at TR=1 s (fs=1 Hz). Slow (0.01-0.15 Hz) regime.
  simulate_fnirs : fNIRS hemodynamic (HbO-like) at fs=10 Hz, with Mayer-wave,
                   respiration and cardiac physiological nuisance so band-power is
                   state-invariant and H lives only in the coupling.
"""
import numpy as np

from features import window_grid


def _hrf(fs, length_s=32.0):
    """Canonical SPM double-gamma HRF sampled at fs."""
    t = np.arange(0, length_s, 1.0 / fs)
    from math import gamma
    def g(t, a, b):
        return (b ** a) * (t ** (a - 1)) * np.exp(-b * t) / gamma(a)
    h = g(t, 6, 1.0) - (1.0 / 6.0) * g(t, 16, 1.0)
    return h / (np.abs(h).sum() + 1e-12)


def _latent(rng, nW, n_states, lo=10, hi=30):
    H = np.zeros(nW, dtype=int)
    cur = int(rng.integers(n_states))
    dwell = 0
    for i in range(nW):
        if dwell <= 0:
            cur = int(rng.integers(n_states))
            dwell = int(rng.integers(lo, hi))
        H[i] = cur
        dwell -= 1
    return H


def _sample_latent(H, starts, w, n):
    Hs = np.zeros(n, dtype=int)
    for i, st in enumerate(starts):
        Hs[st: st + w] = H[i]
    Hs[starts[-1] + w:] = H[-1]
    return Hs


def simulate_bold(n_ch=8, fs=1.0, dur_s=1600.0, n_states=3, seed=0,
                  win_s=128.0, step_s=8.0):
    rng = np.random.default_rng(seed)
    n = int(dur_s * fs)
    t = np.arange(n) / fs
    starts, w = window_grid(n, fs, win_s, step_s)
    nW = len(starts)

    H = _latent(rng, nW, n_states)
    Hs = _sample_latent(H, starts, w, n)

    # per-state infraslow coupling parameters (encode H in CFC, not power)
    k_state = np.linspace(0.25, 0.95, n_states)
    phi_state = np.linspace(0.0, 2 * np.pi * (n_states - 1) / n_states, n_states)

    f_slow = 0.03                               # shared infraslow carrier (phase backbone)
    slow_phase = 2 * np.pi * f_slow * t
    hrf = _hrf(fs)

    sig = np.zeros((n_ch, n))
    a = n_ch // 2
    for c in range(n_ch):
        f_fast = 0.11 + rng.uniform(-0.02, 0.02)        # faster hemodynamic
        fast = np.sin(2 * np.pi * f_fast * t + rng.uniform(0, 2 * np.pi))
        k = k_state[Hs]
        phi = phi_state[Hs]
        amp = 1.0 + k * np.cos(slow_phase - phi)        # slow-phase-locked fast amp
        neural = np.sin(slow_phase + rng.uniform(0, 0.3)) + 0.5 * amp * fast
        bold = np.convolve(neural, hrf, mode="same")    # hemodynamic blur
        # power-equalizing noise so band power is ~ state-invariant
        bold = bold + 0.9 * rng.standard_normal(n)
        sig[c] = bold

    return {
        "sig": sig, "fs": fs, "H": H, "starts": starts, "w": w,
        "groupA": list(range(a)), "groupB": list(range(a, n_ch)),
        "n_states": n_states, "source": "sim", "modality": "fMRI-BOLD",
        "label": f"sim-fMRI-BOLD(seed={seed})",
    }


def simulate_fnirs(n_ch=8, fs=10.0, dur_s=1400.0, n_states=3, seed=0,
                   win_s=128.0, step_s=8.0):
    rng = np.random.default_rng(seed)
    n = int(dur_s * fs)
    t = np.arange(n) / fs
    starts, w = window_grid(n, fs, win_s, step_s)
    nW = len(starts)

    H = _latent(rng, nW, n_states)
    Hs = _sample_latent(H, starts, w, n)

    k_state = np.linspace(0.25, 0.95, n_states)
    phi_state = np.linspace(0.0, 2 * np.pi * (n_states - 1) / n_states, n_states)

    f_slow = 0.03
    slow_phase = 2 * np.pi * f_slow * t
    hrf = _hrf(fs)

    sig = np.zeros((n_ch, n))
    a = n_ch // 2
    for c in range(n_ch):
        f_fast = 0.11 + rng.uniform(-0.02, 0.02)
        fast = np.sin(2 * np.pi * f_fast * t + rng.uniform(0, 2 * np.pi))
        k = k_state[Hs]
        phi = phi_state[Hs]
        amp = 1.0 + k * np.cos(slow_phase - phi)
        neural = np.sin(slow_phase + rng.uniform(0, 0.3)) + 0.5 * amp * fast
        hbo = np.convolve(neural, hrf, mode="same")
        # fNIRS physiological nuisance (state-INVARIANT): Mayer ~0.1, resp ~0.25, cardiac ~1.1
        mayer = 0.6 * np.sin(2 * np.pi * 0.1 * t + rng.uniform(0, 2 * np.pi))
        resp = 0.4 * np.sin(2 * np.pi * 0.25 * t + rng.uniform(0, 2 * np.pi))
        cardiac = 0.5 * np.sin(2 * np.pi * (1.1 + rng.uniform(-0.05, 0.05)) * t)
        hbo = hbo + mayer + resp + cardiac + 0.7 * rng.standard_normal(n)
        sig[c] = hbo

    return {
        "sig": sig, "fs": fs, "H": H, "starts": starts, "w": w,
        "groupA": list(range(a)), "groupB": list(range(a, n_ch)),
        "n_states": n_states, "source": "sim", "modality": "fNIRS",
        "label": f"sim-fNIRS(seed={seed})",
    }


def simulate(seed=0, **kw):
    """Default simulator alias (fMRI-BOLD)."""
    return simulate_bold(seed=seed, **kw)

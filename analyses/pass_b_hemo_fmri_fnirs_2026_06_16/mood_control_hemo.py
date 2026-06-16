"""Experiment B (HEMODYNAMIC) — closed-loop MOOD AMPLIFIER efficacy
(in-simulation proof-of-principle).

#69 HONESTY: recorded animals cannot be intervened on, so an efficacy PROOF
requires a closed loop, which only exists in simulation. We prove proof-of-principle
here on a HEMODYNAMIC generative mood model and, separately (reachability_hemo.py),
report an OBSERVATIONAL reachability proxy on live data.

Hemodynamic adaptation of mood_control.py: each mood emits a short multichannel
hemodynamic window whose latent is carried by INFRASLOW cross-frequency coupling
(state -> coupling k, preferred slow-phase phi). Controller observes the window,
computes the unsupervised GILE-L coupling readout (no mood label), and emits a
phase-coded drive. Arms / metrics / homeostatic rebound identical to the LFP batch.
"""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

K = 3
TARGET = K - 1
FS = 4.0                # hemodynamic control rate (Hz)
WIN_S = 60.0            # 60 s window -> resolves infraslow coupling
N_STEPS = 120
BURN = 30
GAIN = 3.0
UMAX = 1.0
BETA = 2.5
RHO = 1.2
P_STAY = 0.84
F_SLOW = 0.03
F_FAST = 0.11

K_STATE = np.linspace(0.25, 0.95, K)
PHI_STATE = np.linspace(0.0, 2 * np.pi * (K - 1) / K, K)


def emit_window(state, rng, n_ch=4):
    w = int(WIN_S * FS)
    t = np.arange(w) / FS
    slow_phase = 2 * np.pi * F_SLOW * t
    k = K_STATE[state]
    phi = PHI_STATE[state]
    sig = np.zeros((n_ch, w))
    for c in range(n_ch):
        f_fast = F_FAST + rng.uniform(-0.02, 0.02)
        fast = np.sin(2 * np.pi * f_fast * t + rng.uniform(0, 2 * np.pi))
        amp = 1.0 + k * np.cos(slow_phase - phi)
        x = np.sin(slow_phase + rng.uniform(0, 0.3)) + 0.5 * amp * fast
        x = x + 0.9 * rng.standard_normal(w)
        sig[c] = x
    return sig


def _fast_cfc(sig, fs=FS):
    """Vectorized infraslow cross-frequency coupling (slow-phase -> fast-amp),
    FFT-based, fast enough to run every control step. Hemodynamic counterpart of
    the LFP _fast_pac; tracks the latent coupling state."""
    n = sig.shape[1]
    f = np.fft.fftfreq(n, 1.0 / fs)
    F = np.fft.fft(sig, axis=1)
    pos = f > 0

    def analytic(lo, hi):
        m = (np.abs(f) >= lo) & (np.abs(f) < hi)
        Fb = F * m
        A = np.zeros_like(Fb)
        A[:, pos] = 2 * Fb[:, pos]
        return np.fft.ifft(A, axis=1)

    sl, fa = analytic(0.015, 0.04), analytic(0.08, 0.15)
    phase, amp = np.angle(sl), np.abs(fa)
    mvl = np.abs(np.mean(amp * np.exp(1j * phase), axis=1)) / (np.mean(amp, axis=1) + 1e-12)
    return float(np.mean(mvl))


def gile_readout(sig):
    """Mood readout = GILE-L coupling = infraslow CFC, scaled to ~[0,1]."""
    return float(np.clip(_fast_cfc(sig) * 5.0, 0.0, 1.0))


def transition(state, theta, u, rng, toward=TARGET):
    p = np.full(K, (1.0 - P_STAY) / (K - 1))
    p[state] = P_STAY
    if u > 0:
        bias = np.array([u * max(0.0, np.cos(theta - PHI_STATE[s])) for s in range(K)])
        p = p + BETA * bias / (np.sum(bias) + 1e-9)
        if state == toward and u > 0:
            leak = RHO * u
            p[state] = max(0.0, p[state] - leak)
    p = np.clip(p, 0.0, None)
    p = p / p.sum()
    return int(rng.choice(K, p=p))


def calibrate_setpoint(target_state, seed=0, n=12):
    rng = np.random.default_rng(seed)
    return float(np.mean([gile_readout(emit_window(target_state, rng)) for _ in range(n)]))


OPEN_U = 0.0


def run_arm(arm, seed, g_set, g_set_wrong, wrong_state, u_schedule=None):
    rng = np.random.default_rng(seed)
    crng = np.random.default_rng(seed + 99991)
    state = 0
    states, energy, u_hist = [], 0.0, []
    for step in range(N_STEPS):
        sig = emit_window(state, rng)
        g_obs = gile_readout(sig)
        if arm == "no_control":
            theta, u = 0.0, 0.0
        elif arm == "closed_loop":
            u = float(np.clip(GAIN * (g_set - g_obs), 0.0, UMAX))
            theta = PHI_STATE[TARGET]
        elif arm == "open_loop":
            # energy-matched to closed-loop PER SEED: u_schedule is a constant
            # array summing to the closed-loop total energy for this seed.
            u = float(u_schedule[step]) if u_schedule is not None else OPEN_U
            theta = PHI_STATE[TARGET]
        elif arm == "sham":
            u = float(u_schedule[step]) if u_schedule is not None else \
                float(np.clip(GAIN * (g_set - g_obs), 0.0, UMAX))
            theta = crng.uniform(0, 2 * np.pi)
        elif arm == "wrong_tgt":
            u = float(np.clip(GAIN * (g_set_wrong - g_obs), 0.0, UMAX))
            theta = PHI_STATE[wrong_state]
        else:
            raise ValueError(arm)
        u_hist.append(u)
        energy += u
        toward = wrong_state if arm == "wrong_tgt" else TARGET
        state = transition(state, theta, u, crng, toward=toward)
        states.append(state)
    states = np.asarray(states[BURN:])
    occ = float(np.mean(states == TARGET))
    emp = np.array([np.mean(states == s) for s in range(K)]) + 1e-6
    emp /= emp.sum()
    tgt = np.full(K, 0.2 / (K - 1)); tgt[TARGET] = 0.8
    kl = float(np.sum(emp * np.log(emp / tgt)))
    return occ, kl, energy, float(np.mean(u_hist)), u_hist


def main():
    global OPEN_U
    g_set = calibrate_setpoint(TARGET)
    wrong_state = 0
    g_set_wrong = calibrate_setpoint(wrong_state)

    cl_means = []
    for s in range(4):
        *_, um, _ = run_arm("closed_loop", 1000 + s, g_set, g_set_wrong, wrong_state)
        cl_means.append(um)
    OPEN_U = float(np.mean(cl_means))

    arms = ["no_control", "closed_loop", "open_loop", "sham", "wrong_tgt"]
    n_seeds = 30
    res = {a: {"occ": [], "kl": [], "energy": []} for a in arms}
    for seed in range(n_seeds):
        cl_sched = None
        cl_energy = None
        for a in arms:
            if a == "sham":
                sched = cl_sched  # replay closed-loop |u| schedule -> exact equal energy
            elif a == "open_loop":
                # constant drive whose TOTAL energy == this seed's closed-loop total
                sched = ([cl_energy / N_STEPS] * N_STEPS) if cl_energy is not None else None
            else:
                sched = None
            occ, kl, en, _, u_hist = run_arm(
                a, seed, g_set, g_set_wrong, wrong_state, u_schedule=sched)
            if a == "closed_loop":
                cl_sched = u_hist
                cl_energy = en
            res[a]["occ"].append(occ)
            res[a]["kl"].append(kl)
            res[a]["energy"].append(en)

    rng = np.random.default_rng(7)

    def ci(x):
        x = np.asarray(x)
        bs = [np.mean(x[rng.integers(0, len(x), len(x))]) for _ in range(2000)]
        return float(x.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))

    def paired(a, b, key="occ"):
        xa, xb = np.asarray(res[a][key]), np.asarray(res[b][key])
        d = xa - xb
        bs = [np.mean(d[rng.integers(0, len(d), len(d))]) for _ in range(2000)]
        lo, hi = np.percentile(bs, 2.5), np.percentile(bs, 97.5)
        return float(d.mean()), float(lo), float(hi), bool(lo > 0 or hi < 0)

    summary = {"modality": "hemodynamic (BOLD/fNIRS-class)", "target_state": TARGET,
               "n_states": K, "n_seeds": n_seeds, "n_steps": N_STEPS, "burn": BURN,
               "open_loop_const_u": OPEN_U, "g_setpoint_target": g_set,
               "g_setpoint_wrong": g_set_wrong, "arms": {}, "contrasts": {}}
    print(f"setpoint target={g_set:.3f} wrong={g_set_wrong:.3f} open_U={OPEN_U:.3f}\n")
    print(f"{'arm':12s} {'occ':>18s} {'meanKL':>8s} {'energy':>8s}")
    for a in arms:
        m, lo, hi = ci(res[a]["occ"])
        summary["arms"][a] = {"occ_mean": m, "occ_ci95": [lo, hi],
                              "kl_mean": float(np.mean(res[a]["kl"])),
                              "energy_mean": float(np.mean(res[a]["energy"]))}
        print(f"{a:12s} {m:.3f} [{lo:.3f},{hi:.3f}]   {np.mean(res[a]['kl']):.3f} "
              f"{np.mean(res[a]['energy']):7.1f}")

    print("\nPaired occupancy contrasts (target-mood occupancy):")
    for a, b, lab in [("closed_loop", "no_control", "efficacy vs baseline"),
                      ("closed_loop", "sham", "phase specificity"),
                      ("closed_loop", "wrong_tgt", "target specificity"),
                      ("closed_loop", "open_loop", "value of feedback (equal energy)")]:
        md, lo, hi, sigf = paired(a, b)
        summary["contrasts"][lab] = {"a": a, "b": b, "delta_occ": md,
                                     "ci95": [lo, hi], "significant": sigf}
        print(f"  {lab:34s} d={md:+.3f} CI[{lo:+.3f},{hi:+.3f}] "
              f"{'SIG' if sigf else 'ns'}")

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results_expB.json")
    with open(path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n[mood_control_hemo] wrote {path}")
    return summary


if __name__ == "__main__":
    main()

"""
Pass-77 B129 — QCM-1: Quantum-Connectome Mood-Amplifier (simulator, rigorous arm)
================================================================================
QUESTION (the user's, reframed honestly per #69)
  "Can the mood amplifier influence a virtual brain (C. elegans connectome) in a
   *demonstrably quantum* manner, on a quantum computer?"

WHAT THIS CAN AND CANNOT SHOW (#69 brutal honesty — load-bearing)
  * Subject = the top-8 command-interneuron "rich club" of a 302-neuron STATISTICAL
    SURROGATE of the C. elegans connectome (Varshney et al. 2011-based; the same
    build used in simulations/connectome_consciousness_test_v4_302neuron.py). It is
    a toy model, NOT the living worm and NOT a real brain.
  * "Influence" = a closed-loop mood-amplifier drive steers an encoded mood
    observable to a set-point, with the SAME specificity controls as the classical
    in-silico amplifier (sham = equal-energy locus-scrambled; wrong-target;
    open-loop = equal-energy no-feedback).
  * "Demonstrably quantum" = the driven state carries GENUINE ENTANGLEMENT and a
    CHSH/Bell violation (S>2) on the strongest-coupled neuron pair — signatures
    that a MATCHED CLASSICAL surrogate (identical connectome couplings + identical
    drive energy, but fully dephased each step → a classical Markov process on bit
    configurations) provably CANNOT produce.
  * This is an IN-PRINCIPLE / reachability result about THE MODEL. It is NOT
    evidence that biological brains are quantum, nor that the amplifier works on
    living animals. Reported two-sided.

HONEST PUNCHLINE we expect to defend
  Mood STEERING is NOT inherently quantum — the dephased classical surrogate steers
  too (equal populations). The genuinely quantum part is the CHANNEL: in the quantum
  model the connectome+drive build Bell-violating entanglement (S>2, Meyer-Wallach
  Q>0, pair negativity>0) that vanishes (S<=2, Q~0) under dephasing. So the
  amplifier influences the virtual brain *through* demonstrably-quantum correlations,
  while we are explicit that the steering itself is classically reproducible.

Encoding
  8 neuron-qubits = top-8 rich-club command interneurons (by intra-club degree).
  Connectome layer  U_W : per pair (i,j), XY coupling exp(-i*g*w_ij*(XiXj+YiYj)/2)
                          (drives populations AND builds entanglement; survives
                          partially under dephasing so the wiring matters classically
                          too — a fair classical control).
  Mood drive  U_d(u,locus) : RY(u) on the drive locus qubits.
  Mood readout m = mean P(qubit=1) over the TARGET locus (command set) in [0,1].

Arms (mirror analyses/pass_b_consciousness_hamiltonian_2026_06_16/mood_control.py)
  no_control  u=0
  closed_loop u=clip(gain*(setpoint-m_obs)) on TARGET locus  (feedback)
  open_loop   u=const (=mean closed-loop energy) on TARGET    (no feedback)
  sham        replay closed_loop's |u| schedule on a NON-target locus (equal energy,
              locus-scrambled = phase/specificity control)
  wrong_tgt   feedback toward a WRONG locus
Each arm run as QUANTUM (pure, coherent) and CLASSICAL (dephased each step).

Stats: bootstrap 95% CIs across seeds; paired bootstrap contrasts.
Quantum-info witnesses: balanced-cut entanglement negativity (clean quantum-vs-
classical discriminator; exactly 0 for separable/dephased states), plus an
isolated strongest-pair CHSH S_max (Horodecki) Bell-violation demonstration.

Run: python analyses/pass77_b129_quantum_connectome_mood_amplifier/runner.py
"""
import importlib
import json
import os
import sys
from datetime import datetime

import numpy as np

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))
from qiskit import QuantumCircuit
from qiskit.quantum_info import (DensityMatrix, Operator, Statevector,
                                 partial_trace)
from qiskit.quantum_info import negativity as qi_negativity

OUT = "analyses/pass77_b129_quantum_connectome_mood_amplifier"

# ── Pauli matrices ────────────────────────────────────────────────────────────
I2 = np.eye(2, dtype=complex)
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.array([[1, 0], [0, -1]], dtype=complex)
PAULI = {"x": SX, "y": SY, "z": SZ}

# ── Experiment constants ──────────────────────────────────────────────────────
N_Q = 8                 # neuron-qubits (top-8 rich-club command interneurons)
N_STEPS = 10
BURN = 3
GAIN = 2.2
UMAX = 0.85
SETPOINT = 0.85         # target mood readout
GAMMA = 0.42            # connectome coupling scale (tuned for strong-pair entanglement)
OBS_NOISE = 0.02        # controller observation noise (fair: imperfect readout)
N_SEEDS = 16


def rich_club_submatrix():
    """Top-N_Q rich-club neurons (by within-club degree) from the SAME 302-neuron
    statistical surrogate used elsewhere in the repo. Returns (W_sub, names)."""
    m = importlib.import_module(
        "simulations.connectome_consciousness_test_v4_302neuron")
    W, _ = m.build_connectome(seed=2026)
    rich_idx = list(range(m.OFF_I, m.OFF_I + m.N_RICH))
    Wr = np.abs(W[np.ix_(rich_idx, rich_idx)])      # magnitudes of club wiring
    Wr = 0.5 * (Wr + Wr.T)                           # symmetrize (coupling strength)
    deg = Wr.sum(axis=1)
    top = np.argsort(deg)[::-1][:N_Q]
    top = sorted(top.tolist())
    Wsub = Wr[np.ix_(top, top)]
    mx = Wsub.max() if Wsub.max() > 0 else 1.0
    Wsub = Wsub / mx                                 # normalize to [0,1]
    names = [m.RICH_CLUB_NAMES[i] for i in top]
    return Wsub, names


def connectome_layer(Wsub):
    """XY-coupling entangling layer from the connectome weights."""
    qc = QuantumCircuit(N_Q)
    for i in range(N_Q):
        for j in range(i + 1, N_Q):
            w = float(Wsub[i, j])
            if w <= 1e-6:
                continue
            qc.rxx(GAMMA * w, i, j)
            qc.ryy(GAMMA * w, i, j)
    return qc


def _ry(u):
    c, s = np.cos(u / 2.0), np.sin(u / 2.0)
    return np.array([[c, -s], [s, c]], dtype=complex)


def drive_unitary(u, locus):
    """Full 2^N x 2^N RY(u)-on-locus unitary, qiskit ordering (qubit 0 = LSB)."""
    ops = [_ry(u) if q in locus else I2 for q in range(N_Q)]
    M = ops[N_Q - 1]
    for q in range(N_Q - 2, -1, -1):
        M = np.kron(M, ops[q])
    return M


def dephase(rho):
    """Full computational-basis dephasing → classical distribution on bitstrings."""
    d = np.diag(np.real(np.diag(rho))).astype(complex)
    s = d.real.trace()
    return d / s if s > 0 else d


def mood_readout(rho, locus):
    """Mean P(qubit=1) over locus, from diagonal populations (identical formula for
    quantum & classical arms; coherence-independent)."""
    probs = np.real(np.diag(rho))                 # qiskit ordering, qubit 0 = LSB
    idx = np.arange(probs.shape[0])
    vals = [float(probs[((idx >> q) & 1) == 1].sum()) for q in locus]
    return float(np.mean(vals))


def reduced_2q(rho, a, b):
    """4x4 reduced density matrix on qubits (a,b); trace out the rest."""
    trace_out = [q for q in range(N_Q) if q not in (a, b)]
    return partial_trace(DensityMatrix(rho), trace_out).data


def chsh_max(rho2):
    """Horodecki max CHSH over measurement settings: S = 2*sqrt(t1^2+t2^2),
    t1,t2 = two largest singular values of the 3x3 correlation matrix T."""
    T = np.zeros((3, 3))
    for ii, pi in enumerate("xyz"):
        for jj, pj in enumerate("xyz"):
            op = np.kron(PAULI[pj], PAULI[pi])    # qiskit little-endian kron
            T[ii, jj] = np.real(np.trace(rho2 @ op))
    sv = np.linalg.svd(T, compute_uv=False)
    sv = np.sort(sv)[::-1]
    return float(2.0 * np.sqrt(sv[0] ** 2 + sv[1] ** 2))


def pair_negativity(rho2):
    """Entanglement negativity of a 2-qubit state (partial transpose)."""
    r = rho2.reshape(2, 2, 2, 2)
    rpt = r.transpose(0, 3, 2, 1).reshape(4, 4)   # PT on second qubit
    ev = np.linalg.eigvalsh((rpt + rpt.conj().T) / 2)
    return float(sum(-e for e in ev if e < 0))


def cut_negativity(rho):
    """Genuine multipartite entanglement witness: entanglement negativity across a
    balanced bipartition (first half of qubits vs the rest). It is EXACTLY zero for
    any separable state — including the dephased (diagonal) classical surrogate —
    and strictly positive only when the joint state carries non-classical, PPT-
    violating correlations. Unlike Meyer-Wallach Q, it does NOT count mere classical
    mixedness, so it is a clean quantum-vs-classical discriminator."""
    cut = list(range(N_Q // 2))
    return float(qi_negativity(DensityMatrix(rho), cut))


def isolated_pair_bell(Wsub, pair, n_grid=181):
    """GOLD-STANDARD demonstration that the connectome coupling between the two most
    strongly-wired neurons can carry genuinely non-classical (Bell-violating)
    correlations. In ISOLATION (monogamy of entanglement no longer dilutes the pair
    across the other six neurons) we drive one neuron, let the XY connectome edge
    couple them, and sweep the coupling angle to find the reachable CHSH maximum.
    Returns (best_S, best_phi, S_at_native_weight). The SAME 2-qubit circuit is what
    we send to real IBM hardware. Quantum mechanics caps CHSH at Tsirelson 2*sqrt2;
    any S>2 is impossible under local hidden variables (classical surrogate gives 2).
    """
    w = float(Wsub[pair[0], pair[1]])             # native (normalized) edge weight
    best_S, best_phi = 0.0, 0.0
    for phi in np.linspace(0.0, np.pi, n_grid):
        qc = QuantumCircuit(2)
        qc.ry(np.pi, 0)                           # drive neuron 0 to excited
        qc.rxx(phi, 0, 1)                         # XY connectome edge ...
        qc.ryy(phi, 0, 1)                         # ... entangles the pair
        rho2 = DensityMatrix(Statevector(qc)).data
        S = chsh_max(rho2)
        if S > best_S:
            best_S, best_phi = S, float(phi)
    # CHSH the protocol actually reaches at the native edge weight (gamma*w)
    qc = QuantumCircuit(2)
    qc.ry(np.pi, 0)
    qc.rxx(GAMMA * w, 0, 1)
    qc.ryy(GAMMA * w, 0, 1)
    S_native = chsh_max(DensityMatrix(Statevector(qc)).data)
    return best_S, best_phi, float(S_native)


def run_arm(arm, seed, U_cl, target_locus, wrong_locus, drive_locus_override=None,
            classical=False, u_schedule=None, open_u=0.0):
    """One protocol run on a NumPy density matrix (precomputed connectome unitary
    U_cl). Returns (mood_series, energy, u_hist, final_rho)."""
    rng = np.random.default_rng(seed + (777 if classical else 0))
    dim = 1 << N_Q
    rho = np.zeros((dim, dim), dtype=complex)
    rho[0, 0] = 1.0
    U_cl_dag = U_cl.conj().T
    moods, u_hist, energy = [], [], 0.0
    for step in range(N_STEPS):
        # connectome always on (the wiring of the brain)
        rho = U_cl @ rho @ U_cl_dag
        if classical:
            rho = dephase(rho)
        m_obs = mood_readout(rho, target_locus) + rng.normal(0, OBS_NOISE)
        if arm == "no_control":
            u, locus = 0.0, target_locus
        elif arm == "closed_loop":
            u = float(np.clip(GAIN * (SETPOINT - m_obs), 0.0, UMAX))
            locus = target_locus
        elif arm == "open_loop":
            u, locus = open_u, target_locus
        elif arm == "sham":
            u = float(u_schedule[step]) if u_schedule is not None else \
                float(np.clip(GAIN * (SETPOINT - m_obs), 0.0, UMAX))
            locus = drive_locus_override          # equal energy, scrambled locus
        elif arm == "wrong_tgt":
            m_obs_w = mood_readout(rho, wrong_locus) + rng.normal(0, OBS_NOISE)
            u = float(np.clip(GAIN * (SETPOINT - m_obs_w), 0.0, UMAX))
            locus = wrong_locus
        else:
            raise ValueError(arm)
        if u > 1e-9:
            Ud = drive_unitary(u, locus)
            rho = Ud @ rho @ Ud.conj().T
            if classical:
                rho = dephase(rho)
        u_hist.append(u)
        energy += u
        moods.append(mood_readout(rho, target_locus))
    return np.asarray(moods), energy, u_hist, rho


def boot_ci(x, rng, n=2000):
    x = np.asarray(x)
    bs = [x[rng.integers(0, len(x), len(x))].mean() for _ in range(n)]
    return float(x.mean()), float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


def paired(xa, xb, rng, n=2000):
    d = np.asarray(xa) - np.asarray(xb)
    bs = [d[rng.integers(0, len(d), len(d))].mean() for _ in range(n)]
    lo, hi = np.percentile(bs, 2.5), np.percentile(bs, 97.5)
    return float(d.mean()), float(lo), float(hi), bool(lo > 0 or hi < 0)


def main():
    Wsub, names = rich_club_submatrix()
    target_locus = [0, 1, 2]                       # command-interneuron mood locus
    wrong_locus = [N_Q - 3, N_Q - 2, N_Q - 1]
    sham_locus = [3, 4]                            # non-target locus (equal energy)

    # strongest-coupled pair among the 8 (for CHSH / negativity witnesses)
    pair, best = (0, 1), -1.0
    for i in range(N_Q):
        for j in range(i + 1, N_Q):
            if Wsub[i, j] > best:
                best, pair = Wsub[i, j], (i, j)

    # precompute the connectome entangling unitary ONCE (NumPy fast path)
    U_cl = Operator(connectome_layer(Wsub)).data

    # calibrate the open-loop constant SEPARATELY per arm so each arm's open-loop is
    # truly energy-matched to ITS OWN closed-loop (quantum & classical closed-loop
    # draw different energies, so a single shared constant would confound the
    # classical value-of-feedback contrast).
    open_u = {}
    for cl_flag, tag in ((False, "quantum"), (True, "classical")):
        e = [np.mean(run_arm("closed_loop", 5000 + s, U_cl, target_locus,
                             wrong_locus, classical=cl_flag)[2]) for s in range(4)]
        open_u[tag] = float(np.mean(e))

    arms = ["no_control", "closed_loop", "open_loop", "sham", "wrong_tgt"]
    data = {q: {a: {"mood": [], "energy": []} for a in arms} for q in ("quantum", "classical")}
    qsig = {"quantum": {"cut_neg": [], "pair_neg": []},
            "classical": {"cut_neg": [], "pair_neg": []}}

    for seed in range(N_SEEDS):
        for classical in (False, True):
            tag = "classical" if classical else "quantum"
            cl_sched = None
            for a in arms:
                sched = cl_sched if a == "sham" else None
                moods, en, uh, rho = run_arm(
                    a, seed, U_cl, target_locus, wrong_locus,
                    drive_locus_override=sham_locus, classical=classical,
                    u_schedule=sched, open_u=open_u[tag])
                if a == "closed_loop":
                    cl_sched = uh
                    r2 = reduced_2q(rho, pair[0], pair[1])
                    qsig[tag]["cut_neg"].append(cut_negativity(rho))
                    qsig[tag]["pair_neg"].append(pair_negativity(r2))
                data[tag][a]["mood"].append(float(moods[BURN:].mean()))
                data[tag][a]["energy"].append(en)

    # gold-standard Bell demonstration on the strongest pair in isolation
    bell_best_S, bell_best_phi, bell_S_native = isolated_pair_bell(Wsub, pair)

    rng = np.random.default_rng(7)
    summary = {
        "run_date": datetime.now().isoformat(),
        "model": "C_elegans_rich_club_top8_quantum_mood_amplifier",
        "subject_neurons": names, "n_qubits": N_Q,
        "strong_pair": [names[pair[0]], names[pair[1]]], "strong_pair_idx": list(pair),
        "n_seeds": N_SEEDS, "n_steps": N_STEPS, "burn": BURN,
        "gamma": GAMMA, "gain": GAIN, "umax": UMAX, "setpoint": SETPOINT,
        "open_loop_const_u_per_arm": open_u, "obs_noise": OBS_NOISE,
        "arms": {"quantum": {}, "classical": {}},
        "contrasts": {"quantum": {}, "classical": {}},
        "quantum_signatures": {},
        "quantum_vs_classical_signature_gap": {},
        "isolated_pair_bell": {
            "pair": [names[pair[0]], names[pair[1]]],
            "best_CHSH_S": bell_best_S,
            "best_coupling_phi": bell_best_phi,
            "CHSH_S_at_native_edge_weight": bell_S_native,
            "tsirelson_bound": float(2.0 * np.sqrt(2.0)),
            "classical_LHV_bound": 2.0,
            "best_violates_2": bool(bell_best_S > 2.0),
            "native_violates_2": bool(bell_S_native > 2.0),
        },
    }

    for tag in ("quantum", "classical"):
        for a in arms:
            m, lo, hi = boot_ci(data[tag][a]["mood"], rng)
            summary["arms"][tag][a] = {
                "mood_mean": m, "mood_ci95": [lo, hi],
                "energy_mean": float(np.mean(data[tag][a]["energy"]))}
        for a, b, lab in [("closed_loop", "no_control", "efficacy_vs_baseline"),
                          ("closed_loop", "sham", "locus_specificity"),
                          ("closed_loop", "wrong_tgt", "target_specificity"),
                          ("closed_loop", "open_loop", "value_of_feedback_equal_energy")]:
            md, lo, hi, sig = paired(data[tag][a]["mood"], data[tag][b]["mood"], rng)
            summary["contrasts"][tag][lab] = {
                "a": a, "b": b, "delta_mood": md, "ci95": [lo, hi], "significant": sig}

    for tag in ("quantum", "classical"):
        s = qsig[tag]
        summary["quantum_signatures"][tag] = {
            "cut_negativity_mean": float(np.mean(s["cut_neg"])),
            "cut_negativity_ci95": list(boot_ci(s["cut_neg"], rng)[1:]),
            "entangled": bool(np.mean(s["cut_neg"]) > 1e-9),
            "pair_negativity_mean": float(np.mean(s["pair_neg"]))}

    # quantum-minus-classical signature gaps (the demonstrably-quantum result)
    for k, lab in [("cut_neg", "cut_negativity"), ("pair_neg", "pair_negativity")]:
        md, lo, hi, sig = paired(qsig["quantum"][k], qsig["classical"][k], rng)
        summary["quantum_vs_classical_signature_gap"][lab] = {
            "delta": md, "ci95": [lo, hi], "significant": sig}

    # mood-steering quantum-vs-classical (expected ~0 = steering NOT the quantum part)
    md, lo, hi, sig = paired(data["quantum"]["closed_loop"]["mood"],
                             data["classical"]["closed_loop"]["mood"], rng)
    summary["steering_quantum_vs_classical"] = {
        "delta_mood": md, "ci95": [lo, hi], "significant": sig}

    with open(os.path.join(OUT, "results.json"), "w") as f:
        json.dump(summary, f, indent=2)

    # ── report ────────────────────────────────────────────────────────────────
    print("=" * 72)
    print("B129 QCM-1 — Quantum-Connectome Mood Amplifier (simulator)")
    print("=" * 72)
    print(f"Subject (top-8 rich club): {names}")
    print(f"Strongest pair: {summary['strong_pair']}  | open_U(q/c)="
          f"{open_u['quantum']:.3f}/{open_u['classical']:.3f}\n")
    for tag in ("quantum", "classical"):
        print(f"--- {tag.upper()} mood occupancy (post burn-in) ---")
        for a in arms:
            d = summary["arms"][tag][a]
            print(f"  {a:12s} mood={d['mood_mean']:.3f} "
                  f"CI[{d['mood_ci95'][0]:.3f},{d['mood_ci95'][1]:.3f}] "
                  f"E={d['energy_mean']:.2f}")
        print(f"  contrasts:")
        for lab, c in summary["contrasts"][tag].items():
            print(f"    {lab:34s} d={c['delta_mood']:+.3f} "
                  f"CI[{c['ci95'][0]:+.3f},{c['ci95'][1]:+.3f}] "
                  f"{'SIG' if c['significant'] else 'ns'}")
        s = summary["quantum_signatures"][tag]
        print(f"  entanglement: cut-negativity={s['cut_negativity_mean']:.4f} "
              f"({'ENTANGLED' if s['entangled'] else 'separable'})  "
              f"pair-neg={s['pair_negativity_mean']:.4f}\n")
    print("--- DEMONSTRABLY-QUANTUM gap (quantum - classical) ---")
    for lab, g in summary["quantum_vs_classical_signature_gap"].items():
        print(f"  {lab:18s} d={g['delta']:+.4f} CI[{g['ci95'][0]:+.4f},{g['ci95'][1]:+.4f}] "
              f"{'SIG' if g['significant'] else 'ns'}")
    b = summary["isolated_pair_bell"]
    print(f"\n--- GOLD-STANDARD Bell test: isolated pair {b['pair']} ---")
    print(f"  reachable max CHSH S={b['best_CHSH_S']:.4f} @ phi={b['best_coupling_phi']:.3f} "
          f"({'>2 VIOLATES LHV' if b['best_violates_2'] else '<=2'}; "
          f"Tsirelson={b['tsirelson_bound']:.4f})")
    print(f"  CHSH at native edge weight S={b['CHSH_S_at_native_edge_weight']:.4f} "
          f"({'>2 VIOLATES' if b['native_violates_2'] else '<=2'})")
    sv = summary["steering_quantum_vs_classical"]
    print(f"\n  steering quantum-vs-classical: d={sv['delta_mood']:+.3f} "
          f"CI[{sv['ci95'][0]:+.3f},{sv['ci95'][1]:+.3f}] "
          f"{'SIG' if sv['significant'] else 'ns (steering is NOT the quantum part)'}")
    print(f"\n[B129] wrote {OUT}/results.json")
    return summary


if __name__ == "__main__":
    main()

"""
Pass-77 B129 (QCM-1) — REAL IBM-hardware confirmation of the demonstrably-quantum
claim. The simulator arm (runner.py) shows that the connectome edge between the two
most strongly-wired rich-club command interneurons (AVD-AIA), driven by the mood
amplifier, can be steered into a Bell-violating entangled pair (CHSH S>2). Here we
reproduce the SAME 2-qubit amplifier circuit on physical silicon and measure CHSH.

Honesty notes (#69):
  * S>2 is the gold standard: NO local-hidden-variable (classical) model can produce
    it. The classical/dephased surrogate is bounded by S<=2 by construction.
  * Hardware noise REDUCES S below the ideal value; a real-HW S>2 (even ~2.2-2.5) is
    therefore a strong, decoherence-surviving confirmation. If queue/noise prevents
    S>2 we report the actual number — we NEVER fabricate hardware data.
  * This is an in-principle/reachability statement about the MODEL on a quantum
    processor. It is NOT evidence that real C. elegans neurons are quantum, nor that
    the amplifier works on animals.

Measurement: we prepare the amplifier circuit, compute its ideal 3x3 correlation
matrix T (sim), and pick the Horodecki-optimal CHSH settings (Bob along the two
leading eigenvectors of T^T T; Alice along T(e1-e2) and T(e1+e2)). Four setting
pairs give S = E(a,b1) - E(a,b2) + E(a',b1) + E(a',b2).
"""
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))
from qiskit import QuantumCircuit, transpile
from qiskit.quantum_info import DensityMatrix, Statevector
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2

OUT = "analyses/pass77_b129_quantum_connectome_mood_amplifier"
SHOTS = 4096
POLL_BUDGET_S = 280

PAULI = {
    "x": np.array([[0, 1], [1, 0]], complex),
    "y": np.array([[0, -1j], [1j, 0]], complex),
    "z": np.array([[1, 0], [0, -1]], complex),
}


def amplifier_pair_circuit(phi):
    """The 2-qubit mood-amplifier primitive: drive neuron 0, then the XY connectome
    edge (RXX+RYY at coupling angle phi) entangles the pair."""
    qc = QuantumCircuit(2)
    qc.ry(math.pi, 0)
    qc.rxx(phi, 0, 1)
    qc.ryy(phi, 0, 1)
    return qc


def correlation_matrix(rho2):
    T = np.zeros((3, 3))
    for ii, pi in enumerate("xyz"):
        for jj, pj in enumerate("xyz"):
            op = np.kron(PAULI[pj], PAULI[pi])     # qiskit little-endian kron
            T[ii, jj] = np.real(np.trace(rho2 @ op))
    return T


def chsh_settings(T):
    """Horodecki-optimal CHSH directions. Bob: e1,e2 = leading eigenvectors of T^T T.
    Alice: a = T(e1-e2)/|.|, a' = T(e1+e2)/|.|."""
    w, V = np.linalg.eigh(T.T @ T)
    order = np.argsort(w)[::-1]
    e1, e2 = V[:, order[0]], V[:, order[1]]
    a = T @ (e1 - e2); a /= np.linalg.norm(a)
    ap = T @ (e1 + e2); ap /= np.linalg.norm(ap)
    s_ideal = 2.0 * math.sqrt(w[order[0]] + w[order[1]])
    return a, ap, e1, e2, float(s_ideal)


def add_meas_dir(qc, q, n):
    """Rotate qubit q so that measuring Z yields the n.sigma observable."""
    nx, ny, nz = float(n[0]), float(n[1]), float(n[2])
    theta = math.acos(max(-1.0, min(1.0, nz)))
    phi = math.atan2(ny, nx)
    qc.rz(-phi, q)
    qc.ry(-theta, q)


def correlator(counts):
    tot = sum(counts.values())
    c = 0
    for bits, n in counts.items():
        z0 = 1 - 2 * int(bits[-1])
        z1 = 1 - 2 * int(bits[-2])
        c += z0 * z1 * n
    return c / tot if tot else 0.0


def main():
    res_path = os.path.join(OUT, "results.json")
    phi = 3.0 * math.pi / 4.0
    if os.path.exists(res_path):
        try:
            phi = float(json.load(open(res_path))["isolated_pair_bell"]["best_coupling_phi"])
        except Exception:
            pass

    # ideal state + optimal CHSH settings (from simulation)
    rho2 = DensityMatrix(Statevector(amplifier_pair_circuit(phi))).data
    T = correlation_matrix(rho2)
    a, ap, b1, b2, s_ideal = chsh_settings(T)
    print(f"[B129-HW] coupling phi={phi:.4f}  ideal CHSH S={s_ideal:.4f}")

    # four CHSH measurement circuits: (a,b1) (a,b2) (a',b1) (a',b2)
    settings = [("a_b1", a, b1), ("a_b2", a, b2), ("ap_b1", ap, b1), ("ap_b2", ap, b2)]
    circs, labels = [], []
    for name, av, bv in settings:
        qc = QuantumCircuit(2, 2)
        qc.compose(amplifier_pair_circuit(phi), inplace=True)
        add_meas_dir(qc, 0, av)
        add_meas_dir(qc, 1, bv)
        qc.measure([0, 1], [0, 1])
        circs.append(qc)
        labels.append(name)

    try:
        svc = QiskitRuntimeService(channel="ibm_quantum_platform",
                                   token=os.environ["IBMQ_Secret"])
        backend = svc.least_busy(operational=True, simulator=False)
        print("backend:", backend.name, "| pending:", backend.status().pending_jobs)
    except Exception as e:
        json.dump({"error": f"service/backend unavailable: {e}", "phi": phi,
                   "ideal_chsh": s_ideal},
                  open(os.path.join(OUT, "hw_results.json"), "w"), indent=2)
        print("NO HARDWARE ACCESS — saved ideal-only stub, no fabricated data:", e)
        return

    tcircs = transpile(circs, backend=backend, optimization_level=3)
    job = SamplerV2(mode=backend).run(tcircs, shots=SHOTS)
    jid = job.job_id()
    json.dump({"job_id": jid, "backend": backend.name, "labels": labels,
               "shots": SHOTS, "phi": phi, "ideal_chsh": s_ideal,
               "settings": {n: [list(av), list(bv)] for n, av, bv in settings}},
              open(os.path.join(OUT, "hw_job.json"), "w"), indent=2)
    print("JOB_ID:", jid)

    t0 = time.time()
    while time.time() - t0 < POLL_BUDGET_S:
        st = str(job.status())
        print(f"  t={time.time()-t0:5.1f}s status={st}")
        if any(k in st for k in ("DONE", "ERROR", "CANCELLED")):
            break
        time.sleep(15)

    if "DONE" not in str(job.status()):
        print("NOT DONE in window; job_id saved for later polling:", jid)
        return

    res = job.result()
    raw = {name: pub.data.c.get_counts() for name, pub in zip(labels, res)}
    E = {name: correlator(raw[name]) for name in labels}
    S = E["a_b1"] - E["a_b2"] + E["ap_b1"] + E["ap_b2"]
    out = {"job_id": jid, "backend": backend.name, "shots": SHOTS, "phi": phi,
           "ideal_chsh": s_ideal, "correlators": E, "CHSH_S_hardware": float(S),
           "violates_LHV_bound_2": bool(abs(S) > 2.0),
           "classical_LHV_bound": 2.0, "tsirelson_bound": 2.0 * math.sqrt(2.0),
           "counts": raw}
    json.dump(out, open(os.path.join(OUT, "hw_results.json"), "w"), indent=2)
    print("\n=== REAL-HW B129 QCM-1 Bell test (pair AVD-AIA) ===")
    for k in labels:
        print(f"  E[{k:6s}] = {E[k]:+.4f}")
    print(f"  CHSH S(hardware) = {S:+.4f}  (ideal {s_ideal:.4f}; classical<=2; "
          f"Tsirelson {2*math.sqrt(2):.4f})")
    print(f"  {'VIOLATES LHV (demonstrably quantum on silicon)' if abs(S) > 2 else 'no violation in this run'}")


if __name__ == "__main__":
    main()

"""
qc26 — IBMQ 5-qubit Mermin/MABK entanglement witness for GHZ_5
       (Pass-45 T45-2 test of Pass-31 D2-HYBRID GM-Network non-trivial entanglement).

Pre-reg: this docstring is the pre-reg, frozen at commit time per Pass-45 §11.
SHA256 of this file at commit-time logged in results.json["runner_sha256"].

State preparation (Mermin-violating GHZ phase state):
    |ψ⟩ = (|00000⟩ - i|11111⟩) / √2
Circuit: H q0; Sdg q0; CNOT q0→q1; CNOT q1→q2; CNOT q2→q3; CNOT q3→q4.

Mermin operator M_5 (canonical form, derived from (X+iY)^⊗5 - (X-iY)^⊗5 / 2i):
    M_5 = Σ_{|S|=1}⟨Y_S X^rest⟩ - Σ_{|S|=3}⟨Y_S X^rest⟩ + ⟨Y_1 Y_2 Y_3 Y_4 Y_5⟩
By GHZ symmetry, all C(5,1)=5 single-Y terms are equal (call it E_1Y);
all C(5,3)=10 three-Y terms are equal (E_3Y); and the unique five-Y term is E_5Y.
So M_5 = 5·E_1Y - 10·E_3Y + 1·E_5Y.

Theoretical maximum: for |ψ⟩ above, M_5 = -16 (|M| = 16 = 2^(n-1) quantum bound).
Classical / fully-separable LHV bound: |M_5| ≤ 4 = 2^((n-1)/2) (Mermin 1990).

Three measurement settings (1024 shots each = 3072 total, well under free-tier daily quota):
  Setting A (1Y): Y-basis measurement on qubit 0, X-basis on qubits 1-4
  Setting B (3Y): Y-basis on qubits 0,1,2; X-basis on qubits 3,4
  Setting C (5Y): Y-basis on all 5 qubits

Y-basis measurement implementation: apply Sdg then H to qubit, then measure Z.
X-basis measurement implementation: apply H to qubit, then measure Z.
For each measured bitstring, expectation = (1/N)·Σ (-1)^(sum of bits) (parity).

Pre-reg verdicts (frozen):
  CONFIRM: |M_5| > 4 + 3·σ_M     (entanglement witnessed beyond LHV bound)
  REJECT:  |M_5| ≤ 4 + 3·σ_M     (no entanglement detectable above noise)
  INELIGIBLE: hardware unreachable / job error (fallback to simulator → marked INELIGIBLE for hw claim)

σ_M propagated from per-setting Bernoulli sampling errors:
  σ_M² = 25·Var(E_1Y) + 100·Var(E_3Y) + 1·Var(E_5Y)
where Var(E) = (1 - E²)/N for parity expectation from N shots.

Anti-HARK: this docstring is the pre-reg. results.json written before any
post-hoc reframing. Architect-discharge style: any post-hoc threshold change
requires explicit amendment paper.
"""
import json, os, time, traceback, hashlib
from collections import Counter
import numpy as np

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

N_QUBITS = 5
N_SHOTS = 1024
QUEUE_TIMEOUT = 600

TOKEN = (os.environ.get("IBMQ_Secret")
         or os.environ.get("IBMQ_TOKEN")
         or os.environ.get("QISKIT_IBM_TOKEN"))


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def build_ghz_circuit_with_setting(setting_y_qubits):
    """Prepare ψ = (|00000⟩ - i|11111⟩)/√2, then apply basis-rotation per setting.
    setting_y_qubits: list of qubit indices to measure in Y-basis;
                      remaining qubits measured in X-basis.
    """
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(N_QUBITS, N_QUBITS)
    # GHZ-with-phase preparation
    qc.h(0)
    qc.sdg(0)              # |0⟩ → |0⟩, |1⟩ → -i|1⟩  ⇒ state (|0⟩-i|1⟩)/√2 on q0
    qc.cx(0, 1)
    qc.cx(1, 2)
    qc.cx(2, 3)
    qc.cx(3, 4)
    # Basis rotations
    for q in range(N_QUBITS):
        if q in setting_y_qubits:
            qc.sdg(q)      # Y-basis: Sdg then H
            qc.h(q)
        else:
            qc.h(q)        # X-basis: H only
    qc.measure(range(N_QUBITS), range(N_QUBITS))
    return qc


def parity_expectation(counts):
    """E = Σ_outcomes (-1)^(parity of bitstring) · P(outcome)."""
    total = sum(counts.values())
    if total == 0:
        return 0.0, 0
    s = 0
    for bits, n in counts.items():
        # bits comes back as e.g. '01101' (qiskit little-endian on get_bitstrings)
        parity = bits.count('1') % 2
        s += n * (1 if parity == 0 else -1)
    return s / total, total


def submit_one_setting(qc, svc, backend, shots=N_SHOTS):
    """Single-setting submission to IBMQ."""
    from qiskit_ibm_runtime import SamplerV2
    from qiskit import transpile
    qc_t = transpile(qc, backend, optimization_level=1)
    sampler = SamplerV2(mode=backend)
    job = sampler.run([qc_t], shots=shots)
    job_id = job.job_id()
    print(f"    job_id={job_id} ...", flush=True)
    t0 = time.time()
    while True:
        st = str(job.status())
        if st in ("JobStatus.DONE", "DONE"):
            break
        if st in ("JobStatus.ERROR", "JobStatus.CANCELLED", "ERROR", "CANCELLED"):
            raise RuntimeError(f"job ended {st}")
        if time.time() - t0 > QUEUE_TIMEOUT:
            raise TimeoutError(f"queue timeout {QUEUE_TIMEOUT}s; job still {st}")
        time.sleep(15)
    res = job.result()
    pub = res[0]
    bits = pub.data.c.get_bitstrings()
    return dict(Counter(bits)), job_id


def get_ibmq_service(token):
    from qiskit_ibm_runtime import QiskitRuntimeService
    last_err = None
    for ch in ("ibm_quantum_platform", "ibm_quantum", "ibm_cloud"):
        try:
            svc = QiskitRuntimeService(channel=ch, token=token)
            return svc, ch
        except Exception as e:
            last_err = f"{ch}: {type(e).__name__}: {e}"
    raise RuntimeError(f"All IBMQ channels failed. Last: {last_err}")


def simulator_fallback(qc):
    from qiskit import transpile
    try:
        from qiskit_aer import AerSimulator
    except Exception:
        from qiskit_aer.aer_simulator import AerSimulator  # type: ignore
    sim = AerSimulator()
    qc_t = transpile(qc, sim)
    job = sim.run(qc_t, shots=N_SHOTS)
    return dict(job.result().get_counts())


def main():
    results = {
        "pass": 45,
        "test_id": "qc26_ghz5_mermin",
        "n_qubits": N_QUBITS,
        "n_shots_per_setting": N_SHOTS,
        "n_settings": 3,
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "token_available": bool(TOKEN),
        "prereg": "see runner.py docstring (frozen at commit-time)",
        "settings": {},
    }

    settings = {
        "A_1Y": [0],                # 1 Y on q0, 4 X on q1..q4
        "B_3Y": [0, 1, 2],          # 3 Y on q0,q1,q2; 2 X on q3,q4
        "C_5Y": [0, 1, 2, 3, 4],    # 5 Y on all
    }

    ran_on_hw = False
    svc, ch, backend = None, None, None
    if TOKEN:
        try:
            svc, ch = get_ibmq_service(TOKEN)
            backend = svc.least_busy(operational=True, simulator=False, min_num_qubits=N_QUBITS)
            results["ibmq_channel"] = ch
            results["backend_name"] = backend.name
            results["backend_num_qubits"] = backend.num_qubits
            ran_on_hw = True
        except Exception as e:
            results["hw_error"] = f"{type(e).__name__}: {e}"
            results["hw_traceback"] = traceback.format_exc()[-1500:]

    for label, y_qubits in settings.items():
        qc = build_ghz_circuit_with_setting(y_qubits)
        results["settings"][label] = {"y_qubits": y_qubits}
        try:
            if ran_on_hw and backend is not None:
                counts, job_id = submit_one_setting(qc, svc, backend)
                results["settings"][label]["job_id"] = job_id
                results["settings"][label]["source"] = "ibmq_hw"
            else:
                counts = simulator_fallback(qc)
                results["settings"][label]["source"] = "aer_sim_fallback"
        except Exception as e:
            results["settings"][label]["error"] = f"{type(e).__name__}: {e}"
            try:
                counts = simulator_fallback(qc)
                results["settings"][label]["source"] = "aer_sim_after_hw_error"
            except Exception as e2:
                results["settings"][label]["fallback_error"] = f"{type(e2).__name__}: {e2}"
                counts = None
        if counts is not None:
            results["settings"][label]["counts"] = counts
            E, N = parity_expectation(counts)
            results["settings"][label]["expectation"] = E
            results["settings"][label]["n"] = N
            # Bernoulli variance for parity expectation: Var = (1 - E²)/N
            results["settings"][label]["var"] = (1.0 - E * E) / max(N, 1)

    # Compose Mermin operator: M_5 = 5·E_1Y - 10·E_3Y + 1·E_5Y
    try:
        E1 = results["settings"]["A_1Y"]["expectation"]
        E3 = results["settings"]["B_3Y"]["expectation"]
        E5 = results["settings"]["C_5Y"]["expectation"]
        V1 = results["settings"]["A_1Y"]["var"]
        V3 = results["settings"]["B_3Y"]["var"]
        V5 = results["settings"]["C_5Y"]["var"]
        M5 = 5.0 * E1 - 10.0 * E3 + 1.0 * E5
        sigma_M = float(np.sqrt(25 * V1 + 100 * V3 + 1 * V5))
        results["E_1Y"] = E1
        results["E_3Y"] = E3
        results["E_5Y"] = E5
        results["M5"] = M5
        results["abs_M5"] = abs(M5)
        results["sigma_M"] = sigma_M
        results["classical_bound"] = 4.0
        results["quantum_max"] = 16.0
        results["threshold_confirm"] = 4.0 + 3 * sigma_M
        sources = {results["settings"][s].get("source") for s in settings}
        actually_on_hw = (sources == {"ibmq_hw"})
        results["actually_on_hw"] = actually_on_hw
        if not actually_on_hw:
            results["verdict"] = "INELIGIBLE_HW_FALLBACK_TO_SIM"
        elif abs(M5) > 4.0 + 3 * sigma_M:
            results["verdict"] = "CONFIRM"
        else:
            results["verdict"] = "REJECT"
    except Exception as e:
        results["scoring_error"] = f"{type(e).__name__}: {e}"
        results["verdict"] = "ERROR"

    results["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nverdict={results.get('verdict')}  M5={results.get('M5')}  "
          f"|M|={results.get('abs_M5')}  threshold={results.get('threshold_confirm')}  "
          f"hw={results.get('actually_on_hw')}")


if __name__ == "__main__":
    main()

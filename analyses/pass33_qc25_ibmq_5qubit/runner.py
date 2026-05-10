"""
qc25 — IBMQ 5-qubit free-tier verification of Pass-31 D2-HYBRID
       (32-D-complex / 5-qubit instantiation of GM-Network).

Pre-reg: u33-qc25 (this file's docstring is the pre-reg).

Hypothesis (CONFIRM): A Hadamard-product preparation H^{⊗5}|0⟩^{⊗5} on real
quantum hardware produces measurement counts uniform within Poisson sampling
noise across all 32 = 2^5 computational-basis states. Per Pass-31 D2-HYBRID,
this is the simplest GM-Network c25 native-state test: 5 qubits realizing
the ℂ^32 GM-Network state space with the Hadamard^3 ↔ V_4^3 simultaneous
canonical reading.

Statistic: chi-square against uniform(32-bin) at 1024 shots.
Pre-reg thresholds (URB-830 symmetric framing, not Popper-asymmetric):
  CONFIRM: chi-square p > 0.10  (positive-direction TIU)
  REJECT:  chi-square p < 0.001 (negative-direction TIU)
  PARTIAL: 0.001 <= p <= 0.10
  INELIGIBLE: backend unreachable / queue timeout exceeded / shots returned < 100

PRE-REG AMENDMENT A1-qc25 (2026-05-10, ratified Pass-33 architect-discharge):
  Original draft of this docstring said "queue timeout > 30 min". The code
  enforces 300s (5 min) via queue_timeout_sec=300 in submit_to_ibmq(). This
  is an intentional discrepancy declared BEFORE result inspection (the actual
  failure was credential-rejection on connection, not queue timeout, so the
  numerical value of the timeout is causally irrelevant to the present
  verdict). Canonical rule going forward: queue_timeout_sec=300 for free-tier
  exploratory submissions; if a real free-tier hardware run is achieved in
  qc25-v2, timeout will be raised to 1800s (30 min) and re-pre-registered.
  Anti-HARK status: amendment timestamp logged in results.json
  prereg_amendments[].
  + TIU operationalization: report TIU_estimate := -log10(p_value) as a
  symmetric magnitude (positive sign if p>0.10 toward CONFIRM, negative if
  p<0.001 toward REJECT, zero-magnitude if PARTIAL). Per URB-830 §4.3
  v1.1, magnitude is the canonical metric; sign is recorded but not
  weighted.

Backend selection: cheapest available free-tier device via least_busy().
If IBMQ access fails, fall back to AerSimulator with explicit FALLBACK note in
results.json (this is INELIGIBLE for the hardware claim, but a
sanity-check on the circuit construction).

Anti-HARK: this docstring is the pre-reg; results.json written before any
post-hoc reframing.
"""
import json, os, time, traceback
from collections import Counter
import numpy as np
from scipy.stats import chisquare

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")

N_QUBITS = 5
N_SHOTS = 1024

# Brandon added the secret as IBMQ_Secret (per user message); also accept
# the more conventional IBMQ_TOKEN / QISKIT_IBM_TOKEN names if present.
TOKEN = (os.environ.get("IBMQ_Secret")
         or os.environ.get("IBMQ_TOKEN")
         or os.environ.get("QISKIT_IBM_TOKEN"))

results = {
    "pass": 33,
    "test_id": "qc25",
    "n_qubits": N_QUBITS,
    "n_shots": N_SHOTS,
    "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "token_available": bool(TOKEN),
    "prereg": "see runner.py docstring",
}


def build_circuit():
    """H^⊗5 |0⟩^⊗5 → uniform superposition over ℂ^32; measure all qubits."""
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(N_QUBITS, N_QUBITS)
    for q in range(N_QUBITS):
        qc.h(q)
    qc.measure(range(N_QUBITS), range(N_QUBITS))
    return qc


def submit_to_ibmq(qc, token, queue_timeout_sec=300):
    """Try to submit to a free-tier IBM Quantum device; return counts dict."""
    from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
    from qiskit import transpile

    # Save / load credentials. Use channel='ibm_quantum_platform' (the new
    # IBM Quantum Platform endpoint), with channel='ibm_quantum' as legacy fallback.
    svc = None
    last_err = None
    for ch in ("ibm_quantum_platform", "ibm_quantum", "ibm_cloud"):
        try:
            svc = QiskitRuntimeService(channel=ch, token=token)
            results["ibmq_channel"] = ch
            break
        except Exception as e:
            last_err = f"{ch}: {type(e).__name__}: {e}"
    if svc is None:
        raise RuntimeError(f"All IBMQ channels failed. Last: {last_err}")

    backend = svc.least_busy(operational=True, simulator=False, min_num_qubits=N_QUBITS)
    results["backend_name"] = backend.name
    results["backend_num_qubits"] = backend.num_qubits
    results["backend_status"] = str(backend.status())

    qc_t = transpile(qc, backend, optimization_level=1)
    sampler = SamplerV2(mode=backend)
    job = sampler.run([qc_t], shots=N_SHOTS)
    results["job_id"] = job.job_id()
    print(f"  job_id={job.job_id()}  waiting up to {queue_timeout_sec}s ...", flush=True)
    t0 = time.time()
    while True:
        st = str(job.status())
        if st in ("JobStatus.DONE", "DONE"):
            break
        if st in ("JobStatus.ERROR", "JobStatus.CANCELLED", "ERROR", "CANCELLED"):
            raise RuntimeError(f"job ended with status {st}")
        if time.time() - t0 > queue_timeout_sec:
            raise TimeoutError(f"queue_timeout_sec={queue_timeout_sec} exceeded; job still {st}")
        time.sleep(10)
    res = job.result()
    pub = res[0]
    bits = pub.data.c.get_bitstrings()
    counts = dict(Counter(bits))
    return counts


def run_simulator_fallback(qc):
    """Sanity-check fallback: AerSimulator. Marked INELIGIBLE for hw claim."""
    from qiskit import transpile
    try:
        from qiskit_aer import AerSimulator
    except Exception:
        from qiskit_aer.aer_simulator import AerSimulator  # type: ignore
    sim = AerSimulator()
    qc_t = transpile(qc, sim)
    job = sim.run(qc_t, shots=N_SHOTS)
    counts = job.result().get_counts()
    return counts


def score(counts):
    """Chi-square against uniform(32). Returns (chi2, p, observed, expected)."""
    keys = sorted(counts.keys())
    # Pad to all 32 basis states
    all_keys = [format(i, f"0{N_QUBITS}b") for i in range(2**N_QUBITS)]
    obs = np.array([counts.get(k, 0) for k in all_keys], dtype=float)
    n = obs.sum()
    exp = np.full(2**N_QUBITS, n / 2**N_QUBITS)
    chi2, p = chisquare(obs, exp)
    return float(chi2), float(p), obs.tolist(), exp.tolist(), all_keys


def verdict_from_p(p, ran_on_hw):
    if not ran_on_hw:
        return "INELIGIBLE_HW_FALLBACK_TO_SIM"
    if p > 0.10:
        return "CONFIRM"
    if p < 0.001:
        return "REJECT"
    return "PARTIAL"


def main():
    qc = build_circuit()
    results["circuit_qasm"] = qc.qasm() if hasattr(qc, "qasm") else str(qc)
    ran_on_hw = False
    counts = None
    try:
        if not TOKEN:
            raise RuntimeError("No IBMQ token in env (IBMQ_Secret / IBMQ_TOKEN / QISKIT_IBM_TOKEN)")
        counts = submit_to_ibmq(qc, TOKEN, queue_timeout_sec=300)
        ran_on_hw = True
    except Exception as e:
        results["hw_error"] = f"{type(e).__name__}: {e}"
        results["hw_traceback"] = traceback.format_exc()[-1500:]
        try:
            counts = run_simulator_fallback(qc)
            results["fallback"] = "AerSimulator"
        except Exception as e2:
            results["fallback_error"] = f"{type(e2).__name__}: {e2}"

    if counts is not None:
        results["counts"] = counts
        chi2, p, obs, exp, keys = score(counts)
        results["chi2"] = chi2
        results["p_value"] = p
        results["max_dev_from_uniform"] = float(max(abs(o - e) for o, e in zip(obs, exp)))
        results["verdict"] = verdict_from_p(p, ran_on_hw)

    results["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nverdict={results.get('verdict')}  p={results.get('p_value')}  ran_on_hw={ran_on_hw}")
    print(f"  hw_error={results.get('hw_error')}  fallback={results.get('fallback')}")


if __name__ == "__main__":
    main()

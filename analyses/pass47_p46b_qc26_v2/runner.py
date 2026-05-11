"""
p46-B — qc26 GHZ-5 Mermin v2: 4096 shots/setting (4× Pass-46 v1).

Identical preparation + measurement protocol as Pass-46 qc26 (state
ψ = (|00000⟩ - i|11111⟩)/√2, three settings A_1Y/B_3Y/C_5Y), but with
N_SHOTS = 4096 per setting (12,288 total) to tighten σ_M.

Expected σ_M improvement: σ_M ∝ 1/√N → 4× shots = 2× tighter error bar.
v1 σ_M ≈ 0.146 → v2 expected σ_M ≈ 0.073.

Pre-reg verdicts (frozen, identical to Pass-46 qc26 v1):
  CONFIRM: |M_5| > 4 + 3·σ_M
  REJECT:  |M_5| ≤ 4 + 3·σ_M
  INELIGIBLE: HW unreachable / job error
"""
import json, os, time, traceback, hashlib
from collections import Counter
import numpy as np

ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")
RUNNER_PATH = os.path.abspath(__file__)

N_QUBITS = 5
N_SHOTS = 4096
QUEUE_TIMEOUT = 900

TOKEN = (os.environ.get("IBMQ_Secret")
         or os.environ.get("IBMQ_TOKEN")
         or os.environ.get("QISKIT_IBM_TOKEN"))


def runner_sha256():
    with open(RUNNER_PATH, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def build(setting_y_qubits):
    from qiskit import QuantumCircuit
    qc = QuantumCircuit(N_QUBITS, N_QUBITS)
    qc.h(0); qc.sdg(0)
    qc.cx(0, 1); qc.cx(1, 2); qc.cx(2, 3); qc.cx(3, 4)
    for q in range(N_QUBITS):
        if q in setting_y_qubits:
            qc.sdg(q); qc.h(q)
        else:
            qc.h(q)
    qc.measure(range(N_QUBITS), range(N_QUBITS))
    return qc


def parity(counts):
    total = sum(counts.values())
    if total == 0: return 0.0, 0
    s = sum(n * (1 if bits.count('1') % 2 == 0 else -1) for bits, n in counts.items())
    return s / total, total


def get_svc(token):
    from qiskit_ibm_runtime import QiskitRuntimeService
    last = None
    for ch in ("ibm_quantum_platform", "ibm_quantum", "ibm_cloud"):
        try: return QiskitRuntimeService(channel=ch, token=token), ch
        except Exception as e: last = f"{ch}: {e}"
    raise RuntimeError(last)


def submit(qc, backend, shots=N_SHOTS):
    from qiskit_ibm_runtime import SamplerV2
    from qiskit import transpile
    qc_t = transpile(qc, backend, optimization_level=1)
    job = SamplerV2(mode=backend).run([qc_t], shots=shots)
    jid = job.job_id()
    print(f"    job_id={jid} ...", flush=True)
    t0 = time.time()
    while True:
        st = str(job.status())
        if st in ("JobStatus.DONE", "DONE"): break
        if st in ("JobStatus.ERROR", "JobStatus.CANCELLED", "ERROR", "CANCELLED"):
            raise RuntimeError(f"job {st}")
        if time.time() - t0 > QUEUE_TIMEOUT:
            raise TimeoutError(f"timeout {QUEUE_TIMEOUT}s; job {st}")
        time.sleep(15)
    pub = job.result()[0]
    return dict(Counter(pub.data.c.get_bitstrings())), jid


def main():
    results = {
        "pass": 47, "test_id": "p46b_qc26_v2",
        "n_qubits": N_QUBITS, "n_shots_per_setting": N_SHOTS,
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "runner_sha256": runner_sha256(),
        "token_available": bool(TOKEN),
        "settings": {},
    }
    settings = {"A_1Y": [0], "B_3Y": [0,1,2], "C_5Y": [0,1,2,3,4]}
    svc, ch, backend, ran_hw = None, None, None, False
    if TOKEN:
        try:
            svc, ch = get_svc(TOKEN)
            backend = svc.least_busy(operational=True, simulator=False, min_num_qubits=N_QUBITS)
            results["ibmq_channel"] = ch; results["backend_name"] = backend.name
            ran_hw = True
        except Exception as e:
            results["hw_error"] = f"{type(e).__name__}: {e}"
            results["hw_traceback"] = traceback.format_exc()[-1500:]

    for label, yq in settings.items():
        results["settings"][label] = {"y_qubits": yq}
        try:
            if ran_hw:
                counts, jid = submit(build(yq), backend)
                results["settings"][label]["job_id"] = jid
                results["settings"][label]["source"] = "ibmq_hw"
            else:
                raise RuntimeError("no hw")
        except Exception as e:
            results["settings"][label]["error"] = f"{type(e).__name__}: {e}"
            counts = None
        if counts is not None:
            E, N = parity(counts)
            results["settings"][label].update({
                "expectation": E, "n": N,
                "var": (1 - E*E) / max(N, 1),
                "counts_top5": dict(sorted(counts.items(), key=lambda x: -x[1])[:5]),
            })

    try:
        E1 = results["settings"]["A_1Y"]["expectation"]
        E3 = results["settings"]["B_3Y"]["expectation"]
        E5 = results["settings"]["C_5Y"]["expectation"]
        V1 = results["settings"]["A_1Y"]["var"]
        V3 = results["settings"]["B_3Y"]["var"]
        V5 = results["settings"]["C_5Y"]["var"]
        M5 = 5.0*E1 - 10.0*E3 + 1.0*E5
        sigma_M = float(np.sqrt(25*V1 + 100*V3 + V5))
        results.update({
            "E_1Y": E1, "E_3Y": E3, "E_5Y": E5,
            "M5": M5, "abs_M5": abs(M5), "sigma_M": sigma_M,
            "classical_bound": 4.0, "quantum_max": 16.0,
            "threshold_confirm": 4.0 + 3*sigma_M,
            "actually_on_hw": all(results["settings"][s].get("source") == "ibmq_hw" for s in settings),
        })
        if not results["actually_on_hw"]:
            results["verdict"] = "INELIGIBLE_HW_FAILED"
        elif abs(M5) > 4.0 + 3*sigma_M:
            results["verdict"] = "CONFIRM"
        else:
            results["verdict"] = "REJECT"
    except Exception as e:
        results["scoring_error"] = f"{type(e).__name__}: {e}"
        results["verdict"] = "ERROR"

    results["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    with open(RESULTS_PATH, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nverdict={results.get('verdict')} M5={results.get('M5')} "
          f"|M|={results.get('abs_M5')} sigma_M={results.get('sigma_M')}")


if __name__ == "__main__":
    main()

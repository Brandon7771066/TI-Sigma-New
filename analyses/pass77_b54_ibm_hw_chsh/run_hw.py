"""
Pass-77 B54: REAL IBM Quantum hardware CHSH — the root-2 diagonal on physical silicon.
Submits the optimal-angle CHSH set (theory S = 2*sqrt2) to a real backend and checks
whether physical quantum hardware breaks the classical/binary bound of 2 (the staircase
"stuck at 2"), walking toward the sqrt(2) diagonal.
"""
import os, math, json, time
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2

OUT = "analyses/pass77_b54_ibm_hw_chsh"
SHOTS = 4096
sqrt2 = math.sqrt(2)
svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=os.environ["IBMQ_Secret"])
backend = svc.backend("ibm_marrakesh")
print("backend:", backend.name, "| pending:", backend.status().pending_jobs)

a0, a1, b0, b1 = 0.0, math.pi/4, math.pi/8, 3*math.pi/8   # optimal CHSH angles
settings = [("a0b0", a0, b0), ("a0b1", a0, b1), ("a1b0", a1, b0), ("a1b1", a1, b1)]

def chsh_circ(ta, tb):
    qc = QuantumCircuit(2, 2)
    qc.h(0); qc.cx(0, 1)          # Bell |Phi+>
    qc.ry(-2*ta, 0); qc.ry(-2*tb, 1)
    qc.measure([0, 1], [0, 1])
    return qc

circs = [chsh_circ(ta, tb) for _, ta, tb in settings]
tcircs = transpile(circs, backend=backend, optimization_level=1)
print("transpiled", len(tcircs), "circuits; submitting...")

job = SamplerV2(mode=backend).run(tcircs, shots=SHOTS)
jid = job.job_id()
json.dump({"job_id": jid, "backend": backend.name, "settings": [s[0] for s in settings],
           "shots": SHOTS}, open(f"{OUT}/job.json", "w"), indent=2)
print("JOB_ID:", jid)

t0 = time.time()
while time.time() - t0 < 95:
    st = job.status()
    print(f"  t={time.time()-t0:5.1f}s status={st}")
    if str(st) in ("DONE", "ERROR", "CANCELLED", "JobStatus.DONE", "JobStatus.ERROR"):
        break
    time.sleep(8)

if str(job.status()) in ("DONE", "JobStatus.DONE"):
    res = job.result()
    E = {}
    for (name, _, _), pub in zip(settings, res):
        counts = pub.data.c.get_counts()
        tot = sum(counts.values()); corr = 0
        for bits, n in counts.items():
            a = 1 - 2*int(bits[-1]); b = 1 - 2*int(bits[-2])
            corr += a*b*n
        E[name] = corr/tot
    S = E["a0b0"] - E["a0b1"] + E["a1b0"] + E["a1b1"]
    out = {"job_id": jid, "backend": backend.name, "E": E, "S_measured": abs(S),
           "classical_bound": 2.0, "tsirelson": 2*sqrt2, "shots": SHOTS}
    json.dump(out, open(f"{OUT}/results.json", "w"), indent=2)
    print(json.dumps(out, indent=2))
    print(f"\n  |S| = {abs(S):.4f}  (classical/binary bound = 2.0, Tsirelson = {2*sqrt2:.4f})")
    print("  VIOLATION >2 :", abs(S) > 2.0)
else:
    print("NOT DONE in window; job_id saved to job.json for polling:", jid)

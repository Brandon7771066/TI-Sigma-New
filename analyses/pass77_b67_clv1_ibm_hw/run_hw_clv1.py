"""
Pass-77 B67: CLV-1-F1 on REAL IBM quantum hardware.
Tests the load-bearing CLV-1 claim — that the dysphoric SINGLET (Psi-) and the euphoric
symmetric Bell (Phi+) are CONSCIOUSNESS-LEVEL-DEGENERATE (both reduced states maximally
mixed => max integration/entropy) yet VALENCE-OPPOSITE (<SWAP> = -1 vs +1) — on physical
silicon, not just in simulation.

Per state we run 3 measurement bases (ZZ, XX, YY). From counts:
  <SWAP> = (1 + <XX> + <YY> + <ZZ>)/2          -> symmetry S (valence axis)
  reduced-qubit purity  Tr(rho0^2) = (1+<X0>^2+<Y0>^2+<Z0>^2)/2  -> LEVEL axis
A maximally mixed reduced state (purity 0.5, vN entropy 1 bit) = max integration/level.
CLV-1-F1 prediction: both states show ~equal (near-maximal) level but OPPOSITE symmetry.
"""
import os, math, json, time
from qiskit import QuantumCircuit, transpile
from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2

OUT = "analyses/pass77_b67_clv1_ibm_hw"
SHOTS = 4096
svc = QiskitRuntimeService(channel="ibm_quantum_platform", token=os.environ["IBMQ_Secret"])
backend = svc.least_busy(operational=True, simulator=False)
print("backend:", backend.name, "| pending:", backend.status().pending_jobs)

def prep(state):
    qc = QuantumCircuit(2, 2)
    if state == "Phi+":                 # (|00>+|11>)/sqrt2  symmetric
        qc.h(0); qc.cx(0, 1)
    elif state == "Psi-":               # (|01>-|10>)/sqrt2  singlet / antisymmetric (MI)
        qc.x(0); qc.x(1); qc.h(0); qc.cx(0, 1)
    return qc

def add_basis(qc, basis):
    if basis == "XX":
        qc.h(0); qc.h(1)
    elif basis == "YY":
        qc.sdg(0); qc.h(0); qc.sdg(1); qc.h(1)
    qc.measure([0, 1], [0, 1])
    return qc

states = ["Psi-", "Phi+"]
bases = ["ZZ", "XX", "YY"]
labels, circs = [], []
for s in states:
    for b in bases:
        qc = prep(s); add_basis(qc, b)
        labels.append((s, b)); circs.append(qc)

tcircs = transpile(circs, backend=backend, optimization_level=2)
print("transpiled", len(tcircs), "circuits; submitting...")
job = SamplerV2(mode=backend).run(tcircs, shots=SHOTS)
jid = job.job_id()
json.dump({"job_id": jid, "backend": backend.name, "labels": labels, "shots": SHOTS},
          open(f"{OUT}/job.json", "w"), indent=2)
print("JOB_ID:", jid)

t0 = time.time()
while time.time() - t0 < 100:
    st = str(job.status())
    print(f"  t={time.time()-t0:5.1f}s status={st}")
    if st in ("DONE", "ERROR", "CANCELLED", "JobStatus.DONE", "JobStatus.ERROR", "JobStatus.CANCELLED"):
        break
    time.sleep(12)

if str(job.status()) in ("DONE", "JobStatus.DONE"):
    res = job.result()
    raw = {}
    for (s, b), pub in zip(labels, res):
        raw[f"{s}|{b}"] = pub.data.c.get_counts()

    def exp_pair(counts):   # <Z0 x Z1>-style two-qubit correlator
        tot = sum(counts.values()); c = 0
        for bits, n in counts.items():
            z0 = 1 - 2*int(bits[-1]); z1 = 1 - 2*int(bits[-2]); c += z0*z1*n
        return c/tot
    def exp_single(counts, q):
        tot = sum(counts.values()); c = 0
        for bits, n in counts.items():
            zi = 1 - 2*int(bits[-1-q]); c += zi*n
        return c/tot

    out = {"job_id": jid, "backend": backend.name, "shots": SHOTS, "states": {}}
    for s in states:
        XX = exp_pair(raw[f"{s}|XX"]); YY = exp_pair(raw[f"{s}|YY"]); ZZ = exp_pair(raw[f"{s}|ZZ"])
        swap = (1 + XX + YY + ZZ)/2
        # reduced qubit-0 Bloch vector from the three single-qubit marginals
        x0 = exp_single(raw[f"{s}|XX"], 0); y0 = exp_single(raw[f"{s}|YY"], 0); z0 = exp_single(raw[f"{s}|ZZ"], 0)
        purity = (1 + x0**2 + y0**2 + z0**2)/2
        # von Neumann entropy of reduced qubit from Bloch radius r
        r = min(1.0, math.sqrt(x0**2 + y0**2 + z0**2))
        ev = [(1+r)/2, (1-r)/2]; H = -sum(p*math.log2(p) for p in ev if p > 1e-12)
        out["states"][s] = {"XX": XX, "YY": YY, "ZZ": ZZ, "SWAP_symmetry": swap,
                            "reduced_purity": purity, "reduced_entropy_bits": H,
                            "bloch_r": r}
    json.dump({**out, "counts": raw}, open(f"{OUT}/results.json", "w"), indent=2)
    a, b = out["states"]["Psi-"], out["states"]["Phi+"]
    print("\n=== REAL-HW CLV-1-F1 ===")
    print(f"  SINGLET Psi-:  level(entropy)={a['reduced_entropy_bits']:.3f} bits  purity={a['reduced_purity']:.3f}  SWAP/symmetry={a['SWAP_symmetry']:+.3f}")
    print(f"  Bell    Phi+:  level(entropy)={b['reduced_entropy_bits']:.3f} bits  purity={b['reduced_purity']:.3f}  SWAP/symmetry={b['SWAP_symmetry']:+.3f}")
    print(f"  level gap |dEntropy| = {abs(a['reduced_entropy_bits']-b['reduced_entropy_bits']):.3f} bits  (CLV-1: ~0 => level-degenerate)")
    print(f"  symmetry gap = {abs(a['SWAP_symmetry']-b['SWAP_symmetry']):.3f}  (CLV-1: large => valence-opposite)")
else:
    print("NOT DONE in window; job_id saved for polling:", jid)

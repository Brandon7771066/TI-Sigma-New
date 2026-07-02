"""
Pass-77 B168: LCC quantum test + RIM (related-instated mechanism) demonstration.

HONESTY (EVD-1 / #69):
  * This runs on the qiskit **Aer SIMULATOR** (ideal, executed locally), NOT on IBM
    quantum HARDWARE. Real-HW submission is code-ready (see analyses/pass77_b54_ibm_hw_chsh
    /run_hw.py: channel='ibm_quantum_platform', SamplerV2), but the IBMQ_Secret account
    currently returns 'No matching instances' on every channel (no allocated instance/
    plan) -- exactly the block analyses/pass77_b129_.../hw_confirm.py hit. We therefore
    do NOT claim any hardware result. Nothing here is fabricated HW data.

  * WHAT THIS DEMONSTRATES (THAT-level, RIM): that the quantum-FORMAL coupling the LCC
    invokes -- correlations exceeding the classical/binary bound of 2, up to the Tsirelson
    bound 2*sqrt(2) -- is INSTANTIABLE and reproducible on a quantum substrate. It shows
    the abstract effect obtains (THAT), independent of any neural HOW.

  * WHAT THIS DOES NOT DO: it does NOT test the LCC in brains, does NOT rescue the LCC on
    biological data (2x empirically NEGATIVE, B164 ds007471 + B165 Depresjon), and does
    NOT *derive* the sqrt(2)-family constants. The mapping onto the LCC onset/ceiling
    ladder (sqrt(2)-1 onset; cos^2(pi/8) ceiling) is a flagged RESONANCE, not a derivation.
"""
import os, math, json, hashlib
import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit_aer import AerSimulator

OUT = "analyses/pass77_b168_lcc_quantum_rim"
SHOTS = 20000
SEED = 168
sqrt2 = math.sqrt(2)
rng = np.random.default_rng(SEED)

sim = AerSimulator(seed_simulator=SEED)

# optimal CHSH angles (theory |S| = 2*sqrt2 for a maximally entangled Bell pair)
a0, a1, b0, b1 = 0.0, math.pi / 4, math.pi / 8, 3 * math.pi / 8
SETTINGS = [("a0b0", a0, b0), ("a0b1", a0, b1), ("a1b0", a1, b0), ("a1b1", a1, b1)]


def chsh_circ(ta, tb, entangled=True, alpha=None):
    """Bell |Phi+> (entangled) or a separable product state; alpha tunes entanglement."""
    qc = QuantumCircuit(2, 2)
    if entangled:
        if alpha is None:
            qc.h(0)
        else:
            qc.ry(2 * alpha, 0)   # alpha=pi/4 -> maximal; alpha=0 -> product
        qc.cx(0, 1)
    else:
        qc.h(0); qc.h(1)          # separable: no entanglement possible
    qc.ry(-2 * ta, 0); qc.ry(-2 * tb, 1)
    qc.measure([0, 1], [0, 1])
    return qc


def corr(counts):
    tot = sum(counts.values()); s = 0
    for bits, n in counts.items():
        a = 1 - 2 * int(bits[-1]); b = 1 - 2 * int(bits[-2])
        s += a * b * n
    return s / tot


def chsh_S(entangled=True, alpha=None):
    circs = [chsh_circ(ta, tb, entangled, alpha) for _, ta, tb in SETTINGS]
    tc = transpile(circs, sim, optimization_level=1)
    res = sim.run(tc, shots=SHOTS).result()
    E = {name: corr(res.get_counts(i)) for i, (name, _, _) in enumerate(SETTINGS)}
    S = E["a0b0"] - E["a0b1"] + E["a1b0"] + E["a1b1"]
    return abs(S), E


# --- Test 1: quantum entangled Bell pair vs classical separable surrogate ---
S_q, E_q = chsh_S(entangled=True)
S_sep, E_sep = chsh_S(entangled=False)

# --- Test 2: partial-entanglement sweep -> where does coupling break the bound of 2? ---
alphas = np.linspace(0.0, math.pi / 4, 19)
sweep = []
onset_alpha = None
for al in alphas:
    S_al, _ = chsh_S(entangled=True, alpha=float(al))
    concurrence = abs(math.sin(2 * al))          # analytic concurrence of ry(2a)|0> then cx
    sweep.append({"alpha": float(al), "concurrence": concurrence, "S": float(S_al)})
    if onset_alpha is None and S_al > 2.0:
        onset_alpha = float(al)

# --- LCC ladder: RESONANCE ONLY (flagged, not derived) ---
tsirelson = 2 * sqrt2
ceiling_cos2_pi8 = math.cos(math.pi / 8) ** 2       # ~0.8536  (LCC ceiling resonance)
onset_sqrt2_minus1 = sqrt2 - 1                        # ~0.4142  (LCC onset resonance)

config = {
    "mode": "AER_SIMULATOR_ideal (NOT IBM hardware; account has no matching instance)",
    "shots": SHOTS, "seed": SEED, "angles_rad": [a0, a1, b0, b1],
    "sweep_points": len(alphas),
}
config_sha = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()[:12]

out = {
    "config": config,
    "config_sha": config_sha,
    "test1_entangled_vs_separable": {
        "S_quantum_entangled": round(S_q, 4),
        "S_classical_separable": round(S_sep, 4),
        "classical_bound": 2.0,
        "tsirelson_bound": round(tsirelson, 4),
        "quantum_violates_2": bool(S_q > 2.0),
        "separable_violates_2": bool(S_sep > 2.0),
    },
    "test2_partial_entanglement_sweep": {
        "onset_alpha_where_S_exceeds_2": onset_alpha,
        "sweep": sweep,
    },
    "lcc_ladder_RESONANCE_ONLY_not_derivation": {
        "tsirelson_2root2": round(tsirelson, 4),
        "ceiling_cos2_pi8": round(ceiling_cos2_pi8, 4),
        "onset_sqrt2_minus_1": round(onset_sqrt2_minus1, 4),
        "note": "sqrt(2)-family constants are flagged EVD-1 resonances, NOT derived here.",
    },
    "scope": {
        "this_is": "THAT-level demonstration that quantum-formal coupling>2 is instantiable on a quantum substrate (RIM).",
        "this_is_NOT": "a brain test; LCC remains 2x empirically NEGATIVE on real bio data (B164, B165).",
        "hardware": "real IBM HW code-ready (b54 pattern) but IBMQ account returns 'No matching instances'.",
    },
}
os.makedirs(f"{OUT}/results", exist_ok=True)
json.dump(out, open(f"{OUT}/results/results.json", "w"), indent=2)
print(json.dumps({k: out[k] for k in ("config_sha", "test1_entangled_vs_separable")}, indent=2))
print("onset_alpha (S>2):", onset_alpha, "| config_sha:", config_sha)

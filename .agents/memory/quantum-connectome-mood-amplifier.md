---
name: Quantum-connectome mood amplifier (QCM-1)
description: How to honestly test "demonstrably quantum" influence when running the mood amplifier on a connectome inside a quantum computer.
---

# Demonstrably-quantum mood amplifier on a connectome (QCM-1)

**The honest punchline:** mood STEERING is substrate-neutral — a dephased classical
surrogate (diagonalise the density matrix each step) steers the same neurons just as
well. The genuinely quantum content is the **entanglement structure**, NOT the
control. Always run a dephased-classical arm on the SAME pipeline as the steelman.

**Witness choice is load-bearing — two traps:**
- **Meyer-Wallach Q is NOT a clean quantum/classical witness for mixed states** — it
  measures single-qubit mixedness, so a dephased classical state scores Q≈0.7+.
  Discard it. Use **entanglement negativity across a balanced cut**
  (`qiskit.quantum_info.negativity(DensityMatrix(rho), cut)`): it is **exactly 0 for
  any separable/dephased state** and >0 only for non-classical correlations →
  perfect discriminator (got 4.12 quantum vs 0.000 classical).
- **Monogamy of entanglement** means that with N>2 all-coupled qubits, NO single
  PAIR looks entangled (pair-negativity≈0, naive pair-CHSH S≈0.6<2). That is correct
  physics, not a null result. For a gold-standard **CHSH S>2 Bell violation** you
  must **isolate the strongest pair** (2-qubit circuit) — then drive + XY-coupling
  reach Tsirelson 2.83 (and >2 at native edge weight).

**Why:** the first run reported S<2 and a "quantum" Q gap that the classical arm
also showed — both artifacts of the wrong witnesses. Switching to cut-negativity +
isolated-pair CHSH gave a clean, defensible demonstrably-quantum result.

**Performance:** evolving an 8-qubit (256×256) density matrix via
`DensityMatrix.evolve(circuit)` per step is far too slow (recompiles each call;
times out >120s). Precompute the connectome unitary ONCE
(`Operator(layer).data`) and do `rho = U @ rho @ U†` in raw NumPy; build the RY-drive
unitary by `kron` (qiskit little-endian: qubit n-1 outermost). ~100× faster.

**IBM real-hardware access (2026-06):** the token authenticates but has **no usable
instance/plan** — both `channel="ibm_quantum_platform"` and `"ibm_cloud"` raise
`IBMInputValueError('No matching instances found for the following filters: .')` at
`least_busy`/`backends`. The open plan was retired; an instance must be attached to
the account. Do NOT fabricate hardware numbers — save an explicit UNAVAILABLE stub
and leave the submit-script ready (`hw_confirm.py`).

**Scope discipline:** this is reachability/in-principle about the MODEL on a quantum
processor only — never evidence that real biological neurons are quantum or that the
amplifier works on animals. The connectome supplies only the coupling graph.

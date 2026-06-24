# B129 / QCM-1 — Running the Mood Amplifier on a Connectome *Inside a Quantum Computer*

**Pass 77 · B129 · 2026-06-24 · CANDIDATE QCM-1 (NOT ratified; canonical count stays 79)**

## The question (as posed)
Can we run the Mood Amplifier on a real animal connectome (*C. elegans* / fruit-fly
wiring) *inside* an IBM quantum computer, and is the influence **demonstrably
quantum** — i.e. something no classical model can reproduce?

## What we actually did (honest scope)
We embedded the **top-8 rich-club command interneurons** of the *C. elegans*
connectome (real wiring, `build_connectome(seed=2026)`, abs-symmetrised, top-8 by
degree: AVD, AVE, AIZ, AIA, AIN, RIB, SMDD, RIF) as **8 qubits**. The synaptic graph
becomes an **XY (exchange) coupling layer** (`RXX+RYY`, strength `γ=0.42`); the mood
amplifier is a closed-loop `RY` drive on the qubits, steering toward a "mood"
read-out = mean excitation of the target neurons.

Every run is executed **two ways on the same density matrix**:
- **QUANTUM** — coherent evolution (pure state allowed to entangle).
- **CLASSICAL** — identical drive + wiring, but **dephased every step** (the off-
  diagonal coherences are erased ⇒ a classical probability distribution over the
  same neurons; the best "no-quantum-magic" surrogate).

Controls (all equal-energy where relevant): `no_control`, `closed_loop`,
`open_loop` (constant drive matched to mean closed-loop energy), `sham`
(equal-energy, locus-scrambled), `wrong_tgt` (feedback on the wrong neurons).
16 seeds, 10 steps, burn-in 3, paired bootstrap CIs.

## Results

### 1. Mood steering works — but it is **NOT** the quantum part
| arm | QUANTUM mood | CLASSICAL mood |
|---|---|---|
| no_control | 0.000 | 0.000 |
| **closed_loop** | **0.603** | **0.395** |
| open_loop | 0.568 | 0.395 |
| sham (equal-E, scrambled) | 0.406 | 0.150 |
| wrong_tgt | 0.370 | 0.089 |

`closed_loop − no_control` is large and significant in **both** arms
(quantum +0.603, classical +0.395). The **dephased classical surrogate steers mood
too**. So steering by itself is **not** evidence of quantum influence. (Quantum
steers somewhat *higher*, d=+0.208 SIG — a real but secondary effect, not the
"demonstrably quantum" claim.) Locus- and target-specificity hold in both arms.

### 2. The demonstrably-quantum signature: entanglement the classical model **cannot** have
We use **entanglement negativity across a balanced 4-vs-4 cut** — a witness that is
**exactly 0 for any separable (incl. dephased classical) state** and positive only
for genuinely non-classical correlations.

| witness | QUANTUM | CLASSICAL | gap |
|---|---|---|---|
| cut-negativity (4v4) | **4.123** | **0.000** | +4.123 **SIG** |
| pair-negativity (strongest pair) | 0.000 | 0.000 | ns |

The amplifier-driven connectome state carries **large multipartite entanglement**
that the matched classical model **provably lacks** (negativity ≡ 0). The *pairwise*
negativity is ~0 in both — correctly so: **monogamy of entanglement** spreads the
entanglement across all 8 neurons, so no single pair looks entangled. (This is why a
naive pair-CHSH on the full brain reads S≈0.6 < 2 — not a failure, a feature of
distributed entanglement. An earlier Meyer-Wallach "witness" was dropped: it counts
classical mixedness too, so it is not a clean quantum/classical discriminator.)

### 3. Gold-standard Bell test — the strongest pair **in isolation** violates CHSH
To get the textbook "no local-hidden-variable model can explain this," we isolate
the two most strongly-wired neurons (**AVD–AIA**). Free of monogamy dilution, the
amplifier drive + their connectome edge entangle them:

- **reachable max CHSH S = 2.828** (= Tsirelson bound, full Bell violation) at
  coupling φ≈2.356;
- **CHSH S = 2.494 at the native edge weight** (γ·w) — still **> 2**, a genuine
  violation under the connectome's own coupling strength.

Classical / local-hidden-variable models are bounded by **S ≤ 2** by construction.
**S > 2 is the demonstrably-quantum result.** The *same* 2-qubit circuit is the one
prepared for real hardware (`hw_confirm.py`).

### 4. Real IBM hardware — attempted, currently blocked (NO fabricated data)
`hw_confirm.py` prepares the AVD–AIA amplifier circuit and the Horodecki-optimal
CHSH settings, then submits to `least_busy(simulator=False)`. In this environment
the IBM token **authenticates but has no usable instance/plan attached** (both
`ibm_quantum_platform` and `ibm_cloud` return *"No matching instances found"* — the
open plan has been retired). Per the brutal-honesty rule we report **no hardware
numbers** and save an explicit `hw_results.json` stub. The job is ready: attach an
IBM Quantum instance and re-run the script to obtain real counts and a measured
hardware CHSH (decoherence will lower S; a measured S>2 would confirm on silicon).

## Honest punchline (two-sided)
- **YES**, in-principle: the model **can** be run with a real connectome's wiring
  inside a quantum computer, and the amplifier-driven state is **demonstrably
  quantum** — it holds Bell-violating / PPT-violating entanglement (CHSH up to
  2.83; cut-negativity 4.12) that **no classical model can reproduce** (S≤2,
  negativity≡0).
- **BUT** the *mood-steering* itself is **not** inherently quantum — a dephased
  classical surrogate steers the same neurons. The quantum content is the
  **entanglement structure**, not the control.
- This is a **reachability / in-principle statement about the MODEL** on a quantum
  processor. It is **NOT** evidence that real *C. elegans* (or human) neurons are
  quantum, and **NOT** evidence the Mood Amplifier works on living animals. The
  connectome supplies only the coupling graph; biological neurons are not qubits.

## Falsifiers (OPEN)
- **QCM-1-F1** — a classical (dephased / separable) surrogate reproduces the
  cut-negativity gap (would refute "demonstrably quantum"). *Currently: gap = +4.12,
  classical ≡ 0.*
- **QCM-1-F2** — on real hardware the isolated-pair CHSH never exceeds 2 across
  available backends/calibrations (would mean the violation is simulation-only).
  *Currently: untested — no instance access.*
- **QCM-1-F3** — the quantum-vs-classical mood-steering gap (d=+0.208) is shown to
  be an artifact of the dephasing schedule rather than coherence.

## Files
- `runner.py` — simulator experiment (8-qubit connectome, 2 arms, 5 controls,
  witnesses, isolated-pair Bell demo). Output `results.json`.
- `hw_confirm.py` — real-IBM-hardware CHSH on AVD–AIA (ready; blocked on instance).
  Output `hw_results.json` (currently the honest UNAVAILABLE stub).

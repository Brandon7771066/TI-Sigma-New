# Pass 77 · B129 — Quantum-Connectome Mood Amplifier (QCM-1)
### Running the Mood Amplifier on a *C. elegans* connectome *inside* a quantum computer, and what "demonstrably quantum" honestly means

**Date:** 2026-06-24 · **Status:** CANDIDATE (QCM-1), **NOT ratified** · canonical
principle count **unchanged 79** · **Analysis package:**
`analyses/pass77_b129_quantum_connectome_mood_amplifier/`
(`runner.py`, `hw_confirm.py`, `results.json`, `hw_results.json`, `RESULTS_WRITEUP.md`)

---

## 0. The user's question
"Run the Mood Amplifier on a *C. elegans* / fruit-fly connectome *within* an IBM
quantum computer and test whether the influence is **demonstrably quantum**." The
user chose a **hybrid** design: a rigorous **Aer-simulator** experiment plus **one
small real-IBM-hardware CHSH confirmation**.

This paper reports the simulator experiment (complete) and the hardware arm (ready,
currently blocked on IBM instance access — no fabricated data).

---

## 1. Construction
- **Subject.** Top-8 **rich-club command interneurons** of the real *C. elegans*
  connectome (`build_connectome(seed=2026)`, abs-symmetrised, top-8 by degree):
  **AVD, AVE, AIZ, AIA, AIN, RIB, SMDD, RIF** → **8 qubits** (256×256 density matrix,
  small enough to handle the quantum and classical arms uniformly).
- **Wiring → coupling.** Each synaptic weight `w_ij` becomes an **XY / exchange
  coupling** `RXX(γw)+RYY(γw)`, `γ=0.42`. (Exchange coupling preserves the all-zero
  state and only entangles once the drive creates excitations — physically apt.)
- **Amplifier.** Closed-loop `RY(u)` drive; "mood" read-out = mean P(excited) over
  the target neurons; gain 2.2, setpoint/U_max 0.85, observation noise 0.02.
- **Two execution modes on the identical pipeline.**
  - **QUANTUM** — coherent (entanglement allowed).
  - **CLASSICAL** — **dephased every step** (computational-basis diagonalisation ⇒
    a classical distribution over the same neurons). This is the steelman
    "no-quantum-magic" surrogate.
- **Controls.** `no_control`, `closed_loop`, `open_loop` (constant drive, energy-matched
  to that arm's OWN mean closed-loop — calibrated per-arm so the classical
  value-of-feedback contrast is not energy-confounded), `sham` (equal-energy,
  locus-scrambled), `wrong_tgt`. 16 seeds,
  10 steps, burn-in 3; paired bootstrap CIs.

---

## 2. Results

### 2.1 Steering works in BOTH arms ⇒ steering is *not* the quantum part
`closed_loop` mood: **quantum 0.603**, **classical 0.395**; both significantly above
the 0.000 `no_control` baseline, and above their equal-energy `sham`/`wrong_tgt`
controls (locus- and target-specific in both arms). **The dephased classical model
steers mood too.** Quantum steers modestly higher (Δ=+0.208, SIG) — real but
secondary, *not* the headline.

### 2.2 The demonstrably-quantum signature = entanglement absent classically
**Witness:** entanglement **negativity across a balanced 4-vs-4 cut** — exactly **0**
for any separable state (including the dephased classical surrogate), positive only
for non-classical, PPT-violating correlations.

| witness | QUANTUM | CLASSICAL | gap |
|---|---|---|---|
| **cut-negativity (4v4)** | **4.123** | **0.000** | **+4.123 SIG** |
| pair-negativity (AVD–AIA) | 0.000 | 0.000 | ns |

The amplifier-driven state holds **large multipartite entanglement** the matched
classical model **provably cannot** (negativity ≡ 0). Pairwise negativity ≈ 0 in
both arms is **correct physics — monogamy of entanglement** distributes entanglement
across all eight neurons, so no single pair looks entangled.

> **Method honesty.** An initial Meyer-Wallach *Q* "witness" was **discarded**: for
> mixed states *Q* counts classical mixedness, so the dephased arm scored Q=0.745 —
> not a clean quantum/classical discriminator. Cut-negativity is the correct witness
> (classical ≡ 0 by separability). An initial pairwise-CHSH on the *full* brain read
> S≈0.6 (<2) — again monogamy, not a null result.

### 2.3 Gold-standard Bell violation on the strongest pair *in isolation*
Isolating **AVD–AIA** removes monogamy dilution; the amplifier drive + their
connectome edge entangle them:
- **reachable max CHSH S = 2.828** (= Tsirelson bound) at coupling φ≈2.356;
- **CHSH S = 2.494 at the native edge weight** (γ·w) — **> 2**, a real violation
  under the connectome's own coupling.

LHV/classical models are capped at **S ≤ 2**. **S>2 is the demonstrably-quantum
result** — no classical model reproduces it.

### 2.4 Real IBM hardware — ready, currently blocked (NO fabricated data)
`hw_confirm.py` prepares the AVD–AIA amplifier circuit + Horodecki-optimal CHSH
settings and submits to `least_busy(simulator=False)`. The IBM token
**authenticates but no usable instance/plan is attached** (`ibm_quantum_platform`
and `ibm_cloud` both return *"No matching instances found"*; the open plan has been
retired). We therefore report **no hardware CHSH** and save an explicit UNAVAILABLE
stub. Attaching an instance and re-running yields real counts; hardware noise lowers
S, so a measured S>2 would confirm on physical silicon.

---

## 3. The candidate (QCM-1)

> **QCM-1 — Quantum-Connectome Mood Amplifier (CANDIDATE, NOT ratified).**
> When an animal connectome's wiring is embedded as a qubit-coupling graph and driven
> by the closed-loop mood amplifier on a quantum processor, (a) **mood steering is
> reproducible but substrate-neutral** — a dephased classical surrogate steers the
> same neurons, so steering is *not* a quantum signature; while (b) the driven joint
> state is **demonstrably quantum** — it carries Bell-/PPT-violating entanglement
> (isolated-pair CHSH up to the Tsirelson bound 2.83, ≥2.49 at native coupling;
> 4-vs-4 cut-negativity 4.12) that **no classical model can reproduce** (CHSH≤2,
> negativity≡0). The quantum content lives in the **entanglement structure**, not in
> the control.

**Scope / anti-overclaim (#69).** QCM-1 is a **reachability / in-principle statement
about the MODEL on a quantum computer**. It is **NOT** evidence that real *C.
elegans* or human neurons are quantum, and **NOT** evidence the Mood Amplifier works
on living animals. The connectome supplies only the coupling graph; biological
neurons are not qubits. "Demonstrably quantum" means *the simulated quantum state is
provably non-classical*, nothing more.

**Relation to corpus.** Sits with the Mood-Amplifier reachability-only results
(decoding / efficacy sims are necessary-condition, not in-vivo proof); the
quantum/classical separation mirrors the corpus discipline of always testing a
matched classical surrogate (retrieval-operator and CH-vs-BASE work). No bearing on
the ratified principle count (stays 79).

---

## 4. Falsifiers (OPEN)
- **QCM-1-F1** — a classical (dephased/separable) surrogate reproduces the
  cut-negativity gap. *Currently refuted-direction: gap +4.12, classical ≡ 0.*
- **QCM-1-F2** — real-hardware isolated-pair CHSH never exceeds 2 across available
  backends/calibrations (violation would be simulation-only). *Untested — no
  instance access.*
- **QCM-1-F3** — the quantum-vs-classical steering gap (Δ=+0.208) is an artifact of
  the dephasing schedule, not of coherence.

---

## 5. Reproduce
```
python analyses/pass77_b129_quantum_connectome_mood_amplifier/runner.py      # simulator
python analyses/pass77_b129_quantum_connectome_mood_amplifier/hw_confirm.py  # real HW (needs IBM instance)
```

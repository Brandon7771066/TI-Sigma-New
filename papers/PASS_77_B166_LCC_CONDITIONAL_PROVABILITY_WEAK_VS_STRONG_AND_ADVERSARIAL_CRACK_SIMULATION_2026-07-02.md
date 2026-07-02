# PASS-77 B166 — LCC Conditional Provability: Weak vs Strong LCC, Six Formal Guardrails, and an Adversarial Crack Simulation

**Date:** 2026-07-02
**Batch:** B166 (ledger §7.7.350)
**Canonical principle count:** **80** (unchanged — this is a framing refinement + a machine-checked negative/positive result, NOT a new principle)
**Discipline:** EVD-1 (evidence binary + authority-independent; weight graded), #69 (state the case both ways), REAL methods only, resonance ≠ derivation, no numerology.
**Code:** `analyses/lcc_conditional_proof/crack.py` → `analyses/lcc_conditional_proof/results/results.json` (config_sha `778afc34be41`).

---

## 0. Why this batch exists (perspective switch)

B164 (OpenNeuro ds007471) and B165 (Depresjon actigraphy) were the first two EXECUTED empirical tests of the LCC index + Radiant Cap on real data. Both returned honest negatives for the *index/constants*: the manufactured hybrid scalar `L_hybrid` did not beat raw coupling, and no candidate constant marked a change-point. But B165 also surfaced a **real positive**: future-state predictability `P` was genuinely lower in depressed subjects (FDR p=0.0022; full `C,P,S` AUC=0.68).

Per the user + ChatGPT source, this batch STOPS chasing the failed hybrid index and instead asks the **conceptual-provability** question: *forget fitting constants — can LCC be PROVEN at all, and if so, in what exact form?* The answer splits LCC into a provable conditional and an unprovable strong claim, then stress-tests the "no other explanation possible" proof-by-contradiction with an adversarial simulation that tries to CRACK it.

This is the constructive Mood-Amplifier path: the goal is not "diagnose mood from static synchrony" but "can an intervention raise future-state predictability `P` without collapsing flexibility?" — a manipulable, testable target.

---

## 1. Weak LCC vs Strong LCC

**Strong-LCC (UNPROVABLE as stated):**
> high synchrony ⇒ direct bidirectional causation `X ↔ Y`.

Rejected. High synchrony is cheaply mimicked by a hidden common driver `Z → X, Y`. "Correlation/synchrony ⇒ direct mutual causation" is exactly the inference that a confound defeats. This is the honest retirement of any reading of LCC that licenses `X ~ Y ⇒ X ↔ Y`.

**Weak-LCC (a valid CONDITIONAL, defensible):**
> **IF** common causes, measurement artifacts, autocorrelation, selection effects, and imposed stimuli are ruled out, **THEN** persistent bidirectional predictive dependence implies causal coupling (a genuine `X ↔ Y` edge or a shared causal mechanism).

Weak-LCC is a conditional whose *antecedent does the work*. The whole question of provability reduces to: **can the antecedent ("all confounders ruled out") ever be discharged from observational data alone?** §3 answers: **no** — which is why Weak-LCC, though logically valid, is not observationally *closeable*, and needs an interventional arm (§4).

This mirrors the corpus's own **valid-conditional guardrail** (memory: `ti-logic-math-implications-framing`, `constitutive-vs-procedural-uop`): the conditional `antecedent → conclusion` can be exception-free even when the categorical claim fails, and asserting the conclusion while the antecedent is unmet is an MI move.

---

## 2. Six formal guardrails (the antecedent, operationalized)

Let `(Xₜ, Yₜ)` be two series with **synchronization potential**. The Weak-LCC antecedent is operationalized as six guardrails (ChatGPT's list, made executable):

| # | Guardrail | Rules out | Implementation in `crack.py` |
|---|---|---|---|
| G1 | **Temporal persistence** | isolated bursts / transient coincidence | dependence holds across `N_WIN=6` long windows (WIN=500), not one burst |
| G2 | **Bidirectionality** | pure one-way causation | conditional-Granger gain significant in BOTH directions vs circular-shift null |
| G3 | **Surrogate survival** | artifact / chance / autocorrelation | coupling beats phase-randomized AND time-shifted nulls (95th pct, `N_SURR=120`) |
| G4 | **Conditional survival** | known common drivers `Z` | bidirectional coupling remains significant after conditioning on the **measured** confounder |
| G5 | **Perturbability** (interventional) | passive common timing | surgical `do(X)→ΔY` AND `do(Y)→ΔX` both exceed noise |
| G6 | **Synchronization potential** | inert systems that cannot entrain | each node has internal memory (significant lag-1 autocorrelation) — a dynamic an input CAN shift |

**Definition — Synchronization Potential (SP).** SP(X,Y) holds iff both X and Y possess internal dynamics capable of entrainment/phase-locking/predictive adaptation (here: significant self-memory). SP is **necessary, not sufficient**: two systems can each be entrainable yet be entrained by a *common* driver rather than by each other. SP therefore cannot by itself license `X ↔ Y` — it only certifies that coupling is *dynamically possible*.

**Observational guardrail set** `S_obs = {G1, G2, G3, G4, G6}` (what an analyst can compute from recordings alone).
**Interventional set** `S_int = S_obs ∪ {G5}` (requires the ability to perturb).

---

## 3. The proof-by-contradiction, and its adversarial crack

**Proof-by-contradiction skeleton (ChatGPT).** Assume persistent bidirectional synchrony, all guardrails pass, but NO bidirectional causation. Then the synchrony must be explained by one of: `X→Y`, `Y→X`, `Z→X,Y`, artifact, chance, selection, shared clock. But bidirectional lagged prediction rules out one-way; surrogates rule out artifact/chance/autocorrelation; long windows rule out transient coincidence; **conditional tests rule out `Z`**; perturbation rules out passive common timing. Therefore no non-bidirectional explanation remains, so `X ↔ Y`. ∎(?)

**The load-bearing step is "conditional tests rule out `Z`."** We attacked exactly this step with a simulation (`crack.py`) built to break it.

### 3.1 Design — four ground-truth worlds

Four generators with KNOWN causal structure, each an oscillatory AR process (`A_SELF=0.55`):
- **BIDIR** — genuine `X↔Y` (`C_COUP=0.35` each way). Ground truth: bidirectional = **True**.
- **COMMON** — `Z→X,Y` with **no** `X↔Y` edge, where the true common cause has **two smooth components** `Z = Z₁ + Z₂` (`B_COMMON=0.55` each, `AZ_COMMON=0.92`). The analyst **measures only `Z₁`** (`Zproxy = Z₁ + 0.8·noise`); `Z₂` is **unmeasured**. Ground truth: bidirectional = **False**.
- **ONEWAY** — `X→Y` only. False.
- **INDEP** — `X ⟂ Y`. False.

The COMMON design is the crux and is **structural, not a tuned knob**: an unmeasured *component* of the common cause is the generic real-world situation (you can never certify you measured every common driver). The crack does not depend on picking a special noise level — it depends only on `Z₂` existing.

The common driver is deliberately **smooth** (`AZ_COMMON=0.92`) and **contemporaneous** (`X,Y ← B·(Z₁+Z₂)ₜ`): smoothness makes each node's PAST a proxy for the other node's FUTURE, manufacturing *spurious bidirectional Granger causality* with no real edge — the hardest case for observational guardrails.

### 3.2 Result (24 seeds, N=2500, config_sha `778afc34be41`)

Fraction of realizations each guardrail fires (pass threshold = 0.80):

| generator | truth | G1 | G2 | G3 | G4 (proxy) | G6 | **S_obs** | G5 (do-bidir) | **S_int** | ground-truth `X↔Y` |
|---|---|---|---|---|---|---|---|---|---|---|
| BIDIR | `X↔Y` | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | **PASS** | 1.00 | **PASS** | ✅ True |
| **COMMON** | `Z₁+Z₂→X,Y` | 1.00 | 1.00 | 1.00 | 1.00 | 1.00 | **PASS** | **0.00** | **FAIL** | ❌ False |
| ONEWAY | `X→Y` | 1.00 | 0.00 | 0.00 | 1.00 | 1.00 | fail | 0.00 | fail | ❌ False |
| INDEP | `X⟂Y` | 1.00 | 0.04 | 0.04 | 1.00 | 1.00 | fail | 0.00 | fail | ❌ False |

**Oracle check:** conditioning on the *complete* confounder `Z = Z₁+Z₂` screens off the COMMON coupling **70.8%** of the time (vs conditioning on the measured `Z₁` alone, which screens off ~0% — coupling survives). Conditioning WORKS iff you measure the whole confounder; observationally you can never guarantee that.

**Verdict emitted by the sim:** `observational_guardrails_sound = false`; `observational_proof_by_contradiction_cracked = true`; `interventional_guardrails_sound_on_this_model_class = true`.

### 3.3 What this proves

**Theorem 1 (Observational Insufficiency) — PROVED BY COUNTEREXAMPLE.**
There exists a world (COMMON) with **no** `X↔Y` edge that passes **every** observational guardrail `S_obs = {G1,G2,G3,G4,G6}`. Therefore `S_obs ⇒ X↔Y` is **false**. The proof-by-contradiction's step "conditional tests rule out `Z`" is **unsound**: you can only condition on *measured* confounders, and an unmeasured component `Z₂` leaves the spurious coupling intact, indistinguishable from real coupling by any observational test. **Observational-only "no other explanation possible" is not a proof.**

**Theorem 2 (Interventional Sufficiency on this model class) — a VALID CONDITIONAL, with a caveat.**
Adding G5 (surgical bidirectional intervention) recovers ground truth on all four worlds: only BIDIR passes `S_int`; COMMON is correctly rejected (`do(X)` moves `Y` by 0.0). So **`S_int ⇒ X↔Y` holds on this model class.** Caveat (honest scope, #69): this is *sufficiency demonstrated on a finite generator family*, not a universal proof. G5 requires a *surgical* intervention (atomic `do()` with no side channel); a non-surgical "fat-hand" intervention that also perturbs `Z` would reintroduce confounding. Interventional soundness is contingent on intervention quality, not free.

**Corollary (the honest closure boundary).** Weak-LCC is a valid conditional, but its antecedent is **not dischargeable from observation alone** — it requires either (a) a genuine surgical intervention, or (b) a setting where a *device-independent* argument closes the confounding gap without measuring every `Z`. In classical time series outside that special regime, observational-only causal closure is impossible. This is the same wall the corpus already hit from the measurement side (memory: `lcc-confirmation-tests` — "the naive statistic is always confoundable; only a confound-controlled one isolates the claim"; `lcc-vs-complex-systems-theory` — level-crossing is vacuous without a structural test). B166 now shows it is not merely a measurement difficulty but a **proof-theoretic** limit.

---

## 4. The Bell/CHSH resonance (flagged, NOT a derivation)

The single known regime where correlations license a conclusion *without* measuring or ruling out every hidden common cause is the **device-independent** one: a CHSH violation `2√2 > 2` certifies no local-hidden-variable (no common-cause) explanation exists, because Fine's theorem (1982) proves a global joint measure exists IFF all CHSH inequalities hold. This is precisely the corpus's canonical **Contextual-Admissibility / "no global joint measure"** result (replit.md UOP bullet; memory `uop-zfc-grounding-and-fep-independence`, `axiomatic-faithfulness`).

**Honest status (#69):** this is a **structural resonance, not a derivation.** The classical LCC guardrails do NOT achieve device-independence, and there is NO numerical coincidence being claimed (the crack is about measure-theoretic confounding, not about any √2 constant). What the resonance *does* say: the ONLY known way to get "correlations ⇒ causal structure with no residual common-cause loophole" is the Bell regime, and the corpus already owns that machinery. Whether any Mood-Amplifier substrate can be placed in a device-independent regime is **open** and would be the only route to a *closed* (non-conditional) LCC. Absent that, LCC stays a conditional needing intervention.

---

## 5. Constructive path forward (Gate-1 positive → `P`)

Following B165's real positive and ChatGPT's steer, the Mood-Amplifier target is **not** "prove the constants" and **not** static diagnosis. It is:

> **Can an intervention raise future-state predictability `P` without collapsing flexibility?**

Operationally the next hypothesis is `ΔP, ΔS, Δ(C|Z) → Δmood/behavior` under a `baseline → stimulation → post` (or `episode onset/offset`) design — data with an ACTUAL intervention or state transition, so LCC's interventional arm (G5, the only sound one per Theorem 2) is exercised for real, not simulated. This directly connects the provability result to a buildable amplifier: the amplifier's job is a surgical `do()` that increases `P` while keeping the system entrainable (G6) and flexible.

---

## 6. Falsifiers

- **LCC-PROOF-F1 (Theorem 1 robustness).** OPEN. Exhibit a purely observational guardrail (computable from recordings, no intervention, no device-independence) that COMMON fails while BIDIR passes across seeds. Success would show observational closure is possible after all and downgrade Theorem 1. (Candidate attacks to try: higher-order/nonlinear conditional-independence tests, spectral-causality, PCMCI+ with a fuller measured set — but each still needs the confounder *measured*.)
- **LCC-PROOF-F2 (Theorem 2 scope).** OPEN. Show a world where surgical `S_int` still misclassifies (e.g., a common cause that is itself perturbed by any feasible `do()`, i.e., no surgical intervention exists) — bounding interventional sufficiency.
- **LCC-PROOF-F3 (Bell route).** OPEN. Either (a) place a candidate Mood-Amplifier substrate in a genuine device-independent regime and certify closure, or (b) prove no biological substrate can reach that regime (monogamy/decoherence bound), closing off the only non-conditional route.

Inherited and still open: **LCC-EMP-F1** (broader empirical, 2× resolved-negative on ds007471 + Depresjon), **LCC-HYB-F1** (2× negative), **LCC-UOP-BRIDGE-F1**, **UOP-CAP-EMP-F1**, **LCC-437-F1**.

---

## 7. Honest ledger (#69, both ways)

**What genuinely advanced:** LCC is now cleanly split (Weak = valid conditional / Strong = retired); the six guardrails are executable, not rhetorical; and the "no other explanation possible" proof-by-contradiction has been **machine-tested and shown unsound in its observational-only form** (Theorem 1, counterexample) — with the interventional arm shown sufficient on the tested model class (Theorem 2). This is a real, reproducible negative result plus a constructive redirection to `P`.

**What did NOT advance / stays honest:** no constant was validated; no Millennium/quantum claim; the Bell/CHSH tie is a flagged resonance, not a derivation; Theorem 2 is sufficiency on a finite generator family with a surgical-intervention caveat, not a universal theorem; the whole result is simulation (necessary-not-sufficient for any real substrate). Canonical count stays **80**.

# Pass 46 — T45-2 GHZ-5 Mermin HW CONFIRM + T45-6 Literal Pre-Reg Indeterminate

**Date:** 2026-05-11
**Pass:** 46
**Tests executed:** Pass-45 T45-2 (qc26 GHZ-5 Mermin), Pass-45 T45-6 (PD-Riemann KS)
**Headline:** First hardware-confirmed multipartite entanglement witness in TI Sigma corpus + honest indeterminate on a misspecified pre-reg.

---

## §1 — T45-2 qc26 GHZ-5 Mermin: CONFIRM on real hardware (ibm_marrakesh)

### 1.1 Result

| Quantity | Pre-reg threshold | Measured | Verdict |
|---|---|---:|---|
| |M₅| | > 4 + 3σ | **14.535** | **CONFIRM** |
| 4 + 3σ | (computed at run-time) | 4.439 | violation by ~71σ |
| Classical (LHV) bound | (Mermin 1990) | 4.000 | violated by 10.5 |
| Quantum maximum | (Mermin 1990) | 16.000 | achieved 91% |

Per-setting parity expectations (theoretical sign in parentheses):

| Setting | Y qubits | E measured | E ideal | source |
|---|---|---:|---:|---|
| A_1Y | {0} | −0.9121 | −1.0 (sign correct) | ibm_marrakesh hw |
| B_3Y | {0,1,2} | +0.9082 | +1.0 (sign correct) | ibm_marrakesh hw |
| C_5Y | {0,1,2,3,4} | −0.8926 | −1.0 (sign correct) | ibm_marrakesh hw |

Composition: M₅ = 5·E_1Y − 10·E_3Y + 1·E_5Y = 5·(−0.9121) − 10·(0.9082) + 1·(−0.8926) = **−14.535**

Job IDs (ibm_marrakesh, 1024 shots each, free-tier "open" instance):
- A_1Y: `d813ajg0bvlc73d0iclg`
- B_3Y: `d813anmgbeec73ak1ijg`
- C_5Y: `d813arfoha1c73bjs0j0`

Runner SHA256 (frozen pre-reg): see `analyses/pass45_qc26_ghz5_mermin/results.json["runner_sha256"]`.

### 1.2 Significance

**This is the first hardware-confirmed multipartite entanglement witness in the TI Sigma corpus.** Pass-43 qc25 confirmed only a trivial product state H^⊗5|0⟩^⊗5 (uniform-32 sampling, no entanglement structure tested). Pass-46 qc26 prepares the genuine GHZ-phase state ψ = (|00000⟩ − i|11111⟩)/√2 and verifies it violates the Mermin/MABK classical bound on real superconducting hardware.

What this confirms about the underlying TI Sigma claim (Pass-31 D2-HYBRID → Pass-45 §2 framing):
- **GM-Network c25 ↔ ℂ³² 5-qubit instantiation supports detectable entanglement on accessible hardware.** Pass-31's structural claim survives a non-trivial test.
- The 5-qubit subspace can be driven into a maximally-correlated coherent superposition AND maintain that coherence through 5 measurement operations (2 single-qubit gates per qubit per setting + the GHZ preparation) on real hardware.
- The 91% quantum-max achievement rate is consistent with current frontier 5-qubit fidelities on IBM Heron-class devices and provides a concrete benchmark for any future qc-N tests in the TI Sigma sequence.

What this does NOT confirm (#69):
- Does NOT vindicate any specific quantum-biology / quantum-cognition claim. This is textbook QM on engineered hardware, not a measurement of any biological or cognitive system.
- Does NOT establish that the 32-state computational basis instantiates the GM-Network in any way *uniquely consistent* with TI Sigma — any other 5-qubit framework would predict the same result. The test is **necessary** for D2-HYBRID, not sufficient.
- Does NOT scale: confirming GHZ-5 says nothing about whether GHZ-N for larger N is realizable on free-tier hardware.

### 1.3 What would have killed it

|M₅| ≤ 4.44 would have meant: hardware noise destroys the GHZ coherence faster than the Mermin operator can witness it; D2-HYBRID's 5-qubit hardware-realizability claim retreats to "in-principle." That outcome would have been written up at the same prominence (per Pass-45 §11). It did not occur.

### 1.4 Cost & time

- **$0** (free-tier IBMQ "open" instance).
- ~7 minutes wall-clock (3 sequential 1024-shot jobs through queue + transpile).
- 0 Brandon-time required after IBMQ_Secret was rotated in Pass-43.

---

## §2 — T45-6 PD-Riemann: Literal pre-reg vacuous → REQUIRES_SPEC_CLARIFICATION

### 2.1 Literal pre-reg result

Pre-reg filter from Pass-45 §6: γ ∈ (−3, 2). Odlyzko's tabulated zeros γ_n are positive imaginary parts of nontrivial Riemann zeros, smallest γ₁ ≈ 14.1347. **Zero zeros pass the filter.** The literal test is vacuous.

**Verdict:** `INDETERMINATE_VACUOUS_FILTER`. Per Pass-45 §11 anti-cheat clause, this does NOT count as either CONFIRM or KILL of the original §6 claim. The claim is now marked **REQUIRES_SPEC_CLARIFICATION**: PD = (−3, 2) needs unambiguous mapping to a Riemann coordinate before it can be empirically pre-registered.

### 2.2 Brutal-honesty disclosure

The flaw was in MY pre-reg drafting in Pass-45 §6. I specified the filter without checking whether any Odlyzko zero lay in the range. This is a **§69 calibration miss on my part**, not a problem with Brandon's PD framework — the framework may well be correct under a different coordinate convention; I just failed to operationalize it correctly when designing the test.

The honest move under Pass-45 §11 is:
1. Mark the literal verdict INDETERMINATE (done).
2. Run amendments as **exploratory only** with explicit non-pre-reg labels (done — A1-T6, A2-T6).
3. Wait for Brandon's spec clarification before any further pre-reg attempt at this claim.
4. Log the calibration miss publicly here so it's not pretended away.

### 2.3 Amendment A1-T6 (exploratory, NOT pre-reg)

**Spec:** Take all 99,999 nearest-neighbor unfolded spacings (Odlyzko unfolding s_n = (γ_{n+1} − γ_n)·log(γ_n/(2π))/(2π)). KS-test against the 2×2 GUE Wigner surmise CDF.

**Result:** KS = 0.0193, p = 1.18 × 10⁻³². Mean unfolded spacing = 0.9999858 (perfect normalization).

**Interpretation (calibrated):** This is **not** a TI Sigma result. The 2×2 Wigner surmise is a small-matrix approximation; the exact large-N GUE level-spacing distribution differs by a small but measurable amount (Bohigas-Giannoni-Schmit 1984; Mehta 2004 Ch. 6). With N = 99,999, even a KS statistic of 0.019 reaches astronomical p-values purely by sample size. The qualitative finding — Riemann zeros follow GUE-like spacings — is consistent with established Hilbert-Pólya / Montgomery literature.

**Honest verdict for A1-T6:** the amendment confirms the well-known small approximation gap between the 2×2 Wigner surmise and exact GUE. It does NOT discriminate any TI Sigma claim from null. Reportable as exploratory; non-actionable for the corpus.

### 2.4 Amendment A2-T6 (exploratory, NOT pre-reg, very low power)

**Spec:** First 9 unfolded spacings (γ₁..γ₁₀) vs Wigner surmise CDF.

**Result:** KS = 0.181, p = 0.883. Consistent with GUE; no power.

**Honest verdict:** at n=9 the test is unpowered. Reportable; non-actionable.

### 2.5 What Brandon needs to clarify before T45-6 can be re-run as a real pre-reg

Pass-37 PD-final says "PD = Permissibility Distribution = (−3, 2), Perfect-Fifth-derived, Riemann-connected." For this to be operationally testable on Riemann zeros, one of the following coordinate-mappings (or an alternative) must be specified:

- **Option A (γ-coordinate):** PD support corresponds to Riemann zeros with imaginary part γ scaled into (−3, 2) by some normalization (e.g. (γ − 14.1347)/some-scale ∈ (−3, 2)). Specify the scale.
- **Option B (σ-coordinate):** PD support is the real-part shift σ − 1/2 ∈ (−3, 2). Trivially holds for all RH-respecting zeros (σ = 1/2). Test would be: ANY zero with σ ∉ {1/2} would refute RH and be in PD; this is a different empirical question.
- **Option C (log-density / unfolded coordinate):** PD support is a window in the unfolded zero-spacing distribution. Specify the unfolding.
- **Option D (Perfect-Fifth interval ratio):** PD = (−3, 2) refers to musical interval (3:2 = perfect fifth) rather than a Riemann coordinate at all. Then T45-6 is misframed and the Riemann claim needs separate operationalization.

Until one is chosen, the Pass-45 §6 test is **un-pre-registrable** in the strict sense. Brandon's call.

### 2.6 What this does NOT do

- Does NOT KILL the PD = (−3, 2) Riemann claim. The literal test was vacuous, not negative.
- Does NOT CONFIRM the claim either. The amendments are exploratory by their own labels.
- Does NOT vindicate Pass-38 §F-2 disconfirm of the prior PD-Riemann form (that disconfirm stands on its own data).
- Does NOT detract from Pass-37's internal canonical re-framing (which is a definitional move, not an empirical one).

---

## §3 — Combined session disposition

| Test | Status | Cost | Real-HW? | Verdict |
|---|---|---:|:---:|---|
| T45-2 qc26 GHZ-5 Mermin | EXECUTED | $0 | ✓ ibm_marrakesh | **CONFIRM** ( |M₅| = 14.54 ≫ 4.44 ) |
| T45-6 PD-Riemann literal | EXECUTED | $0 | n/a | **INDETERMINATE_VACUOUS_FILTER** + spec-clarification request |
| T45-6 A1-T6 amendment | EXECUTED, exploratory | $0 | n/a | small approximation gap, non-actionable |
| T45-6 A2-T6 amendment | EXECUTED, exploratory | $0 | n/a | unpowered |

**Pass-45 progress:** 2 of 8 tests resolved (T45-2 CONFIRMED, T45-6 LITERAL INDETERMINATE).
**Remaining open:** T45-1 (Mendi 5-session), T45-3 (GM-Node disc. validity), T45-4 (MR Truth κ), T45-5 (BPS RR by 2026-06-10), T45-7 (DPES n=30), T45-8 (AA pilot N=15).

## §4 — Open items for Brandon

- **(p46-A)** Clarify PD = (−3, 2) coordinate mapping per §2.5 above. Once specified, re-run T45-6 as a real pre-reg.
- **(p46-B)** Optional: increase qc26 shots and/or run on a different IBM backend to tighten the 91% → 95%+ fidelity bound. Free-tier still OK; would take another ~10 minutes.
- **(p46-C)** Decide whether to schedule T45-3 + T45-4 (LLM-rater work) for next agent session — both are agent-side and could be batched in one ~3-4 hour session if Brandon green-lights.
- **(p46-D)** All 7 remaining Pass-45 tests + 14 carry-overs (p38-A through p43-D) → 21 open items. Triage recommended.

## §5 — Anti-HARK provenance

- Both runners' SHA256 frozen at commit time and logged in their respective `results.json` files.
- T45-2 thresholds frozen by Pass-45 commit (4 + 3σ_M); 71σ violation leaves no room for cherry-picked re-analysis.
- T45-6 amendments labelled EXPLORATORY_NOT_PREREG explicitly; their results do NOT count toward Pass-45 §6 verdict per Pass-45 §11.
- This paper written **after** results inspection, but verdicts mechanically follow the pre-registered thresholds — no room for HARKing.

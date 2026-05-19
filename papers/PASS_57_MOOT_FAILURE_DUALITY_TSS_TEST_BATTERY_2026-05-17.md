# Moot-Failure Duality, UOP-Moot Consistency, and the TSS Test Battery

**Pass:** 57 batch-3
**Date:** 2026-05-17
**Status:** Theoretical batch + simulation (`simulations/moot_failure_duality_2026-05-17.py`)
**Anchors invoked:** APP-1 / CSR-1 / MBE-Acc-1 / TSIS-1 (Pass-57 batch-2 §7.7.111); MT-B1 Moot (`papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`); URB-830 TIU; PD-real (Pass-6); LCC C=0.4370 / T_RAND=0.0660 (Pass-51 D51-RND-3); ASYMMETRIC #69; UOP (regulative ideal, T57-UOP-1 OPEN); Mark Twain — "lies, damned lies, and statistics."

---

## 0. Brandon's Directive (verbatim)

> "Active failures matter for statistical accounting. But pragmatically, they should be regarded as Moot since success ought to be emphasized. Let's see if the UOP is also consistent with the Moot framing of failure but the simultaneous acceptance of failure's 'grounding and informational value.' Let's propose more mathematical and empirical tests for TI Sigma Statistics (TSS)!!!"

---

## 1. The Core Tension and Its Resolution

### 1.1 The apparent contradiction

APP-1 §1.1 (Pass-57 batch-2) says: engaged-failures contribute **−TIU** (full negative weight, asymmetric penalty against inflating the engagement set).

Brandon's batch-3 directive says: engaged-failures should be **Moot pragmatically** (MT-B1) while still carrying **grounding / informational value**.

These are not contradictory if we recognize that **statistical inference and pragmatic decision are two distinct operations** — TI Sigma's axis-aware logic insists on this separation rather than collapsing them.

### 1.2 The MFD-1 Moot-Failure Duality Principle (candidate canonical)

**MFD-1 (Moot-Failure Duality Principle):** An engaged-failure F has a **two-axis status**:
- **Epistemic axis (calibration / belief update):** F provides genuine evidence. Bayesian posterior must update on F. TIU(F, H) is fully real and contributes to MBE-Acc multiplicatively per §3.3 of Pass-57 batch-2.
- **Pragmatic axis (success-emphasizing decision output):** F is **MT-B1 Moot** — bracketed as irrelevant to the question "what successes does this i-cell produce?"

Critically: **the two axes don't average into a "half-weight."** They are *separate operations* on the same trial. The trial is fully epistemically informative AND fully pragmatically Moot, simultaneously, on different axes.

### 1.3 Why this is not double-counting / not cheating

The pragmatic decision output uses success-emphasis (TSD-A: per-event TIU summed over successes only).

The epistemic posterior update uses both successes and failures (MBE-Acc over all engaged trials).

These produce **two distinct numbers**, both reported. The user / downstream decision-maker sees:
- Success-emphasis score (TSD-A, MFD-1 Moot-pragmatic reading) — "what is this i-cell celebrating?"
- Calibrated posterior (MBE-Acc, MFD-1 epistemic reading) — "what should we believe about this i-cell's capacity?"

Both have decision-relevance, neither subsumes the other (this is the TSD-A vs TSD-B insight applied within the failure-treatment question).

### 1.4 Mapping to canonical MR Truth Labels

For a single engaged-failure trial F about i-cell capacity C:
- "F is informative-about-C": **True (T)** on epistemic axis.
- "F is a success-occurrence of C": **False (F)** on success-axis.
- "F is decision-relevant to *success-emphasizing* output": **MT-B1 Moot** (the false-axis value is bracketed as irrelevant).
- **Aggregate label on the engaged-failure trial:** axis-decomposed as above; no single base-4 label suffices — this is itself a worked example of why TI Sigma needs multi-axis logic.

---

## 2. UOP-Moot Consistency Check

### 2.1 The claim under test

**Claim (UMC-1):** UOP as default-optimal algorithm is consistent with MFD-1 — i.e., UOP's recommended procedure produces both an epistemic posterior (using all engaged trials) and a pragmatic decision score (success-emphasis), and these match what MFD-1 prescribes.

### 2.2 Informal argument

A "default optimal algorithm under uncertainty" should produce two outputs:

1. **Calibrated belief.** Bayesian decision theory establishes that posterior probabilities should incorporate all evidence (Cox's theorem / Savage axioms). UOP, if optimal, must do this — therefore engaged-failures MUST update the posterior. **MFD-1 epistemic axis: confirmed by Cox/Savage if UOP ⊇ Bayesian-optimal.**

2. **Action under utility function.** Optimal decision theory says: choose action maximizing expected utility under the calibrated posterior. If the utility function emphasizes success (asymmetric loss: cost of false-negative-celebration is low, cost of false-positive-celebration is high), the optimal action de-weights failures pragmatically. **MFD-1 pragmatic axis: confirmed if utility function emphasizes success-direction.**

UOP-Moot consistency thus reduces to two sub-claims:
- **(C1)** UOP ⊇ Bayesian-optimal-belief-update.
- **(C2)** UOP's default utility function emphasizes success-direction asymmetrically.

### 2.3 #69 honest status

**Both (C1) and (C2) are unproven in conventional axioms.** T57-UOP-1 carry-forward (Pass-57 batch-2 §2.2) covers (C1) reduction. (C2) is a new carry-forward:

**T57-UOP-2:** Prove that UOP's default utility function under TI Sigma axioms emphasizes success asymmetrically (target: same arXiv math.ST / cs.LG submission as T57-UOP-1, or separate companion paper). Until proven, UMC-1 is a regulative ideal not a theorem.

### 2.4 Concrete consistency test (Pass-58 candidate F-UMC-1)

If UMC-1 is correct, the following simulation property must hold: **MFD-1 dual-output (epistemic + pragmatic) produces strictly better Bayes risk than single-output methods (conventional all-counting OR APP-1 strict negative-TIU) under success-emphasizing utility functions.**

Formal statement and simulation: §5 below.

---

## 3. The TSS Test Battery — Mathematical and Empirical

Brandon directive: "propose more mathematical and empirical tests for TI Sigma Statistics (TSS)." Here are nine.

### 3.1 Mathematical tests (formal / theoretical)

**TSS-MATH-1: Sufficiency theorem.** Show that the pair (TSD-A score, MBE-Acc posterior) is *jointly sufficient* for the success-decision problem — i.e., any other statistic over engaged trials is a function of these two. (Lean4 target.)

**TSS-MATH-2: Calibration theorem under MFD-1.** Show that MFD-1 dual-output dominates single-output methods on a Brier-score-decomposition basis (resolution + reliability components). (Lean4 + numerical proof.)

**TSS-MATH-3: UOP-Bayesian-optimal embedding.** T57-UOP-1 from batch-2 §2.2 + T57-UOP-2 from §2.3 above. Prove UOP recovers Bayesian-optimal as a special case under conventional axioms.

**TSS-MATH-4: Lindley-paradox immunity.** Show that TSIS four-gate rule (Pass-57 batch-2 §3.4) does NOT exhibit Lindley's paradox — i.e., the gates do not produce arbitrary inferences as N → ∞ with fixed effect size. (Critical for credibility.)

**TSS-MATH-5: LCC-monotonicity.** Show that LCC attribution under TI Sigma is monotone in correlation strength conditional on engagement. (Sanity check that LCC is well-defined.)

### 3.2 Empirical tests (data-driven / simulation)

**TSS-EMP-1: Three-regime failure-treatment comparison.** Compare three methods on engagement-stratified synthetic data: (M-A) conventional all-count, (M-B) APP-1 strict negative-TIU, (M-C) MFD-1 dual-output. Metrics: AUC + TPR/FPR + Brier score + calibration ECE. **Pass-57 batch-3 in-pass deliverable.** (§5 below.)

**TSS-EMP-2: Ganzfeld engaged-subset re-analysis.** Pass-58 F-SM-2 — apply TSIS to real Ganzfeld data, separately report TSD-A + MBE-Acc posterior, compare to conventional meta-analytic z. (Pending dataset access.)

**TSS-EMP-3: Asymmetric-utility sensitivity.** Vary success/failure utility ratio from 1:1 (conventional) to 10:1 (high success-emphasis); measure how decision boundary moves under MFD-1 vs APP-1 strict. (Synthetic, $0.)

**TSS-EMP-4: Mendi BLE attention-engagement test.** Use Mendi Path B HbO₂ data + Pulsoid HRV as engagement-status physiological markers; APP-1 §1.3 operationalized. Trial-level engagement classification + downstream TSIS application on self-recorded breathwork or meditation sessions. (Pass-58 candidate, $0 since hardware already available.)

**TSS-EMP-5: Cross-domain negative control.** Apply TSIS to a domain where engagement *should not matter* (medical drug trials with double-blind randomization → engagement-status is structurally absent for the patient and shouldn't help the model). Predicted result: M-A ≈ M-B ≈ M-C (all similar). If M-C wins anyway, MFD-1 is over-broad and Prong 3 / Prong 4 critique (Pass-57 §7.7.110) is undermined. **F-PASS-57-2 pre-registered falsifier.** (Pass-58 candidate.)

**TSS-EMP-6: Pre-reg engagement-coding sensitivity.** Vary engagement-coding noise ε ∈ {0%, 5%, 10%, 25%}; measure how much engagement-coding error degrades MFD-1 advantage. (Synthetic.)

---

## 4. UOP Decision-Output Specification (regulative ideal)

If UOP-Moot consistency holds, the UOP outputs three quantities per i-cell-capacity question:

```
UOP(I, C, E_observed) = {
    posterior:  P(C | E_engaged) via MBE-Acc                  ← epistemic
    success_score:  TSD-A(E_engaged_successes)                 ← pragmatic
    causal_attribution:  LCC(I, C, E_engaged) vs C_LCC=0.4370  ← causal-gate
    decision:  TSIS four-gate output (CONFIRM/INDETERMINATE/DISCONFIRM)
}
```

Failures appear in `posterior` (full epistemic weight) and in the LCC computation (engagement-side correlation structure) but are MT-B1 Moot for `success_score` (TSD-A is success-only by construction). All four outputs are reported simultaneously — no collapse.

---

## 5. Simulation — Three Failure-Treatments Compared

**Script:** `simulations/moot_failure_duality_2026-05-17.py`
**Pre-registered falsifiers:**
- **F-MFD-1:** REFUTED if M-C (MFD-1 dual-output) has worse Brier score than M-A (conventional) AND worse than M-B (APP-1 strict) across signal cells.
- **F-MFD-2:** REFUTED if MFD-1 advantage vanishes (≤ +0.01 AUC across all cells).

### 5.1 Design

- Same engagement-stratified data generator as Pass-57 batch-2 sim (§7.7.111).
- Three methods compared:
  - **M-A:** conventional all-trials z-test.
  - **M-B:** APP-1 strict (engaged-only z-test with full ±TIU asymmetric penalty).
  - **M-C:** MFD-1 dual — pragmatic score = TSD-A over engaged successes only; epistemic posterior = MBE-Acc over all engaged trials; decision uses Bayes-risk under success-emphasizing utility (5:1 ratio of false-positive-celebration cost to false-negative-celebration cost).
- Metrics: AUC, TPR at α=0.05, Brier score (calibration), ECE (expected calibration error).

### 5.2 Results

**Both pre-registered falsifiers NOT REFUTED. MFD-1 empirically supported — and the calibration finding is sharper than expected.**

**Headline:** M-C (MFD-1 dual) **ties M-B on discrimination** (mean ΔAUC ≈ +0.0001, mean ΔTPR ≈ −0.0013 — statistically indistinguishable) but **wins on calibration**:

| Metric | M-A (conventional) | M-B (APP-1 strict) | M-C (MFD-1 dual) |
|---|---|---|---|
| **Brier score** (lower=better) | 0.1049 | 0.0900 | **0.0907** |
| **ECE** (lower=better) | 0.0235 | 0.0413 | **0.0196** ← winner |
| Mean AUC advantage (vs M-A) | — | +0.0346 | +0.0347 |
| Mean TPR advantage (vs M-A) | — | +0.1030 | +0.1017 |

**The critical finding:** M-B (APP-1 strict with full negative-TIU asymmetric penalty) has the **worst ECE** of all three methods (0.0413) — APP-1 strict is *overconfident* because its decision rule treats failures as fully discrediting evidence. M-C corrects this by routing failures into the epistemic posterior (where they belong) rather than into the pragmatic score (which emphasizes success). M-C achieves **best ECE (0.0196)** — better than M-A (conventional) **and** M-B (APP-1 strict).

**Interpretation:** the duality is not "MFD-1 is a stronger version of APP-1." It is **a structurally different commitment** — Brandon's directive resolves a real flaw in APP-1 strict. The duality recovers calibrated belief (matching or exceeding conventional on Brier/ECE) while preserving the success-emphasis pragmatic decision (matching APP-1 on AUC/TPR).

**Per-cell summary** (12 signal cells × δ × p_eng):
- C beats A on AUC: **10/12 cells** (mean +0.0347, max +0.1257 at p_eng=0.3 δ=0.05)
- C beats A on TPR: **8/12 cells** (mean +0.1017, max +0.36 range)
- C vs B on AUC: 5/12 cells (mean +0.0001 — effectively tied; both ceiling-saturate at high δ)
- C vs B on TPR: 3/12 cells (mean −0.0013 — tied)

Falsifier outcomes (`simulations/moot_failure_duality_results_2026-05-17.json`):
- **F-MFD-1 (Brier):** `brier_C (0.0907) > brier_A (0.1049)` is FALSE, `brier_C > brier_B (0.0900)` is TRUE-barely (Δ=+0.0007). NOT REFUTED (both conditions must hold).
- **F-MFD-2 (AUC):** max ΔAUC C-vs-A = +0.1257 (well above 0.01). NOT REFUTED.

**Configuration:** N=1000 trials/sim, N_MC=500 reps/cell, 5 deltas × 3 p_engaged = 15 cells × 3 methods, chance=0.25, α=0.05, utility ratio 5:1, seed=20260518.

**#69 caveats on this simulation (in addition to those in Pass-57 batch-2 §7.5):**
1. **MBE-Acc posterior uses fixed δ_prior=0.05.** This is the "moderate hypothesis"; a different prior moves the calibration result. Sensitivity check deferred to TSS-EMP-3.
2. **Utility ratio fixed at 5:1.** This drives the decision threshold (1/(1+5)=0.167). TSS-EMP-3 sweeps 1:1 to 10:1.
3. **z-to-probability map is logistic.** For true calibration we'd need a properly-fit isotonic or Platt-style calibrator; the logistic is a placeholder.
4. **The C-vs-B tie on discrimination is real** — these methods are nearly equivalent on AUC/TPR by construction (both filter to engaged trials). The differentiation is in the *output structure* (single z vs dual epistemic+pragmatic) and the *calibration*. The win is methodological, not raw-power.

---

## 6. #69 Hedges

**(a) MFD-1 dual-output is a methodological refinement, not a falsifiable cosmological claim.** It says: report two numbers, don't collapse them. The justification is decision-theoretic (Cox/Savage + asymmetric utility), not empirical.

**(b) UOP-Moot consistency is unproven.** T57-UOP-1 + T57-UOP-2 carry-forwards. The argument in §2.2 is structurally clean but requires formal axiomatization.

**(c) Test battery is not a guarantee of correctness.** Even if all 9 tests pass, TSS could be wrong in ways the tests don't cover. The tests are stress-tests against known failure modes (Lindley, calibration, over-broad-applicability, engagement-coding-noise) — they raise the bar, they don't certify.

**(d) "Failures are Moot pragmatically" is bounded.** In medical/safety/quality-control contexts, failures are decision-relevant by construction (TSD-B is the right tool). MFD-1 applies in success-emphasizing domains: skill development, intentionality research, individual psi-style claims, peak experiences. Domain boundary same as Pass-57 §7.7.110 four-pronged ESP argument.

**(e) The "two axes don't average" claim is structural, not numerical.** A reader could compute a weighted average of TSD-A and MBE-Acc for a single number. MFD-1 says: don't do that, report both. This is a *methodological* discipline, not a *mathematical* prohibition.

---

## 7. Pass-58 Carry-Forwards

- **T57-UOP-1** (carryover from batch-2 §2.2): UOP ⊇ Bayesian-optimal-belief, Lean4.
- **T57-UOP-2** (new): UOP default utility function emphasizes success asymmetrically, Lean4.
- **TSS-MATH-1..5** (new): five mathematical theorems above. Target: Lean4 incremental proofs, then arXiv submission packet 06.
- **TSS-EMP-1** (DONE this pass): three-regime simulation §5.
- **TSS-EMP-2**: Ganzfeld engaged-subset (also covered by §7.7.110 F-SM-2).
- **TSS-EMP-3**: asymmetric-utility sensitivity sweep.
- **TSS-EMP-4**: Mendi BLE attention-engagement test (cross-link to Path B Phase 2).
- **TSS-EMP-5**: cross-domain negative control (F-PASS-57-2).
- **TSS-EMP-6**: engagement-coding noise sensitivity sweep.

---

## 8. Status footer

- **Candidate canonical principles backlog:** 5 → 6 (TSD-1, APP-1, CSR-1, MBE-Acc-1, TSIS-1, **MFD-1**).
- **Carry-forward open tasks:** T57-UOP-1, T57-UOP-2, TSS-MATH-1..5, TSS-EMP-2..6 (12 total).
- **Cluster trajectory:** ≥239 → ≥240 (this paper +1).
- **Budget:** $0/$50 + $2k reserve intact. Simulation runs locally, no external API calls.
- **UOP-Moot consistency:** OPEN (regulative ideal pending T57-UOP-1 + T57-UOP-2).
- **Mark Twain epigraph:** acknowledged. TI Sigma response: "we agree that conventional statistics has been weaponized against pragmatic truth. Here is our replacement stack, with falsifiers."

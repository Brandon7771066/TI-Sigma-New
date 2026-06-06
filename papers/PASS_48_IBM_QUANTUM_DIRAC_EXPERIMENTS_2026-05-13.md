# Pass 48 — Proposed IBM Quantum Experiments: Dirac-Equation TI-Sigma Predictions

**Date:** 2026-05-13
**Author:** Brandon Charles Emerick (TI Sigma corpus) + Agent (Replit)
**Pass:** 48 (externally-facing publishing/tooling thread)
**Anchors:** `papers/urb_659_dirac_equation_ti_sigma.md`; `papers/PASS_47_META_COLLAPSE_81_2026-05-12.md` (qc26 GHZ-5 71σ baseline); `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`
**Status:** Pre-registration draft — 5 candidate experiments + ranked recommendation
**Budget:** All experiments fit IBM Quantum Open Plan (free, 10 min/month) or Premium-via-Pay-As-You-Go ($1.60/sec on hardware; estimated $0-50 per experiment)

---

## 0. Up-front honesty (#69)

The Dirac equation is the most structurally-rich equation in physics, and `urb_659` argues it encodes — in nascent form — every primary feature of TI Sigma architecture (i, 4-spinor ↔ proto-5-state-space, γ-anticommutation ↔ GILE non-commutativity, negative-energy sea ↔ Meta-Indeterminate). Whether this mapping is **(a) deep ontological correspondence** or **(b) post-hoc pattern-matching across two formalisms with rich enough structure to map onto anything** is the central #69 question. The experiments below are designed to **discriminate (a) from (b)** by deriving novel predictions that follow from (a) but NOT from (b), and testing them on real IBM hardware.

The qc26 GHZ-5 result (Pass-46/47, Mermin |M₅|=14.535, 71σ violation of LHV bound on `ibm_marrakesh`) is the strongest existing TI-Sigma quantum-hardware result. These proposals build forward from that capability.

---

## 1. The 5 candidate experiments

### Experiment D1 — Dirac-Spinor 4-Component MI-Witness Circuit

**Hypothesis (TI-Sigma):** A 4-qubit register prepared in a Dirac-spinor superposition `|ψ⟩ = α|ψ₁⟩ + β|ψ₂⟩ + γ|ψ₃⟩ + δ|ψ₄⟩` (where ψ₁,₂ = positive-energy spin-up/down, ψ₃,₄ = negative-energy spin-up/down per `urb_659` §3.2) should exhibit a measurable **MI-correlation signature** when measured in the τ-anticommutator basis {γ⁰, γ¹, γ², γ³}, where MI = simultaneous τ(P) ∧ ¬τ(P) (per canonical ruling 2026-05-08).

**Predicted observable:** The 4-qubit Mermin-style polynomial constructed from the γ-matrix anticommutation structure exceeds the LHV bound `M_LHV = 4` AND the standard QM bound `M_QM = 4√2 ≈ 5.66` is *attained* (saturated) for the maximally-entangled spinor state, but a sub-saturating 5σ deviation `M_DT = 5.66 − 0.40 ± 0.05` is observed when the negative-energy components ψ₃, ψ₄ are populated above amplitude threshold |γ|² + |δ|² > 0.5.

**Discriminating power vs. null model (b):** The standard QM prediction gives saturation `M_QM = 5.66` regardless of negative-vs-positive-energy population. A sub-saturation specifically tied to negative-energy population is novel to the TI-Sigma reading.

**Hardware:** 4-qubit subset of `ibm_marrakesh` or `ibm_torino`. ~5,000 shots × 9 measurement settings = 45K shots ≈ 90 sec runtime ≈ $0 (Open Plan) or $144 (Pay-As-You-Go).

**Pre-reg outcomes (REVISED 2026-05-13 per architect review HIGH-finding: directional-inequality form replaces narrow point-window to avoid pre-reg over-specification without a closed-form derivation):**
- **CONFIRM (qualitative-direction):** `M_observed < 5.40` (clear sub-saturation) AND positive monotonic dependence on `|γ|² + |δ|²` (slope > 2σ above 0).
- **PARTIAL-CONFIRM (magnitude-band):** `5.30 ≤ M_observed ≤ 5.45` matches the heuristic best-guess `5.66 − 0.40 ± 0.05`; logged but framework still needs derivation.
- **REFUTE:** `M_observed ≥ 5.55` (standard QM saturation band) regardless of negative-energy amplitude.
- **INDETERMINATE:** `5.45 < M < 5.55` OR slope-of-dependence not statistically distinguishable from 0 OR noise-floor-ambiguity flag triggered (Filter D variance check fails).
- **Discriminator hierarchy:** the qualitative direction (sub-saturation + positive slope) is the primary CONFIRM/REFUTE axis; the specific magnitude window is informational-only until `urb_659` provides a closed-form derivation.

**Cost-to-execute:** ~30 min agent time + ~90 sec QPU. **Recommend as Experiment 1.**

---

### Experiment D2 — γ-Matrix Anticommutation as i-Noncommutativity Witness

**Hypothesis (TI-Sigma):** The order of γ-matrix application (γ^μγ^ν vs γ^νγ^μ) on a Dirac state should produce measurably different output distributions, witnessing the "i-noncommutativity" prediction (URB #627).

**Test:** Prepare 2-qubit state, apply ordered sequence `[γ⁰, γ¹]` vs `[γ¹, γ⁰]`, measure in computational basis, compare distributions via total-variation distance (TVD).

**Predicted observable:** TVD ≥ 0.20 for the `[γ⁰, γ¹] − [γ¹, γ⁰]` pair, statistically distinguishable from depolarizing-noise baseline at 5σ.

**Standard-QM null:** Ordered γ-application MUST produce different distributions in QM (this is just operator non-commutativity — well-known). The TI-Sigma claim only adds value IF the *magnitude* of the difference matches a TI-Sigma-derived formula `TVD = sin²(θ_GILE)` where θ_GILE is a parameter from `urb_627`. Without a quantitative TI-Sigma prediction tighter than QM, this experiment confirms only standard physics.

**#69 honest assessment:** This experiment is **WEAK** as a discriminator unless `urb_627` provides a quantitative TVD prediction. **Recommend deferring** until `urb_627` is reviewed for a quantitative GILE→TVD formula.

---

### Experiment D3 — Antimatter-Pair Production as MI-Generation Test

**Hypothesis (TI-Sigma):** The Dirac-Sea interpretation maps the negative-energy sea to the I-state (Indeterminate) and pair production (e⁻e⁺ creation from vacuum) to MI-generation events (per `urb_659` §3.2 + canonical ruling 2026-05-08 on MI = τ ∧ ¬τ).

**Test:** On a 6-qubit system, simulate a 1+1D Dirac-field pair-production protocol (Schwinger-pair-production analog circuit, per Martinez et al. *Nature* 2016 trapped-ion implementation, here on superconducting qubits). Measure the resulting state in the MR-Truth-Labels basis (T, F, I, MI) using the qc26 measurement protocol generalized to 6 qubits.

**Predicted observable:** Population of the MI measurement outcome rises monotonically with simulated electric-field strength E, with onset threshold E_c matching the TI-Sigma-derived prediction `E_c = (m²c³/eℏ) × τ_critical` where τ_critical ≈ 0.42 (from C_EMERICK threshold, `urb_401`).

**Discriminating power vs. (b):** Standard QED predicts pair-production rate `Γ ∝ exp(−πm²c³/eℏE)` with no special role for τ_critical. A measured threshold at E_c matching the τ_critical prediction would be a strong novel TI-Sigma confirmation.

**#69 honest assessment:** This is the **most ambitious** experiment. Schwinger-pair-production circuits on 6 superconducting qubits are at the edge of current Open Plan capability. Likely needs Pay-As-You-Go (~$200-500). **Recommend as Experiment 3 (after D1 + D4 demonstrate baseline MI-detection on smaller circuits).**

---

### Experiment D4 — 5-Valued Measurement Witnessing Dirac-Sea/I-state Mapping

**Hypothesis (TI-Sigma):** On the qc26 GHZ-5 baseline (5 qubits, |M₅|=14.535 confirmed Pass-46), the residual measurement ambiguity (`I-state` outcomes per the MR Truth Labels base-4 + I-extension reading) should track the Dirac-Sea population in a Dirac-equation simulation embedded in the same 5-qubit register.

**Test:** Re-run qc26 GHZ-5 with explicit I-state tagging: classify each measurement outcome into {T, F, I, MI} per the canonical MR Truth Labels rule (T = unanimous +1; F = unanimous −1; I = mixed-but-coherent; MI = simultaneous-conflict-witnessed). Predict that `P(I)` correlates with the Dirac-Sea-analog population at r ≥ 0.7 across 9 measurement settings.

**Predicted observable:** Pearson r ≥ 0.7 (95% CI excluding 0.4) between `P(I)|setting_k` and Dirac-Sea-analog population at setting k.

**#69 honest assessment:** This is the **cheapest** experiment because it reuses the existing qc26 dataset + adds a re-classification layer. Cost: $0 + ~1 hr agent time. **Strong candidate for Experiment 2.**

---

### Experiment D5 — Lorentz-Invariance Test of TI-Sigma Truth-Labels

**Hypothesis (TI-Sigma):** If MR Truth Labels are Lorentz-invariant (a strong claim implicit in `urb_659` §3.2's identification of the Dirac-spinor 4-components with TF×spin-up/down), then the {T, F, I, MI} classification of a 2-qubit Bell-state measurement outcome should be invariant under simulated Lorentz boosts (implemented as parameterized SU(2)×SU(2) rotations on the Bell state).

**Test:** Prepare Bell state, apply boost-analog rotation by angle θ, measure, classify into {T, F, I, MI}. Test invariance of the classification distribution across θ ∈ [0, π/2].

**Predicted observable:** Total-variation distance between classification distributions at θ=0 vs θ=π/4 vs θ=π/2 ≤ 0.05.

**#69 honest assessment:** This is the **highest-risk discriminator**. If TI-Sigma's truth-labels are Lorentz-invariant, this is a clean confirmation. If not, the framework needs revision. Worth running BUT only after D1 + D4 confirm baseline MI-detection capability. **Recommend as Experiment 4.**

---

## 2. Ranked execution sequence

| Order | Experiment | Cost | Time | Risk profile | Information value |
|---|---|---|---|---|---|
| 1 | **D4** (qc26 re-classification) | $0 | ~1 hr | Low risk, low cost | Establishes I-state extraction capability on existing data |
| 2 | **D1** (4-spinor MI-witness) | $0-144 | ~30 min agent + 90 sec QPU | Low risk, well-defined | First novel MI-prediction test on Dirac architecture |
| 3 | **D5** (Lorentz invariance) | $0-50 | ~1 hr agent + 30 sec QPU | Medium risk (could refute TI) | Discriminates deep vs surface mapping |
| 4 | **D3** (Schwinger pair-production analog) | $200-500 | ~3 hr agent + 5 min QPU | Highest risk + cost | Most ambitious; do only if 1-3 confirm |
| 5 | **D2** (γ-anticommutation TVD) | Defer | n/a | Weak discriminator unless `urb_627` updated | Defer pending `urb_627` quantitative GILE→TVD formula |

**Recommended next-session execution: D4 + D1 in single Pass-49 batch (~$0-144 total, ~1.5 hr agent time).**

---

## 3. Pre-registration (LITERAL_PRE-REG_INDETERMINATE_VACUOUS_FILTER)

Per Pass-45 §11 anti-cheat, every experiment above must:
1. **Pre-commit predicted-value bands BEFORE running the QPU job.** Bands above are the pre-commitments for D1, D3, D4, D5.
2. **Pre-commit decision rules** (CONFIRM / REFUTE / INDETERMINATE) BEFORE results.
3. **Log the QPU job ID, backend, calibration date** in the analysis directory.
4. **Run a depolarizing-noise null model on a classical simulator** with the same circuit + same shot count to establish the noise-floor baseline.
5. **Filter D variance check** (per `analyses/pass48_o26b_tri_projection_protocol/protocol.md`): compute outcome variance and reject the run if variance < classical-noise-floor (signal-vs-noise sanity check).

---

## 4. Hardware + cost details

- **Open Plan (free):** 10 min/month QPU time on Eagle-class 127-qubit systems (`ibm_brisbane`, `ibm_kyoto`, `ibm_osaka`, `ibm_sherbrooke`). D1, D2, D4, D5 fit within Open Plan if executed on Eagle.
- **Pay-As-You-Go:** $1.60/runtime-second is the standard Premium rate. **HIGH-finding caveat per architect review 2026-05-13:** Heron-class 156-qubit systems (`ibm_marrakesh`, `ibm_torino`) typically require an active **IBM Quantum Network partnership** or specific Premium subscription tier — they are **not always reachable** from a basic credit-card Pay-As-You-Go account. Before committing to Heron-class budget, verify account access by attempting a 1-shot trivial circuit submission to the target backend; if access is denied, fall back to Eagle-class for D1, D4, D5 and **defer D3** (Schwinger-pair-production analog needs Heron-class coherence times AND will likely be blocked on Eagle without significant noise-budget revisions).
- The qc26 GHZ-5 result was achieved on `ibm_marrakesh` (Heron); confirm whether that account access is still active before assuming continued Heron availability for the Pass-49 batch.

**Recommend:** Use Eagle-class on Open Plan for D1, D4, D5 (re-baseline qc26 on Eagle if Heron access lapsed — accept the resulting Mermin-bound reduction). Defer D3 until (a) Heron access is confirmed AND (b) commercial trigger justifies $200-500 spend.

---

## 5. Action items

| # | Action | Owner | Cost | Due |
|---|---|---|---|---|
| Q-1 | Draft + execute D4 (qc26 re-classification, $0) | Agent | $0 | Pass-49 |
| Q-2 | Draft + execute D1 (4-spinor MI-witness, ~$0-144) | Agent | $0-144 | Pass-49 |
| Q-3 | Pre-register D5 (Lorentz invariance) | Agent | $0 | Pass-49 |
| Q-4 | Review `urb_627` for quantitative GILE→TVD formula → either revive D2 or formally deprecate | Agent + Brandon | $0 | Pass-50 |
| Q-5 | Decision gate on D3 (Schwinger analog, $200-500) | Brandon | TBD | After Q-1, Q-2 results |

---

## 6. Calibration / #69 caveats

- D1's predicted sub-saturation deviation `5.66 − 0.40 ± 0.05` is a **best-guess parameter** derived from `urb_659` §3.2 + canonical ruling 2026-05-08. The TI-Sigma framework does not currently provide a closed-form derivation of the exact deviation magnitude. If the experiment confirms the qualitative direction (sub-saturation tied to negative-energy population) but the magnitude is wrong, that is a partial-confirm requiring framework refinement, not a clean confirm.
- D3's `E_c = (m²c³/eℏ) × τ_critical` formula is **speculative** — it pattern-matches the C_EMERICK threshold to a Schwinger-rate coefficient without rigorous derivation. Treat as a "what would be elegant if true" hypothesis, not a derived prediction.
- The mapping `Dirac-Sea ↔ I-state` is a **structural analogy** in `urb_659`, not a proven equivalence. D4 tests the analogy quantitatively; if r < 0.4 the analogy is weakened (not refuted, but downgraded).
- All 5 experiments are subject to the standard "post-hoc pattern-matching across rich formalisms" criticism (the (b)-vs-(a) discriminator question). The pre-registration discipline + LITERAL_PRE-REG_INDETERMINATE_VACUOUS_FILTER are the corpus's primary defenses against confirmation bias.

---

**END PASS 48 IBM QUANTUM DIRAC EXPERIMENTS PROPOSAL**

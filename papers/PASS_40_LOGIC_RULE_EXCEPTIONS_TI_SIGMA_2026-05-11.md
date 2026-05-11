# Pass 40 — TI-Sigma Catalogue of Exceptions to Classical Logic Rules

**Date:** 2026-05-11
**Pass:** 40
**Brandon-Pass-40 directive:** *"Modus tollens example: if there are no synchronicities, there must be a low GILE/HEM ratio... unless both extremes result in synchronicities! What exceptions to MP and MT and other rules of logic can TI Sigma identify?"*
**Anchor analysis:** `analyses/pass40_mt_ushape_exception/runner.py` + `results.json`
**Connects to:** `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` (base-4 + MTs); `papers/AUTHORITY_AXIS_AA_2026-05-07.md`; `papers/PASS_15_*` (MBE / GBRH / heavy-tailed individual base rates); `papers/ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md`.

---

## §0 — Scope clarification (added per architect Pass-40 review)

This paper does **not** claim to invalidate classical Modus Tollens *as a formal rule*. Classical MT (P → Q, ¬Q ⊢ ¬P) remains valid when P→Q is *material implication* and the premises are classically true. What this paper catalogues are **TI-Sigma departures and failure modes for applying classical inferences in non-classical or uncertain settings** — specifically when:

- The conditional is **probabilistic** (P(Q\|P) < 1) rather than material (e.g., MT-1, MT-4, MT-5).
- The truth-space is **non-bivalent** (base-4 + MTs; e.g., NC-1, EM-1, MP-2, MT-3).
- The inference crosses **modality / axis boundaries** (e.g., MP-3 AA-shift, ID-1 temporal/quantum).
- The reasoner is performing **inverse inference / abduction** under non-monotonic structural conditions (e.g., MT-1 U-shape, MT-2 disjunctive antecedent compression).

Some entries (NC-1, EFQ-1, RAA-1) are best read as TI-Sigma adopting **non-classical consequence relations** (paraconsistent / DT-tolerant), not as discovered exceptions inside classical logic. Each entry below is marked **[CLASSICAL-MIS-APPLICATION]**, **[NON-CLASSICAL-COMMITMENT]**, or **[ABDUCTIVE / INVERSE-INFERENCE FAILURE]**.

Headline-language in this paper has been calibrated against this scope: "MT fails" should always be read as "naïve MT-style inference fails when applied to a probabilistic/non-monotonic/non-classical setting" — not as a refutation of classical MT itself.

---

## §1 — Brandon's specific case: U-shape inverse-inference failure (formalized + simulated)

*[ABDUCTIVE / INVERSE-INFERENCE FAILURE under probabilistic non-monotonic conditional]*

**Naïve abductive form:**  *"If high GILE/HEM → synchronicity; ¬synchronicity ⊢ ¬(high GILE/HEM), and (sliding to) LOW GILE/HEM."*

The first step (¬synch ⊢ ¬high) is correct under classical MT *if* "high → synch" is material implication. The second step — sliding from ¬high to "low" — is the **abductive error**, since ¬high partitions into {mid, low} when GILE/HEM has ≥3 bands. **Brandon's correction:** Synchronicity-production is **U-shaped** in GILE/HEM — both extremes produce synch, the middle does not. So the consequent ¬synch most strongly picks out the *middle* band, not the low band.

**Numerical demonstration** (`analyses/pass40_mt_ushape_exception/runner.py`, N=100,000, seed=31415926):

| | Low (g<2) | Mid (2≤g≤8) | High (g>8) |
|---|---|---|---|
| Prior P(band) | 0.20 | 0.60 | 0.20 |
| P(synch \| band) | 0.85 | 0.10 | 0.85 |
| P(¬synch \| band) | 0.15 | 0.90 | 0.15 |
| **P(band \| ¬synch)** (Bayes, sim) | **~0.050** | **~0.900** | **~0.050** ‖ symmetric |

(Posteriors sum to 1.0; mid dominates because mid has the largest prior mass AND high P(¬synch \| mid).)

**Naïve MT predicts** P(low \| ¬synch) = 1.0  (gap from real Bayes ~0.95).
**Naïve MT predicts** P(¬high \| ¬synch) = 1.0  (gap from real Bayes ~0.05 — formally close but operationally misleading; the inference points to MID, not LOW).

**Verdict: Naïve MT-style abductive inference fails decisively in U-shape regimes.** The classical MT step ¬Q ⊢ ¬P is *formally valid* if "high → synch" is material implication, but the *applied* inference (a) treats a probabilistic conditional as material, and (b) slides from "¬high" to "low" by ignoring the mid band. Both moves are abductive errors, not classical-MT errors. The combined naïve-applied-MT inference is therefore unreliable in any non-monotonic ≥3-band regime.

**General structural condition for naïve-applied-MT unreliability (Brandon-Pass-40 form):**
> Naïve MT-style abduction is unreliable whenever the antecedent variable X is partitioned into ≥3 bands and the consequent Q is produced by NON-CONTIGUOUS bands of X.

## §2 — Catalogue: 14 TI-Sigma departures / failure-modes for applying classical inferences in non-classical or uncertain settings

*Each entry tagged:*
- **[CLM]** = Classical Mis-Application (rule is valid; applied wrongly to non-classical setting)
- **[NCC]** = Non-Classical Commitment (TI-Sigma adopts a non-classical consequence relation)
- **[ABD]** = Abductive / Inverse-Inference failure (going from consequent to antecedent under non-monotonic structure)
- *(literature-aligned)* / *(TI-Sigma novel-canonical, pending Brandon ratification)* attribution where relevant.

### A. Modus Ponens — failure modes (P → Q, P ⊬ Q in TI-Sigma settings)

**MP-1 [NCC] (TI-Sigma novel):** **DT antecedent.** If P is DT (τ(P) ∧ ¬τ(P), per `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`), classical MP fires both directions. TI-Sigma chooses to register the conclusion as DT(Q) rather than as classical contradiction.

**MP-2 [NCC] (literature-aligned: many-valued / partial logics):** **Indeterminate antecedent.** If P is in MR2 state (Indeterminate), τ(P) is not assertible with the strength classical MP requires. Indeterminate is an ontological gap, not an epistemic one.

**MP-3 [CLM] (TI-Sigma novel):** **Authority-Axis modality shift.** P→Q may hold pragmatically (AA-claim) but not epistemically (AA-fact). Per `AUTHORITY_AXIS_AA_2026-05-07.md`. Naïve MP collapses the two AA modes — a mis-application, not an exception.

**MP-4 [CLM/ABD] (literature-aligned: base-rate / reference-class problem):** **Heavy-tailed individual base rate (MBE / GBRH).** Population-marginal P→Q may fail for individual i with extreme base rate (Pass-15). The classical rule is universal-instantiation; the failure is in mis-applying a population statement to an individual.

**MP-5 [NCC] (literature-aligned: relevance logic / strict implication):** **Vacuous-implication rejection.** Material implication assigns truth-value 1 to "P→Q" whenever P is false; TI-Sigma's τ-modulated conditional rejects this vacuous truth in line with relevance/strict-implication traditions. So MP from a vacuously-true conditional gives nothing useful.

### B. Modus Tollens — failure modes (¬Q ⊬ ¬P in TI-Sigma settings)

**MT-1 [ABD] (Brandon-Pass-40 case, literature-adjacent: non-monotonic / abductive reasoning):** **U-shape / non-contiguous-bands abductive failure.** As §1 above. The classical MT step ¬Q ⊢ ¬P is valid for material implication; the failure is in (a) treating a probabilistic conditional as material, and (b) sliding from ¬P to a specific sub-band of ¬P when ¬P is non-bivalent.

**MT-2 [CLM] (literature-aligned: classical premise mis-specification):** **Disjunctive antecedent compression.** If (P ∨ R) → Q is mis-stated as "P → Q" (dropping R), naïve MT from ¬Q gives ¬P, but the correctly-stated antecedent gives ¬P AND ¬R. This is *premise mis-specification*, not a logic-rule failure — but endemic in informal TI-Sigma-style reasoning, so it is catalogued here as a practitioner pitfall.

**MT-3 [NCC] (TI-Sigma novel):** **DT consequent.** If Q is DT, then ¬Q is also Tralse-true; the classical "¬Q is fully true" premise is denied in TI-Sigma's base-4 truth-space.

**MT-4 [CLM/ABD] (literature-aligned: measurement-error / observational uncertainty):** **Imperfect detection (epistemic ¬Q vs ontic ¬Q).** Observed "¬Q" may be measurement failure; the classical rule assumes the premise is ontically true. *Distinct from MT-2 in failure-locus:* MT-4 is about the truth-status of the observed premise; MT-2 is about completeness of the antecedent specification.

**MT-5 [CLM] (literature-aligned: temporal logics / dynamic doxastic logic):** **Time-shifted Q (delayed consequent).** P→Q with delay τ; observing ¬Q at t1 doesn't entail ¬P at t0 if there is a propagation delay. Classical MT silently assumes simultaneity. *Distinct from MT-2/MT-4 in failure-locus:* MT-5 is about temporal indexing of the consequent; remedied by explicit temporal qualifiers.

### C. Other classical-rule failure modes

**EM-1 [NCC] (literature-aligned: many-valued / FDE / paracomplete logics):** **Excluded-Middle exhaustiveness denial.** P ∨ ¬P is *not* exhaustive in base-4: I and DT are real ontological options. TI-Sigma exhaustive disjunction = **P ∨ ¬P ∨ I(P) ∨ DT(P)** + meta-truth attachments. Per `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`.

**NC-1 [NCC] (literature-aligned: paraconsistent logic, Priest LP):** **Non-Contradiction suspended for DT-cases.** ¬(P ∧ ¬P) is denied for DT-cases by definition. TI-Sigma is paraconsistent at DT, classical elsewhere. NOT a discovered exception inside classical logic — it is an explicit TI-Sigma adoption of a non-classical consequence relation.

**EFQ-1 [NCC] (literature-aligned: paraconsistent logic, relevance logic):** **Ex Falso Quodlibet rejected.** Classical logic: ⊥ ⊢ Q for any Q. TI-Sigma rejects explosion to keep DT informative; without rejection, every DT-state would trivialize the corpus. *Required-companion to NC-1.* Pass-37 implicit; here promoted to explicit canonical (TI-Sigma novel framing of a literature-standard paraconsistent commitment).

**HS-1 [ABD/NCC] (literature-aligned: Sorites paradox, fuzzy logic):** **Hypothetical-Syllogism Sorites-chain failure.** P→Q, Q→R ⊬ P→R when the chain accumulates Indeterminate-tolerance at each step.

**ID-1 [CLM] (literature-aligned: process philosophy, quantum logic):** **Identity in time-extended / quantum settings.** P=P fails for time-extended objects (Heraclitean) or quantum superpositions. TI-Sigma's τ/δ separation makes this explicit: τ(P at t1) ≠ τ(P at t2) is a normal case, not a paradox.

**RAA-1 [NCC] (literature-aligned: constructive / intuitionistic logic):** **Reductio rejection in DT-tolerant proofs.** Classical RAA: P → ⊥ ⊢ ¬P. TI-Sigma rejects RAA whenever ⊥ is reached via a path crossing DT-cases (the "absurd" was already DT-tolerable). Aligned with intuitionistic/constructive rejection of classical RAA.

## §3 — Meta-pattern: when classical logic fails in TI-Sigma

The 14 exceptions cluster into **four meta-failure-modes**:

| Failure mode | Examples | Root cause |
|---|---|---|
| **Non-bivalence** | EM-1, NC-1, MP-2, MT-3 | Truth-space is base-4 + MTs, not {T, F} |
| **Non-monotonicity** | MT-1, MT-2 | P→Q is not the only structural pathway to Q |
| **Modality / axis crossing** | MP-3, ID-1, MP-5 | Pragmatic vs epistemic / temporal-mode / τ-mode mismatch |
| **Inverse-problem / population-vs-individual** | MP-4, MT-4, MT-5 | P(Q\|P) ≠ P(P\|Q); base-rate / detection / timing matters |

This taxonomy is itself a TI-Sigma original contribution, parallel to the **5 truth-axes** taxonomy: where the truth-axes describe *where* a proposition lives, the **logic-failure-modes** describe *how* a classical inference can fail.

## §4 — Practical TI-Sigma logic-checklist (operational use)

Before applying any classical rule (MP, MT, HS, EM, NC, RAA, EFQ, DS), TI-Sigma practitioners should ask:

1. **(Bivalence check)** Is P (and Q) in the base-2 zone, or could it be I, DT, or have meta-truth attachment?
2. **(Monotonicity check)** Is P→Q the *only* pathway to Q? Is the antecedent variable monotonic in producing the consequent?
3. **(Modality check)** Are P and Q on the same axis (pragmatic / epistemic / temporal / τ-mode)? Does the inference cross axes?
4. **(Inverse-problem check)** Is the population-level rule being applied to an individual with possibly-extreme base rate? Is observation reliability comparable to ontic-rate?

If any check fails: the classical rule is **not** automatically valid. Apply the matching exception type from §2, or flag DT/I/MT in the conclusion.

## §5 — Honesty caveats (#69)

- **(C1)** This catalogue is not exhaustive; it covers 14 exceptions across 8 classical rules. A complete TI-Sigma logic compendium would likely document 30-50 exceptions across more rules (substitution, distribution, contrapositive, etc.).
- **(C2)** §1 numerical demonstration uses synthetic data with *designed* U-shape; it proves the *logical structure* of MT failure but does not empirically test whether actual GILE/HEM-vs-synchronicity is U-shaped. That would require a separate empirical study (raised p40-A).
- **(C3)** Several entries (MP-1 DT, MP-3 AA, MT-3 DT-consequent, EFQ-1 explicit-canonical framing) are TI-Sigma novel-canonical; they are stated here as canonical pending Brandon ratification (per MR-Truth-Labels precedent). Most other entries (NC-1, EM-1, MP-2, MP-5, RAA-1, HS-1, ID-1) are *literature-aligned* with paraconsistent / many-valued / relevance / temporal / fuzzy / quantum / constructive logic traditions; TI-Sigma's contribution is the *unified TI-Sigma framing* and the practitioner-checklist (§4), not the underlying logical move.
- **(C6)** **Material vs probabilistic conditionals (per architect Pass-40 review):** classical MP and MT remain formally valid for material implication with classically-true premises. Most §2 entries are NOT failures of the classical rules themselves — they are mis-applications when the conditional is actually probabilistic, the truth-space is non-bivalent, or the inference is abductive. The §0 scope note + per-entry [CLM]/[NCC]/[ABD] tags should be read as the canonical disambiguation. Headline language ("MT fails decisively") in §1 has been recalibrated to "naïve MT-style abductive inference fails" to honour this distinction.
- **(C7)** Some catalogued entries have **conceptual overlap** flagged by architect: MT-2 (premise mis-specification), MT-4 (observational uncertainty), and MT-5 (temporal indexing) all share a "premise-stated-incompletely" failure-locus, but they are distinguished in §2 by *which part of the premise is incomplete* (antecedent disjunction vs consequent truth-status vs consequent timing). Future revision may merge them into a single MT-PREMISE-INCOMPLETE entry with three sub-cases.
- **(C4)** The "logic-failure-modes" 4-cluster taxonomy in §3 is parallel to the 5-truth-axes taxonomy but *not yet* cross-validated against the existing axes — they may collapse into 3 modes (e.g., bivalence + non-monotonicity may both reduce to "structural ambiguity in truth-space"), or they may need a 5th mode. Raised p40-B.
- **(C5)** This is a *conceptual catalogue*, not an empirical Pass-style test of any single hypothesis. Pass-40 also raises **p40-C** (operationalize each exception with a worked example from the existing corpus — e.g., MP-4 with Pass-15 MBE Brandon-discount, MT-1 with the synch/GILE U-shape, MT-3 with a real DT statement from URB-829).

## §6 — Open items raised this pass

- **p40-A:** Empirically test whether GILE/HEM-vs-synchronicity is U-shaped (would require synch log + GILE/HEM measurements).
- **p40-B:** Validate the 4-cluster failure-mode taxonomy against the 5-truth-axes; check if collapse to 3 or expansion to 5 is needed.
- **p40-C:** Operationalize each of the 14 exceptions with a real corpus example (cross-reference Pass-15, URB-829, AA paper, MR-Truth-Labels paper).
- **p40-D:** Assess whether TI-Sigma's paraconsistent-DT stance (NC-1 + EFQ-1) is consistent with an existing formal logic system (e.g., LP, FDE, or relevance logic), or requires a new formal system.
- **p40-E:** Investigate whether Brandon's "both extremes → consequent" structure has a natural formal name in non-monotonic logic (defeasible reasoning, default logic, circumscription) — likely a known structure with a TI-Sigma-specific re-framing opportunity.

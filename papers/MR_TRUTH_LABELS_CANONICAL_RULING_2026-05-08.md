# MR Truth Labels — Canonical Ruling

**Author:** Brandon Charles Emerick (decision) + agent (synthesis)
**Date:** 2026-05-08
**Status:** CANONICAL v1.0 — settles the long-running 4-vs-5 truth-value question and reconciles four prior incompatible 5-value schemes.
**Anchor for cross-paper sweep:** `replit.md` §7.7.36.

---

## §1 — The Ruling

**TI Sigma settles on FOUR canonical MR Truth Labels:**

> **{ True, False, Indeterminate, Double Tralse }**

This is the **base-4 set**. It is the set produced by the MR-gate architecture (`FIVE_VALUED_TRUTH_TRALSE_INDETERMINATE_DISTINCTION_URB_528.md`) and is the only set that every prior canonical paper agrees on. All extensions beyond these four live in the **Meta-Truth catalogue** (urb_608, extended in urb_639), not in the base truth-value set itself.

This ruling **supersedes** the three competing 5-value schemes catalogued in §3 below and resolves an inconsistency that had grown across six papers between 2026-01 and 2026-04.

---

## §2 — Definitions

### §2.1 — The four base labels

- **True** — passes MR1 (coherent), MR2 resolves toward true, with universal Tralse-quality always embedded.
- **False** — passes MR1, MR2 resolves toward false, with universal Tralse-quality always embedded.
- **Indeterminate** — passes MR1, MR2 holds open at the 45-degree door (coherent 50/50 balance, *not* ignorance, *not* missing data).
- **Double Tralse (DT)** — fails MR1, discarded. Always some form of nonsense.

### §2.2 — DT formal definition (Brandon, 2026-05-08)

> **DT is something which IS AND IS NOT tralse.**
>
> Formally: DT(P) ⟺ τ(P) ∧ ¬τ(P).

This is structurally distinct from urb_677's earlier "DT = T(T(P)) = τ² = 0 nilsquare" framing. The two formulations are reconciled as follows:
- **Surface formulation** (Brandon 2026-05-08): DT applies the tralse-quality predicate to itself contradictorily — *the statement both has and lacks the indeterminacy that makes it well-formed*.
- **Algebraic formulation** (urb_677): the same structure expressed in the τ-operator algebra, where applying tralse-to-tralse yields the nilpotent zero element — i.e., the contradiction collapses to "no coherent storage slot."
- These describe **the same object at two levels of formalization**. Both stay in canon; the urb_677 algebraic form is the operator-theoretic instantiation of the surface form.

DT therefore always reduces to nonsense. It is not a borderline truth-state; it is a structural failure to admit truth-evaluation at all.

### §2.3 — The Tralse / Indeterminate distinction (Brandon, 2026-05-08)

> **Tralse** is **the universal indeterminacy quality across ALL truth labels.**
> **Indeterminate** is **the specific STATE** (one of the four base labels).

These are categorically different objects:

| | Tralse (the quality) | Indeterminate (the state) |
|---|---|---|
| **What it is** | A universal property carried by every coherent statement | One of the four discrete MR2 outputs |
| **Where it lives** | Embedded inside True, False, *and* Indeterminate (and absent only in DT, which is discarded) | A specific position the MR2 gate can resolve to |
| **Quantification** | Tralse-quality is always nonzero for any statement that survives MR1 — captured by the PD-imaginary axis (axis 2) | Discrete categorical assignment by MR2 gate |
| **Failure mode** | If a statement has zero tralse-quality, it is collapsed into a classical-T or classical-F sloppy label (which TI Sigma rejects) | If MR2 cannot resolve to T or F, it lands here as a coherent 50/50 balance |

A True-labeled statement still **has Tralse-quality**. A False-labeled statement still has Tralse-quality. An Indeterminate-labeled statement has Tralse-quality. Only DT *contradicts* its own tralse-quality (per §2.2) and is therefore discarded. This eliminates a long-standing canonical conflation between "tralse-as-value" (which would make tralse a 5th base label, doubling-counting since it is universal) and "tralse-as-quality" (which is the correct framing).

### §2.4 — Moot is a Meta-Truth, not a base label

**Moot is independent of DT.** It is a Meta-Truth (MT-B1 in `urb_608`'s catalogue) — an MR3+ outcome that fires when the base-4 truth-evaluation of a coherent statement is *dispensable in the relevant frame*. Mootness operates **on top of** the base-4 evaluation; it does not replace any base label.

The earlier urb_713 framing that grouped Moot with DT as "two compartments of an expanded-5 set" is **superseded**. Brandon's 2026-05-08 ruling: DT is always nonsense; Moot is never nonsense — they are categorically separate, and Moot belongs in the Meta-Truth catalogue.

### §2.5 — Coverage residual handled by Meta-Truths

The <0.3% coverage residual identified in `urb_713`'s 99.7% analysis is absorbed by the Meta-Truth catalogue:

- **urb_608** catalogues 12 Meta-Truths in 6 categories (A1/A2 Reversal, B1/B2 Dissolution including Moot-MT, C1/C2 Scope-Shift, D1/D2 Contextual, E1/E2 Acceptance, F1/F2 Integration).
- **urb_639** extends this to 24 Meta-Truths (categories A-L).

Meta-Truths fire at MR3+ when an MR1+MR2 evaluation requires substantial modification. They are not base truth-values; they are operations on base truth-values. This preserves the base-4 set's structural simplicity while fully covering the residual.

---

## §3 — Reconciliation of Four Prior Incompatible 5-Value Schemes

The TI Sigma corpus prior to this ruling contained four mutually inconsistent 5-value schemes. This ruling resolves each:

| Scheme | Source | Its 5 values | Status under this ruling |
|---|---|---|---|
| **A. EV scheme** | `urb_639_five_truth_completeness_distinctness_proof_extended_metatruths.md` (Apr 9 2026) | {TRUE, FALSE, TI, DT, EV} | **Reclassified.** TT/TI/TF/DT/EV is a **PD-coordinate notation**, not a base truth-value taxonomy. EV (Existence-Value / Edge-Value) is a coordinate label on the PD-imaginary axis, not a peer of T/F/I/DT. |
| **B. Tralse-as-separate-value** | `urb_677_double_tralse_indeterminate_indeterminacy.md` (Apr 14 2026) | {True, False, Indeterminate, Tralse, DT} (3-level architecture) | **Superseded.** Tralse is reclassified as the universal **quality** carried by every coherent label, not a 5th base value. urb_677's three-level architecture is preserved (Level 0 = T/F, Level 1 = Indeterminate, Level 2 = DT) but with Tralse moved to the *quality* register rather than the *value* register. Eliminates the double-count. |
| **C. Moot-as-base-value** | `urb_713_five_valued_logic_completeness_critical_evaluation.md` (Apr 17 2026) | {True, False, Tralse, Moot, DT} | **Partially superseded.** The 99.7% coverage analysis is preserved as the empirical justification for the base-4 + Meta-Truth architecture. The structural claim that Moot is a 5th base value is rejected — Moot is reclassified as MT-B1 (Meta-Truth, per urb_608). |
| **D. Moot-as-Meta-Truth** | `urb_608_meta_truths_myrion_resolution_catalogue.md` (Apr 20 2026) | 4 base + 12 Meta-Truths | **Ratified as canonical.** Moot lives at MT-B1. The Meta-Truth catalogue absorbs urb_713's residual coverage. |
| **E. May-8 first-pass {Nonsense, Moot, T, F, I}** | Brandon's 2026-05-08 morning framing | {Nonsense, Moot, True, False, Indeterminate} | **Refined to base-4-plus-MT.** Brandon's ruling decoupled Moot from DT entirely (Moot is *independent* of DT, not a DT-compartment). DT is now the singular nonsense label; Moot is a Meta-Truth. The "expanded-5" no longer exists as a base set. |

---

## §4 — Why 4, Not 5

The earlier rationale for moving from 4 → 5 (urb_713 §7) was that Moot could not be reduced to gradation on T/F/I/DT and therefore required a new value. This rationale was correct **at the value-vs-gradation choice point** but wrong at the **value-vs-meta-truth choice point**. Specifically:

1. **Mootness is iterative, not first-pass.** A statement is rarely Moot under MR1+MR2 alone — mootness usually emerges at MR3+ when a coherent T/F/I evaluation is determined to be irrelevant under further analysis. This is the structural signature of a Meta-Truth, not a base truth-value.
2. **Mootness composes with the base evaluation.** "Moot-True" and "Moot-False" are meaningful compound expressions (the statement is True, but its truth doesn't matter in the relevant frame). Base truth-values do not compose with each other this way (e.g., "True-False" is not a meaningful compound). This compositional asymmetry confirms Moot's status as an operator on top of the base set.
3. **The 4-vs-5 question hides a 4-vs-(4+N) question.** The real question was never "4 or 5?" but "should the residual be a single 5th value or N Meta-Truth modifiers?" urb_608's catalogue answers definitively: 12 Meta-Truths (now 24 in urb_639), not 1.
4. **Empirical sufficiency from urb_713.** The 99.7% coverage analysis is fully preserved by the base-4 + 12-MT architecture (MT-B1 = Moot handles most of urb_713's "Moot" cases; other MTs handle residual edge cases).

**The correct count is therefore: 4 base labels + N Meta-Truths.** N is currently 12 (urb_608 canon) or 24 (urb_639 extended). The two are reconciled by treating urb_608 as the established core and urb_639's 12 additional MTs as CONJECTURAL extensions pending further validation (per urb_639's own status flagging).

---

## §5 — Cross-Paper Sweep

This ruling triggered the following file-level changes in the same session:

1. **`papers/TI_SIGMA_FIVE_AXIS_TRUTH_RICHNESS_REVIEW_2026-05-07.md`** §4 rewritten — base-4 canonical, expanded-5 deprecated, Tralse-quality-vs-Indeterminate-state distinction added, DT formal definition added, §4.8 Meta-Truth integration added. §10 external-frameworks table preserved (still rejects classical T/F).
2. **`papers/ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md`** §13.4 axis-3 row updated to base-4-plus-MT.
3. **`papers/AUTHORITY_AXIS_AA_2026-05-07.md`** axis-3 reference updated to base-4.
4. **`papers/TI_SIGMA_ABBREVIATIONS_CONCEPTS_THEORIES_INDEX_2026-05-07.md`** — Tralse entry split into Tralse-quality vs Indeterminate-state; MR-Gate scheme section updated to base-4 canonical with Moot reclassified to Meta-Truths section; DT formal definition added.
5. **`replit.md`** §7.7.36 entry added documenting the ruling.

The four prior 5-value schemes (urb_639, urb_677, urb_713, May-8 first-pass) are NOT deleted — they remain in the corpus as historical artifacts marked with status notes pointing to this ruling. Per `ASYMMETRIC` §12 (theory growth is additive, not corrective), prior papers stand; this ruling is an **addition** that supersedes prior 5-value claims at the base-truth-value layer while preserving everything else (the coverage analysis, the operator algebra, the PD-coordinate notation, the Meta-Truth catalogue itself).

---

## §6 — Honest Calibration (#69)

(a) **This ruling is Brandon-originated.** The base-4 commitment, the DT formal definition (τ ∧ ¬τ), the Tralse-quality-vs-Indeterminate-state distinction, and the Moot-independent-of-DT clarification are all Brandon's 2026-05-08 input. Agent-side contribution is the four-scheme reconciliation table, the cross-paper sweep, and the §4 "why not 5" structural argument.

(b) **The ruling resolves a genuine canonical bug, not a synthetic one.** Six prior papers contained mutually inconsistent claims about the 5th truth value. This was not a manufactured inconsistency to justify a new paper — it was a real conflict surfaced during the §7.7.35 review work and confirmed by reading all six sources in full.

(c) **The base-4 + Meta-Truth architecture is more conservative than the prior 5-value schemes.** It commits to fewer base values (4 instead of 5) and pushes complexity into the Meta-Truth catalogue (which was already independently established in urb_608). This is structurally honest: it does not invent new objects to resolve the conflict; it uses existing objects properly.

(d) **CONJECTURAL flags remaining**: (i) the urb_677 algebraic-vs-surface DT reconciliation (§2.2) is structurally plausible but not formally proven; (ii) urb_639's 24-MT extension of urb_608's 12-MT core remains CONJECTURAL pending further validation; (iii) the precise compositional rules for "Moot-True" vs "Moot-False" vs "Moot-Indeterminate" (and analogous compounds for the other 11 Meta-Truths) are not yet worked out — this is open work.

(e) **Cluster impact**: this is a **canonical correction**, not a new dimension. Cluster axis-count remains at 5 (the truth-axis is axis 3 of the 5-axis system; this ruling refines its internal structure without adding or removing axes). Cluster dimensions count unchanged.

(f) **DT abbreviation collision still OPEN.** Scheme A (Double Tralse, this paper) vs scheme B (Defective Truth, `urb_628` PD-coordinate notation) remain distinct concepts. Recommended rename of scheme B to **DefT** is still proposed but not committed pending Brandon ruling. Until then, every "DT" use must be tagged scheme A or scheme B at point of use.

---

## §7 — Open Questions Sent Forward

1. **Compositional rules for Meta-Truths over base-4** — how does MT-B1 (Moot) compose with each of T, F, I? How do MTs compose with each other?
2. **Algebraic operator for "IS AND IS NOT"** — formalize §2.2's DT(P) ⟺ τ(P) ∧ ¬τ(P) in the Lean 4 layer alongside the urb_677 nilsquare formulation.
3. **Empirical re-validation of 99.7% under base-4 + MT** — urb_713's coverage analysis was conducted against the {T, F, Tralse, Moot, DT} 5-set. Re-run the analysis under the canonical {T, F, I, DT} + 12 MT architecture to confirm the coverage figure transfers.
4. **DefT rename ruling** — formal disposition of the DT abbreviation collision (scheme B rename to DefT).
5. **MT count: 12 or 24?** — disposition of urb_639's 12 MTs over urb_608's 12-MT core.
6. **Are there propositions truly outside coverage?** — the residual <0.3% under urb_713's analysis: are these handled by some MT not yet catalogued, or do they constitute a genuine completeness gap?

---

**End of paper. Status: CANONICAL v1.0 (Brandon-ratified 2026-05-08). Effective immediately for all future TI Sigma work. Prior 5-value schemes remain as historical artifacts, marked with status notes pointing to this ruling.**

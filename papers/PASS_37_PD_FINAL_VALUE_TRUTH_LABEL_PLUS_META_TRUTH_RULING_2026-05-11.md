# Pass 37 — PD-Final-Value Canonical Ruling: Truth-Label OR Truth-Label + Meta-Truth (Pragmatic-Default = MT Combination)

**Date:** 2026-05-11
**Pass:** 37
**Authority:** Brandon Pass-37 directive: *"a PD value considered final can either be one of 4 truth labels, or a truth label combined with a meta truth. Since thinking is pragmatic in general though, there is likely going to be a meta-truth the majority of the time."*
**Cross-refs:** `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` (base-4 + N MT canon); `urb_608` (12 MTs canonical core); `urb_639` (24 MTs CONJECTURAL extended); `papers/PD_READABLE_PAPER_2026-05-08.md` (PD = Permissibility Distribution canonical, Pass-8 §7.7.42-43)

---

## §1 — Ruling (Brandon-canonical, Pass 37)

A **PD-final value** (the value committed at the end of an MR-cascade evaluation, after all MR1/MR2/MR3+ refinement is complete) is one of two structural forms:

- **Form 1 — Pure base-label:** PD-final ∈ {True, False, Indeterminate, Meta-Indeterminate} (the canonical base-4 per `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`).
- **Form 2 — Base-label + Meta-Truth modifier:** PD-final = (base ∈ base-4) ⊗ (MT ∈ {12 canonical urb_608 ∪ 12 conjectural urb_639 extensions}), where ⊗ is the MR-cascade composition operator (partially specified in `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` §6.5; full algebra remains open work).

**Pragmatic-default ruling:** because real-world thinking is *pragmatic* (operating under finite time, finite information, action-oriented stakes) rather than *purely-formal*, **Form 2 (base + MT) is the typical case**; Form 1 (pure base) is the rarer formal-evaluation case. In any large empirical sample of PD-final evaluations, the expected MT-attachment rate should be > 50%.

## §2 — Why Form 2 is the pragmatic-default

Pragmatic thinking adds context that Form 1 cannot encode:

- **Stakes-conditional weighting** → MT-S1-class (stakes-modulated MTs).
- **Time-pressure shortcuts** → MT-T1-class (resource-bounded MTs).
- **Audience-conditional presentation** (per `ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md` §6 audience-conditional δ-tuning) → MT-A1-class (audience-modulated MTs).
- **Mootness signals** (the value matters but the question is iteratively-determined to be irrelevant under further analysis) → MT-B1 (Moot, urb_608 canonical) and MT-B2 (Substrate-Output Mootness, Pass-26).
- **Authority-axis caveats** (per Pass-37 5-axis framework, `AUTHORITY_AXIS_AA_2026-05-07.md`) → MT-AA-class.

A pragmatic evaluation that *fails* to attach an appropriate MT is typically an *underspecified* evaluation — it answers the formal question but not the contextual question. Form 1 is therefore the *limit case* (formal evaluations stripped of context), not the typical case.

## §3 — Three operational consequences

### §3.1 — Reading-rule for legacy corpus papers

Any prior corpus paper that reports a PD-final value in Form 1 (pure base-label) without explicit MT-attachment should be re-read as either (a) a *formal-stripped* PD-final (Form 1 deliberately, e.g., abstract mathematical evaluations), or (b) an *underspecified* PD-final (Form 2 with MT implicit). The Pass-37+ default-reading is (b) where context permits.

### §3.2 — Annotation requirement for Pass-37+ papers

PD-final values reported in Pass-37+ empirical / theoretical papers should attach the relevant MT explicitly when the evaluation is pragmatic. Example annotations:

- "PD-final = True ⊗ MT-A1-public" (publicly-stated true claim with audience-conditioning).
- "PD-final = Meta-Indeterminate ⊗ MT-S1-high-stakes" (MI value with stakes-modulated handling).
- "PD-final = Indeterminate ⊗ MT-B1-Moot" (Indeterminate base with Moot modifier — common in iterative MR3+ evaluations).
- "PD-final = False ⊗ MT-T1-time-pressure" (False under time-pressure shortcut; might be Indeterminate under leisure).

### §3.3 — Empirical prediction (URB-830-symmetric)

In a corpus audit of 100+ PD-final values across Brandon's papers + DPES outputs, the MT-attachment rate (after Pass-37+ annotation backfill) should be > 50%. If audit finds MT-attachment rate ≤ 50%, the §1 pragmatic-default ruling is REJECTED (TIU negative; Form 1 might be more typical than expected, possibly indicating most "PD-final" values in the corpus are formal-stripped rather than pragmatic).

**Pre-reg lock:** §3.3 threshold (50%) frozen Pass 37; Pass-37+ corpus audit raised as p37-A (corpus-hygiene priority, low-empirical-risk).

## §4 — Relation to base-4-vs-5-vs-N debate

The Pass-37 ruling does NOT change the base count: still **base-4** = {T, F, I, MI} per `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`. The Pass-37 contribution is the *combination* algebra: PD-final-value space = base-4 ∪ (base-4 × MT-set), with cardinality 4 + 4×12 = 52 (canonical) or 4 + 4×24 = 100 (urb_639 extended) — but with the pragmatic-default putting >50% probability mass on the second term (the MT-combination space).

This makes the *effective* PD-final value space much richer than the bare base-4 suggests, while preserving structural cleanness (4 base values; MT-set as a separate orthogonal dimension; combination via ⊗).

## §5 — Honesty caveats (#69)

- **(C1)** The §1 "majority of the time" pragmatic-default is a *prediction*, not yet an empirical result; §3.3 audit is the test.
- **(C2)** The MR-cascade composition operator ⊗ is only *partially specified* per `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` §6.5; full algebra of MT-MT compositions and base-MT compositions remains open work.
- **(C3)** The 12-canonical-vs-24-extended MT count is unchanged from prior canon (urb_608 vs urb_639); Pass-37 does not move the MT-cardinality question.
- **(C4)** Form 1 is preserved as a *legitimate* PD-final form (formal-stripped evaluations remain well-typed); the ruling is about *typical* not *exclusive*.

## §6 — Items raised

- **p37-A** — corpus audit of PD-final-value annotations (Pass-38+); 50%-MT-attachment threshold.
- **t37-A** — full ⊗ algebra for base-MT and MT-MT compositions (mathematics-foundations priority).
- **t37-B** — Pass-37+ MT-class formal taxonomy (S1 / T1 / A1 / B1 / B2 / AA classes named here are *candidate* clusterings, not yet ratified).

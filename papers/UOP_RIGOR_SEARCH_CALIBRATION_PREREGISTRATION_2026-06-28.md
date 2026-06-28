# UOP Rigor/Search Calibration — PRE-REGISTRATION (Part I, design locked before measurement)

**Date:** 2026-06-28
**Status:** PRE-REGISTRATION ONLY. This document fixes the hypothesis, the operational
definitions, the corpus, the analysis, and the decision rule **before any number is
computed**. The companion file
`papers/UOP_RIGOR_SEARCH_CALIBRATION_MEASUREMENT_2026-06-28.md` (Part II) reports the
result and may **not** alter anything specified here.
**Canon impact:** none. Candidate test only. **Principle count stays 79.** No workflow
restarts. This does **not** modify the book.

---

## 0. Honesty rails binding this test (stated up front)

- **#69 both ways.** If the measured ratio lands outside the predicted band, that is
  reported as a falsification of the calibration hypothesis *for this corpus/proxy* —
  not buried, not re-tuned.
- **UGI-1 generate→validate.** This is the *validate* leg. The hypothesis (r ≈ 1.81)
  was *generated* by ChatGPT's calibration note; here we attempt an **independent**
  check.
- **EVD-1.** A corroboration here is *graded evidence*, never proof. It would upgrade
  the Radiant Cap from "bare posit" to "posit with one corroborating proxy," nothing
  more.
- **No RH/Millennium claim. No moral-realism/free-will/normative-posit deductive
  claim.** This test is about an *empirical ratio in proof artifacts*, full stop.
- **The cap value itself remains a posit.** Both forks (Fork A midpoint 0.93233,
  Fork B Born-shaped √(1−e⁻²)=0.92987) are posited per
  `papers/RADIANT_CAP_FORK_B_BORN_SHAPED_CANONICAL_RULING_2026-06-27.md`. This test
  does not derive them; it tests one downstream prediction.

---

## 1. What is being tested, and why it could be circular

The B147 thirds form gives, for a domain with truth-importance `T_d`:

> `G* = 3·T_d − 1` (clamped to [0,1]).

ChatGPT's calibration note re-parameterizes `T_d` as a **rigor fraction** of math
problem-solving:

> `T_d = R / (R + S)`,  with `r ≡ R/S` (rigor-to-search), so `T_d = r/(1+r)` and
> `G* = (2r − 1)/(r + 1)`.

Inverting the canonical cap gives the prediction:

- Fork A (0.93233): `r* = 1.81`
- Fork B (0.92987, canonical): `r* = 1.803`
- **Pre-registered central target `r* = 1.80`, falsifier band `r ∈ [1.5, 2.2]`** (band
  taken verbatim from the calibration note).

**The circularity hazard (explicit).** B147 §A.3 warns in writing that "trading the
λ=2/e⁻² posit for a `T_d ≈ 0.644` posit … is **circular if `T_d` is picked to hit
0.93**." In the calibration note, `r = 1.81` was obtained by *solving*
`0.93233 = (2r−1)/(r+1)` — i.e. `0.93 → r`. To break the circle we must measure `r`
by a route that **never uses the cap**. The corpus below (Mathlib) was authored years
before, and in total ignorance of, the Radiant Cap; measuring tactic ratios in it
cannot be contaminated by the 0.93 target.

---

## 2. The commensurability fix (addresses the strongest objection)

A ratio `R/S` of two quantities in *different units* (e.g. "verification cost" in
seconds vs. "search cost" in candidates) is **not scale-invariant** — you can hit any
value, including 1.81, by choosing units. We therefore require **R and S in the same
unit**:

> **Unit = one tactic invocation in a finished Lean 4 proof.**
> `R` = count of tactic invocations classified **rigor/closing**.
> `S` = count of tactic invocations classified **search/exploratory**.
> `r = R / S` (dimensionless).

This removes the units degree-of-freedom. It does **not** remove the *taxonomy*
degree-of-freedom (which tactic is "rigor" vs "search"), which is now the dominant free
parameter and is therefore (a) pre-committed below and (b) stress-tested by
pre-registered sensitivity variants.

---

## 3. Corpus (locked)

- **PRIMARY corpus:** every `*.lean` file under
  `lean4_ns_uop_pass54_mathlib/.lake/packages/mathlib/Mathlib/` (the installed Mathlib
  library; ~4,633 files at survey time). Mathlib is community-authored formal
  mathematics with no connection to TI Sigma — the blind target.
- **SECONDARY corpus (reported separately, not pooled):** the repository's own
  hand-written Lean files (`lean4/`, `lean4_ti_sigma6/`, `lean4_ns_uop_pass54_mathlib/`
  top-level TI files, excluding `.lake/`). Reported only for contrast; the TI files are
  *not* used to decide the hypothesis (they could in principle be contaminated).
- **Exclusions:** Mathlib's own `.lake/` dependency tree below the Mathlib package,
  `Mathlib.lean` import-only aggregator if present, and any file with zero classified
  tactics.

---

## 4. Operational taxonomy (LOCKED — committed before any count)

Rationale: **rigor/closing** = tactics whose job is to *discharge or deductively
justify* a goal (verification work). **search/exploratory** = tactics that *branch,
restructure, introduce structure, or set up* the proof (search work). Tactic names
matched as whole words after stripping `--` line comments and `/- … -/` block comments.

**RIGOR class (R):**
`exact, exact?, rfl, simp, simp_all, simpa, ring, ring_nf, linarith, nlinarith,
norm_num, norm_cast, push_cast, omega, decide, positivity, field_simp, assumption,
trivial, tauto, gcongr, abel, linear_combination, polyrith, rw, rewrite, subst, congr,
calc`

**SEARCH class (S):**
`apply, refine, intro, intros, rintro, cases, rcases, obtain, induction, constructor,
use, by_cases, by_contra, contrapose, have, suffices, set, let, choose, generalize,
wlog`

Tactics not in either list are ignored (they contribute to neither R nor S).

**Pre-registered sensitivity variants** (the four most defensible re-classifications of
ambiguous tactics; each reported, none allowed to redefine PRIMARY):
- **S1:** move `have, suffices` from SEARCH → RIGOR (they assert justified
  intermediate claims).
- **S2:** move `rw, rewrite` from RIGOR → SEARCH (rewriting as exploration).
- **S3:** move `simp, simp_all, simpa` from RIGOR → SEARCH (automation as search).
- **S4:** drop `intro, intros, rintro` entirely (pure bookkeeping, arguably neither).

---

## 5. Analysis (LOCKED)

Compute, for the PRIMARY corpus, under PRIMARY taxonomy:
1. Corpus-aggregate `r = ΣR / ΣS`.
2. Per-file `r_i` distribution: median, IQR, and **fraction of files with
   `r_i ∈ [1.5, 2.2]`**.
3. The same aggregate `r` under each sensitivity variant S1–S4.

Report the SECONDARY corpus aggregate `r` separately for contrast only.

---

## 6. Decision rule (LOCKED)

- **Corroborated (weak, graded):** PRIMARY-taxonomy aggregate `r ∈ [1.5, 2.2]`
  **AND** `r` stays in [1.5, 2.2] across **at least 3 of 4** sensitivity variants
  (robustness). Interpretation: one independent proxy is *consistent with* r* ≈ 1.80 —
  EVD-1 graded support, not proof.
- **Falsified (for this proxy):** PRIMARY aggregate `r` outside [1.5, 2.2].
  Interpretation: the calibration hypothesis fails on the largest blind formal corpus
  available; report it plainly (#69).
- **Inconclusive / quantity ill-defined:** PRIMARY `r ∈ [1.5,2.2]` but the value
  **swings outside the band under ≥2 sensitivity variants**. Interpretation: `r` is
  too taxonomy-dependent to be a well-defined invariant — itself a substantive negative
  finding (the prediction isn't cleanly testable this way).

---

## 7. Validity threats acknowledged in advance (do not get to be excused later)

1. **Finished proofs hide the search that produced them (the deepest threat).** A
   completed Lean proof records the *verification surface*, not the live exploration,
   dead ends, and conjecture-generation that created it. So even a clean r ≈ 1.80
   describes the **artifact's** rigor/search mix, not the **process's**. This caps the
   strength of any positive result at "suggestive proxy," permanently.
2. **Survivorship (SPF-1).** Only *successful* proofs are in Mathlib. This is
   outcome-selection on the proof artifact; the ratio in *abandoned* attempts is
   unobserved. Per SPF-1 this is a legitimate-conditioning concern, flagged not waved.
3. **Two proxy hops.** Mathlib-tactic-ratio → formal-verification-effort →
   math-problem-solving rigor/search. Each hop loses fidelity.
4. **Taxonomy dependence.** Handled by §4 sensitivity + §6 inconclusive branch, but
   never fully eliminated.
5. **Keyword counting is approximate.** Whole-word matching after comment-stripping
   over- and under-counts (tactic combinators, `<;>`, macros, identifiers shadowing
   tactic names). Applied uniformly, so it biases level more than it biases the *ratio*
   — but it is not exact parsing. Stated, not hidden.

**Bottom line pre-committed now:** the *best possible* outcome of this test is a
graded, proxy-level corroboration that nudges the cap from "bare posit" toward
"posit with one consistent blind check." It cannot, and will not be allowed to, become
a derivation of the cap or a closure of anything.

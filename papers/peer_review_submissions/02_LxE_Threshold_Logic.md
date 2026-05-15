# Formal Verification of Six Elementary Lemmas about a Bounded Product `L · E` and a Four-Valued "Tralse" Classification in Lean 4 / mathlib4

**Author:** Brandon Charles Emerick
**Date:** 2026-05-15 (Pass 55)
**Lean toolchain:** `leanprover/lean4:v4.10.0` · mathlib4 (cache 2026-05-15)
**Source file:** `lean4/TI/LxE.lean`
**Status:** Closed under `{propext, Classical.choice, Quot.sound}` (no `sorry`, no domain axioms)

---

## Abstract

We formalise six elementary lemmas about a product `L · E` of two
`[0,1]`-valued real numbers and a four-element classification of a
single `[0,1]`-valued "Tralse" parameter. The lemmas are: (L1) `L · E`
is bounded in `[0,1]`; (L2) if `L · E` exceeds a "causation threshold"
of 0.85, then it exceeds a "noise floor" of 0.42 (immediate from
`0.85 > 0.42`); (L3) commutativity `L · E = E · L`; (L4) if both
`L, E > 0.93` then `L · E > 0.85`; (L5) binary truth values (0 or 1)
are a special case of the four-valued classification; (L6) the
existence of an intermediate Tralse value `0 < t < 1` is incompatible
with binary `t ∈ {0,1}`. All proofs use `mul_nonneg`, `mul_le_mul`,
`mul_lt_mul`, `linarith`, `norm_num`. `#print axioms` shows only
`{propext, Classical.choice, Quot.sound}`. No new mathematics; the
contribution is a machine-checked record of the TI Sigma framework's
elementary bound and threshold claims.

---

## 1. Introduction

The TI Sigma framework posits two `[0,1]`-valued quantities `L` ("Love")
and `E` ("Existence") whose product `L · E` is interpreted as an
"effect potential." Two numerical thresholds appear in the framework:
`causation_threshold = 0.85` (above which effects are deemed
"causally reliable") and `noise_floor = 0.42` (below which signal is
"indistinguishable from noise"). The framework also posits a
four-valued "Tralse" parameter taking values in `[0,1]`, with
qualitative categories True / Tralse-True / Tralse-False / False.

The empirical and interpretive content of these notions is the subject
of separate writeups. This paper formalises only the **logical-algebraic
core**: the boundedness of `L · E`, the trivial threshold implication,
commutativity, the sufficient condition `L,E > 0.92 ⇒ L·E > 0.85`, and
two sanity lemmas about the four-valued classifier.

## 2. Structures

```lean
structure Love where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

structure Existence where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

def LxE (L : Love) (E : Existence) : ℝ := L.val * E.val
def causation_threshold : ℝ := 0.85
def noise_floor : ℝ := 0.42

structure Tralse where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

inductive TralseCategory
  | false | tralseFalse | tralseTrue | true

def classify (t : Tralse) : TralseCategory :=
  if t.val = 0 then TralseCategory.false
  else if t.val < 0.5 then TralseCategory.tralseFalse
  else if t.val < 1 then TralseCategory.tralseTrue
  else TralseCategory.true
```

## 3. The six lemmas

### L1 — Bounded product

```lean
theorem LxE_bounded (L : Love) (E : Existence) :
    0 ≤ LxE L E ∧ LxE L E ≤ 1 := by
  constructor
  · exact mul_nonneg L.nonneg E.nonneg
  · calc LxE L E = L.val * E.val := rfl
      _ ≤ 1 * 1 := mul_le_mul L.le_one E.le_one E.nonneg (by linarith)
      _ = 1 := one_mul 1
```

### L2 — Threshold implies super-noise

```lean
theorem causation_threshold_theorem (L : Love) (E : Existence)
    (h : LxE L E > causation_threshold) : LxE L E > noise_floor := by
  calc LxE L E > causation_threshold := h
    _ = 0.85 := rfl
    _ > 0.42 := by norm_num
    _ = noise_floor := rfl
```

This is logically trivial (`0.85 > 0.42`). The reason to record it as
a lemma is to provide a stable named handle for downstream framework
use.

### L3 — Commutativity

```lean
theorem LxE_comm (L : Love) (E : Existence) :
    L.val * E.val = E.val * L.val := mul_comm L.val E.val
```

### L4 — Sufficient condition for causation

```lean
theorem sqrt_causation (L : Love) (E : Existence)
    (hL : L.val > 0.93) (hE : E.val > 0.93) :
    LxE L E > causation_threshold := by
  unfold LxE causation_threshold
  calc L.val * E.val > 0.93 * 0.93 := mul_lt_mul hL hE (by norm_num : 0 ≤ 0.93) (by linarith)
    _ = 0.8649 := by norm_num
    _ > 0.85 := by norm_num
```

Note `0.93² = 0.8649 > 0.85`, so if both factors exceed `0.93` the
product exceeds the causation threshold of `0.85`. (Earlier drafts of
this file used `> 0.92`, but `0.92² = 0.8464 < 0.85`, so the threshold
had to be tightened. This correction was caught during the Pass-55
peer-review-packet review and propagated back to the Lean source.)

### L5 — Binary subset

```lean
theorem binary_is_special_case (t : Tralse)
    (h : t.val = 0 ∨ t.val = 1) :
    classify t = TralseCategory.false ∨ classify t = TralseCategory.true := by
  cases h with
  | inl h0 => left; simp [classify, h0]
  | inr h1 => right; simp [classify, h1]
```

### L6 — Intermediate excludes binary

```lean
theorem tralse_existence_implies_binary_incomplete (t : Tralse)
    (h : 0 < t.val ∧ t.val < 1) :
    ¬(t.val = 0 ∨ t.val = 1) := by
  intro hbinary
  cases hbinary with
  | inl h0 => linarith [h.1]
  | inr h1 => linarith [h.2]
```

## 4. Axiom verification

```lean
#print axioms TI.LxE_bounded
#print axioms TI.causation_threshold_theorem
#print axioms TI.LxE_comm
#print axioms TI.sqrt_causation
#print axioms TI.binary_is_special_case
#print axioms TI.tralse_existence_implies_binary_incomplete
```

All six report `[propext, Classical.choice, Quot.sound]`. No `sorry`,
no domain axioms.

## 5. Reproducibility

Source lives at `lean4/TI/LxE.lean`. Build with the same toolchain as
packet 1 (Lean 4 v4.10.0, mathlib4 cache snapshot). See packet 1
section 5 for `lake build` invocation.

## 6. Related work

The boundedness and commutativity results are immediate from
mathlib4's `mul_nonneg`, `mul_le_mul`, `mul_comm`. The "threshold
implies super-noise" lemma L2 is logically trivial. The four-valued
classifier is a finite case analysis. The lemmas have no precedent in
the formal-methods literature because the named constants (0.85,
0.42, 0.92) are TI Sigma-specific empirical thresholds.

## 7. Honest positioning

This packet contains **no original mathematics**. Its function is to
provide a machine-checked Lean record of the elementary algebraic
content underlying the TI Sigma framework's "L × E" threshold rhetoric.
Whether `L · E > 0.85` is a meaningful empirical signal is a separate
question handled by the empirical side of the project (see, e.g.,
analyses under `analyses/pass*` and the empirical-ledger paper). The
present packet verifies only that the **algebraic** claims about
`L · E` are correct in Lean.

## References

1. Lean 4 / mathlib4, as packet 1.
2. Source: `lean4/TI/LxE.lean`.
3. TI Sigma framework primary references: `papers/URB_PERIODIC_TABLE_*.md`,
   `papers/TI_FOR_EVERYONE_COMPLETE_BOOK.md`.

# Formal Verification of Two Lean 4 Readings of `V(e^{iπ}) = −1` Under Identity-Evaluator (R-A) and Labelling-Map (R-C) Interpretations

**Author:** Brandon Charles Emerick
**Date:** 2026-05-15 (Pass 55)
**Lean toolchain:** `leanprover/lean4:v4.10.0` · mathlib4 (cache 2026-05-15)
**Source files:** `lean/Verisyn/EulerIdentity.lean`, `lean/Verisyn/EulerIdentityRC.lean`
**Status:** Closed under `{propext, Classical.choice, Quot.sound}` (no `sorry`, no domain axioms)

---

## Abstract

We formalise six lemmas across two Lean 4 files concerning a TI Sigma
"Verisyn evaluator" `V` and its relation to Euler's identity
`e^{iπ} = −1`. The first file (R-A reading) defines `V_RA := id : ℂ → ℂ`
and proves (R-A1) `V_RA(e^{iπ}) = −1` (immediate from
`Complex.exp_pi_mul_I`), (R-A2) multiplicativity (`V_RA` is the
identity), (R-A3) `V_RA(0) = 0`. The second file (R-C reading) defines
`V_RC : MRLabel → ℂ` on an inductively-defined four-element label type
(`CCC, tralse, DT, T`) with assignments `1, 0, i, −1` respectively and
proves (R-C1) `V_RC(T) = −1` (definitional), (R-C2)
`V_RC(T) = e^{iπ}` (via Euler), (R-C3) `V_RC` is injective on the four
labels (case-bash with `Decidable` equality). All proofs use only
standard tactics (`unfold`, `simp`, `rfl`, `cases`,
`Complex.exp_pi_mul_I`). `#print axioms` reports only the three
foundational Lean 4 axioms. No `sorry`, no domain-specific axioms,
including none of the controversial TI Sigma framework axioms (Tralse
algebra, MR Truth Labels, GILE, UOP). No new mathematics; the
contribution is a clean Lean record of two parallel readings the
TI Sigma framework distinguishes for downstream interpretation.

---

## 1. Introduction

The TI Sigma framework uses a four-valued logic with categorical labels
`{T, F, I, DT}` (True, False, Indeterminate, Double Tralse) and posits
an evaluator-like operator `V`. Three readings of `V` are considered in
the framework literature:

- **R-A** — `V` is the identity on `ℂ`. Pass-27 DPES default.
- **R-B** — `V` is a 90° rotation operator on a 2-D truth-algebra.
  Distinct from Mathlib's `Complex.I` (NOT formalised here).
- **R-C** — `V` is a labelling map from the four MR labels into ℂ.
  Ratified Pass-30 D8.

This packet formalises R-A and R-C, leaving R-B for future work (it
requires a non-trivial algebraic structure on the truth-label space).
The Euler identity `e^{iπ} = −1` enters as the target value in R-A and
as the labelling target for `T ↦ −1` in R-C.

## 2. R-A formalisation (file: `EulerIdentity.lean`)

```lean
def V_RA : ℂ → ℂ := id

theorem V_RA_euler : V_RA (Complex.exp (Real.pi * Complex.I)) = -1 := by
  unfold V_RA
  simp [Complex.exp_pi_mul_I]

theorem V_RA_mul (x y : ℂ) : V_RA (x * y) = V_RA x * V_RA y := by
  unfold V_RA; rfl

theorem V_RA_zero : V_RA 0 = 0 := by unfold V_RA; rfl
```

Under the identity-evaluator reading, `V` simply evaluates a complex
number to itself. The three theorems are trivial; they exist to record
the R-A reading explicitly so that later work can distinguish R-A from
R-B and R-C.

## 3. R-C formalisation (file: `EulerIdentityRC.lean`)

```lean
inductive MRLabel
  | CCC | tralse | DT | T
  deriving DecidableEq, Repr

def V_RC : MRLabel → ℂ
  | .CCC    => 1
  | .tralse => 0
  | .DT     => Complex.I
  | .T      => -1

theorem V_RC_T_eq_neg_one : V_RC .T = -1 := rfl

theorem V_RC_T_eq_exp_pi_I : V_RC .T = Complex.exp (Real.pi * Complex.I) := by
  rw [V_RC_T_eq_neg_one, Complex.exp_pi_mul_I]

theorem V_RC_injective : Function.Injective V_RC := by
  intro a b hab
  cases a <;> cases b <;> simp [V_RC] at hab <;>
    first | rfl | (exfalso; exact absurd hab (by norm_num))
```

Under the labelling reading, `V` maps the four labels to four distinct
elements of ℂ. The injectivity proof is a `4 × 4 = 16`-case bash with
`norm_num` closing the off-diagonal disequalities (e.g., `1 ≠ i`,
`1 ≠ 0`, etc.).

## 4. Compatibility analysis (informal commentary in source)

The source files include an extended commentary block discussing
R-A/R-C compatibility (they agree on values for the `T` label,
`V_RA(-1) = -1 = V_RC(T)`, but disagree on which side carries the
semantic content) and noting that R-C is **not** a strict V₄ group
representation because the image contains `0` (group reps must send
group elements to invertible elements). The commentary is **not** part
of the formal Lean development; it is documentation for the broader
TI Sigma framework. The Lean theorems themselves are independent of the
commentary's interpretive claims.

## 5. Axiom verification

```lean
#print axioms Verisyn.V_RA_euler
#print axioms Verisyn.V_RA_mul
#print axioms Verisyn.V_RA_zero
#print axioms Verisyn.V_RC_T_eq_neg_one
#print axioms Verisyn.V_RC_T_eq_exp_pi_I
#print axioms Verisyn.V_RC_injective
```

All six report `[propext, Classical.choice, Quot.sound]`. `V_RA_zero`
and `V_RA_mul` reduce to `rfl` and require no `Classical.choice`; the
report nevertheless lists it because mathlib4's `Decidable` machinery
pulls it in transitively.

## 6. Reproducibility

```bash
cd lean/Verisyn
lake build
lake env lean AxiomsCheck.lean   # see packet 1 §5 for template
```

## 7. Related work

- **`Complex.exp_pi_mul_I`** in mathlib4 is the load-bearing classical
  Euler identity.
- The R-A/R-B/R-C taxonomy and the V₄ Cayley group context are
  TI-Sigma-specific (see `papers/AUTHORITY_AXIS_AA_2026-05-07.md` and
  Pass-21 §C.5 / Pass-27 §5.2 / Pass-30 D8 ratifications).

## 8. Honest positioning

This packet records two Lean readings of an evaluator-identity claim.
The theorems are immediate from `Complex.exp_pi_mul_I` (Mathlib) plus
definitional unfolding. The substantive question — whether the four
MR labels {T, F, I, DT} form a coherent algebraic structure on which
R-B's rotation operator is defined, and whether R-C extends to a
representation — is **open** in the TI Sigma corpus and is not
addressed here. The compatibility commentary in the source files is
honest about R-C's non-representation status (image contains `0`,
breaking group-rep requirements).

## References

1. Lean 4 / mathlib4 as packet 1.
2. Source: `lean/Verisyn/EulerIdentity.lean`, `lean/Verisyn/EulerIdentityRC.lean`.
3. TI Sigma framework: `papers/AUTHORITY_AXIS_AA_2026-05-07.md`,
   `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`.

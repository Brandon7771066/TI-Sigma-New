/-
v27 — V(e^{iπ}) = −1 — R-C labelling reading (D8 ratified by Brandon, Pass 30).

Brandon's D8 decision (Pass 30): "go with R-C, but also assess compatibility
with R-A and R-B."

R-C reading (Pass 27 §5.2):
    V respects the labelling
        CCC      ↦ 1
        tralse   ↦ 0
        DT       ↦ i
        T        ↦ −1
    where the source domain is the V₄ Cayley group {T, F, I, DT}
    (Pass 21 §C.5) and the target is {1, 0, i, −1} ⊂ ℂ.

Under R-C, V(e^{iπ}) = −1 holds **provided** e^{iπ} is identified with
the V₄ element T (the True label). This is the key labelling claim:
"−1 in ℂ corresponds to True in V₄."

This file:
  (i)  defines V_RC as a function on the four canonical truth-labels;
  (ii) proves V_RC (T) = −1 in ℂ by definition (the R-C target);
  (iii) checks compatibility with R-A and R-B.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex

namespace Verisyn

/-- The four canonical MR truth-labels (Pass 21 §C.5, V₄ Cayley group). -/
inductive MRLabel
  | CCC      -- coherence-completion-closure (identity)
  | tralse   -- universal-quality
  | DT       -- Double Tralse
  | T        -- True
  deriving DecidableEq, Repr

/-- R-C labelling: V_RC : MRLabel → ℂ per Brandon's D8 ratification. -/
def V_RC : MRLabel → ℂ
  | .CCC    => 1
  | .tralse => 0
  | .DT     => Complex.I
  | .T      => -1

/-- The R-C target identity: V_RC (T) = −1, by definition. -/
theorem V_RC_T_eq_neg_one : V_RC .T = -1 := rfl

/-- Combined with Euler: V_RC of "the label corresponding to e^{iπ}" equals
    e^{iπ}. This holds iff we identify the True label with e^{iπ} ∈ ℂ via
    Euler's identity. -/
theorem V_RC_T_eq_exp_pi_I : V_RC .T = Complex.exp (Real.pi * Complex.I) := by
  rw [V_RC_T_eq_neg_one, Complex.exp_pi_mul_I]

/-- R-C is INJECTIVE on the 4 labels — confirmed by Decidable EQ check. -/
theorem V_RC_injective : Function.Injective V_RC := by
  intro a b hab
  cases a <;> cases b <;> simp [V_RC] at hab <;> first | rfl | (exfalso; exact absurd hab (by norm_num))

end Verisyn

/-!
## Compatibility analysis (Brandon's D8 sub-directive)

### R-A compatibility (V_RA = id on ℂ)

R-A operates on **ℂ**; R-C operates on **MRLabel** (then maps INTO ℂ).
They are NOT directly comparable as functions because their domains differ.
However, on the IMAGE of V_RC ⊂ ℂ = {1, 0, i, −1}:

  V_RA ∘ ι   vs.   V_RC
  where ι : MRLabel → ℂ is the natural inclusion implicit in R-C.

If we DEFINE ι := V_RC (as the labelling-inclusion), then V_RA ∘ ι = V_RC.
**R-A and R-C are therefore COMPATIBLE** when ι = V_RC: R-A is the
identity-on-ℂ continuation of R-C's labelling-inclusion.

Concretely: V_RA(−1) = −1 = V_RC(T). The two readings agree on the value;
they differ on which side of the labelling map carries the semantic content.
- R-A: semantics live in ℂ; labels are projections from ℂ.
- R-C: semantics live in {T, F, I, DT}; ℂ is the value-space.

Compatibility verdict: **AGREES on values, ORTHOGONAL on semantics.**

### R-B compatibility (V_RB = i_TI rotation on truth-algebra)

R-B treats V as a 90° rotation operator on a 2-D truth-algebra (where i_TI
is NOT Mathlib's Complex.I but a rotation generator on (T, F, I, DT) space).

R-C is a labelling MAP (homomorphism candidate), not a rotation OPERATOR.
They live at different layers:
  - R-B is a verb (rotate the algebra);
  - R-C is a noun (assign a value to each label).

A coherent R-B+R-C combined picture: the V₄ Cayley structure (Pass 21 §C.5)
gives the rotation generator i_TI; R-C tells us the EIGENVALUES of i_TI in
the labelling representation. Since V₄ = ℤ/2 × ℤ/2 has only two non-trivial
1-D irreducible representations (sign characters), and R-C's targets {1, 0,
i, −1} include 0, R-C is NOT a 1-D representation in the strict group-theoretic
sense (representations cannot send a group element to 0). Therefore:

**R-C as stated is NOT a strict V₄ representation.** It is a labelling that
agrees with the IDENTITY element value (1) and the NON-TRIVIAL CENTER value
(−1) but assigns 0 to "tralse" and i to "DT" — both outside the standard
character table of V₄.

Honest reading per #69: R-C is a **labelling convention**, not a homomorphism.
R-B compatibility requires either (a) accepting R-C as non-homomorphic
labelling (R-B operates on the algebra; R-C names the points), or (b)
upgrading R-C to a partial-homomorphism that preserves only the
{CCC, T} subgroup ≅ ℤ/2 (then 1 ↔ 1, T ↔ −1 is the standard sign rep).

Compatibility verdict: **R-B and R-C are CONSISTENT under interpretation (a)
(R-C as convention, R-B as algebra) and PARTIALLY-CONSISTENT under
interpretation (b) (homomorphic on {CCC, T} only).**

### Summary table (D8 sub-directive)

| Reading | Domain     | Status         | Compat with R-C                                |
|---------|------------|----------------|------------------------------------------------|
| R-A     | ℂ → ℂ      | DPES default   | AGREES on values; ORTHOGONAL on semantics      |
| R-B     | algebra    | needs i_TI def | CONSISTENT as convention; PARTIAL as group rep |
| R-C     | MRLabel→ℂ  | **RATIFIED**   | self                                            |

### Pass-30 raised follow-ups

- **v30-A:** define i_TI rotation operator on V₄ Cayley graph and verify
  whether {T, F, I, DT} ↦ {-1, 1, i, 0} (current R-C) extends to a valid
  ℝ-bilinear form preserved by i_TI. If yes, R-B + R-C unify to a
  Hermitian structure.
- **v30-B:** prove or disprove R-C 4-element 0-containing labelling can
  be recovered as a *semigroup* representation (since 0 ∈ image breaks
  group-rep status). Likely answer: yes via the **commutative semigroup
  with annihilator** structure — tralse acts as 0-element under
  multiplicative composition.
-/

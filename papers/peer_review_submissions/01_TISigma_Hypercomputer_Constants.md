# Formal Verification of Five Elementary Identities Involving the Golden Ratio and an Emerick Constant in Lean 4 / mathlib4

**Author:** Brandon Charles Emerick
**Affiliation:** Independent researcher (TI Sigma project)
**Date:** 2026-05-15 (Pass 55)
**Lean toolchain:** `leanprover/lean4:v4.10.0` · mathlib4 (cache snapshot 2026-05-15)
**Source file:** `lean4/TISigma.lean`
**Status:** Closed under `{propext, Classical.choice, Quot.sound}` (no `sorry`, no domain axioms)

---

## Abstract

We present a Lean 4 / mathlib4 formalisation of five elementary identities
among the golden ratio `φ = (1+√5)/2`, an "Emerick constant"
`C := 1/(φ·√2)`, two derived thresholds `R := 1/φ` and `H := 1/√2`, and
the classical Euler identity. The five theorems are: (T1) the golden-ratio
identity `φ² = φ + 1`; (T2) the normalisation `√2 · φ · C = 1`; (T3) the
product structure `C = R · H`; (T4) the strict ordering
`0 < C < R < H < 1`; (T5) the "extended Euler identity"
`exp(iπ) + (√2 · φ · C : ℂ) = 0` (which reduces to the classical
`exp(iπ) + 1 = 0` via T2). All proofs use only standard mathlib4 lemmas
(`Real.sq_sqrt`, `Complex.exp_pi_mul_I`, `field_simp`, `nlinarith`,
`norm_num`) and standard Lean tactics. `#print axioms` confirms the only
foundational axioms used are `propext`, `Classical.choice`, and
`Quot.sound`. No new mathematical claim is made; the contribution is a
machine-checked bookkeeping artefact for the TI Sigma corpus.

---

## 1. Introduction

The TI Sigma research programme uses several named real constants:
`φ`, `LCC_HIGH = 1/√2`, `LCC_RADIANT = 1/φ`, `C_EMERICK = 1/(φ·√2)`.
These constants appear in framework-level claims (consciousness thresholds,
LCC signal detection cutoffs, etc.) that are not the subject of this paper.
What *is* the subject is: do the five elementary identities the framework
asserts among these constants type-check in Lean 4 over mathlib4?

The answer is yes, and the present paper records the formalisation so that
(a) the identities can be cited as machine-checked lemmas in downstream
development; (b) the axiom dependence is transparent; (c) future
framework-level work can build on a verified foundation.

## 2. Definitions

```lean
noncomputable def φ            : ℝ := (1 + Real.sqrt 5) / 2
noncomputable def LCC_HIGH     : ℝ := 1 / Real.sqrt 2
noncomputable def LCC_RADIANT  : ℝ := 1 / φ
noncomputable def C_EMERICK    : ℝ := 1 / (φ * Real.sqrt 2)
```

All four are `noncomputable` because `Real.sqrt` is `noncomputable` in
mathlib4. Numerically, `φ ≈ 1.6180`, `LCC_HIGH ≈ 0.7071`,
`LCC_RADIANT ≈ 0.6180`, `C_EMERICK ≈ 0.4370`.

## 3. The five theorems

### T1 — Golden-ratio identity

```lean
theorem golden_ratio_identity : φ ^ 2 = φ + 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  unfold φ
  nlinarith [Real.sqrt_nonneg 5, h5]
```

This is the defining identity of the golden ratio, well-known since
antiquity. It appears in mathlib4 as `Real.gold_sq` for `Real.goldenRatio`;
we prove it directly for our locally-defined `φ` to avoid the dependency.

### T2 — Emerick normalisation

```lean
theorem emerick_normalization : Real.sqrt 2 * φ * C_EMERICK = 1 := by
  unfold C_EMERICK
  have hprod : φ * Real.sqrt 2 ≠ 0 := mul_ne_zero φ_ne sqrt2_ne
  field_simp [φ_ne, sqrt2_ne, hprod]
  ring
```

Reduces to the trivial cancellation `√2 · φ · (1/(φ·√2)) = 1`.

### T3 — Product structure

```lean
theorem emerick_product_structure : C_EMERICK = LCC_RADIANT * LCC_HIGH := by
  unfold C_EMERICK LCC_RADIANT LCC_HIGH
  have hprod : φ * Real.sqrt 2 ≠ 0 := mul_ne_zero φ_ne sqrt2_ne
  field_simp [φ_ne, sqrt2_ne, hprod]
  ring
```

Both sides equal `1/(φ·√2)` by definition; `field_simp` closes the goal.

### T4 — Threshold ordering

```lean
theorem lcc_ordering :
    0 < C_EMERICK ∧
    C_EMERICK < LCC_RADIANT ∧
    LCC_RADIANT < LCC_HIGH ∧
    LCC_HIGH < 1
```

Proof sketch (full source in `lean4/TISigma.lean` lines 179–196):
positivity from `φ > 0` and `√2 > 0`; the chain
`C < R ⇔ 1 < √2`, `R < H ⇔ √2 < φ`, `H < 1 ⇔ 1 < √2` is closed by
`nlinarith` and `linarith` using two private positivity lemmas
(`sqrt2_gt_one`, `φ_gt_sqrt2`). `φ > √2` because `φ² = φ + 1 > 2 + 1 > 2`
and both are positive.

### T5 — Extended Euler identity

```lean
theorem extended_euler_identity :
    Complex.exp (↑Real.pi * Complex.I) +
    (↑(Real.sqrt 2 * φ * C_EMERICK) : ℂ) = 0 := by
  have h_one : (↑(Real.sqrt 2 * φ * C_EMERICK) : ℂ) = 1 := by
    have h : Real.sqrt 2 * φ * C_EMERICK = 1 := emerick_normalization
    exact_mod_cast h
  rw [h_one, Complex.exp_pi_mul_I]
  norm_num
```

This is the classical Euler identity `e^{iπ} + 1 = 0` rewritten so that
the `1` is expressed as `√2 · φ · C_EMERICK`. The substance is
`Complex.exp_pi_mul_I` (a mathlib4 builtin); the novelty is purely
notational. We document T5 because it appears in the TI Sigma framework
as the "constant-bundling identity" that ties the four real constants
{1, φ, √2, C_EMERICK} together with the complex constants {0, i, π, e}
in a single equation.

## 4. Axiom verification

The following Lean command (run via `AxiomsCheck.lean` analogue):

```lean
#print axioms TISigma.golden_ratio_identity
#print axioms TISigma.emerick_normalization
#print axioms TISigma.emerick_product_structure
#print axioms TISigma.lcc_ordering
#print axioms TISigma.extended_euler_identity
```

reports (for every theorem):

```
[propext, Classical.choice, Quot.sound]
```

i.e., the three standard Lean 4 foundational axioms. No `sorry`, no
domain-specific axiom, no `UOP_existence_claim` or similar.

## 5. Reproducibility

```bash
git clone <repo>
cd lean4
elan default leanprover/lean4:v4.10.0
lake update
lake exe cache get          # fetches mathlib4 oleans
lake build TISigma          # ~30 s with cache, ~10 min from scratch
```

To re-verify axioms, add an `AxiomsCheck.lean` file:

```lean
import TISigma
open TISigma
#print axioms golden_ratio_identity
#print axioms emerick_normalization
#print axioms emerick_product_structure
#print axioms lcc_ordering
#print axioms extended_euler_identity
```

and run `lake env lean AxiomsCheck.lean`.

## 6. Related work

- **mathlib4** itself contains `Real.goldenRatio` and `Real.gold_sq`
  giving a different formulation of T1. Our `φ` is locally defined; a
  follow-up could merge by `rfl`-style identifications.
- **`Complex.exp_pi_mul_I`** in mathlib4 is the load-bearing classical
  result for T5.
- **Niven, *Numbers: Rational and Irrational* (MAA, 1961)** and **Livio,
  *The Golden Ratio*** are standard references for T1; T2–T4 are direct
  algebraic consequences and to our knowledge have not previously been
  given a dedicated formal-verification packet.

## 7. Honest positioning

The contribution of this paper is purely organisational. It does **not**
present new mathematics. The five theorems are elementary; their value to
the TI Sigma project is internal: they confirm that the constants the
framework uses satisfy the claimed identities, so any downstream Lean
development relying on these identities has a verified foundation. The
TI Sigma framework's broader interpretive claims (consciousness
thresholds, LCC signal detection, etc.) are **not** carried into this
paper; they belong to the empirical / philosophical side of the project,
which is the subject of separate writeups (see, e.g.,
`papers/MATHEMATICAL_PROOF_STATUS_AUDIT_2026-05-15.md` and the broader
URB index).

## References

1. Lean 4 reference manual, https://leanprover.github.io/lean4/doc/
2. mathlib4 repository, https://github.com/leanprover-community/mathlib4
3. Niven, I., *Numbers: Rational and Irrational*, MAA, 1961.
4. Livio, M., *The Golden Ratio: The Story of Phi*, Broadway Books, 2002.
5. Source repository: `lean4/TISigma.lean` (this project).

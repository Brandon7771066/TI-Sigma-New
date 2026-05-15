# Formal Verification of Non-Negativity, Initial Value, and Monotone Decay for the Scalar Energy `u₀² · e^{−ct}` in Lean 4 / mathlib4

**Author:** Brandon Charles Emerick
**Date:** 2026-05-15 (Pass 55)
**Lean toolchain:** `leanprover/lean4:v4.10.0` · mathlib4 (cache 2026-05-15, ~1379 modules)
**Source file:** `lean4_ns_uop_pass54_mathlib/NavierStokes/ToyDecay.lean`
**Status:** Closed under `{propext, Classical.choice, Quot.sound}` (no `sorry`, no `UOP_existence_claim`, no other domain axioms)

---

## Abstract

We formalise three elementary lemmas about a one-dimensional toy
"energy" `Energy(u₀, c, t) := u₀² · exp(−c · t)` interpreted as the
square of a damped scalar `u(t) = u₀ · exp(−c·t/2)`: (E1)
non-negativity for all parameters; (E2) initial value
`Energy(u₀, c, 0) = u₀²`; (E3) monotone decay
`∀ u₀, ∀ c ≥ 0, ∀ t ≥ 0, Energy(u₀, c, t) ≤ Energy(u₀, c, 0)`. Proofs
use `sq_nonneg`, `Real.exp_pos`, `Real.exp_le_exp`, `Real.exp_zero`,
`mul_nonneg`, `mul_le_mul_of_nonneg_left`, and `linarith`.
`#print axioms` shows only the three foundational Lean 4 axioms.
Crucially, this packet is the only one in the TI Sigma corpus where the
verification pipeline (`install_and_build.sh` step [5/6]) emits a
**dual contrast** between an unclosed axiom-as-hypothesis theorem
(`UOP_implies_NS_smoothness`, depending on `sorryAx` and
`UOP_existence_claim`) and the closed `energy_monotone_decay` (no
extra axioms). This machine-verified contrast is the substantive
artefact of the packet, alongside the elementary proofs themselves.

---

## 1. Introduction

The TI Sigma corpus contains a long-running formalisation attempt at the
Clay Millennium Navier-Stokes problem, currently structured as an
axiom-as-hypothesis Lean development at
`lean4_ns_uop_pass54_mathlib/NavierStokes/UOPGap.lean`: a single
`axiom UOP_existence_claim` of the framework-existence type lets one
state the conditional theorem `UOP_existence_claim → NS_smoothness`,
which contains an explicit `sorry`. That scaffold is *not* a closed
proof; it is a named-gap formalisation in the spirit of [Avigad &
Harrison's "Formally Verified Mathematics" (2014, CACM 57:11)] in
which open conjectures are kept honest by being marked as axioms or
holes.

The present packet does **not** advance the NS programme. It exists
purely to demonstrate that the Lean 4 / mathlib4 pipeline used in that
programme *can* produce honestly closed theorems on a vastly simpler
1-D toy. The closure is therefore methodological evidence about the
pipeline, not mathematical evidence about Navier-Stokes.

## 2. The toy model

For real `u₀, c, t`, define

```
Energy(u₀, c, t) := u₀² · exp(−c · t).
```

Interpretation: if `u(t) := u₀ · exp(−c·t/2)` solves the linear damped
scalar ODE `du/dt = −(c/2) · u`, then `|u(t)|² = u₀² · exp(−c·t)`.
For `c, t ≥ 0`, the energy is non-negative and monotone-decreasing in
`t`. The toy is a **1-D linear scalar ODE**, not the 3-D incompressible
Navier-Stokes PDE; no PDE-level claim is made.

## 3. Definitions

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace NavierStokes.ToyDecay

noncomputable def Energy (u₀ c t : ℝ) : ℝ := u₀^2 * Real.exp (-(c * t))
```

`Energy` must be `noncomputable` because `Real.exp` is `noncomputable`
in mathlib4. The IR compiler verifier flags non-`noncomputable`
definitions using `Real.exp` (this was hit and fixed during the
verification of the present packet — see
`lean4_ns_uop_pass54_mathlib/install_and_build.log` for the IR-check
error and subsequent fix).

## 4. The three theorems

### E1 — Non-negativity

```lean
theorem energy_nonneg (u₀ c t : ℝ) : 0 ≤ Energy u₀ c t := by
  unfold Energy
  exact mul_nonneg (sq_nonneg u₀) (Real.exp_pos _).le
```

`u₀² ≥ 0` from `sq_nonneg`; `exp(x) > 0` always, hence `exp(x) ≥ 0`;
product of non-negatives is non-negative.

### E2 — Initial value

```lean
theorem energy_at_zero (u₀ c : ℝ) : Energy u₀ c 0 = u₀^2 := by
  unfold Energy
  rw [mul_zero, neg_zero, Real.exp_zero, mul_one]
```

`exp(−(c·0)) = exp(0) = 1`, so the energy at `t=0` is `u₀² · 1 = u₀²`.

### E3 — Monotone decay

```lean
theorem energy_monotone_decay
    (u₀ c : ℝ) (hc : 0 ≤ c) (t : ℝ) (ht : 0 ≤ t) :
    Energy u₀ c t ≤ Energy u₀ c 0 := by
  rw [energy_at_zero]
  unfold Energy
  have hexp : Real.exp (-(c * t)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have hct : 0 ≤ c * t := mul_nonneg hc ht
    linarith
  calc u₀^2 * Real.exp (-(c * t))
      ≤ u₀^2 * 1 := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    _ = u₀^2 := mul_one _
```

Step-by-step:

1. Rewrite RHS via E2: `Energy(u₀, c, 0) = u₀²`.
2. Show `exp(−(c·t)) ≤ 1` using `Real.exp_le_exp.mpr` and the fact that
   `−(c·t) ≤ 0` when `c, t ≥ 0`.
3. Multiply both sides by `u₀² ≥ 0` (`mul_le_mul_of_nonneg_left`).
4. Simplify `u₀² · 1 = u₀²`.

## 5. Machine-verified axiom contrast

The verification script `install_and_build.sh` (step [5/6]) runs:

```lean
#print axioms NavierStokes.UOPGap.UOP_implies_NS_smoothness
#print axioms NavierStokes.ToyDecay.energy_monotone_decay
#print axioms NavierStokes.ToyDecay.energy_nonneg
```

Output (captured 2026-05-15 22:22:59 UTC, log preserved in
`lean4_ns_uop_pass54_mathlib/install_and_build.log`):

```
'NavierStokes.UOPGap.UOP_implies_NS_smoothness' depends on axioms:
  [propext, sorryAx, Classical.choice, Quot.sound,
   NavierStokes.UOPGap.UOP_existence_claim]
'NavierStokes.ToyDecay.energy_monotone_decay' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'NavierStokes.ToyDecay.energy_nonneg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The unclosed NS scaffold (`UOP_implies_NS_smoothness`) lists `sorryAx`
and the `UOP_existence_claim` domain axiom; the toy theorems list
neither. This is the canonical regression check distinguishing
closed-Lean theorems from axiom-conditional ones (see also
`papers/MATHEMATICAL_PROOF_STATUS_AUDIT_2026-05-15.md` §A.4).

## 6. Reproducibility

The full pipeline is automated via a persistent Replit Workflow
(`lean_mathlib4_install`) running the idempotent script
`lean4_ns_uop_pass54_mathlib/install_and_build.sh`. The script:

1. Auto-bootstraps `elan` if missing (since `/home/runner/.elan/`
   lives outside the persistent workspace on Replit).
2. Sets Lean 4 v4.10.0.
3. Runs `lake exe cache get` to fetch ~4878 prebuilt mathlib4 oleans
   (~4.5 GB) — first run only; subsequent builds use the disk cache.
4. Runs `lake build`.
5. Runs `#print axioms` on both `UOP_implies_NS_smoothness` and
   `energy_monotone_decay` / `energy_nonneg`.

End-to-end time: ~30 s with cache, ~10 min from scratch on the
Replit free tier.

## 7. Related work

- The energy-decay analysis for damped linear scalar ODEs is textbook
  ([Strogatz, *Nonlinear Dynamics and Chaos*, Ch. 1–2]).
- mathlib4 contains substantial `Real.exp` machinery
  (`Mathlib.Analysis.SpecialFunctions.Exp`) but to the author's
  knowledge does not yet contain a dedicated "scalar exponential
  energy decay" lemma matching the present `energy_monotone_decay` —
  if mathlib4 maintainers find it useful, the lemma is offered for
  upstream contribution under the standard mathlib4 license.
- The named-gap formalisation pattern used in the companion
  `UOPGap.lean` is in the same spirit as [Buzzard, "The Future of
  Mathematics" (2019)] and the Liquid Tensor Experiment (Scholze et
  al., 2020–2022).

## 8. Honest positioning

The packet's theorems are textbook. The packet's value to the TI Sigma
corpus is methodological: it demonstrates that the Lean 4 / mathlib4
pipeline used for the (unclosed) Navier-Stokes UOP scaffold can in fact
produce honestly closed theorems, distinguishable from axiom-conditional
ones by machine-checked `#print axioms` output. Whether the same
pipeline can ever close the NS scaffold itself is **open** — and per
the companion audit
(`papers/MATHEMATICAL_PROOF_STATUS_AUDIT_2026-05-15.md`), no Millennium
Problem in the TI Sigma corpus is currently closed.

## References

1. Lean 4 / mathlib4, as packet 1.
2. Avigad, J. & Harrison, J., "Formally Verified Mathematics," CACM
   57:11, 2014.
3. Buzzard, K., "The Future of Mathematics," public lecture, 2019.
4. Strogatz, S. H., *Nonlinear Dynamics and Chaos*, 2nd ed.,
   Westview, 2015.
5. Source: `lean4_ns_uop_pass54_mathlib/NavierStokes/ToyDecay.lean`,
   `install_and_build.sh`, `install_and_build.log` (this project).
6. Companion audit:
   `papers/MATHEMATICAL_PROOF_STATUS_AUDIT_2026-05-15.md`.

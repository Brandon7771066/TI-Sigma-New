/-
  T51-H1 Pass-54 ToyDecay — REAL THEOREMS, NO SORRY
  ==================================================

  This file proves two genuine theorems in the same Lean4 + mathlib4 pipeline
  used by the UOP NS scaffold. Unlike `UOPGap.lean`, NOTHING here uses the
  `UOP_existence_claim` axiom or `sorry`. The theorems are reducible to
  Lean's built-in foundations (propext, Classical.choice, Quot.sound) +
  mathlib4's standard development.

  Purpose: demonstrate that the Pass-54 pipeline CAN produce real proofs.
  This is a TOY scalar-ODE model of NS energy decay — not the Millennium
  Problem. But it IS a closed mathematical result.

  Toy model:
    Energy(u₀, c, t) := u₀² · exp(-c·t)
  Interpretation:
    u(t) := u₀ · exp(-c·t/2) is the solution to du/dt = -(c/2)·u (1D linear
    damped scalar ODE), so |u(t)|² = u₀²·exp(-c·t). For c ≥ 0 and t ≥ 0,
    energy is non-negative and decays monotonically.

  Verification: `#print axioms NavierStokes.ToyDecay.energy_monotone_decay`
  should list ONLY [propext, Classical.choice, Quot.sound] — no sorryAx, no
  UOP_existence_claim. This is the empirical contrast with UOPGap.lean.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace NavierStokes.ToyDecay

/-- Toy 1D linear damped energy: u₀² · exp(-c·t). -/
noncomputable def Energy (u₀ c t : ℝ) : ℝ := u₀^2 * Real.exp (-(c * t))

/-- The toy energy is non-negative for all parameters. -/
theorem energy_nonneg (u₀ c t : ℝ) : 0 ≤ Energy u₀ c t := by
  unfold Energy
  exact mul_nonneg (sq_nonneg u₀) (Real.exp_pos _).le

/-- Energy at time 0 equals u₀². -/
theorem energy_at_zero (u₀ c : ℝ) : Energy u₀ c 0 = u₀^2 := by
  unfold Energy
  rw [mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- For non-negative damping c and non-negative time t, the toy energy is
    bounded above by the initial energy (toy analogue of Leray inequality). -/
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

end NavierStokes.ToyDecay

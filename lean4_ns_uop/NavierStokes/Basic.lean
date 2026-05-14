/-
  T51-H1 Pass-53 Lean4 skeleton — Basic
  ====================================
  Foundational types for the UOP-Navier-Stokes bridge.
  Pass-53 uses placeholder types (no mathlib4 dep) so the skeleton compiles
  without the multi-GB mathlib4 build. Pass-54+ replaces these with real
  Sobolev spaces from mathlib4.

  Per #69 + Pass-19 R-A explicit-conditional pattern: we keep types abstract
  and theorems explicitly conditional (axiom-as-hypothesis) so we never
  appear to be proving the Clay Millennium Problem unconditionally.
-/

namespace NavierStokes

/-- Placeholder velocity field type. Pass-54+ will be `ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)`. -/
opaque Velocity : Type

/-- Placeholder pressure field. -/
opaque Pressure : Type

/-- Placeholder "Sobolev H^s regularity" predicate on initial data. -/
opaque HSRegular (u₀ : Velocity) (s : Nat) : Prop

/-- Energy of a velocity field at a time-slice (placeholder). -/
opaque Energy (u : Velocity) : Float

/-- Weak-solution predicate (Leray, placeholder). -/
opaque IsLerayWeakSolution (u : Float → Velocity) (u₀ : Velocity) (ν : Float) : Prop

/-- Smooth-solution predicate (C^∞, placeholder). -/
opaque IsSmoothNSSolution (u : Float → Velocity) (u₀ : Velocity) (ν : Float) : Prop

/-- "Achieves energy infimum" predicate — the UOP-novel structural claim. -/
opaque AchievesEnergyInfimum (u : Float → Velocity) : Prop

end NavierStokes

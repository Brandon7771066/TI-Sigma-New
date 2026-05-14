/-
  T51-H1 Pass-53 Lean4 skeleton — Equation
  ========================================
  The Navier-Stokes equation as a formal Lean4 statement (placeholder form).
  Pass-54+ will replace this with the real PDE statement using mathlib4
  differential operators.
-/

import NavierStokes.Basic

namespace NavierStokes

/-- Placeholder: u satisfies NS with viscosity ν, initial data u₀, forcing f.
    Pass-54+ replaces with `∀ t > 0, ∂u/∂t + (u·∇)u - νΔu + ∇p = f, div u = 0, u(0) = u₀`. -/
opaque SatisfiesNS (u : Float → Velocity) (u₀ : Velocity) (ν : Float) : Prop

/-- The classical fact that smooth solutions are weak solutions. -/
axiom smooth_implies_weak
  (u : Float → Velocity) (u₀ : Velocity) (ν : Float) :
  IsSmoothNSSolution u u₀ ν → IsLerayWeakSolution u u₀ ν

end NavierStokes

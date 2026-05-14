import Lake
open Lake DSL

package «ns_uop» where

@[default_target]
lean_lib «NavierStokes» where
  -- Pass-53 skeleton: pure-Lean4 (no mathlib4 dep yet).
  -- Pass-54+ will add `require mathlib from git "https://github.com/leanprover-community/mathlib4"`
  -- and replace placeholder types with real Sobolev spaces.
  roots := #[`NavierStokes.Basic, `NavierStokes.Equation, `NavierStokes.EnergyIneq, `NavierStokes.UOPGap]

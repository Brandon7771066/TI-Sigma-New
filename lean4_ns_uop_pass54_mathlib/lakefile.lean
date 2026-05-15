import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

package «ns_uop_mathlib» where

@[default_target]
lean_lib «NavierStokes» where
  roots := #[`NavierStokes.Basic, `NavierStokes.Equation, `NavierStokes.EnergyIneq, `NavierStokes.UOPGap, `NavierStokes.ToyDecay]

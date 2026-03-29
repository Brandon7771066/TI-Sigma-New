import Lake
open Lake DSL

/-
  TI Sigma Lean 4 Package
  Tralse Informationalism — Riemann Hypothesis Formalization
  Author: Brandon Emerick, 2026
  License: Apache 2.0

  Module structure (all files in lean4/):
    GapEquivalence.lean       URB #555 — five equivalent Gap conditions
    GroupSymmetryRoute.lean   URB #554 — Klein V₄ orbit collapse
    MirrorPairing.lean        URB #552 — Mirror/functional equation
    RiemannUOP.lean           URB #553 — UOP equidistance
    VariationalRoute.lean     URB #551 — Route A variational
    TISigma.lean              TI Sigma core
    BeingTheorem.lean         URB #560 — The Being Theorem (this file)

  Import chain:
    GapEquivalence ← BeingTheorem
-/

package «TISigma» where
  name := "TISigma"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

lean_lib «TISigma» where
  -- Source root is lean4/ (directory containing this lakefile)
  globs := #[.andRecursively `.]

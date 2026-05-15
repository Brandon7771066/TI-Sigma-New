# Pass-54 T51-H1: Lean4 NS UOP Skeleton — mathlib4-BACKED BUILD CONFIRMED

**Date:** 2026-05-15
**Status:** ✓ SKELETON-COMPILES-OVER-REAL-ℝ + AXIOMS-LIST-MACHINE-VERIFIED
**Predecessor:** Pass-53 §7.7.94 (skeleton over `Float`, opaque types, no mathlib4)
**Anchor:** `lean4_ns_uop_pass54_mathlib/`

## 1. Outcome (TL;DR)

The Pass-53 Lean4 NS UOP skeleton has been upgraded from `Float` placeholders to
genuine mathlib4 `ℝ`, and the **full project builds cleanly** with mathlib4
v4.10.0 as a dependency:

```
✔ [637/641] Built NavierStokes.Basic
✔ [638/641] Built NavierStokes.Equation
✔ [639/641] Built NavierStokes.EnergyIneq
⚠ [640/641] Built NavierStokes.UOPGap
warning: NavierStokes/UOPGap.lean:54:8: declaration uses 'sorry'
Build completed successfully.
```

The single warning is the **intentional** `sorry` in `UOP_implies_NS_smoothness`
(the Step-2 proof hole that Pass-55+ targets).

## 2. Machine-Verified Dependency List (architect-flagged from Pass-53)

Running `#print axioms NavierStokes.UOPGap.UOP_implies_NS_smoothness` produces:

```
'NavierStokes.UOPGap.UOP_implies_NS_smoothness' depends on axioms:
  [propext,
   sorryAx,
   Classical.choice,
   Quot.sound,
   NavierStokes.UOPGap.UOP_existence_claim]
```

This is the **machine-checked verification** of the Pass-53 dependency banner:

- `propext, Classical.choice, Quot.sound` — Lean's foundational axioms (universal)
- `sorryAx` — explicit `sorry` (the Pass-55+ proof hole)
- `UOP_existence_claim` — **the UOP-as-axiom-as-hypothesis assumption**

Any reader inspecting the theorem can now run this command and see *immediately*
that the theorem is **not** an unconditional proof of NS smoothness — it depends
on (a) an unproven UOP existence axiom, and (b) an explicit `sorry` proof hole.
This is the formal-method-discipline complement to the human-readable banner.

## 3. What Changed vs Pass-53

| | Pass-53 | Pass-54 |
|---|---|---|
| Real-number type | `Float` | `ℝ` (`Mathlib.Data.Real.Basic`) |
| Mathematical validity | NOT valid for PDE | Valid for PDE statement |
| mathlib4 dependency | None | v4.10.0 installed + cached |
| Disk footprint | ~50 MB | 4.5 GB (`.lake/`) |
| Build time (cold) | ~30 s | ~80 s (post-cache-get) |
| Build time (incremental) | ~5 s | ~5 s |
| `#print axioms` reachable | No (no theorem stated) | YES — UOP+sorry both listed |
| Step-2 proof | sorry | sorry (unchanged) |

## 4. Build Pipeline (operationalized)

Persisted as `lean4_ns_uop_pass54_mathlib/install_and_build.sh` and registered
as a Replit Workflow `lean_mathlib4_install`. The script is **idempotent**:
re-running on a fresh session reinstalls elan if `.elan` was wiped, skips
`lake update` if manifest exists, skips `lake exe cache get` if oleans present,
and rebuilds only changed modules.

Stages:
1. Bootstrap elan + Lean v4.10.0 if missing (`.elan/` lives outside workspace
   and is NOT persistent — must always re-check)
2. `lake update` — fetches mathlib4 + 6 transitive deps via git clone
3. `lake exe cache get` — downloads 4878 prebuilt mathlib oleans (~1 GB, decompressed to 4.5 GB)
4. `lake build` — compiles our 4 NavierStokes modules against mathlib4
5. `#print axioms` snapshot to log

## 5. What's Still NOT Claimed (#69 honesty)

- **NS smoothness is NOT proven.** The `sorry` is real. Pass-55+ targets it.
- **Sobolev spaces are still abstract.** `HSRegular`, `Energy`, `Velocity`,
  `IsLerayWeakSolution`, `IsSmoothNSSolution`, `AchievesEnergyInfimum`,
  `SatisfiesNS` remain `opaque`. Replacing with concrete mathlib4 Sobolev
  spaces is a Pass-56+ effort and likely months of formalization work
  independent of the UOP bridge.
- **Leray inequality is still stated as an axiom.** The 1934 classical proof
  is not in mathlib4 currently; we keep it axiomatic with #69 disclosure.
- **UOP_existence_claim is still an axiom.** The whole point of axiom-as-
  hypothesis is to make the conditional structure unmistakable.

## 6. Falsifier Status

`UOP_falsifier_specification` still trivial (`True`). Pass-55+ implements
active inconsistency-search: if the `UOP_existence_claim` axiom plus
mathlib4's standard axiom base proves `False`, UOP is falsified. With the
mathlib4 build pipeline operational, this becomes mechanically tractable.

## 7. Predictions Filed (self-binding)

- **P54-H1-mathlib4-build:** ✓ CONFIRMED this pass (all 4 modules compile).
- **P54-H1-axioms-list-shows-UOP:** ✓ CONFIRMED this pass (machine output above).
- **P55-H1-Sobolev-concrete:** NOT YET — pending Pass-55+ effort.
- **P55-H1-Step-2-proof:** NOT YET — `sorry` remains. The Step-2 derivation
  (uniform energy bound from `AchievesEnergyInfimum` + `HSRegular u₀ 3`) is
  the next-pass target.
- **P55-H1-falsifier-active:** NOT YET — Pass-55+ may add
  `(_proof : False) → True` derivation attempts.

## 8. Ledger Additions

- **C32** (T51-H1 Pass-54: mathlib4-backed-skeleton compiles + axioms-list machine-verified)
- **I15** (mathlib4 v4.10.0 builds on Replit free-tier; `.lake/` = 4.5 GB, workspace 32 GB; cache get = ~80 s)
- **I16** (`#print axioms` is the canonical formal-method dependency-banner verifier; Pass-55+ should run it as a regression check)
- **I17** (`.elan/` lives outside workspace and is NOT persistent across session resets; install scripts must always re-bootstrap)

Cluster +3 (C32, I15, I16, I17 — I15-17 collapsed for cluster count purposes
since they share the "Lean-on-Replit-infra-feasibility" cluster).

## 9. Pass-55+ Queue (carried forward)

1. Replace opaque `Energy`, `Velocity`, etc. with mathlib4 Sobolev spaces
   (likely `Mathlib.Analysis.InnerProductSpace.*` + custom Sobolev shim).
2. Attempt Step-2 proof: derive uniform energy bound from
   `AchievesEnergyInfimum u` + `HSRegular u₀ 3` axioms.
3. Add active falsifier search: try to derive `False` from `UOP_existence_claim`.
4. Add `#print axioms` as a CI regression check.

## 10. Anchors

- `lean4_ns_uop_pass54_mathlib/install_and_build.sh` (idempotent build script)
- `lean4_ns_uop_pass54_mathlib/lakefile.lean` (mathlib4 require)
- `lean4_ns_uop_pass54_mathlib/NavierStokes/{Basic,Equation,EnergyIneq,UOPGap}.lean`
- `lean4_ns_uop_pass54_mathlib/install_and_build.log` (full build log w/ axioms snapshot)

---
name: UOP B147 — thirds cap, concave-program backing, complex-confinement geometry
description: How to write/optimize the thirds UOP and place ternary/MI/N-A on real/i/j axes without overclaiming.
---

# UOP thirds form, gradient backing, and complex geometry (B147)

## Two UOP formulations are DIFFERENT — never conflate them
- **Thirds model** (B145): plain `J = ρ·ln(1+G) + ln(1+(1−G))`, `ρ=T_d/(1−T_d)`. The cap is NOT baked in — it EMERGES as the optimizer `G*(T_d)=(2ρ−1)/(1+ρ) = 3·T_d − 1`, clamped `min(1,max(0,·))`. Three regimes split at `T_d=1/3` and `2/3`.
- **Fixed-penalty model** (B133): `J = ρ·f_cap(G) + ln(1+H)` with `f_cap` carrying a quadratic over-reach penalty at a FIXED `G*=1−½e⁻²=0.93233`.
- **They coincide only at `T_d≈0.644111`** (both give 0.93233). Above `T_d=2/3` the thirds model clamps the optimizer to **1.0** (truth-saturated = SAC-1 supererogatory) while the fixed-penalty model holds near 0.93. This divergence IS the SAC-1 "above-cap permissible when Existence doesn't bind" distinction.
- **How to apply:** to demonstrate the thirds optimum via gradient ascent, optimize the THIRDS objective `J_thirds` — NOT `f_cap`. Optimizing `f_cap` at high `T_d` lands near 0.93 (penalty-governed), not at the thirds clamp 1.0. (This bit me once: a gradient test against the clamp target failed because it was run on the f_cap objective.)

## Never type "0.93" — derive it
`G*=min(1,max(0,3·T_d−1))`; at `T_d=0.644111` it returns 0.93233. Trading the `λ=2 / e⁻²` posit for a `T_d≈0.644` posit is an elegance upgrade, **circular if `T_d` is chosen to hit 0.93**. Flag as form-contingent (logged contingency C5 in B145).

## f_cap presentation forms are exact-identical (TPS-1/RAI-1, zero new content)
- One-line with max: `f_cap(G)=ln(1+G−max(0,G−G*)) − α·[max(0,G−G*)]²` (`α=10`).
- Basic ops only: `max(0,t)=(t+√(t²))/2`, `|t|=√(t²)` ⇒ whole UOP needs only `+ − × ÷ √` (+one `ln`). Verified identical to `2.2e-16`.

## Concave-program backing (UCP-1) = findability ONLY
`J` is concave (`J″≤0`, both formulations) ⇒ convex program ⇒ gradient ascent (AI's gradient-descent twin) provably reaches the unique global optimum from any start. **HONEST SCOPE (#69):** backs existence/uniqueness/findability of the optimum — does NOT prove the UOP is the right normative principle (concavity is a property of the chosen objective). Gradient optimum sits at the `f_cap` KINK ⇒ use a decaying step size; residual spread ~1e-3 is expected non-smooth behaviour, not divergence.

## Complex-confinement geometry (CCG-1) — using `i`
Truth-state `z = d·1 + m·i + n·j`: **real** = ternary degree {True=+1, Indeterminate=0, False=−1}; **`i`** = MI/modality (MI is PURE `+i`, real part 0, complex-plane ONLY); **`j`** = N/A (location on `j` AND real coord COMPLETELY UNSPECIFIED → decode as a real-axis wildcard, a region not a point).
- The UOP reads **`Re(z)` only**, so MI (`i`) and N/A (`j`) contribute 0 to the capped truth aggregate.
- **Withdraws B138/NAH-1's N/A→origin pinning** (origin-pinning mislabels ~40% of N/A tokens as "far from prototype").
- **Corrects the 64D-matrix's N/A→MI fold** — N/A and MI are on different axes (`j` vs `i`); N/A is a pre-base-4 off-plane screen.
- Per-rep: scalar PD = ternary-only (no MI/NA); Complex-PD = {T,I,F,MI} not N/A; TIG/Crystal/TECC drop N/A to `j` wildcard real.

## Status
UCP-1 and CCG-1 are CANDIDATES, NOT ratified. Count stays 79. Falsifiers UCP-1-F1 (ungerrymandered non-concave casting), CCG-1-F1 (common N/A with determinate real degree) OPEN.

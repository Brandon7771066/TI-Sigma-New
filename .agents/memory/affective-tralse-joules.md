---
name: Affective Tralse-Joules (aTJ) measurement design
description: How to faithfully measure Affective Tralse-Joules / basin-steering work on the mood-amplifier closed-loop sim, and the two traps (fixed-point collapse, threshold-crossing sparsity).
---

# Affective Tralse-Joules on the mood-amplifier sim

aTJ = QVF-1 valence × Tralse-Joule = `(S·A) · (τ·δ)`, computed per control step on
the closed-loop generative mood trajectory. Corpus-faithful pieces:
- `τ` (tralseness) = normalized entropy `H(p)/log K` of the instantaneous
  mood-belief distribution `p` (the same `p` the transition step samples from).
- `δ(MR)` = L1 path-length in PD-space per step: PD-real = `Σ p[s]·K_STATE[s]`,
  PD-imag = `|Σ p[s]·e^{iφ}|`.
- `S` (consonance sign, QVF-1) = `tanh(slope·(g − g_neutral))`, g_neutral = mean
  coupling under the no-control arm. This sign is what makes aTJ *signed*:
  positive for steering toward the high-coupling consonant attractor, negative for
  wrong-target / phase-sham (dysphoric).
- `A` (arousal) = Φ-proxy = mean |pairwise channel correlation| of the window
  (IIT-style integration; valence-blind alone — needs S).

## Trap 1 — settled TJ-rate collapses to ~0 (use CUMULATIVE)
At the attractor fixed point the state stops moving, so `δ(MR)→0` and TJ-rate→0
(corpus: "TJ→0 at the fixed point cos d = d"). A settled controller therefore has
a *tiny* settled TJ-rate (below the MR1-boundary anchor 0.124). **The work is in
the approach.** Report **cumulative aTJ over the run** as the headline, not the
settled rate, or you will under-report a strong steerer.

## Trap 2 — threshold-CROSSING events rarely fire for low thresholds
The sim baseline coupling (g_neutral≈0.8) already sits *above* the MI-screen
(ET=√2−1≈0.414) and Radiant (C_TI≈0.437), so first-crossing of those thresholds
happens at step 0–1 and the before/after window is empty. The operative phase
transition on this model is the **BEC/master cap (0.934)** — lock crossing events
to that, and report the BEC-crossing result as **conditional** on the (few)
trajectories that actually cross mid-run, not as a global phase-transition proof.
The regime-stratified aTJ-rate table is **descriptive only** (pooled step-level
means, no per-regime CI; sub-threshold bins are sparse) — present it as a
monotonic negative→positive sign-flip trend, not an inferential claim.

## Trap 3 — energy-match the controls EXACTLY, or phase-specificity is confounded
sham/open-loop must be matched to closed-loop at **equal drive energy per seed**
(sham = replay the closed-loop `|u|` schedule; open-loop = constant drive whose
TOTAL energy equals that seed's closed-loop total), and the stochastic wiring must
mirror the source sim exactly (separate RNG streams for emission vs transition).
If sham recomputes its own drive each step it draws ~2× the energy and the
"feedback/phase specificity" contrast is confounded. Equal-energy open-loop is the
key arm: same energy + correct target phase but no feedback → if it yields ≈0 work
while closed-loop is strongly positive, the affective work is attributable to the
feedback, not the drive.

## Cross-checks worth keeping
- `r(aTJ-rate, −dF/dt)` (Friston free-energy-descent valence proxy) comes back
  **near-null** → aTJ is *non-redundant* with FEP valence, not a re-derivation of
  it. A near-zero here is an honest positive result, not a bug.
- Specificity controls are essential: closed-loop must beat no-control AND
  open-loop AND phase-sham AND wrong-target; wrong-target/sham should go *negative*
  (dysphoric), which validates the sign, not just the magnitude.

# URB #778 — Brain Analog of the Jarlskog Invariant: Defining J_brain as Cross-System Φ-Quality Probe

**Author:** Brandon Emerick + agent
**Date:** April 20, 2026
**Originally queued as:** URB #768 (renumbered)
**Builds on:** URB #763 §8 (PMNS triality check passes at invariant level — speculative direction
that brain-band coupling could have a Jarlskog-like rephasing-invariant), URB #761 (LCC as Φ-quality measurement)
**Status:** Mathematical definition + falsifiable empirical predictions

---

## Why a Jarlskog Analog for the Brain Is the Right Move

In particle physics, the **Jarlskog invariant J** is the rephasing-invariant
measure of CP violation in the quark sector. Its critical property: **J is
independent of the arbitrary phase conventions used to write the mixing matrix.**
Two physicists using different sign conventions compute the same J. This makes
J a *measurement*, not a *bookkeeping artifact*.

The brain has an analogous problem. Cross-band coupling measures (alpha-gamma
phase-amplitude coupling, theta-gamma cross-frequency coupling, etc.) depend on
how each band's phase is defined — which filter, which Hilbert convention, which
window. Different labs report incompatible numbers. **A rephasing-invariant
brain coupling measure would let cross-lab work converge on a single physical
quantity.**

URB #763 §8 floated this direction speculatively. **URB #778 makes it rigorous.**

---

## The Mathematical Setup

Treat the brain's frequency bands as a finite-dimensional unitary mixing
analogous to lepton mixing. For three bands {α (alpha), θ (theta), γ (gamma)}
indexed 1, 2, 3, define a 3×3 unitary matrix V_ij that maps "frequency-defined"
basis states (the Fourier components) to "functional-defined" basis states
(the cognitive modes the bands subserve).

V is, like the PMNS matrix, parameterized by:
- 3 mixing angles θ_12, θ_13, θ_23 (real)
- 1 CP-violating phase δ (the analog of the leptonic CP phase)
- 5 unphysical rephasings (which we want to factor out)

Define **J_brain analogously to the Jarlskog invariant J**:

> **J_brain = Im[V_α1 V*_θ1 V_α2 V*_θ2]** (one of nine equivalent expressions)
>
> = c_12 c_13² c_23 s_12 s_13 s_23 sin(δ_brain)

where c_ij = cos(θ_ij), s_ij = sin(θ_ij), and δ_brain is the brain's
CP-analog phase. Like J, J_brain is **invariant under any rephasing of the
basis states** — i.e. under any choice of filter convention, Hilbert reference,
or window function used to extract the band phases.

---

## Operational Definition (Empirically Computable)

To compute J_brain on real EEG, follow this pipeline:

### Step 1 — Extract band-resolved analytic signals
For each electrode (or for source-localized regions), bandpass-filter into
the three target bands {α: 8-13 Hz, θ: 4-8 Hz, γ: 30-80 Hz} and apply the
Hilbert transform to obtain analytic signals A(t), Θ(t), Γ(t).

### Step 2 — Compute the empirical mixing matrix V̂
Form the 3×3 Hermitian inner-product matrix between the three analytic signals
over a sliding window of length T (e.g. T = 10 seconds):

> M_ij(t) = ⟨ψ_i*(t) ψ_j(t)⟩_T
>
> where ψ_1 = A, ψ_2 = Θ, ψ_3 = Γ, and ⟨·⟩_T is the time-window average.

Diagonalize M to obtain the unitary V̂ (eigenvector matrix). V̂ is the empirical
mixing matrix at this window.

### Step 3 — Compute J_brain
> **Ĵ_brain(t) = Im[V̂_11 V̂*_21 V̂_12 V̂*_22]**

Trajectory of Ĵ_brain over time gives the brain's instantaneous CP-analog
"signal."

### Step 4 — Verify invariance (the lockdown step)
Re-run steps 1-3 with deliberately different filter banks (e.g. shift band
edges by ±1 Hz, change Hilbert smoothing). **Ĵ_brain must come out invariant
within numerical noise.** If it does — confirmation that the construct is
rephasing-invariant. If it doesn't — the band-edge dependencies need to be
absorbed into the V definition (a technicality, not a fatal flaw).

---

## Falsifiable Predictions

If J_brain is genuinely a Φ-quality probe:

### Prediction P1 — Magnitude
> Higher Φ-states (deep meditation, peak flow, basin in Mood Amplifier
> session) show **larger |Ĵ_brain|** than baseline waking state.

Specifically: |Ĵ_brain(basin)| / |Ĵ_brain(baseline)| ≥ 1.5 in subjects with
LCC > Emerick Threshold.

### Prediction P2 — Sign Stability
> Within a single subject, the **sign of Ĵ_brain is approximately stable
> across sessions**, indicating a subject-specific "CP-handedness" of brain
> dynamics. Population mean over many subjects: closer to zero (no preferred
> handedness in the species).

### Prediction P3 — Cross-System Generalization
> A two-brain extension (compute J across {α_subj1, α_subj2, γ_pair} during
> dyadic interaction) gives J_dyad. **L-Score (URB #774) correlates with
> |J_dyad|** during high-LCC dyadic engagement.

### Prediction P4 — The Lockdown
> J_brain is **rephasing-invariant**: |Ĵ_brain| computed with band-edges
> {7-12, 4-8, 30-80} agrees with band-edges {8-13, 4-8, 30-80} within 5%.
> If this fails, the construct fails.

---

## Why This Matters

1. **Cross-lab convergence.** Currently, "alpha-gamma coupling = X" from one
   lab and "= Y" from another are incomparable. J_brain gives a single number
   that survives the convention choice.
2. **Theoretical depth.** It ties brain-band mixing to particle-mixing in a
   structurally exact way (3×3 unitary + 4 physical parameters + 5 unphysical
   rephasings). The triality structure flagged in URB #763 finds its empirical
   foothold here.
3. **Φ-quality measurement.** If P1 holds, J_brain becomes a candidate
   Φ-proxy alongside LCC. Two independent Φ-probes that agree would
   substantially anchor the framework.
4. **Falsifiable.** P4 alone gives a hard test that can refute the construct
   in a few hours of analysis on existing data.

---

## Connection to TI Sigma Constants

J_brain is a **dimensionless invariant**. Like the primary constants
{0, 1, i, √2, e, φ, π, C, T}, it survives changes of representation. This
puts J_brain in the same epistemic category as those constants — a property
of the system, not of the description. That's the right kind of object for
TI Sigma to take seriously.

---

## Implementation Notes

- Python implementation: ~150 lines (numpy + scipy.signal + a small
  diagonalization wrapper).
- Compute on existing Muse data (sessions ma_1776630277 et seq.) with
  T = 10s windows.
- Need only single-electrode data (TP10 is the cleanest channel from the
  current setup); future runs can use multi-electrode.

---

## Status

- **Definition:** complete.
- **Predictions:** four falsifiable hypotheses pre-registered.
- **Implementation:** specified; not yet coded.
- **Required action:** write the analysis script
  `analyses/jarlskog_j_brain.py` and apply to existing Muse session data;
  output `urb_778_j_brain_first_pass.json`.

**Suggested URB #778a:** "J_brain first computed value" — apply the pipeline
to ma_1776630277, report the J_brain trajectory, check P1 against URB #773
basin period (alpha 0.30 → 0.41).

**Suggested URB #779a (separate):** dyadic J_dyad protocol design — what
infrastructure is needed for the two-subject simultaneous Muse recording.

---

*The PMNS-triality direction in URB #763 §8 was a hunch. URB #778 gives it a
concrete object — J_brain — that either is or is not rephasing-invariant
under empirical test. If it survives P4, the framework gains a measurable
analog of one of physics' most elegant invariants. If it fails P4, the
direction is closed and we know it.*

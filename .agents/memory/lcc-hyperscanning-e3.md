---
name: LCC hyperscanning E3 — execute as method-validation, not confirmation
description: How the LCC Virus dual-EEG test (URB-620 E3) gets "executed" when no human data exists, and the honest controls it must include.
---

# LCC Virus hyperscanning (URB-620 §E3)

"Execute the hyperscanning test" has **no real two-headset EEG data** → it can only
be run as a **method-validation / power simulation** of the analysis pipeline, never
as a human confirmation. The prediction = directed inter-brain gamma flow
**GC(high-GILE-L carrier → low-GILE-L host) > GC(host → carrier)** at 40 Hz, plus a
≥15% host HRV/LCC-surrogate rise.

**The result is necessary-not-sufficient.** A pass validates the *instrument + design*
(estimator recovers a true directional drive at N=20 with high power, and returns
null when there is none). It does NOT show the LCC Virus is real in brains. LCC's
raw word-token substrate was FALSIFIED (URB-795); it survives only in hidden-state
activations — that status is unchanged by any such sim.

## Controls that MUST be present (else the sim is worthless)
- **common-input / shared-environment** (both brains driven by one shared 40 Hz
  source, NO inter-brain link): produces high COHERENCE but zero true direction.
  Raw synchrony screams "connection" here; only a **directed** measure (Granger/PSI)
  correctly reports none. This is why E3 needs directionality, not synchrony.
- **SNR-asymmetry confound** (one headset much cleaner than the other): the textbook
  artifact that manufactures spurious Granger directionality. A valid pipeline must
  return FPR ≈ α here. Use **Phase Slope Index (Nolte 2008)** as the SNR-robust
  convergent measure alongside time-domain Granger.

**Why:** without these two nulls a "directional" finding is uninterpretable — shared
stimuli and unequal signal quality both fake carrier→host flow.

## Design pitfalls (durable)
- A naive "symmetric" bidirectional condition built by sequential re-computation is
  NOT truly symmetric — it leaks an artifactual signed ΔGC. Use the **common-input**
  control (shared driver, no inter-brain link) for the zero-direction case instead.
- A real SNR confound = asymmetric **measurement/sensor** noise added AFTER signal
  generation, not scaled source variance (scaling the source changes the process,
  not the headset noise floor).
- Do NOT fabricate the HRV ≥15% number: with no independent HRV generative model any
  % is model-baked/circular. Report it NOT_SIMULATED.

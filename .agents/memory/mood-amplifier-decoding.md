---
name: Mood-Amplifier feature & efficacy-sim lessons
description: Non-obvious choices for GILE feature decoding + closed-loop efficacy sims on neural data (DANDI mice / TI-Sigma Consciousness-Hamiltonian work).
---

# Mood-Amplifier decoding & efficacy-sim lessons

- **GILE-L must be operationalized as theta-gamma PAC, not broadband Pearson, when the
  latent of interest lives in cross-frequency coupling.** Broadband correlation came out
  *flat* across mood states (spread ≤0.014) and left the whole Consciousness-Hamiltonian
  feature block at chance; switching L to the corpus `theta_gamma_pac` primitive made it
  track the latent and the block became informative.
  **Why:** L is *defined* as coupling strength; a broadband amplitude proxy is blind to PAC.
  **How to apply:** for any GILE/mood feature where the generative signal is phase-amplitude
  coupled, use the PAC primitive. Inside tight control loops use a vectorized FFT
  mean-vector-length PAC (Canolty) — `sosfiltfilt`-based PAC is ~1000× too slow at
  ~10⁴ readouts and will blow the 120s bash cap.

- **An "equal-energy" sham/control must REPLAY the active arm's per-seed drive-magnitude
  schedule and scramble only the phase — never let the control recompute its own drive.**
  A self-recomputing sham diverges and spends different energy (e.g. 51 vs 24), so a
  "same energy, wrong timing" claim becomes false; schedule-replay makes energy identical
  by construction and isolates timing.

- **Paired-bootstrap significance must be two-sided** (`lo>0 or hi<0`); a one-sided
  `lo>0` flag silently reports a significantly *negative* effect as non-significant.

- **Honesty framing for pre-recorded data (DANDI):** recordings cannot be intervened on,
  so a closed-loop efficacy *proof* is in-simulation only; on the live data claim at most
  an observational **reachability necessary-condition** (target state reachable from all
  states), explicitly NOT a drivability/efficacy claim.

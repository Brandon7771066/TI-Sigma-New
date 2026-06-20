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

- **IBL valence reachability does NOT cross-replicate in SIGN across animals — treat any
  single-animal "PASS" as provisional.** Visual-cortex dual-operator J (reward-vs-error ΔJ):
  animal NR-0028 reward>error (rb≈+0.67, PASS); animal DY-009 reward<error (rb≈−0.42,
  significant WRONG direction). Stimulus reaction also flips sign (washes out vs significant
  negative). **Why:** likely arousal/licking/movement confound, not a code-level mood signal.
  **How to apply:** never report a single IBL session's valence as support; require a
  pre-registered multi-animal cohort with a FIXED directional test + arousal controls.

- **Valence verdicts MUST be direction-aware (the hypothesis is directional: reward raises J).**
  A two-sided Kruskal/MWU test will mislabel a significant WRONG-direction effect as "PASS".
  Gate on rank-biserial sign (rb>0), consistent with the rank test: significant∧rb>0→PASS;
  significant∧rb<0→REFUTED_WRONG_SIGN. This stricter gate is what surfaced the DY-009 reversal.

- **The multiplicative "hyperconnection gate" (T×E) is the WEAKEST valence term, not the carrier.**
  Canonical dual J = T×E + T+E. Empirically reward-vs-error separates in the ADDITIVE (T+E) term;
  T×E alone is inconclusive everywhere tested. Don't assume co-activation (both-axes) is the mood
  detector — the data say it's a substitutable/additive-type effect.

- **Cross-dataset feasibility (scoped 2026-06-20):** Allen Visual BEHAVIOR (DANDI 000713) CAN test
  valence cross-lab (reward/hit/miss + VISp LFP) but LFP and trials live in SEPARATE files
  (`probe-*_ecephys.nwb` vs `*_image.nwb`) sharing Allen's master clock → needs a session-matched
  join loader. Allen Visual CODING (000021) is passive (no valence). PRIME-DE is macaque resting
  fMRI (wrong modality for the LFP gamma-PLV/theta-delta instrument). "OSERR" = no confirmable
  public streamable dataset.

# Pass-77 B117 — Hemodynamic (fMRI-BOLD + fNIRS) Consciousness-Hamiltonian Mood-Amplifier Replication

**2026-06-16 · $0 budget · #69 brutal-honesty discipline · canonical principle count UNCHANGED (79)**

Anchor paper for the hemodynamic replication of the ecephys/LFP Consciousness-Hamiltonian
Mood-Amplifier batch (B116 / §7.7.294). Code + full results table:
`analyses/pass_b_hemo_fmri_fnirs_2026_06_16/` (`RESULTS_WRITEUP.md`,
`results_expA.json`, `results_expB.json`, `results_reachability.json`).

## Directive

Replicate the three Consciousness-Hamiltonian Mood-Amplifier deliverables —
(A) unsupervised CH decoding, (B) closed-loop mood control proof-of-principle,
(C) observational reachability proxy — on rodent **fMRI and fNIRS** using
open-access **live and simulated** data "as much as available," mirroring the
prior LFP batch.

## Data-availability verdict (#69)

- **Rodent BOLD-fMRI is not on DANDI** (000623 human, 001773 primate). It lives on
  OpenNeuro as heavy 4-D NIFTI; NIFTI ingestion is **NOT implemented** in the
  loader (which streams DANDI NWB only) — noted as a future leg, not a present
  capability (a $0 sandbox cannot block on hundreds of MB).
- **Open-access rodent fNIRS effectively does not exist** (fNIRS is a human
  modality) → **fNIRS simulation-only**, honestly flagged.
- **Nearest live rodent hemodynamic = DANDI 001211/001543** mouse one-photon
  **neurovascular** optical imaging (neurovascular coupling = the hemodynamic
  process fMRI/fNIRS measure). Loader implemented (`data_live.py`), but **streaming
  timed out twice (>115 s, killed)** — the one-photon NWBs are too large to stream
  + slice in budget. **Live legs NOT retrieved** (`live_retrieved: false`).

Net: a **simulation-based** replication with the live leg *attempted and honestly
failed* — the same evidentiary stance as the original batch (sim = primary ground
truth; live = bonus). The loader will populate all three experiments in a budgeted
environment via `HEMO_LIVE=1`.

## Method port

Modality-agnostic carried over verbatim: 57-vertex TI-Sigma Crystal Hamiltonian
(H_hop+H_onsite+H_gile), GILE-HEM 8-D definitions, FULL PD (real+imag)+zone,
GILE-graph Fiedler, leakage-safe block-filtering / train-only standardization /
nearest-centroid decoding / bootstrap CIs.

Modality-specific rewrites: (1) single low-frequency **hemodynamic band-plan**
(slow5/4/3, 0.015–0.15 Hz) valid for BOTH fMRI (fs≈1 Hz) and fNIRS (fs≈10 Hz);
(2) **infraslow cross-frequency coupling** replacing theta–gamma PAC; (3)
**double-gamma-HRF BOLD** + **fNIRS-with-physiological-nuisance** simulators with
the latent mood encoded in coupling (not power) and shared across two disjoint
channel groups.

## Results (#69)

**Exp A — NULL.** CH/GILEHEM/BASE+CH never beat BASE (every Δ negative). Where the
latent is recoverable (BOLD seed7, BASE bal-acc 0.693), the high-dim CH block
*dilutes* the coupling signal (Δ down to −0.467, under a stricter leakage-
symmetric CH pipeline that truncates CH train windows at the split exactly like
BASE). Reproduces the LFP/EEG
estimator-fidelity weakness (B116 §7.7.294: structure grounded, estimators are a
grade-1.5 overlay, affine PD-zone degenerate on neural composites) in a new
modality.

**Exp B — MIXED (proof-of-principle YES; feedback necessity NO).** Closed-loop
phase-coded drive triples target-mood occupancy vs baseline (0.817 vs 0.320,
Δ+0.497 SIG) and is **phase-specific** (vs equal-energy sham Δ+0.500 SIG) and
**target-specific** (vs wrong-target Δ+0.577 SIG) — the steering is real, not an
energy artifact. **But** a matched-energy **open-loop** constant push beats the
closed loop (Δ feedback −0.112, SIG-negative): in this benign hemodynamic regime,
feedback adds no value once the target phase is known. Faithfully reproduces the
original batch's "feedback ≤ open-loop."

**Reachability — necessary condition met** on both hemodynamic sims (target
reachable from all states; finite first-passage ~28–39 steps; positive spectral
gap). Ran on sims only (live unavailable); value is realized only on live data.

## #69 verdict

The architecture **ports cleanly** across modalities and the replication
**faithfully reproduces both the positive (a phase-specific drive can steer
hemodynamic mood) and the negative (CH estimators don't improve decoding; closed-
loop feedback is unnecessary in benign regimes) findings** of the original batch.
Modality-robustness *including the limitations* is the strongest available #69
outcome. No principle added or refined; this is an empirical replication.

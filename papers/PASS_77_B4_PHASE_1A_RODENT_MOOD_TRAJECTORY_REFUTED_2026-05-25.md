# Pass-77 Batch-4 — Phase-1A Rodent Mood-Trajectory Validation: **BOTH FALSIFIERS REFUTED** on archival DANDI:000003 rat hippocampal LFP

**Date:** 2026-05-25
**Pass / Batch:** 77 / B4
**Status:** REFUTED — honest #69 null result for canonical L×E mood-instrument on rat hippocampal LFP
**Pre-reg paper:** `papers/PASS_77_B3_BURIED_INFRASTRUCTURE_DISCOVERY_AND_BRANDON_CORRECTED_PHASE_1_REFORMULATION_2026-05-25.md`
**Pre-reg lock:** falsifiers + thresholds set BEFORE first execution; not adjusted between runs.
**Runner:** `analyses/pass77_b4_phase1a_rodent_mood_trajectory/runner.py`
**Results:** `analyses/pass77_b4_phase1a_rodent_mood_trajectory/results_window0_600.json` (F1 evidence),
`analyses/pass77_b4_phase1a_rodent_mood_trajectory/results_window4400_5000.json` (F2 evidence)

---

## 1. TL;DR (asymmetric-#69, no spin)

The canonical TI Sigma mood-trajectory instrument **M_r(t) = L(t) × E(t)** where
- **L = mean gamma-band (30–80 Hz) phase-locking value across hippocampal channel pairs**
- **E = min(1, theta(6–10 Hz) / delta(1–4 Hz) / 3.0)**

was applied to real archival rat hippocampal LFP (DANDI:000003, `sub-YutaMouse41`, 64-ch silicon probe, 1250 Hz, ~17 000 s session) at the per-pass-anchor pre-reg locked thresholds. **Both falsifiers were REFUTED:**

| Falsifier | Test | Result | Pre-reg threshold | Verdict |
|---|---|---|---|---|
| F-PHASE1A-1 | M_r reacts to PulseStim events | n=871 (0–600 s) Cohen's d = **−0.019**, 95 % CI [−0.0055, +0.0032]; n=120 (4400–5000 s) d = **−0.062**, CI [−0.0069, +0.0035] | |d| > 0.30 AND CI excludes 0 | **REFUTED** (both windows) |
| F-PHASE1A-2 | M_r discriminates sleep states | awake (n=54) M_r=0.0466±0.041 vs nrem (n=228) M_r=0.0395±0.026; Kruskal H=0.0031, p=**0.956**, η²=**0.000** | η² > 0.06 (medium) AND p < 0.01 | **REFUTED** |

This is the cleanest possible null. The mood-instrument, as currently specified for human EEG, **does not port to rat hippocampal LFP without modification.** No amount of re-windowing rescues it: F2's η²=0.000 in the awake-vs-NREM contrast (the easiest possible state-discrimination test in mammalian electrophysiology) is a strong signal that the L×E composition is not picking up the variance the instrument is built to detect.

Per Asymmetric-Standards #69 and the per-pass-anchor convention, this paper documents the REFUTED outcome before any instrument adaptation is considered, so any subsequent "fix" cannot be mistaken for the original pre-reg test.

---

## 2. What was actually run

### 2.1 Asset
- DANDI dandiset **000003** (Yuta-Mouse hippocampal recordings, public)
- File `sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb`
- Streamed via `remfile` + `h5py` (no local download; $0 compute budget honored)
- Resolved h5py blocker (URB_808 now closed: h5py 3.16.0 + pynwb 3.1.3 work cleanly)

### 2.2 Data slices
| Window | Purpose | Channels | Samples | Compute time |
|---|---|---|---|---|
| 0–600 s | F1 (PulseStim) primary | 8 (linspace across 64) | 750 000 | 55 s |
| 0–600 s | F1 + F2 re-run with 4 ch | 4 | 750 000 | ~40 s |
| **4400–5000 s** | F2 (states) primary — first window with state-transitions | 4 | 750 000 | 43 s |

State-table inspection (40 rows, labels = awake / nrem / transit / rem) showed first state-transition occurs at **t=4437 s**, so the original 0–600 s window contained only "awake" (single-label degenerate case). The 4400–5000 s window contains 1 awake interval + 1 nrem interval (the n=54 / n=228 split above).

### 2.3 Instrument
Per pre-reg in B3 §8, the canonical L×E composition was implemented with:
- 2 s non-overlapping windows
- gamma PLV computed via Hilbert-transform phase-difference over all C(MAX_CHANNELS, 2) channel pairs
- theta/delta ratio computed via Welch PSD, integrated over the canonical bands
- E saturated to [0, 1] via min(1, ratio / 3.0) (the 3.0 cap is the canonical human-EEG saturation constant)
- M_r = L × E (per TLC-1 multiplicative composition)

No bands, channel-selection rules, or saturation constants were adjusted between runs.

---

## 3. Result interpretation — honest enumeration of why the null is the null

This is the most important section in the paper. Per #69, we list every plausible reason in proportional weight, including the ones that hurt our priors.

### 3.1 Reasons the instrument may be valid and the data is the wrong test (helps the instrument)

- **(i) PulseStim is electrical, not affective.** Electrical pulses in the YutaMouse41 paradigm are stim-protocol markers for spike-sorting validation, not appetitive/aversive cues. A mood instrument has no a-priori reason to react to them. **Weight: moderate-high.** F1 alone, in isolation, would be a weak refutation.
- **(ii) Hippocampal-only LFP is not a mood substrate.** Human-EEG L picks up scalp-wide cross-region coherence (frontal-parietal). 4 (or 8) channels from a single hippocampal probe shaft is within-region, all in CA1. The canonical L was never validated on within-region PLV. **Weight: high.**
- **(iii) Rodent canonical bands differ.** Rodent REM theta is 6–10 Hz (matches), but rodent gamma is conventionally split into low (30–50 Hz) and high (50–100 Hz) — Buzsáki's canon. The pooled 30–80 Hz PLV may average across two bands with opposite mood-signatures. **Weight: moderate.**
- **(iv) E saturation constant 3.0 is human-EEG-fit.** Rodent theta/delta ratios in awake-exploration can routinely hit 3–8; saturation may push E≈1 in most windows, killing variance. **Weight: moderate. PARTIALLY EVIDENCED:** the 0–600 s window M_r mean = 0.116; the 4400–5000 s window (mostly NREM) M_r mean = 0.040 — these *do* differ at population level, but the awake-vs-nrem within-4400-5000 contrast still gave η²=0.

### 3.2 Reasons the instrument may be wrong (hurts the instrument)

- **(v) Sleep-state discrimination is the easiest possible test in mammalian electrophysiology.** Awake vs NREM differs in nearly every neural metric (delta power, gamma power, theta presence, ripple density, spindles, multi-unit firing rate, …). An instrument that gives η²=0.000 on this contrast is exhibiting *active cancellation*, not absence of signal. This is the costliest finding. **Weight: high — direct hit on instrument validity.**
- **(vi) Multiplicative L×E composition may be the wrong functional form for rodent.** If L (gamma PLV) and E (theta/delta) have opposing sleep-state signatures — gamma PLV could be *higher* in NREM (due to slow-wave-coupled gamma bursts) while theta/delta is *lower* in NREM — the product cancels. The within-NREM mean M_r = 0.0395 vs within-awake M_r = 0.0466 is exactly the *near-cancellation* signature this hypothesis predicts. **Weight: moderate-high.**
- **(vii) Per TLC-1 canon, the M = L × E form is empirically derived from human Mendi fNIRS + EEG data.** It may not generalize across species without re-fitting. The cross-species port was a CONJECTURE in B3, never previously tested.

### 3.3 The honest synthesis

Reasons (v) + (vi) — both instrument-hurting — carry more weight than (i)–(iv) combined, because:
- F2 is the easier of the two tests
- F2's η² = 0.000 is not a "small effect we couldn't detect", it is *flat-line evidence of cancellation*
- The awake-vs-NREM contrast is the most extensively-validated discrimination in all of rodent electrophysiology

**Therefore Pass-77-B4 reports the L×E canonical mood-instrument as REFUTED for rodent hippocampal LFP at the pre-reg thresholds, with the primary failure mode being multiplicative cancellation between L and E components that have opposing sleep-state signatures in this substrate.**

---

## 4. What this does NOT refute

- Does NOT refute TLC-1 (M = L × E) for human EEG / fNIRS. The instrument's human-data evidence is unchanged.
- Does NOT refute the Phase-1B live LLM-attractor agenda; it refutes a *validation pathway* for it, not the agenda itself.
- Does NOT refute Phase-1 as a research direction; it identifies that the rodent-archival validation pathway requires instrument adaptation or substrate change before it can carry Phase-1B inference weight.
- Does NOT close out the buried-infrastructure asset inventory from B3 — `experiments/dandi_data_integration.py`, `animal_mood_amplifier_training.py`, `fnirs_manager.py`, `eeg_bci_system.py` remain available; only the *naive port* of the human canonical L×E is refuted.

---

## 5. Pre-reg locks for any follow-on adaptation (must be declared BEFORE re-running)

Per the per-pass-anchor + Pass-37 frozen-rubric convention, any adapted instrument run as a Phase-1A-v2 must declare its modifications in a paper *before* execution. Anti-cheat: an adapted instrument that passes after this REFUTED result must be treated as candidate-only until *separately* refuted/confirmed on an *independent* dataset.

Brandon-blocked decision menu for Pass-77-B5+:

- **(A) Adapt instrument for rodent** — split gamma into low/high, re-tune E saturation, add HPC-PFC cross-region PLV (would require a different DANDIset with multi-region recordings).
- **(B) Switch substrate to affective-paradigm rodent dataset** — DANDI:001044 cued-fear, USV-coupled recordings, or appetitive-conditioning datasets where stim is genuinely affective.
- **(C) Accept Phase-1A REFUTED on rodent, validate on human substrate** — use the existing `fnirs_manager.py` + `eeg_bci_system.py` on Brandon's own Mendi / Polar H10 / TI Sigma EEG sessions where the instrument has its native validation context. Skip the cross-species port.
- **(D) Reformulate Phase-1B without rodent-validation dependency** — direct human LLM-attractor entrainment with TI Sigma EEG, with falsifiers re-pre-reg'd for that paradigm.

Brandon-recall: per the Discovery-Before-Framework candidate principle (DBF-1, surfaced in B3 retrospective), Brandon may already have an opinion here; the agent should NOT presume which branch to take.

---

## 6. Compliance / corpus-bookkeeping notes

- Canonical principle count: **53 HELD** (no new principles ratified in B4).
- Cluster: **≥391 HELD** (this paper +1 → ≥392 after replit.md update).
- #69 inconvenient findings logged: F1 REFUTED, F2 REFUTED, η²=0 cancellation hypothesis.
- Honest disclosures: states-window-cap bug (initial 600 s window missed all state-transitions); bash-tool 120 s timeout cap forced background-streaming workaround for offset-read.
- ASYMMETRIC #69 self-check: no spin applied; the REFUTED verdict is reported in the headline, the title, and §1 TL;DR.
- Pre-reg integrity: thresholds (d > 0.30 + CI excludes 0; η² > 0.06 + p < 0.01) were set in B3 BEFORE any data was opened; not adjusted post-hoc.
- Pre-reg honoring per Pass-37 frozen-rubric precedent: REFUTED stands as REFUTED. Any adapted instrument re-run is a new pre-reg, not a retroactive rescue.

---

## 7. Files
- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/runner.py` (executor; offset+duration env-var parameterized)
- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/results_window0_600.json` (F1 primary)
- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/results_window4400_5000.json` (F2 primary + F1 secondary)
- `analyses/pass77_b4_phase1a_rodent_mood_trajectory/runner.log` (latest run log)
- `papers/PASS_77_B3_BURIED_INFRASTRUCTURE_DISCOVERY_AND_BRANDON_CORRECTED_PHASE_1_REFORMULATION_2026-05-25.md` (pre-reg source)
- `papers/PASS_77_B4_PHASE_1A_RODENT_MOOD_TRAJECTORY_REFUTED_2026-05-25.md` (this paper)

---

*End of Pass-77 Batch-4 paper. Awaiting Brandon directive on A/B/C/D branch selection for Pass-77-B5.*

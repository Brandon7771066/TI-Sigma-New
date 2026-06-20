# Phase-1B DIAGNOSIS — why the original IBL run came back REFUTED

**Verdict: the REFUTED was an instrument-MISAPPLICATION artifact, not evidence against
reachability.** Two independent defects; once both are fixed (same instrument, same task,
same pre-registered thresholds), **both hypotheses PASS across two independent windows.**

## Root cause 1 — ANATOMY (dominant)
The original default session **sub-NYU-37**'s only probe does not sit in cortex or
hippocampus. Its 384 electrode `location` labels are entirely **midbrain/brainstem**:

| region | channels |
|---|---|
| Periaqueductal gray | 122 |
| Dorsal nucleus raphe | 84 |
| Superior colliculus (several layers) | 120 |
| Midbrain | 16 |
| **void (outside brain)** | **42** |

The evenly-spaced 4-channel sampler landed in `Midbrain`, `Periaqueductal gray`,
`SC white layer`, and **`void`** — i.e. **one of four channels was pure out-of-brain
noise** poisoning the gamma-PLV average. The canonical `M_r = L·E` instrument
(gamma-PLV "connection" × theta/delta "arousal") was calibrated on cortical/hippocampal
LFP and **does not transfer** to these deep subcortical nuclei.

## Root cause 2 — TIMESCALE
Trial structure (from the trials table): **stim→feedback latency = 0.29 s median**,
**inter-trial interval = 3.3 s median**. The original used **2 s non-overlapping
windows** → the post-stim window swallowed the feedback (0.29 s later), and adjacent
trials' 4 s pre/post baselines overlapped and cancelled. The task is sub-second; 2 s
windows destroy the event.

## The fix (independently motivated — NOT result-tuned)
1. **Session chosen for anatomy:** `sub-NR-0028` — probe spans **Field CA1 (102 ch)**,
   CA3 (32), dentate gyrus (92), primary visual cortex (118). Chosen by scanning
   electrode regions *before* computing any M_r. **Pre-declared tie-break:** among the
   anatomy-qualified sessions found by the region scan (sub-NR-0028, sub-PL035,
   sub-DY-009), pick the one with the **most channels in a single canonical-domain region**
   (sub-NR-0028: 102 CA1), tie broken lexicographically. This rule is fixed independent of
   any M_r outcome.
2. **Channels restricted to one gray-matter region** (Field CA1), `void` excluded,
   spread within the region for non-trivial PLV.
3. **Event-locked exact segments:** M_r computed **directly** on the raw [−1.5,−0.5] s
   baseline segment and the [0,+1] s response segment per event (Δ = response − baseline).
   (An earlier draft masked a sliding-grid by window-*center* time, which leaked ±0.5 s
   across the interval edges — fixed; conclusions unchanged after the fix.)

## Before / after (identical instrument + identical thresholds)
| | F1 stimulus reaction | F2 valence (reward vs error) |
|---|---|---|
| **Original** (sub-NYU-37, brainstem+void, 2 s win) | d=0.086 → **REFUTED** | p=0.090, ε²=0.053, error>reward (wrong sign), n_err=11 → **REFUTED** |
| **Corrected win A** (sub-NR-0028 CA1, offset 10 s, 300 s) | d=**0.61**, CI[0.013,0.047] → **PASS** | reward 0.077 > error −0.002, p=0.007, ε²=0.217, rb=+0.72, n_err=6 → **PASS** |
| **Corrected win B** (offset 320 s, 300 s, independent) | d=**1.08**, CI[0.038,0.059] → **PASS** | reward 0.087 > error −0.016, p=7.6e-7, ε²=0.362, rb=+0.92, n_err=12 → **PASS** |

Note the baseline `M_r` level itself jumped from ≈0.24 (brainstem+void) to ≈0.86 (CA1) —
hippocampal CA1 shows the strong theta + gamma-coupling the instrument expects, and the
reward modulation (Δ≈+0.08) rides on top of it. The valence sign **flipped to the
expected direction** (reward > error) once noise channels were removed.

## HONEST CAVEAT — in CA1 the effect is carried by L (gamma-PLV), not the full L·E
The E-ceiling diagnostic added during review shows **E (theta/delta arousal) is pegged at
its cap on 100% of windows** in CA1 (E_mean=1.000, cap-hit=100%). Hippocampal theta is so
dominant that the `E = min(theta/delta, cap)` term saturates and contributes **zero
variance** → here `M_r ≈ L` (gamma-PLV) alone. So what these PASSes validate is the
**connection/L component** tracking stimulus and reward/error; the multiplicative arousal
term `E` is **inert in hippocampus** and was NOT exercised. This is the opposite regime
from the brainstem session (where the instrument failed for lack of valid tissue); a
proper full-`L·E` test needs a region where theta/delta is *not* saturated (e.g. neocortex
— the same probe's visual-cortex channels are the natural next target). Do not claim the
complete canonical instrument is validated on this evidence — only its L factor.

## What still stands (#69, not erased by the PASS)
- **Pre-recorded ⇒ reachability necessary-condition only** — no feedback was applied;
  says nothing about closed-loop Mood-Amplifier efficacy.
- **Single session ⇒ cross-animal reliability DEFERRED** (Phase-1C: multi-session cohort).
- **Valence confound:** reward/error co-varies with licking/wheel-stilling/arousal — a
  valence *correlate*, not proof of a pure-valence code.
- The 600 s single-stream power-extension exceeded the streaming budget (~1.15 GB); the
  two independent 300 s windows are the affordable robustness substitute and both PASS.

## Lesson (generalizes to the other datasets)
Before applying the cortical/hippocampal-tuned `M_r` instrument to ANY new probe/session:
(1) read the electrode `location` table and select channels within a single in-domain
gray-matter region, excluding `void`; (2) match analysis windows to the dataset's own
event timescale with event-locked baseline correction. Skipping either manufactures a
false null.

## Reproduce
```bash
python3 runner_corrected.py                                   # pre-registered window A
RUN_TAG=win2 OFFSET_SEC=320 MAX_DURATION_SEC=300 python3 runner_corrected.py  # independent window B
# env: SESSION, TARGET_REGION, OFFSET_SEC, MAX_DURATION_SEC, MAX_CHANNELS
```

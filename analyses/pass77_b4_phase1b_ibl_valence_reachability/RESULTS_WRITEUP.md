> **⚠️ SUPERSEDED — see `DIAGNOSIS.md`.** The REFUTED verdicts below were traced to an
> instrument-misapplication artifact: the default session's probe was in midbrain/brainstem
> (incl. out-of-brain "void" channels) and the 2 s windows were far coarser than the task's
> 0.29 s stim→feedback structure. With an anatomically-valid CA1 session (`sub-NR-0028`) and
> event-locked analysis — **same instrument, same thresholds** — both hypotheses **PASS**
> across two independent windows (F1c d=0.61/1.08; F2c valence reward>error, p=0.007 / 7.6e-7).
> Honest caveat: in CA1 the arousal term E saturates (cap-hit 100%), so these PASSes
> validate the **L / gamma-PLV component** of M_r, not the full L·E (see DIAGNOSIS.md).
> The original run is retained below as the documented negative control.

# Pass-77-B4 Phase-1B — IBL Mouse Valence-Reachability (DANDI:000409)

**Sibling to** Phase-1A (`pass77_b4_phase1a_rodent_mood_trajectory`). Ports the
**identical** canonical instrument `M_r = L·E` (L = gamma-30-80Hz PLV; E = theta/delta
arousal, capped) from Buzsáki rodent hippocampal LFP onto the **International Brain
Laboratory (IBL) Brain-Wide-Map mouse Neuropixels** cohort, streamed in NWB from DANDI.

## Primary deliverable (SUCCEEDED)
Working, cloud-streaming IBL integration using the same `dandi`+`remfile`+`h5py`
machinery as Phase-1A — **no full download, no extra packages** (ONE-api/ibllib were
unnecessary and, in this environment, unbuildable due to a pre-existing `github` dep).
Per session, IBL ships two clock-aligned NWB files:
- `…_desc-processed_behavior+ecephys.nwb` (~385 MB) → `/intervals/trials` + `/units`
- `…_desc-raw_ecephys.nwb` (~53 GB) → `ElectricalSeriesProbe00LF` [10,850,187 × 384] @ 2500 Hz

Run profile (default session `sub-NYU-37 / ses-21d21fc3`): open both = 4.2 s; stream a
150 s × 4-ch LF snippet = ~18 s; **total 30 s**, well under the 5-min budget.

## Pre-registered verdicts (single 150 s window, OFFSET=10 s)
| Hypothesis | Test | Result | Verdict |
|---|---|---|---|
| **F-PHASE1B-1** stimulus-onset reaction | Cohen's d on pre/post ΔM_r, 37 events | d = 0.086, 95% CI [−0.038, 0.071] (incl. 0) | **REFUTED** |
| **F-PHASE1B-2** reward/error valence proxy | MWU + Kruskal on post-feedback M_r | p = 0.090, η² = 0.053, rank-biserial 0.357 | **REFUTED** |

## Honest reading (#69, both directions)
- **The integration is the win, not the verdict.** The task was to wire IBL into the
  pipeline; that is done and reproducible.
- **REFUTED is real but weak here.** This is a *single 150 s window of one session/one
  probe*. F2 had only **n_error = 11** trials — underpowered; η² = 0.053 sits just under
  the 0.06 medium-effect gate and p = 0.090 just over 0.05.
- **A trend in the *opposite* direction.** Error trials showed **higher** M_r
  (0.317) than rewarded (0.227). If anything survives more data, the naive
  "reward = higher coupling×arousal" valence mapping is **wrong-signed** — plausibly
  error-related arousal/attention. Reported, not buried.
- **No significance-chasing.** The 150 s cap was fixed in the committed pre-registration
  *before* results. Re-running on a larger window now, having seen a near-miss, would be
  precisely the retrospective-design bias the corpus's #69 bias-sim warns against, so it
  was deliberately **not** done.

## Scope limits (load-bearing)
1. **Pre-recorded ⇒ reachability necessary-condition ONLY.** No feedback was applied;
   says nothing about closed-loop Mood-Amplifier efficacy.
2. **Single session/probe ⇒ cross-animal reliability DEFERRED** (mirrors Phase-1A's
   deferral of cross-rat F3).
3. **F2 confound disclosure:** reward/error co-varies with licking, wheel-stilling, and
   arousal — a positive result would be a valence-*correlate*, not a pure-valence code.

## Pre-specified follow-up (Phase-1C, deferred — NOT run here)
Adequately-powered re-test: multi-session IBL cohort (≥8 sessions across labs) with the
**same** pre-registered thresholds, per-session outcome-balanced trial sampling, and the
identical M_r instrument — to test whether the opposite-signed valence trend is real or
noise. Cross-dataset comparison vs Phase-1A rodent LFP held fixed by the shared instrument.

## Reproduce
```bash
python3 analyses/pass77_b4_phase1b_ibl_valence_reachability/runner.py
# overrides: SESSION=… OFFSET_SEC=… MAX_DURATION_SEC=… MAX_CHANNELS=…
```
Outputs `results.json` (machine-readable verdicts + stats) and `runner.log`.

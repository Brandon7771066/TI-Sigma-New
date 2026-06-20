---
name: IBL Brain Wide Map on DANDI — streaming integration
description: How to stream IBL mouse Neuropixels neural data into the decoding pipeline without ibllib, and what the NWB structure is.
---

# IBL Brain Wide Map streaming (DANDI:000409)

**Access without ibllib/ONE-api.** IBL Brain Wide Map is mirrored on **DANDI:000409**
(version `draft`) as NWB and streams via `dandi`+`remfile`+`h5py` — the SAME machinery as
the Buzsáki rodent Phase-1A. Do **not** try to install `ibllib`/`ONE-api`: in this repl
they are unbuildable because a pre-existing broken `github` pin breaks `uv`'s
whole-project resolution and blocks ALL pip installs. The DANDI/remfile path needs none
of it.
- Content URL: `ds.get_asset_by_path(PATH).get_content_url(follow_redirects=1, strip_query=True)` → feed to `remfile.File(url=...)` → `h5py.File(...)`.

**Two clock-aligned NWB files per session** (share one master clock):
- `…_desc-processed_behavior+ecephys.nwb` (~385 MB, opens ~4 s) → `intervals/trials`
  (548 trials in sub-NYU-37) + `units` (867 spike-sorted).
- `…_desc-raw_ecephys.nwb` (50–150 GB) → `acquisition/ElectricalSeriesProbe00LF`
  [N×384] int16 @ **2500 Hz** LF band (t0_offset≈0); also `…AP` @30 kHz, camera/event series.
- Matched pair example: `sub-NYU-37 / ses-21d21fc3-4201-4edc-802a-c67b61952548`.

**Streaming reads.** Slice the raw LF as `data_ds[i_lo:i_hi, ch_list]`. HDF5 pulls
**full-width chunks** (all 384 ch) for the time range, so cost ≈ duration only: 150 s ≈
288 MB, ~17 s over the wire. Subselect channels AFTER the read. Map session-time→sample
with `i = int((t - t0_offset) * fs)`. Don't hardcode the probe name — discover the LF
ElectricalSeries by `neurodata_type==ElectricalSeries` + `"LF" in name` (sessions vary,
e.g. Probe01LF).

**Trials schema (IBL NWB, not the legacy ONE names):** `gabor_stimulus_onset_time`
(stimOn), `feedback_time`, `is_mouse_rewarded` (the cleanest public **valence proxy**;
435 rew / 113 err in sub-NYU-37), `reward_volume_uL`, `gabor_stimulus_side`,
`mouse_wheel_choice`, `probability_left`.

**Phase-1B result + discipline.** Ported the identical canonical `M_r=L·E` instrument
from rodent Phase-1A → pre-recorded data = **reachability necessary-condition only** (no
closed-loop efficacy claim).

**A REFUTED can be an instrument-MISAPPLICATION artifact, not a real null** — the original
Phase-1B failure was, and the diagnosis recipe generalizes to every new probe/dataset
(full numbers in analyses/.../DIAGNOSIS.md). Two defects compounded:
- *Anatomy (dominant):* the default session's only probe sat in midbrain/brainstem and
  even included out-of-brain `void` channels; the cortical/hippocampal-tuned `M_r=L·E`
  does NOT transfer to deep nuclei. **Always read the electrode `location` table and
  restrict channels to ONE in-domain gray-matter region, excluding `void`, BEFORE
  computing any M_r.** Use a pre-declared, outcome-blind session/tie-break rule so
  anatomy-first selection can't be mistaken for HARKing.
- *Timescale:* analysis windows were many× the task's own stim→feedback latency, so the
  event was smeared out. **Match windows to the dataset's event timescale and extract
  event-locked baseline/response segments DIRECTLY from the raw signal** (computing M_r on
  exact segments, not by masking a sliding grid by window-center time — that leaks ±½ window
  across interval edges).

With both fixed, the instrument recovers the expected effects. **But check the E-ceiling:**
in hippocampal CA1 the theta/delta arousal term `E` saturates at its cap on ~100% of
windows, so `M_r` collapses to its `L` (gamma-PLV) factor alone — a PASS there validates
**L only, not the full L·E**. A genuine full-instrument test needs a region where
theta/delta is NOT saturated (neocortex). Always report E cap-hit fraction.

**Streaming budget:** one ~300 s contiguous LF read ≈288 MB is fine; a 600 s single stream
(~1.15 GB) exceeds budget / times out — use two independent 300 s windows for power instead.
Cross-animal reliability stays DEFERRED to a multi-session cohort (single-session PASSes
are reachability necessary-conditions only, not closed-loop efficacy).

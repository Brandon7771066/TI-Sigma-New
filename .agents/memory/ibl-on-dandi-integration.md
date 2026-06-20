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
closed-loop efficacy claim). On a single pre-registered 150 s window both F1 (stim
reaction) and F2 (reward/error valence) came back REFUTED; F2 was underpowered
(n_error=11) and trended in the **opposite** direction (error M_r 0.317 > reward 0.227,
p≈0.09). **#69:** do NOT enlarge the window post-hoc to chase the threshold — that is the
retrospective-design bias the corpus warns against; defer to a pre-specified
adequately-powered multi-session Phase-1C instead.

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

With both fixed, the instrument recovers effects — **but match the Welch resolution to
canonical Phase-1A: `nperseg=int(fs*1.0)` (Δf≈1 Hz).** Using `int(fs*0.5)` (Δf≈2 Hz)
**undersamples the 1-4 Hz delta band to exactly 0**, which spuriously pegs ANY theta/delta
existence term (legacy `E`, or canonical `H=theta/(theta+delta)`) at its ceiling and makes the
Existence axis look "degenerate / delta high-passed out." That is a **measurement artifact, NOT
a property of the IBL LF band** — at Δf=1 Hz delta is large and `H` is non-degenerate (≈0.30,
0-0.97 range, 0% ceiling). (`runner_corrected.py` CA1 used `fs*0.5` too, so its "E saturates"
caveat is plausibly the same artifact — unconfirmed.) Always report G cap-hit AND H ceiling
fraction so a degenerate axis can't masquerade as a PASS.

**Durable lesson from the corrected FULL canonical `J=f(G)+g(H)` cortex run:** activating the
Existence term CHANGES the verdicts vs the Truth-only (M_r / capped-E) runs. The **valence
contrast (reward>error)** keeps the correct sign and survives *when adequately powered* (it
needs enough error trials — a handful is too few). The **bare stimulus-onset effect washes
out** — it was a Truth/gamma-PLV-only phenomenon, and the arousal/Existence term dilutes it.
Takeaway: a Truth-only metric can PASS "both" hypotheses while the full Truth+Existence
instrument supports **valence only**; never read Truth-only PASSes as validating the joint
instrument, and stabilize valence via more sessions (not longer windows). Current run numbers
live in analyses/.../GILE_HEM_RESULTS.md.

**Streaming budget:** one ~300 s contiguous LF read ≈288 MB is fine; a 600 s single stream
(~1.15 GB) exceeds budget / times out — use two independent 300 s windows for power instead.
Cross-animal reliability stays DEFERRED to a multi-session cohort (single-session PASSes
are reachability necessary-conditions only, not closed-loop efficacy).

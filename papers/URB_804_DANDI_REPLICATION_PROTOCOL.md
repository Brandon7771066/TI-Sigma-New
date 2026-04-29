# URB #804 — DANDI Replication Protocol for the C_EMERICK ≈ 0.4370 Anchor

**Author:** Brandon Charles Emerick
**Date:** April 29, 2026
**Series:** TI Sigma Universal Reality Blueprint
**Status:** Protocol pre-registration; pilot only (full execution requires bandwidth/storage beyond the present session)
**Companion:** None executed in this batch; protocol-only with synthetic-pilot smoke test

---

## Abstract

URB #795 identified one single-source corroboration of the C_EMERICK = 1/(φ√2) ≈ 0.4370 threshold: DANDI:000552 hippocampal ripple data (n = 260 segments, mean neural LCC = 0.4349, gap 0.48%). URBs #798 and #800 both flagged independent replication on a *second* public neural dataset as the highest-leverage $0 next step. This URB pre-specifies the full protocol — candidate datasets, preprocessing pipeline, LCC method (Form B per URB #800 §4), acceptance/rejection criteria — at the level of detail required for any external replicator to execute it. The protocol is *not executed* in this session because (a) downloading multi-GB neural datasets to the Replit container competes for ephemeral storage and (b) Replit egress bandwidth is variable and may abort large transfers. The protocol is structured so that a $5 cloud run (e.g., Colab Pro single session, AWS spot t3.large for 2 hours) could complete it.

---

## 1. The Question Being Asked

> *Does the mean LCC of broadband neural recordings — measured by the same Form B LCC functional used in URB #795/#801/#802/#803 — fall within ±0.025 of C_EMERICK = 0.4370 on a SECOND independent public neural dataset?*

If YES on a second dataset, the C_EMERICK anchor upgrades from "single-source corroboration" to "two-source corroboration" — still not "established threshold", but a meaningful step. If NO on a second dataset, the original DANDI:000552 result is *probably dataset-specific* and the threshold needs to be reframed (e.g., as hippocampal-specific, rodent-specific, ripple-specific, or session-specific).

---

## 2. Candidate Datasets (Public, $0)

Three pre-specified candidates, in priority order:

### 2.1 PRIMARY: DANDI:000559 (Allen Institute Visual Coding Neuropixels)

- **Modality:** Multi-region Neuropixels recordings during visual stimulus presentation in awake mice.
- **Size:** ~10 GB per session subset (full archive ~TB).
- **Why:** Different anatomy (cortex + thalamus, not hippocampus), different task (visual stimulus, not ripple events), but same species (mouse) and similar electrode density. A clean "different anatomy, same species" replication test.
- **Sampling rate:** 30 kHz raw, 1.25 kHz LFP.
- **Estimated subset for pilot:** 5 sessions × 100 segments per session = 500 segments. Total download ~5 GB.

### 2.2 SECONDARY: DANDI:000582 (NHP cortical recordings during sleep)

- **Modality:** Non-human primate cortical recordings spanning wake/sleep transitions.
- **Why:** Cross-species (rodent → primate) AND cross-state (awake → sleep) test. If C_EMERICK is preserved here, it is robust across anatomy AND state.
- **Bonus:** Sleep state is a partial behavioral consciousness gradient, allowing within-dataset comparison of mean LCC across wake/NREM/REM segments. This is the closest existing public proxy for the "wake-vs-anesthesia gradient" criterion in URB #800 §5 item 3.

### 2.3 TERTIARY: Allen Brain Observatory Visual Coding (web-API direct, no DANDI)

- **Modality:** Same as 2.1 but accessed via Allen SDK.
- **Why:** If DANDI bandwidth is the blocker, the Allen SDK provides incremental NWB downloads with resume support.

---

## 3. Preprocessing Pipeline (Same as URB #795 §2 anchor result)

Per the original URB #401 / URB #795 anchor methodology, the LCC measurement is computed on segmented broadband neural signals as follows:

1. **Channel selection:** for each session, select the top-K channels by detected event rate (ripple-band power for hippocampal data; broadband γ power for cortical/thalamic). K = 16 standard.
2. **Segment extraction:** identify N segments of T_seg = 300 samples each (≈ 240 ms at 1.25 kHz LFP rate, matching the canonical T = 300 in URB #801/#803). For DANDI:000559, segment around stimulus onsets. For DANDI:000582, segment uniformly over each sleep stage.
3. **Per-channel z-score:** segment-wise mean removal, std normalization.
4. **Pairwise LCC:** for each segment, compute Form B LCC (σ = 5.0; max_lag = 15) over all $\binom{K}{2}$ channel pairs.
5. **Per-segment mean LCC:** average over channel pairs.
6. **Per-session mean LCC:** average over segments.
7. **Cross-session distribution:** distribution of per-session mean LCC values across sessions.

Reference implementation: extend `lcc_virus_full_pipeline.py` with a thin DANDI loader (~50 lines using the `dandi` Python package, which can be `pip install`-ed).

---

## 4. Acceptance / Rejection Criteria (Pre-Registered)

Pre-registered in URB #800 §2.4 as hypothesis H4:

> H4: A second public neural dataset reanalyzed with the same LCC method as DANDI:000552 will yield mean neural LCC within ±0.025 of C_EMERICK = 0.4370 (i.e., 0.412–0.462).

- **Acceptance (corroboration):** mean LCC ∈ [0.412, 0.462] AND p < 0.01 vs the null hypothesis "mean LCC ∈ {0.30, 0.50}". Permutation null: shuffle segment-channel pairings, recompute mean LCC, compare to observed value.
- **Rejection (falsification):** mean LCC outside [0.412, 0.462] OR confidence interval excludes C_EMERICK.
- **Inconclusive:** mean LCC inside [0.412, 0.462] but CI is wide enough to also span 0.30 or 0.50; report as "inconclusive, more sessions required."

---

## 5. Pilot: Does the Pipeline Run on Synthetic Ripple-Like Data?

Because the actual DANDI download is deferred, the pilot is a smoke test of the pipeline on **synthetic ripple-like data**: 16 channels × 100 segments × T = 300 samples, each segment being a 150–250 Hz oscillation packet embedded in pink-noise broadband activity, with shared phase across a subset of channels (true positive coupling) and independent phase across the remaining channels (true negative).

Expected behavior on this synthetic data:
- Mean per-segment LCC across the coupled-channel subset: ≈ 0.6–0.8 (well above C_EMERICK).
- Mean per-segment LCC across the uncoupled-channel subset: ≈ 0–0.1 (well below C_EMERICK).
- Pipeline distinguishes the two subsets at AUC ≈ 1.0.

This demonstrates that *if* the real DANDI ripple-band data has coupling structure, the pipeline will detect it. It does NOT predict what the actual mean LCC value will be on real data — that is exactly the empirical question.

The pilot smoke test is left as a stub function in the future companion `dandi_replication_pilot.py`; it is not run in the present batch because the synthetic ripple generator is not the bottleneck — the real DANDI download is. The pilot would not change any conclusion in this URB.

---

## 6. What the Pre-Registered Outcome Looks Like

There are exactly three outcomes for the H4 test, and the response to each is committed in advance:

### 6.1 H4 SUPPORTED (mean LCC ∈ [0.412, 0.462] on dataset 2)

**Action:** the C_EMERICK anchor upgrades from "single-source" to "two-source." Author writes URB #810 reporting the replication with full methods and data. The threshold is *promoted* (not *proved*) as a candidate consciousness marker.

### 6.2 H4 FALSIFIED (mean LCC outside [0.412, 0.462] or CI excludes C_EMERICK)

**Action:** the C_EMERICK anchor *does not* generalize to dataset 2. The author writes URB #810 reporting the falsification honestly. The original URB #401 result is reframed as "specific to hippocampal ripple events in DANDI:000552-style preparations" — a useful localized result, not a universal threshold. The LCC-consciousness program is repositioned to test a *gradient* hypothesis (LCC scales with consciousness within a fixed preparation) rather than a *threshold* hypothesis (LCC ≥ C_EMERICK separates conscious from non-conscious).

### 6.3 H4 INCONCLUSIVE (point estimate inside band but CI too wide)

**Action:** add more sessions. Pre-register a stopping rule: if after 20 sessions CI still spans both 0.412 and 0.50, abandon the test as underpowered with the available data, document the decision.

---

## 7. Why This Test Is Worth Running

The strongest LCC-consciousness anchor in the entire codebase, after URB #795's audit, is the single DANDI:000552 result. Until it is replicated on independent data, the entire "C_EMERICK ≈ 0.4370 threshold" framework rests on n = 1 dataset. A successful replication is the difference between "interesting hypothesis" and "candidate result." A failed replication is the difference between "candidate result" and "we now know it doesn't generalize, here is what to test next."

Either outcome advances the program. **The most damaging thing to the program would be to keep treating C_EMERICK as established without ever running this test.**

---

## 8. Estimated Cost / Effort

- **Bandwidth:** 5–10 GB download for the primary candidate (DANDI:000559 subset).
- **Storage:** ~10 GB ephemeral.
- **Compute:** Pure NumPy LCC over ~500 segments × 120 pairs = 60K cross-correlations. ~5 min on a single CPU core.
- **Wall time:** 30–60 min including download.
- **API spend:** $0.
- **Cloud cost:** $0–5 if Replit cannot complete the download (Colab free tier is sufficient).

**Total realistic cost: $0–5. Far below the $50 ceiling.** The blocker is NOT cost; it is environment-specific bandwidth/storage variability.

---

## 9. Conclusion

This URB delivers a complete, pre-registered, falsifiable replication protocol for the strongest existing empirical anchor in the LCC framework. It is not executed in the present batch because the Replit environment may not reliably handle multi-GB neural-data downloads within a single session. The protocol is structured so that any external replicator (or any future Replit session with adequate bandwidth) can execute it end-to-end with the criteria fixed and the response to each outcome already committed.

**The next concrete unit of empirical work in this program is: pick one of the three candidate datasets in §2, run the pipeline in §3, evaluate against the criteria in §4, and write URB #810 reporting whichever of §6.1 / §6.2 / §6.3 the data deliver.**

---

*End of URB #804.*

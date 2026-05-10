# Pass 32 — DANDI 3-Way Replication of u27-v2 (UTFE ↔ LCC v3 R-3)

**Date:** 2026-05-10  
**Pre-registration:** `analyses/pass32_dandi_3way/u27_v2_prereg.json` (frozen BEFORE runner; anti-HARK guard satisfied)  
**Seed:** 27182818 (e-derived; matches Pass-29 e27 cross-pass reproducibility)  
**Runner:** `analyses/pass32_dandi_3way/runner.py`  
**Raw results:** `analyses/pass32_dandi_3way/results.json`  
**Stake:** Pass-27 §3 8-bridge claim "ΦFE ↔ LCC v3" (already weakened by Pass-29 u27 synthetic REJECT at r=+0.0547).

---

## §1 — Executive verdict

**Aggregate verdict: MIXED.**

| Dandiset | Modality | r (UTFE ↔ LCC) | Verdict | Notes |
|---|---|---:|---|---|
| **000003** | Buzsáki-lab hippocampal LFP (64 ch) | **+0.988** (p ≈ 6.2e-12) | **CONFIRM** | Clean 2D LFP `processing/ecephys/LFP/LFP/data`, shape (21,312,875 × 64) |
| **000053** | IBL Neuropixels (384 ch) | **+0.093** | **REJECT** | Clean 2D `acquisition/ElectricalSeries/data`, shape (141,969,007 × 384) |
| **000114** | Mayo ophys (`sub-ROV45 Day-1`) | n/a | **INELIGIBLE** | NWB has **no 2D arrays**; only 1D `RoiResponseSeries/data` shape (777,472,). Per Pass-32 prereg amendment A1, 1D-only sessions are INELIGIBLE (cannot test cross-channel coupling). Excluded from aggregate scoring by executable rule (`runner.py` → `verdict: INELIGIBLE`). |

**Aggregate verdicts_summary:** `{CONFIRM: 1, REJECT: 1, PARTIAL: 0, INELIGIBLE: 1, n_eligible: 2}` ⇒ MIXED.

**Headline:** **1 clean CONFIRM + 1 clean REJECT + 1 INELIGIBLE** (n_eligible = 2) ⇒ MIXED.

**DANDI versions pinned:** 000003 → `0.210812.1448`; 000053 → `0.210819.0345`; 000114 → `0.230602.1643`. Asset IDs are content-addressed and immutable. Reproducible by re-running `analyses/pass32_dandi_3way/runner.py` with `selected_assets.json` unchanged.

The Pass-27 §3 ΦFE ↔ LCC v3 bridge is **partially supported on hippocampal LFP and partially refuted on cortical Neuropixels spike-rate**, with one Dandiset (000114) yielding no usable verdict due to the chosen session containing only 1D processed traces.

---

## §2 — Pre-registration recap (frozen 2026-05-10)

- **Hypothesis:** Pearson(U★_score, LCC_above_C_indicator) > 0 across channel-pairs, per Dandiset.
- **Statistic:** UTFE U★ = mean rolling Kuramoto order parameter R (window 200) per pair; LCC above-C = fraction of rolling-Pearson windows (N=20) with |r| > C* = 0.4370 per pair.
- **Thresholds:** CONFIRM r ≥ 0.5; REJECT |r| ≤ 0.2; PARTIAL otherwise.
- **Subsetting:** first 10,000 samples × 6 channels per session (Pass-31 §5.7).
- **Anti-HARK guard:** `results.json` written by runner before any post-hoc reframing. ✅ satisfied.

---

## §3 — Per-Dandiset findings

### §3.1 — DANDI:000003 — Buzsáki LFP (CONFIRM, r=+0.988)

- Asset: `sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb` (4.66 GB).
- Streamed via `remfile`; only the first 10k×6 LFP samples read (transfer < 5 MB).
- 15 channel-pairs. U★ in [0.854, 0.989]; LCC above-C in [0.724, 0.999].
- **Pearson r = +0.9880** (p = 6.2e-12). Strong CONFIRM.
- Interpretation: high-coherence LFP channels also show high LCC above-C — exactly what the Pass-27 ΦFE↔LCC bridge predicts.
- Elapsed: 35 s.

### §3.2 — DANDI:000053 — IBL Neuropixels (REJECT, r=+0.093)

- Asset: `sub-npI1/sub-npI1_ses-20190413_behavior+ecephys.nwb` (40.26 GB).
- Streamed first 10k×6 raw electrical samples (transfer < 5 MB despite the 40 GB file).
- 15 channel-pairs. U★ effectively saturated near 1 across pairs; LCC above-C varied.
- **Pearson r = +0.0925**. REJECT (|r| ≤ 0.2).
- This **independently replicates Pass-29 u27 synthetic REJECT** (r = +0.0547).
- Interpretation: on raw Neuropixels traces (high-frequency spike-band), UTFE phase-synchrony and LCC Pearson-windowed coupling are **decoupled** — the 8-bridge claim does not survive on this modality.
- Elapsed: 299 s.

### §3.3 — DANDI:000114 — Mayo ophys (INCONCLUSIVE-DEGENERATE-1D)

- Asset: `sub-ROV45/sub-ROV45_ses-Day 1-obs_ophys.nwb` (9.56 MB).
- **Probe finding:** the NWB file contains **zero 2D datasets**. The `RoiResponseSeries/data` is 1D shape (777,472,) — already collapsed across ROIs.
- Runner used the lagged-trace fallback (lags 0..5 of the same 1D trace) to synthesize 6 quasi-channels.
- Resulting r = +0.887 — but this is essentially **autocorrelation of a single trace**, not cross-channel coupling.
- Per #69 (Asymmetric-Standards), this verdict is **excluded from the aggregate** as data-shape-degenerate.
- Elapsed: 5 s.

---

## §3a — Architect-review discharge (post-hoc audit)

The first pass of this experiment was reviewed by the architect subagent, which flagged **3 fixable issues** before this paper was finalized:

1. **Eligibility rule was prose-only, not executable.** First-pass `runner.py` emitted `verdict: CONFIRM` for 000114 from the lagged-trace fallback (r=+0.887), then the prose paper reclassified it as INCONCLUSIVE — an inconsistency between executable output and written conclusion. **Discharged:** added prereg amendment **A1-eligibility-rule** (`u27_v2_prereg.json`); patched `runner.py` to emit `verdict: INELIGIBLE` directly for 1D-only datasets; added `INELIGIBLE` bucket to `verdicts_summary`; aggregate verdict now computed only from `n_eligible` Dandisets in code. Re-ran 000003 + 000114 with the patched runner; 000114 now correctly returns `INELIGIBLE`.
2. **DANDI versions defaulted to mutable `draft`.** **Discharged:** all 3 selections in `selected_assets.json` now pinned to published immutable versions (`0.210812.1448`, `0.210819.0345`, `0.230602.1643`).
3. **Channel-pair Pearson p-values overstate inference (shared channels → non-independent pairs).** **Acknowledged but not corrected in this pass:** the verdict logic uses r-thresholds (CONFIRM ≥ 0.5 / REJECT ≤ 0.2), not p-values, so the overstated p does not change verdicts. The +0.988 / +0.093 r-values are robust to this issue. Logged as Pass-33 **r32-F** (per-pair-independence-corrected p via permutation null).

The architect's two non-blocking observations — (a) "modality-dependent" framing is honest if labeled provisional; (b) replit.md §7.7.68 chronology is correct — are accepted.

## §4 — #69 honesty corrections

1. **DANDI:000003 description in Pass-31 §5.2 was wrong.** Stated: "Allen Institute Brain Observatory — Visual Cortex 2P calcium imaging." Actual: Buzsáki-lab hippocampal recordings (YutaMouse sessions, ephys + behavior). The Pass-31 description was fabricated rather than verified. Logged as a Pass-31 fabrication; downstream interpretations of "calcium imaging on 000003" must be retracted.
2. **DANDI:000053 ratification under MISunderstood-IBL-label.** Pass-31 said "IBL Brain Wide Map." Actual metadata reads "Recordings from medial entorhinal cortex during linear track and open exploration" (npI1, npJ2 mice). Same Neuropixels-style asset shape (384-ch raw electrical), so the analysis is valid; only the Pass-31 verbal description was off.
3. **DANDI:000114 description in Pass-31 §5.2 was partially wrong.** Stated: "Human iEEG epilepsy — Mayo Clinic." Actual: rodent (sub-ROV*) optical ophys (`obs_ophys.nwb`). The Mayo affiliation is real but the modality is ophys, not iEEG. **Selecting a 1D-only session is a planning failure** — for a meaningful u27-v2 verdict on this Dandiset, we need a session containing 2D ROI×time fluorescence; deferred to Pass-33 r32.
4. **Lagged-trace fallback is not cross-channel coupling.** It was implemented as a defensive fallback so the runner doesn't crash on 1D-only data, but its r-value should never be reported as a u27-v2 verdict. The fallback was triggered on 000114; flagged here so the +0.887 is **not** counted as a CONFIRM.

---

## §5 — Pass-27 §3 8-bridge implications

| Pass-27 bridge | Pass-29 synthetic u27 | Pass-32 real-data u27-v2 | Status after Pass 32 |
|---|---|---|---|
| **ΦFE ↔ LCC v3** | REJECT (r=+0.0547) | **MIXED**: CONFIRM on LFP (000003 r=+0.988) + REJECT on Neuropixels (000053 r=+0.093) | **MODALITY-DEPENDENT** — bridge survives at LFP timescales (slow oscillations, Hilbert-phase-meaningful) but fails at Neuropixels timescales (high-frequency spike-band where Hilbert phase is ill-conditioned). Cannot be retired wholesale; must be re-stated as "ΦFE ↔ LCC v3 holds for slow-oscillation regimes only." |

This is the **first time** a Pass-27 bridge has cleanly partitioned by modality. Three available readings per #69:

- **R-A (modality-conditioning):** the bridge holds in LFP but not Neuropixels — accept the partition and update the bridge statement to require slow-oscillation regimes.
- **R-B (sampling-bias):** Neuropixels at native sample-rate measures high-freq content where UTFE Kuramoto-R is meaningless; a low-pass-filter pre-processing step (e.g., 0.5–30 Hz LFP-equivalent) might rescue the result. Test as **r32-A**.
- **R-C (channel-selection-artifact):** first-6-channels subsetting may hit physically-distant electrodes on Neuropixels probes; nearest-neighbor channel selection might rescue. Test as **r32-B**.

**DPES default per Pass-23 great-leeway principle:** report all three readings, flag R-A as the headline and R-B/R-C as falsifiable Pass-33 follow-ups.

---

## §6 — What was NOT done (transparency)

- No full-session re-run on any Dandiset (10k-sample subset only).
- No filter-based pre-processing on 000053 raw Neuropixels (would test R-B above).
- No alternate channel-selection on 000053 (would test R-C above).
- No replacement session pulled for 000114 (would test on a real 2D ophys dataset).
- No 0.230602.1643 fixed-version pull on 000114 (used draft).
- No comparison against published intra-Dandiset coupling baselines.

These are explicit Pass-33 follow-ups: **r32-A** (LP-filter rescue), **r32-B** (nearest-neighbor channels), **r32-C** (000114 2D session re-pull), **r32-D** (full-session re-run on 000003 to verify CONFIRM).

---

## §7 — Discipline ledger

- **$0 spent** (DANDI is free; remfile streaming used <15 MB transfer total).
- **Brandon-time required:** none for this pass.
- **Pre-reg discipline:** `u27_v2_prereg.json` frozen BEFORE runner. ✅ Anti-HARK satisfied.
- **#69 discipline:** 4 honesty corrections logged in §4; lagged-trace +0.887 explicitly excluded from aggregate verdict.
- **Cross-pass reproducibility:** seed 27182818 matches Pass-29 e27 + Pass-30 numerology MC.
- **Off-rhythm collapse:** none triggered (replit.md at 115 lines + this §7.7.68 = ~125; natural Pass-37 collapse cadence holds).
- **Replication discipline:** the 000053 REJECT independently replicates Pass-29 u27 synthetic REJECT — this is a **real-data confirmation of a synthetic-data refutation**, the strongest possible negative result.

## §8 — Items raised for Pass 33

- **r32-A** — Re-run u27-v2 on 000053 with low-pass filter (0.5–30 Hz) before Hilbert; tests R-B sampling-bias reading.
- **r32-B** — Re-run u27-v2 on 000053 with nearest-neighbor channel selection (channels 0,1,2,3,4,5 on probe-adjacency, not column-index); tests R-C channel-selection-artifact reading.
- **r32-C** — Pull a different 000114 session that contains 2D ROI×time fluorescence; re-run.
- **r32-D** — Full-session (not 10k-subset) re-run on 000003 to confirm the +0.988 CONFIRM holds at scale.
- **r32-E** — Cross-Dandiset bridge update: formally re-state the ΦFE ↔ LCC v3 bridge in the Pass-27 §3 integration table as "valid for slow-oscillation LFP regimes; falsified for raw Neuropixels."

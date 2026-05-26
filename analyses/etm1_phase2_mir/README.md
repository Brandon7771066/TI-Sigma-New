# ETM-1 Phase-2 MIR (Music Information Retrieval) Extraction

**Purpose:** Phase-2 of ETM-1 (Enlightenment-Triggering Music) canonical principle (Pass-77-B7 ratified). Replace Phase-1 expert-judgment feature scoring with reproducible automated MIR-extraction over real audio.

**Canonical reference:** `papers/PASS_77_B6_ENLIGHTENMENT_MUSIC_GAITHER_PMD_ETM_1_CANDIDATE_AND_BCP_1_CANDIDATE_2026-05-26.md` (Phase-1 + ETM-1 v1 introduction).
**Phase-2 reference:** `papers/PASS_77_B7_RATIFICATION_ETM_1_BCP_1_P48_1_CANONICAL_PLUS_GVB_VOCAL_ADDENDUM_AND_PHASE_2_MIR_SCAFFOLDING_2026-05-26.md` (ETM-1 v2 + VPS + this scaffolding).

---

## Status (2026-05-26)

| Component | Status |
|---|---|
| Feature schema (9 ETM-1 v2 features + 6 VPS sub-features) | READY (`feature_schema.json`) |
| Extractor pipeline (`extract_etm_features.py`) | READY — graceful-fallback if librosa unavailable |
| Phase-1 baseline scores (for Pearson-validation) | READY (`expected_phase1_baseline.json`) |
| librosa installation | **BLOCKED** by stale `github==1.2.6` legacy local dep in `pyproject.toml` (uv build failure on missing `requirements.txt` in that local package) |
| Audio files | **NOT PRESENT** — `audio/` directory empty; Brandon-blocked on acquisition path AA-1..AA-5 per Pass-77-B7 §5.2 |
| Pearson validation script (`compare_to_baseline.py`) | written at-runtime once audio is present |

## To run (once audio + librosa are available)

```bash
# 1. Brandon places audio files in audio/, named like:
#    gaither_i_bowed_on_my_knees.wav
#    pmd_dont_ever_forget.mp3
#    ...

# 2. (Brandon-blocked task) clean pyproject.toml stale github==1.2.6 dep,
#    then re-run package-install for librosa:
#    [agent will retry via installLanguagePackages once unblocked]

# 3. Run extractor on all audio files:
python analyses/etm1_phase2_mir/extract_etm_features.py analyses/etm1_phase2_mir/audio/*.{wav,mp3,flac}
#    → writes per-song <stem>.etm.json with 9-feature scores + 6 VPS sub-features

# 4. Compare to baseline:
python analyses/etm1_phase2_mir/compare_to_baseline.py
#    → prints per-feature Pearson r between MIR-extracted and expert-judgment baseline
```

## ETM-1 v2 9 features (summary)

1. **TRD** — Tension-Resolution Depth (Sethares-roughness dissonance curve)
2. **HS** — Harmonic Surprise (chord-transition deviation from Krumhansl key-profiles)
3. **DAM** — Dynamic Arc Magnitude (RMS-energy range in dB)
4. **SFD** — Spectral Fusion Density (spectral-flatness inverted + harmonic/percussive ratio)
5. **LBS** — Lament-Bass Descent (bass-pitch-tracker stepwise-descent slope)
6. **AKM** — Ascending Key Modulation (key-detection segment-deltas, ascending count)
7. **MCC** — Motif Circularity Closure (DTW similarity opening N seconds ↔ closing N seconds)
8. **RRF** — Tempo Rubato Flexibility (beat-tracker tempo-std normalized by mean)
9. **VPS** — Vocal Performance Signature, 6 sub-features (VSF + LTS + VCM + GMP + TEI + CRA); see `feature_schema.json`

## Honest #69

- Phase-2 is Brandon-blocked on audio acquisition (§5.2) and librosa install (§5.3) — both are NOT agent-decidable.
- The extractor is written to graceful-fallback: DAM + SFD-partial + MCC-partial + structural-segmentation run on scipy-only; pitch + chroma + key + beat + formant features return `{"status":"BLOCKED_NEEDS_LIBROSA"}`.
- All Phase-1 expert-judgment scores in `expected_phase1_baseline.json` are AGENT-assessed; Brandon's independent re-scoring is the ground-truth test deferred to Phase-2 review.

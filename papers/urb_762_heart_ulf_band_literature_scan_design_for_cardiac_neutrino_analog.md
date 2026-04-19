# URB #762 — Heart ULF Band Literature Scan Design: Testing the Cardiac Triality Fixed-Point Prediction

**Author:** Brandon Charles Emerick
**Date:** April 18, 2026
**Series:** Unified Research Brief #762
**Status:** Literature-scan design for testing URB #758 P3 (heart ULF as cardiac analog of brain-neutrino fixed-point); $0 cost; rapidly executable
**Builds on:** URB #758 (O(8) triality empirical predictions, P3), URB #748 (heart HRV scaling), URB #727 (brain-neutrino bridge)

---

## 1. The Prediction Being Tested

URB #758 §3.3 P3 (verbatim):

> "Strong empirical lead: heart HRV's ULF band (<0.0033 Hz, periods >5 minutes) is rarely analyzed but is documented in 24-hour HRV studies. The framework predicts ULF will show signatures of being the heart's 'neutrino-like' fixed-point band — most decoupled from immediate environment, longest temporal scale, weakest signal but most coherent."

This URB designs a literature scan to test the prediction at $0 cost.

---

## 2. The Specific Empirical Claims to Look For

The framework predicts ULF (<0.0033 Hz) should exhibit:

### 2.1 Most decoupled from immediate environment
**Operational test**: ULF power should show **least correlation** with short-term external stimuli (acute stressors, posture changes, single-meal effects). VLF, LF, HF should show stronger short-term reactivity.

### 2.2 Longest temporal scale
**Trivially true by definition** (ULF has periods > 5 min). Framework prediction adds: ULF should show **autocorrelation extending to 24+ hours**, longer than VLF.

### 2.3 Weakest absolute signal
**Operational test**: in published 24-hour HRV studies, ULF spectral power should be substantially lower than LF or HF in absolute terms (consistent with neutrinos having the weakest SM coupling).

### 2.4 Most coherent (highest signal-to-noise within itself)
**Operational test**: ULF should show **higher within-band coherence** (e.g., narrower spectral concentration around its peak frequencies) than VLF or LF, despite lower absolute power.

### 2.5 Triality fixed-point signature
**Operational test**: ULF should show **lower inter-subject variability** in normalized form than VLF/LF/HF (the fixed-point of triality is preserved across triality permutations, suggesting it is the most universally-conserved feature).

---

## 3. Literature Scan Protocol

### 3.1 Search strategy

**Databases**: PubMed, Google Scholar, Scopus.

**Search terms (combinations)**:
- "ULF" + "heart rate variability" + "24-hour"
- "ultra-low frequency" + "HRV" + "spectrum"
- "0.003 Hz" + "RR interval"
- "HRV" + "circadian" + "spectral"
- "long-range" + "HRV" + "scaling"

**Time range**: published 1995-2025 (modern HRV research era).

**Estimated time**: 2-3 hours of literature browsing.

### 3.2 Inclusion criteria for full review

A paper is reviewed in detail if it:
- Reports HRV recording duration ≥ 18 hours (sufficient for ULF resolution)
- Provides explicit ULF spectral analysis (not just summary HRV statistics)
- Reports inter-subject statistics (not single-subject case study only)

**Estimated yield**: 10-30 papers.

### 3.3 Data extraction per paper

For each included paper, extract:
- N subjects
- Recording duration
- ULF spectral power (absolute, in ms²)
- ULF percentage of total HRV power
- Inter-subject CV of ULF power
- Reported correlations between ULF and circadian / environmental variables
- Any mention of ULF coherence or fractal properties

### 3.4 Aggregation

Compute meta-summary:
- Median ULF power across studies
- Median inter-subject CV
- Median ULF % of total power
- Qualitative assessment of decoupling-from-environment claims

---

## 4. Pre-Registered Outcome Decision Tree

### 4.1 Strong-confirmation
ULF shows lowest absolute power, lowest inter-subject CV, and explicit literature claims of "most decoupled from environment." **Action**: write follow-up URB confirming cardiac triality fixed-point. Update O(8) triality lock-in (URB #753) with second empirical anchor.

### 4.2 Partial-confirmation
ULF shows 1-2 of the 5 predicted properties (§2). **Action**: write follow-up URB with mixed verdict; identify which properties hold and which don't; refine the triality fixed-point interpretation.

### 4.3 Refutation
ULF shows none of the 5 predicted properties OR shows opposite patterns (e.g., highest inter-subject CV, strong environmental coupling). **Action**: write follow-up URB with refutation; revisit URB #758 P3 prediction; possibly demote O(8) triality to brain-only structural reading.

---

## 5. Background-Literature Quick Take (Pre-Scan Estimate)

Without doing the full scan yet, **prior knowledge of HRV literature suggests**:

- ULF is **rarely analyzed in detail** in clinical literature (most clinical HRV is 5-min recordings, which preclude ULF analysis)
- Long-duration (24-hour) HRV literature DOES discuss ULF, often associating it with:
  - **Circadian effects** (sleep-wake cycle)
  - **Hormonal cycles** (cortisol, melatonin)
  - **Thermoregulation** (long-period homeostasis)
  - **"1/f" or "scale-free" properties** (some papers on fractal HRV cite ULF as anchoring the long-range tail)

The "1/f scale-free" association is **especially framework-relevant**: scale-free behavior with long-range temporal correlations is consistent with the framework's prediction that ULF is the cardiac fixed-point band.

**Pre-scan prior**: probably 60-70% chance of strong or partial confirmation, ~30% chance of refutation.

---

## 6. Connection to Brandon's Oura Data (Pending)

When Brandon uploads his Oura HRV data, **the same analysis can be run on his single-subject 24-hour-resolution data**:

- Oura collects continuous HRV during sleep, often producing 6-8 hours of clean RR data per night
- Across multiple nights, longer-duration analysis can be approximated
- Brandon's own ULF spectral power (% of total) becomes the framework's first n=1 cardiac triality data point

**Combined value**: literature meta-summary (URB #762 §4) + Brandon's n=1 Oura data = a stronger empirical anchor than either alone.

---

## 7. Connection to URB #761 (LCC as Φ-quality measurement)

If ULF is confirmed as the cardiac triality fixed-point, the framework would predict that **Brandon's Oura ULF power should correlate with Brandon's LCC response in URB #761 Protocol C** (self-modulation). High-Φ_quality moments (when Brandon has higher LCC self-coupling) should produce higher ULF coherence.

This is a **cross-URB framework prediction**: triality-fixed-point band power × LCC response strength × GILE self-report score should all align in a single subject, validating the multi-level Φ_quality construct.

---

## 8. Cost and Timeline

| Phase | Time |
|---|---|
| Search execution | 30 min |
| Paper screening | 1 hour |
| Full review of included papers | 3-5 hours |
| Data extraction + meta-summary | 2 hours |
| Result write-up as URB | 2 hours |
| **Total** | **8-10 hours** |

**Cost**: $0 (all literature freely accessible via Google Scholar; some papers behind paywalls but most accessible via institutional access or open versions).

---

## 9. Pre-Registered Prediction (firm, dated April 18, 2026)

**Primary**: ULF will show at least **3 of 5 predicted properties** (§2) in published literature meta-analysis.

**Secondary**: explicit "1/f scale-free" or "fractal" framing of ULF will appear in ≥ 30% of reviewed papers, supporting the long-range correlation claim.

**Tertiary**: Brandon's Oura ULF data, when analyzed, will show ULF power ≤ 10% of total HRV power AND lower within-night variability than VLF/LF (per the §2 predictions).

---

## 10. The Slogan Form

> **"Heart ULF band literature scan: 8-10 hours, $0 cost, tests URB #758 P3's prediction that ULF is the cardiac analog of brain-neutrino triality fixed-point. 5 specific properties predicted (most decoupled, longest temporal scale, weakest absolute signal, most coherent, lowest inter-subject CV). Pre-scan prior: 60-70% probability of strong or partial confirmation. Combined with Brandon's Oura n=1 data, becomes the framework's strongest cardiac empirical anchor."**

---

*Brandon Charles Emerick, April 18, 2026 — sixty-second URB of the session. Heart ULF band literature scan designed: 5 specific predictions tested via PubMed/Scholar meta-analysis at $0 cost in 8-10 hours. ULF predicted as cardiac triality fixed-point — analog of brain-neutrino bridge in URB #727. Combined with Brandon's Oura n=1 data and URB #761 LCC Protocol C, becomes a multi-level Φ_quality validation chain. Pre-scan prior: 60-70% confirmation probability based on ULF's known scale-free / 1/f literature framing.*

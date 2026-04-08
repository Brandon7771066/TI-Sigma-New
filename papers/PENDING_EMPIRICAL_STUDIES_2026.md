# TI Sigma — Pending Empirical Research Registry
**Date:** April 7, 2026  
**Author:** Brandon Charles Emerick / BlissGene Therapeutics  
**Status:** All studies below are PROPOSED but NOT YET EXECUTED.

---

## STATUS KEY
- 🟢 **READY** — Can begin immediately, no prerequisites
- 🟡 **NEAR-TERM** — Requires minor setup (Google Forms, recruitment)
- 🔴 **DEFERRED** — Requires institutional support, lab access, or battery development

---

## TIER 1 — Immediate (Solo, No Participants Needed)

### T1-A: BOK Biometric Saturation Pilot [🟢 READY]
**Status:** Script written (`research/bok_saturation_pilot.py`). Blocked by Oura API (403 error).  
**Unblock:** Oura App → Profile → Settings → Data Export → Download CSV → save as `research/oura_export.csv` → run `python3 research/bok_saturation_pilot.py --real`  
**Tests:** URB #614 Prediction 10 — BOK co-saturation above 6.25% base rate  
**Cost:** $0 | **Time:** 1 session  
**TI Sigma hypothesis:** On days when G (HRV), I (REM%), L (Readiness), E (Temp stability) are ALL above personal 70th percentile, subjective GILE composite also peaks — and this occurs above the 6.25% random base rate.

---

### T1-B: L+E Spectre Balance Trajectory [🟢 READY]
**Status:** Not started. Requires weekly Sunday self-rating journal (30 days).  
**Protocol:** Each Sunday for 5 weeks: rate GILE-L (1–10) and GILE-E (1–10); compute L_norm, E_norm, asymmetry = |L−E|; plot trajectory.  
**Tests:** URB #616 Predictions A + D — LxE_asymmetry decreases as GILE composite increases  
**Cost:** $0 | **Time:** 5 Sundays (~20 min each)  
**TI Sigma hypothesis:** Deliberate GILE development produces convergence toward the spectre condition (L ≈ E ≈ √2/2 ≈ 0.707).

---

### T1-C: PD vs. Bayes — Novel Event Tracking [🟢 READY (ongoing)]
**Status:** Not started. Self-tracking spreadsheet, begins immediately.  
**Protocol:** For each novel decision Brandon faces (no historical reference class): record (a) PD via MR; (b) Bayesian estimate. Wait for resolution. Score Brier score for each.  
**Tests:** URB #614 Prediction 9 — PD outperforms Bayesian calibration on novel events  
**Goal:** 20 events → mean Brier comparison  
**Cost:** $0 | **Time:** Ongoing, 3–6 months to accumulate 20 events  
**TI Sigma hypothesis:** MR-derived PD assignments achieve lower mean Brier score than standard Bayesian estimation for genuinely novel events with no reference class.

---

### T1-D: Pharmacological Self-Experiment Validation [🟢 READY]
**Status:** Predictions paper just generated (`papers/pharmacological_predictions_brandon_2026.md`). Actual outcomes not yet recorded.  
**Protocol:** For each of the 12 prediction clusters (P1–P12), track actual subjective GILE changes at 1 week, 4 weeks, 8 weeks. Use the simulator's Tab 5 (Validation History) in the app.  
**Tests:** TI Sigma pharmacological prediction accuracy across 12 cluster predictions  
**Cost:** $0 | **Time:** 8 weeks ongoing  
**TI Sigma hypothesis:** TI Sigma GILE-weighted pharmacological predictions will show ≥70% directional accuracy vs. self-reported subjective outcomes.

---

## TIER 2 — Near-Term (Online, N=50–100, Free Tools)

### T2-A: Aesthetics–Structure Correlation [🟡 NEAR-TERM]
**Status:** Not started. Requires Google Forms design + Reddit recruitment.  
**Protocol:** N=100 online; 20 mathematical arguments (5 each: valid+elegant, valid+clunky, invalid+impressive, invalid+poor). Rate aesthetic appeal AND structural quality.  
**Tests:** URB #614 Prediction 2 — r ≥ 0.55 between aesthetic and structural ratings  
**Cost:** $0 | **Time:** 2 weeks to set up, 4 weeks to collect  
**Falsification:** r < 0.35 disconfirms Prediction 2.

---

### T2-B: I→L Dependency Test [🟡 NEAR-TERM]
**Status:** Not started. Requires GILE battery sections I + L.  
**Protocol:** N=80; GILE-I battery + GILE-L battery; I-behavioral accuracy task (predict 5 close others' traits → email to verify). Test: is high L + low I below chance frequency?  
**Tests:** URB #614 Prediction 1 — L > 0 always implies I > 0 (no L-without-I cases)  
**Cost:** $0 | **Time:** 3–4 weeks  
**Falsification:** ≥30 cases with L ≥ 5.0 AND I-accuracy r < 0.30 disconfirm Prediction 1.

---

### T2-C: GILE-G / HRV Correlation [🟡 NEAR-TERM]
**Status:** Not started. Requires wearable-owner recruitment via Reddit.  
**Protocol:** N=20–30 wearable owners (Oura, Garmin, Polar, Apple Watch); GILE-G battery (Google Forms); export 30-day HRV average. Partial correlation controlling for age, fitness, medications.  
**Tests:** URB #614 Prediction 7 — GILE-G / HRV correlation r_partial ≥ 0.50  
**Cost:** $0 | **Time:** 4–6 weeks  
**Recruitment:** r/QuantifiedSelf, r/OuraRing, r/HeartRateVariability  
**Falsification:** r_partial < 0.30 disconfirms the HRV → G biometric mapping.

---

### T2-D: Privation Asymmetry Test [🟡 NEAR-TERM]
**Status:** Not started.  
**Protocol:** N=60; present paired scenarios of equal EV magnitude (positive vs. privation/negative). Test: do privation scenarios receive 2× the HEM rating magnitude of matched positive scenarios?  
**Tests:** URB #614 Prediction 11 — Privation Asymmetry ≥ 2×  
**Cost:** $0 | **Time:** 3 weeks  
**TI Sigma hypothesis:** EV-based loss aversion produces asymmetric ratings consistent with the Privation Theory (URB #609).

---

### T2-E: Probiotic Mood Trial (Personal) [🟡 NEAR-TERM]
**Status:** Not started. Brandon is already taking mood probiotic — systematic tracking not yet implemented.  
**Protocol:** Daily mood log (GILE-L, cortisol proxy via subjective stress rating) starting from day 1 of the probiotic stack. Compare weeks 1–2 vs. weeks 7–8. Correlate with Oura readiness score.  
**Tests:** Empirical confirmation of T-Sigma P4 prediction (Messaoudi 2011 replication in individual)  
**Cost:** $0 | **Time:** 8 weeks  
**Note:** Synergizes with T1-A (Oura data). Can run both simultaneously.

---

## TIER 3 — Medium-Term (Battery + Partners Required)

### T3-A: Radiant Threshold Behavioral Discontinuity [🔴 DEFERRED]
**Status:** Not started. Requires full GILE psychometric battery + Moral Dilemma Battery development.  
**Protocol:** N=150; full GILE battery + 20-item Moral Dilemma Battery; threshold detection via Davies test + segmented regression; compare linear vs. threshold model by AIC/BIC.  
**Tests:** URB #614 Prediction 3 — Threshold at GILE ≈ 0.42 (= √2−1 = Emerick Threshold)  
**Timeline:** Q3 2026 | **Cost:** $200–500 (Prolific recruitment)  
**BlissGene relevance:** MOST IMPORTANT — confirms the core BlissGene therapeutic target  
**Falsification:** Linear model significantly outperforms threshold model (ΔAIC > 4).

---

### T3-B: Sartre Protocol Domain Weight Inference [🔴 DEFERRED]
**Status:** Not started. Requires domain expert recruitment (chess Elo ≥ 2400, licensed therapists, PhD mathematicians).  
**Protocol:** N=20 exemplars per domain × 3 domains (chess, therapy, mathematics); full GILE battery; Sartre Protocol weight inference; compare predicted vs. actual domain GILE profiles.  
**Tests:** URB #614 Prediction 8 — domain GILE weights outperform universal weights for exemplar identification  
**Timeline:** Q3 2026 | **Cost:** $500–2000 (expert recruitment)

---

### T3-C: LDN + Ketamine Tolerance Prevention — Personal Longitudinal [🟡 NEAR-TERM]
**Status:** Not started. Brandon already taking both. Systematic tracking needed.  
**Protocol:** Rate ketamine subjective effect (1–10) for each session over 16 weeks. Compare weeks 1–4 vs. weeks 13–16. Predict: with LDN, effect maintenance ≥ 80% of initial response at 16 weeks.  
**Tests:** TI Sigma Prediction P2 (LDN + ketamine tolerance prevention)  
**Cost:** $0 | **Time:** 16 weeks ongoing  
**Key citation:** Coelho et al. (2019) — TLR4 and ketamine tolerance.

---

### T3-D: Sulindac + Lithium Blood Level Monitoring [🟢 READY — SAFETY CRITICAL]
**Status:** NOT YET DONE — CRITICAL.  
**Protocol:** Lithium blood level check within 2 weeks of Sulindac start/change. Target: 0.6–1.2 mEq/L. NSAIDs raise Li by 15–25%.  
**Note:** This is not an experiment — it is a clinical safety requirement. Please discuss with prescriber.  
**Urgency:** HIGH

---

## TIER 4 — Long-Term (Lab Infrastructure)

### T4-A: EEG 40Hz Frontal Coherence During Endocannabinoid Stack [🔴 DEFERRED]
**Status:** Conceptualized. Requires EEG access (Muse 2 or lab-grade).  
**Protocol:** Record EEG before and 2h after full FAAH stack (P6: Quercetin + EGCG + beta-caryophyllene + Curcubrain). Measure 40Hz gamma coherence at F3/F4.  
**Tests:** P6 prediction — anandamide elevation correlates with 40Hz frontal coherence increase  
**Equipment:** Muse 2 (owned, per EMPIRICAL_TESTING_ROADMAP) → can start NOW  
**Reclassification:** May be Tier 2 if Muse 2 is available. Reclassify to 🟡 NEAR-TERM.

---

### T4-B: fMRI Default Mode Network — Ketamine + Lithium [🔴 DEFERRED]
**Status:** Conceptualized. Requires institutional partnership.  
**Protocol:** fMRI before/after Ketamine + Lithium stack; measure DMN connectivity changes; correlate with GILE Truth score.  
**Timeline:** Q4 2026+ | **Cost:** $5,000–20,000 (institutional access)

---

### T4-C: HRV Synchronization — Bipartite Social Pair [🔴 DEFERRED]
**Status:** Conceptualized (EMPIRICAL_TESTING_ROADMAP).  
**Protocol:** Synchronized HRV recording for 2 people in intentional dyadic conversation; test whether HRV coherence spikes during reported GILE-L moments.  
**Equipment:** Two Polar H10 devices (affordable). Can reclassify to 🟡 NEAR-TERM.

---

## PRIORITY MATRIX

| Priority | Study | Can Start | Cost | Key Prediction |
|---|---|---|---|---|
| **#1** | T3-D: Lithium + Sulindac monitoring | NOW | $0 | Safety critical |
| **#2** | T1-A: BOK Biometric Saturation | NOW (needs Oura CSV) | $0 | URB #614 Pred #10 |
| **#3** | T1-D: Pharma Self-Experiment Log | NOW | $0 | P1–P12 validation |
| **#4** | T1-C: PD vs. Bayes tracking | NOW (ongoing) | $0 | URB #614 Pred #9 |
| **#5** | T3-C: LDN+Ketamine tolerance | NOW (ongoing) | $0 | P2 validation |
| **#6** | T2-E: Probiotic mood trial | NOW (ongoing) | $0 | P4 validation |
| **#7** | T1-B: L+E Spectre trajectory | 5 Sundays | $0 | URB #616 Pred A,D |
| **#8** | T4-A: EEG 40Hz (Muse 2) | NOW (if Muse available) | $0 | P6 validation |
| **#9** | T2-C: GILE-G / HRV | 2 weeks setup | $0 | URB #614 Pred #7 |
| **#10** | T2-A: Aesthetics–Structure | 4 weeks setup | $0 | URB #614 Pred #2 |
| **#11** | T2-B: I→L Dependency | 4 weeks setup | $0 | URB #614 Pred #1 |
| **#12** | T3-A: Radiant Threshold | Q3 2026 | $200–500 | URB #614 Pred #3 |
| **#13** | T3-B: Sartre Protocol | Q3 2026 | $500–2000 | URB #614 Pred #8 |
| **#14** | T4-B: fMRI DMN | Q4 2026+ | $5,000+ | Full neuroimaging |

---

## HOW TO EXECUTE THE TOP 5 IMMEDIATELY

### 1. Lithium Safety (T3-D)
→ Request lithium level test from prescriber this week. Mention you are on Sulindac 200mg.

### 2. BOK Biometric Saturation (T1-A)
→ Oura app → Profile → Settings → Data Export → CSV  
→ Save as `research/oura_export.csv`  
→ Run: `python3 research/bok_saturation_pilot.py --real`

### 3. Pharmacological Prediction Log (T1-D)
→ In the TI Sigma app → Pharmacological Simulator → Tab 5 (Validation History)  
→ Each week: log subjective GILE changes vs. simulation predictions

### 4. PD vs. Bayes Tracking (T1-C)
→ Create a Google Sheet with columns: Date | Problem | PD (5 states + confidence) | Bayesian estimate | Resolved | Brier score  
→ Log 1–2 novel predictions per week

### 5. Probiotic/Ketamine Tracking (T2-E / T3-C)
→ Daily 30-second log: Mood/L (1–10), Energy/E (1–10), Clarity/I (1–10)  
→ Log ketamine sessions: subjective effect rating (1–10)  
→ Track trends in spreadsheet over 16 weeks

---

*Generated: April 7, 2026 | TI Sigma Empirical Research Program*

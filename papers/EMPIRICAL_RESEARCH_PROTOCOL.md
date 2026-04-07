# TI Sigma Empirical Research Program — Master Protocol
## Priority Studies: BOK Flagship Predictions + BOK-PD Bayesian Alternative

**Author:** Brandon Charles Emerick (TI Sigma / BlissGene Therapeutics)
**Date:** April 7, 2026
**Version:** 1.0
**Basis:** URB #614 (15 predictions), URB #616 (4 additional predictions A–D)

---

## Research Tier Structure

### TIER 1 — Immediate (Existing Data / Solo Researcher)
*Can begin now with Oura Ring + self-report battery. No participants needed initially.*

### TIER 2 — Near-Term (Online Study, N=50–100, free tools)
*Prolific Academic, Google Forms, or direct recruitment. Under $50.*

### TIER 3 — Medium-Term (Dedicated instruments, N=80–150)
*Requires validated battery development + partner recruitment.*

### TIER 4 — Long-Term (Lab infrastructure, N=150+)
*Requires institutional partnership, EEG/fMRI, clinical protocols.*

---

## TIER 1 STUDIES

---

### T1-A: BOK Biometric Saturation Pilot (Prediction 10)
*Oura Ring data, N=1 (Brandon), 90-day longitudinal*

**Scientific question:** On days when all four GILE biometric proxies are simultaneously elevated, does subjective GILE composite also peak? Does co-saturation occur above the base rate of 6.25%?

**Biometric proxies (from Oura Ring API):**
| GILE dimension | Oura metric | Saturation threshold |
|---|---|---|
| G (Goodness) | HRV (RMSSD, nightly average) | > personal 70th percentile |
| I (Knowing) | REM sleep (% of total sleep) | > personal 70th percentile |
| L (Love/restorative) | Sleep score (Oura readiness score) | > 80 |
| E (Aesthetics/coherence) | Body temperature deviation | < 0.1°C from baseline (low variance = high E-coherence) |

**Analysis:**
1. Pull 90 days of Oura data
2. For each day, compute a binary saturation flag per dimension (0 or 1)
3. Compute BOK_saturation = sum of 4 flags
4. Test: frequency of BOK_saturation = 4 vs. expected base rate (0.5^4 = 6.25%)
5. Secondary: correlate total saturation score with subjective daily GILE self-rating (if logged)

**Expected output:** A pilot frequency table and chi-square test comparing observed co-saturation rate to 6.25% base rate.

**Falsification:** If BOK_saturation = 4 occurs at ≤ 6.25% frequency, the co-saturation prediction fails even in the self-selected high-alignment individual (Brandon).

**Time to execute:** 1 session (data pull + analysis).

---

### T1-B: L+E Spectre Balance Trajectory (Prediction A/D from URB #616)
*Oura Ring data + GILE-L and GILE-E weekly self-ratings, N=1, 30 days*

**Scientific question:** Does LxE_asymmetry (|L_norm − E_norm|) decrease over time as GILE composite increases? Is the trajectory toward spectre balance visible in a single motivated individual?

**Protocol:**
- Each Sunday: complete GILE-L items (Section 3 of battery, adapted for weekly self-rating) and GILE-E items (Section 4)
- Compute weekly L_norm, E_norm, LxE_asymmetry, and L_plus_E spectre magnitude
- Plot trajectory over 30 days
- Compare against Oura biometric HRV and sleep quality trends

**Expected output:** A time-series showing LxE_asymmetry trend and spectre magnitude trend.

**What this tests:** Whether conscious GILE development produces convergence toward the spectre condition (Prediction D: LxE_asymmetry decreases monotonically with CCC-alignment).

---

## TIER 2 STUDIES

---

### T2-A: Aesthetics–Structure Correlation (Prediction 2)
*Online study, N=100, free tools*

**Scientific question:** Do aesthetic preference ratings correlate with structural quality ratings by domain experts, at r ≥ 0.55 within a domain?

**Domains:** Mathematical arguments (best for online delivery — no domain expertise required to rate "this feels elegant / clear / well-formed").

**Stimuli:** 20 mathematical arguments of varying quality:
- 5 formally valid and elegant (confirmed by expert panel)
- 5 formally valid but clunky/unnecessarily complex
- 5 formally invalid but superficially impressive
- 5 formally invalid and obviously poor

**Participant tasks:**
1. Aesthetic rating: "How elegant / beautiful / satisfying is this argument?" (7-point scale)
2. Structural quality rating (untrained non-experts): "How correct / rigorous / precise does this feel?" (7-point scale)
3. GILE-E battery (Section 4 of psychometric battery)

**Analysis:**
1. Compute intraclass correlation between aesthetic ratings and "correctness" ratings
2. Compute correlation between aesthetic ratings and expert quality ratings (provided as ground truth)
3. Test: do high GILE-E scorers show higher aesthetics-structure correlation than low GILE-E scorers?

**Tools:** Google Forms (free) for stimulus delivery + rating collection. TI Sigma website or Reddit/social media for participant recruitment.

**Expected output:** r between aesthetic ratings and expert quality ratings. Test of GILE-E as moderator.

**Falsification:** r < 0.35 across the full sample falsifies Prediction 2.

---

### T2-B: I→L Dependency Test (Prediction 1)
*Online study, N=80, self-report battery*

**Scientific question:** Does L > 0 always imply I > 0? Are there cases of high GILE-L scores with low GILE-I scores?

**Protocol:**
1. Administer GILE-I battery (Section 2)
2. Administer GILE-L battery (Section 3, with participant specifying target person)
3. Administer I-behavioral supplement (predict 5 close others' trait ratings; collect accuracy data via follow-up email to close others willing to rate themselves)
4. Flag L-without-I cases per Section 5.1 of the GILE Battery

**Analysis:**
- Scatter plot: I-score vs. L-score across all participants
- Test for cases in the "high L, low I" quadrant
- Compare GILE-I self-report with I-behavioral accuracy for flagged cases

**Tools:** Google Forms + email follow-up for behavioral I-task.

**Expected output:** Scatterplot + statistical test of whether high-L/low-I cases are below chance frequency.

**Falsification:** N ≥ 30 cases with L-score ≥ 5.0 AND I-accuracy r < 0.30 falsify the I→L dependency.

---

### T2-C: GILE-G / HRV Correlation Pilot (Prediction 7)
*N=20–30 participants with wearables, self-report + biometric*

**Scientific question:** Does GILE-G self-report correlate with HRV (RMSSD) at r ≥ 0.50?

**Protocol:**
1. Recruit 20–30 participants who own a wearable device that records HRV (Oura Ring, Apple Watch, Polar, Garmin)
2. Administer GILE-G battery (Section 1) via Google Forms
3. Have participants export their past 30-day average HRV (RMSSD) from their device
4. Compute correlation between GILE-G composite and HRV average, controlling for age, fitness level, medications (self-report covariates)

**Recruitment:** Reddit (r/QuantifiedSelf, r/OuraRing, r/HeartRateVariability). Free. Ask for HRV + moral orientation study participants.

**Analysis:** Partial correlation (Pearson) controlling for age, fitness, medications. Report r, 95% CI, and partial r.

**Expected output:** r_partial between GILE-G and HRV with confidence interval.

**Falsification:** r_partial < 0.30 disconfirms the HRV→G biometric mapping.

---

### T2-D: PD vs. Bayes — Novel Event Pilot (Prediction 9)
*N=1 initially (Brandon), expanding to N=10 trained TI Sigma practitioners*

**Scientific question:** For genuinely novel prediction problems (no reference class), does PD-via-MR outperform Bayesian estimation in calibration (Brier score)?

**Protocol:**
1. Identify 20 genuinely novel prediction problems — situations Brandon faces with no historical reference class (e.g., specific negotiations, unusual market events, novel research outcomes)
2. For each: record (a) the PD assignment via MR (with MR level documented); (b) a Bayesian posterior estimate (using whatever reasonable prior is available)
3. Wait for resolution
4. Score calibration: Brier score for PD center mass vs. Bayesian posterior

**Tracking:** A simple spreadsheet. Date → Problem description → PD (center + width) → Bayesian estimate → Resolution → Brier scores.

**Expected output:** After 20 events: mean Brier score comparison PD vs. Bayes.

**Falsification:** If Bayesian estimates achieve lower mean Brier score than PD across 20 novel events, Prediction 9 is disconfirmed for this pilot.

---

## TIER 3 STUDIES

---

### T3-A: Radiant Threshold Behavioral Discontinuity (Prediction 3)
*N=150, GILE battery + moral dilemma battery*

**Scientific question:** Is there a threshold (not a gradient) in decision-making patterns as a function of GILE composite score?

**Protocol:**
1. Administer full GILE psychometric battery (all four sections + composites)
2. Administer Moral Dilemma Battery (20 scenarios with competing GILE vs. Existence pulls):
   - GILE-pull scenarios: situations where the right action requires genuine Goodness, Knowing, or Love orientation
   - Existence-pull scenarios: situations where the EF, Physical Bonds, or valence-maximizing choice is more comfortable
3. Classify each participant's decision patterns as GILE-primary or Existence-primary (proportion of GILE-pull choices)
4. Test for threshold effect: fit both linear and threshold models to the GILE composite → decision-pattern relationship; compare fit

**Moral Dilemma Battery design (sample items):**
- *G-pull:* "You can report a friend's small financial impropriety that harms no one you know, or stay silent. Reporting costs you the friendship. What do you do?"
- *I-pull:* "You have a strong intuition that a colleague's project will fail, but no concrete evidence. Do you speak up at the risk of looking foolish, or stay quiet?"
- *L-pull:* "A person you care about needs a truth that will hurt them to hear. The kind lie is more comfortable for both of you. What do you say?"
- *E-pull:* "A technically inferior but beautiful solution is preferred by your team. The structurally superior solution is ugly. Which do you advocate for?"

**Analysis:** Threshold detection (Davies test or segmented regression) for GILE composite as predictor of GILE-primary decision rate. Compare threshold model vs. linear model by AIC/BIC.

**Expected output:** Estimated Radiant Threshold location (predicted ≈ 0.42 = √2−1) with 95% CI.

**Falsification:** Linear model significantly outperforms threshold model (ΔIC > 4) → no behavioral discontinuity → Prediction 3 disconfirmed.

---

### T3-B: Sartre Protocol Domain Weight Inference (Prediction 8)
*3 domains, N=20 exemplars per domain + GILE assessment*

**Scientific question:** Do domain-calibrated GILE weights (inferred from Existence weights via Sartre Protocol) predict top exemplars' GILE profiles better than universal reference weights?

**Domains:**
1. **Competitive chess** — EF-dominant domain (spatial, physical, high-bandwidth computation)
   - Predicted Sartre-derived weights: G↓, I↑, L↓, E↑↑ (high-E, high-I domain)
2. **Psychotherapy** — L-dominant domain (relational, healing, bidirectional)
   - Predicted Sartre-derived weights: G↑, I↑, L↑↑, E↓
3. **Mathematical research** — I/E-dominant domain (structural knowing + elegant proof)
   - Predicted Sartre-derived weights: G↑, I↑↑, L↓, E↑↑

**Protocol:**
1. Identify N=20 top exemplars per domain (chess: Elo ≥ 2400; therapy: licensed + 10+ years; mathematics: PhD + published research)
2. Assess their GILE profiles via full battery + behavioral supplements
3. Use Sartre Protocol to derive predicted GILE weights from domain Existence measurements
4. Compare: Sartre-predicted weights vs. universal weights vs. actual GILE profiles of exemplars

---

## Cross-Study Design Standards

### Pre-Registration
All Tier 2+ studies will be pre-registered at OSF (Open Science Framework, free) before data collection. Pre-registration elements:
- Exact hypotheses (from URB #614 / #616)
- Sample size justification (power analysis at α=0.05, β=0.80)
- Primary analysis plan
- Falsification criterion

### Open Data
All anonymized datasets will be deposited on Zenodo (free, permanent DOI) alongside their analysis code (Python, open source).

### Reporting Standard
All studies report:
- p-values (for academic audiences)
- Effect sizes (Cohen's d or r)
- PD assignment via MR on the hypothesis (for TI Sigma audiences)
- BOK placement of the result (which loop structure, which loop priority, which LCC level)

This creates a dual-language report that satisfies both conventional peer review and TI Sigma's internal standard.

---

## Timeline

| Study | Start | Expected completion | Prediction tested |
|---|---|---|---|
| T1-A: BOK Biometric Saturation | Immediately | 2 weeks (retrospective Oura data) | #10 |
| T1-B: Spectre Balance Trajectory | Immediately | 5 weeks (prospective) | A, D |
| T2-D: PD vs. Bayes Novel Events | Immediately (ongoing) | 3–6 months | #9 |
| T2-C: GILE-G / HRV Correlation | 2 weeks | 6 weeks | #7 |
| T2-A: Aesthetics–Structure | 4 weeks | 8 weeks | #2 |
| T2-B: I→L Dependency | 4 weeks | 10 weeks | #1 |
| T3-A: Radiant Threshold | Q3 2026 | Q4 2026 | #3 |
| T3-B: Sartre Protocol | Q3 2026 | Q1 2027 | #8 |

---

## BlissGene Therapeutics Integration

The most immediately BlissGene-relevant study is T3-A (Radiant Threshold behavioral discontinuity) + the biometric version (Oura Ring saturation). These map directly onto BlissGene's core thesis: there is a measurable threshold in GILE development above which conscious wellbeing becomes self-sustaining. If T3-A confirms a threshold at GILE ≈ 0.42, BlissGene has a concrete measurement target for its interventions.

Budget note: T1 studies cost $0 (existing data). T2 studies cost $0–$20 (Google Forms + Prolific recruitment at $0 for volunteer studies). T3 studies require institutional support or BlissGene seed funding allocation.

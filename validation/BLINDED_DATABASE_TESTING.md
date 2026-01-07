# Blinded Database Testing Methodology for LCC Virus and Psi Validation

**Purpose:** Establish rigorous, non-fraudulent testing protocols for validating LCC (Local Correlation Coefficient) and psi methods using publicly available databases with hidden/blinded data.

## Anti-Fraud Principles

### 1. Pre-Registration Requirements
- **OSF Pre-Registration:** File analysis plan before accessing data
- **Timestamp Verification:** Third-party timestamping of predictions
- **Analysis Lock:** Cannot change methods after seeing outcomes

### 2. Blinding Verification
- **Data Provenance:** Documented source with verifiable timestamps
- **Access Logging:** All data queries logged with timestamps
- **Independent Verification:** Third party confirms blind was genuine

### 3. Statistical Safeguards
- **Bayesian Calibration:** Prior beliefs explicitly stated
- **Permutation Baselines:** Compare to shuffled data performance
- **Multiple Comparison Correction:** Bonferroni or FDR adjustment
- **Effect Size Reporting:** Not just p-values

---

## Protocol A: Relationship Outcome Prediction

### Data Sources

**1. Panel Study of Income Dynamics (PSID)**
- Longitudinal data since 1968
- Relationship status tracked over decades
- Publicly available with lag

**2. Add Health (National Longitudinal Study)**
- Adolescent to adult relationships tracked
- Romantic relationship outcomes
- Restricted-use dataset available

**3. Couples Longitudinal Studies (Various)**
- Gottman Institute datasets
- Relationship satisfaction trajectories

### Available Information (Blinded Inputs)
- Individual birth dates (year only for privacy)
- Geographic origins (state/region level)
- Demographic categories (education level, occupation)
- Baseline relationship variables (if using couples data)

### Hidden Information (Outcomes to Predict)
- Relationship survival at 1, 5, 10 years
- Satisfaction trajectory (improving/declining)
- Conflict frequency categories
- Separation/divorce dates

### Validation Protocol

**Step 1: Data Request**
1. Request dataset with outcomes masked
2. Receive: ID, demographics, baseline variables
3. Cannot see: Outcome variables

**Step 2: Prediction Generation**
1. Apply LCC/psi methods to available data
2. Generate predictions for each couple/individual
3. Seal predictions with timestamp
4. Submit to data custodian

**Step 3: Blind Removal**
1. Data custodian reveals outcomes
2. Compare predictions to actual outcomes
3. Calculate accuracy metrics

**Step 4: Validation Metrics**

| Metric | Chance Level | Threshold for Success |
|--------|-------------|----------------------|
| Survival prediction | 50% | > 60% at p < 0.01 |
| Satisfaction direction | 50% | > 58% at p < 0.01 |
| Conflict category | 33% | > 45% at p < 0.01 |
| Timing accuracy | Random | < 6 month error |

### Fraud Prevention
- Predictions sealed before outcome access
- Data custodian is independent party
- All queries logged and auditable
- Pre-registration includes exact analysis plan

---

## Protocol B: Success Date Prediction

### Data Sources

**1. Wikipedia Biographies**
- Career milestone dates publicly available
- But can verify against less-public sources
- Use birth date + limited early info to predict achievements

**2. Patent Databases (USPTO)**
- Patent filing dates are precise
- Inventor demographics available
- Predict filing dates from birth + education info

**3. Publication Databases (PubMed, arXiv)**
- First publication dates
- Citation milestone dates
- Predict breakthrough timing

**4. SEC Filings (Edgar)**
- Company founding dates
- IPO dates
- Major transaction dates

### Available Information (Blinded Inputs)
- Birth date (year, sometimes month)
- Educational history (institution, field)
- Geographic origin
- Early career indicators (if available)

### Hidden Information (Outcomes to Predict)
- Specific success dates (patent, publication, milestone)
- Career peak timing
- Major transition dates

### Validation Protocol

**Step 1: Target Selection**
1. Identify 100+ individuals with verified success dates
2. Collect only blinded inputs
3. Blind evaluator to success dates

**Step 2: Prediction Generation**
1. For each individual, predict:
   - Month/year of major success event
   - Type of success (career, creative, financial)
   - Intensity rating (1-10)
2. Predictions must be specific, not vague

**Step 3: Comparison**
1. Reveal actual success dates
2. Calculate temporal error
3. Compare to null distribution

**Step 4: Validation Metrics**

| Metric | Chance Performance | Threshold |
|--------|-------------------|-----------|
| Correct month | 8.3% (1/12) | > 15% |
| Correct quarter | 25% | > 40% |
| Within 3 months | ~50% (random) | > 65% |
| Rank correlation | r = 0 | r > 0.20 |

### Fraud Prevention
- Use historical figures (deceased) for some tests—no way to update predictions
- Cross-validate with multiple independent sources
- Predictions must be made before accessing biographical detail

---

## Protocol C: Financial Event Prediction

### Data Sources

**1. CRSP/Compustat (Academic)**
- Historical stock returns
- Corporate events (earnings, splits, M&A)
- Precise dates available

**2. EDGAR (SEC)**
- Filing dates for corporate events
- Executive changes
- Material events

**3. Bloomberg/Reuters (Commercial)**
- News event timestamps
- Market reaction dates

### Blinding Approach

**Temporal Blind:**
1. Use data up to time T
2. Predict events in T+1 to T+N period
3. Only reveal T+1 to T+N data after predictions sealed

**Cross-Validation:**
1. Train on 80% of time periods
2. Test on held-out 20%
3. Ensure no lookahead bias

### Validation Metrics

| Prediction | Baseline | Threshold |
|------------|----------|-----------|
| Earnings surprise direction | 50% | > 55% |
| Volatility regime change | 33% | > 45% |
| Sector rotation | 20% | > 30% |
| Crisis prediction (binary) | 10% | > 20% |

---

## Protocol D: Physiological Database Validation

### Data Sources

**1. PhysioNet Databases**
- ECG, EEG, PPG signals
- Various clinical conditions
- Some with behavioral outcomes

**2. LEMON Dataset (MPI)**
- EEG + psychology assessments
- Longitudinal component

**3. Human Connectome Project**
- Brain imaging + behavioral measures
- Detailed cognitive assessments

### Blinding Approach

1. Receive physiological signals only
2. Predict behavioral/cognitive outcomes
3. Compare to actual assessments

### LCC Validation

1. Calculate LCC between paired signals
2. Predict inter-subject relationship quality
3. Validate against survey measures

---

## General Statistical Framework

### Bayesian Analysis

```
Prior: P(psi real) = 0.05 (skeptical prior)
Likelihood: P(data | psi real) vs P(data | chance)
Posterior: Updated belief after data

Threshold: Bayes Factor > 10 for claim
```

### Permutation Testing

1. Calculate observed accuracy
2. Shuffle outcomes 10,000 times
3. Calculate null distribution
4. Compare observed to null

### Multi-Study Aggregation

1. Pre-register multi-study plan
2. Use random-effects meta-analysis
3. Report heterogeneity (I²)
4. No selective reporting

---

## Red Flags for Fraud Detection

### In Our Own Work
- [ ] Did we access outcomes before predictions?
- [ ] Did we change methods after seeing results?
- [ ] Are we selectively reporting positive results?
- [ ] Could we be unconsciously biased by partial knowledge?

### In Others' Claims
- [ ] Is raw data available?
- [ ] Was analysis pre-registered?
- [ ] Can results be independently replicated?
- [ ] Are effect sizes plausible?

---

## Implementation Checklist

### Before Data Access
- [ ] Pre-register hypothesis on OSF
- [ ] Specify exact analysis plan
- [ ] Identify blinding mechanism
- [ ] Arrange independent data custodian

### During Analysis
- [ ] Log all data queries
- [ ] Document all decisions
- [ ] Maintain separation between prediction and outcome

### After Analysis
- [ ] Report all results (not just significant)
- [ ] Calculate effect sizes
- [ ] Compare to pre-registered predictions
- [ ] Share data and code for replication

---

## Conclusion

This framework ensures that LCC/psi validation is scientifically rigorous and fraud-resistant. The key principles are:
1. **Genuine Blinds:** Outcomes truly hidden before predictions
2. **Pre-Registration:** Analysis plan locked in advance
3. **Independent Verification:** Third parties confirm process
4. **Full Transparency:** All data and methods shared

Whether results support or refute psi claims, this methodology ensures the conclusions are trustworthy.

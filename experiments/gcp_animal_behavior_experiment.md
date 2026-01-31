# GCP + Animal Behavior Correlation Study

## Theoretical Foundation

**Hypothesis**: The Global Consciousness Project (GCP) measures fluctuations in the Grand Myrion network. If animals participate in this network (LCC < 1), their behavior should correlate with GCP "dot" readings during significant events.

**Prediction**: During global events with significant GCP deviations, zoo animals will show increased activity/agitation compared to baseline periods.

**Threshold for Success**: Any correlation above chance (p < 0.05)

---

## The Global Consciousness Project

### Background
- Network of ~70 Random Event Generators (REGs) worldwide
- Produces continuous random data streams
- Analyzes for deviation from expected randomness
- "GCP dot" shows real-time deviation: green (normal) → red (significant deviation)

### Data Access
- Real-time: https://gcpdot.com/
- Historical: https://noosphere.princeton.edu/data/
- API available for research use

### Key Metrics
- **Z-score**: Standard deviation from expected randomness
- **Variance**: Deviation from expected variance
- **Cumulative deviation**: Running total of departures from chance

---

## Experimental Design

### Phase 1: Event Selection

**Target Events** (known to produce GCP deviations):
1. Major news events (elections, disasters, announcements)
2. Global meditation events (synchronized group meditation)
3. New Year's Eve (worldwide midnight cascade)
4. Major sporting events (World Cup finals, Olympics opening)

**Selection Criteria**:
- GCP Z-score > 2 (or < -2)
- Duration > 30 minutes
- Predictable timing (for zoo observation setup)

### Phase 2: Animal Observation

**Target Species**: Same as Dual Zoo study (elephants), plus:
- Great apes (high R estimate)
- Big cats (different neural architecture)
- Marine mammals if available (dolphins, sea lions)

**Observation Protocol**:
1. Monitor zoo webcam during event period
2. Code behavior every 30 seconds
3. Also code behavior during control periods (no event)
4. Compare event vs. control behavior patterns

---

## Data Collection

### GCP Data

```
Timestamp(UTC) | GCP_Z | Variance | Event_Name
2026-02-01 15:00:00 | 1.2 | 0.98 | None
2026-02-01 15:01:00 | 2.4 | 1.15 | Major_News_Event
...
```

### Animal Behavior Data

```
Timestamp(UTC) | Zoo | Species | Animal_ID | Behavior | Activity_Level | Notes
2026-02-01 15:00:00 | Smithsonian | Elephant | E1 | S | 2 | Normal
2026-02-01 15:01:00 | Smithsonian | Elephant | E1 | A | 5 | Agitated
...
```

### Merged Dataset

```
Timestamp | GCP_Z | Animal_Activity | Event_Active | Distance_to_GCP_egg
...
```

---

## Analysis Plan

### Primary Analysis: Correlation

**Question**: Does GCP deviation predict animal activity level?

```python
correlation = scipy.stats.pearsonr(gcp_z_scores, animal_activity_levels)
```

**Expected Result if LCC < 1**:
- Positive correlation: Higher GCP deviation → Higher animal activity
- r > 0, p < 0.05

### Secondary Analysis: Event-Triggered Averaging

**Question**: Do animals show activity spikes during GCP events?

```python
# Average animal activity during high-GCP periods
high_gcp_activity = mean(activity[abs(gcp_z) > 2])

# Average animal activity during normal periods  
baseline_activity = mean(activity[abs(gcp_z) < 1])

# Test difference
t_stat, p_value = scipy.stats.ttest_ind(high_gcp_activity, baseline_activity)
```

### Tertiary Analysis: Lag/Lead Relationships

**Question**: Does animal behavior predict GCP deviations, or vice versa?

```python
# Cross-correlation with lags
cross_corr = scipy.signal.correlate(animal_activity, gcp_z, mode='full')
```

If animals LEAD GCP: Suggests animals contribute to/detect network changes
If animals LAG GCP: Suggests animals respond to network changes

---

## Controls

| Confound | Control Method |
|----------|---------------|
| Feeding times | Exclude ±30 min from feeding |
| Weather | Include as covariate |
| Visitor density | Weekday vs weekend comparison |
| Time of day | Circadian adjustment |
| Species differences | Analyze separately then pool |
| GCP artifact | Use multiple GCP eggs for validation |

---

## Sample Size and Power

**Target Events**: 
- 10-20 major global events over 3-6 months
- Each event = ~2 hours of observation
- Total: 40-80 hours of paired GCP + animal data

**Power Calculation**:
- At r = 0.10, n = 617 for power = 0.80
- At 2 observations/minute for 40 hours = 4,800 observations
- **Well-powered for small effects**

---

## Timeline

| Phase | Duration | Activity |
|-------|----------|----------|
| Setup | Week 1 | Configure GCP data download, identify webcams |
| Baseline | Week 2-3 | Collect baseline animal behavior (no events) |
| Event Collection | Month 1-3 | Observe during selected global events |
| Analysis | Week 1 | Statistical analysis |
| Report | Week 2 | Write up findings |

**Total Duration**: 3-4 months for robust dataset

---

## Tools Needed

1. **GCP Data Access**: API or web scraping setup
2. **Webcam Recording**: OBS or browser extension
3. **Behavior Coding**: Standardized protocol (same as Dual Zoo)
4. **Analysis**: Python with scipy, numpy, pandas
5. **Event Calendar**: Track upcoming global events

---

## Specific Predictions by Species

Based on estimated R values:

| Species | Est. R | Expected GCP Sensitivity |
|---------|--------|--------------------------|
| Great apes | 7+ | High |
| Elephants | 5-6 | Medium-High |
| Dolphins | 5-6 | Medium-High |
| Big cats | 4 | Medium |
| Birds | 3 | Low-Medium |

**Prediction**: Correlation strength should scale with R

---

## Integration with Dual Zoo Study

These two experiments complement each other:

| Dual Zoo | GCP + Animal |
|----------|--------------|
| Tests animal-animal correlation | Tests animal-network correlation |
| Real-time synchrony | Event-triggered response |
| Spatial distance variable | Temporal event variable |
| LCC across space | LCC across consciousness network |

**Combined Evidence**:
If BOTH show positive results → Strong support for Grand Myrion network
If only one → May indicate different aspects of non-local causation
If neither → LCC ≈ 1 for animals (or measurement too coarse)

---

## Expected Outcomes

**Positive Result**:
- GCP-animal correlation r > 0, p < 0.05
- Effect stronger for high-R species
- Temporal lag suggests direction of influence

**Implications**:
- Animals participate in "global consciousness" network
- Measurable non-local correlation (LCC < 1)
- Validates Grand Myrion network hypothesis
- Opens path for human-animal correlation studies

**Null Result**:
- No significant correlation
- May indicate: animals not connected, or measurement insensitive
- Refine measurement and try again

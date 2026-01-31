# Dual Zoo Webcam Synchrony Experiment

## Theoretical Foundation

**Hypothesis**: PSI phenomena reflect information transmission via the Grand Myrion network (photons, EM waves, dark energy). If LCC < 1, animals at distant locations should exhibit behavioral synchrony above chance, mediated by non-local correlational causation.

**Prediction**: Behavioral synchrony between animals at distant locations will exceed chance expectation, with effect size proportional to:
1. Species cognitive complexity (R)
2. Emotional salience of stimuli
3. Baseline connectedness between populations

**Threshold for Success**: Any synchrony above chance (p < 0.05)

---

## Experimental Design

### Target Species: Elephants

**Rationale**:
- High estimated R (5-6)
- Complex emotional displays (observable via webcam)
- Strong social bonding within and across herds
- Multiple zoos with live webcams
- Documented inter-elephant empathy and awareness

### Zoo Pairs

**Primary Pair**:
- **Zoo A**: Smithsonian National Zoo (Washington DC)
  - Webcam: https://nationalzoo.si.edu/webcams/elephant-cam
  - Species: Asian elephants
  
- **Zoo B**: San Diego Zoo (California)
  - Webcam: https://zoo.sandiegozoo.org/cams/elephant-cam
  - Species: African elephants
  - Distance from Zoo A: ~3,700 km

**Backup Pairs**:
- Houston Zoo + Toronto Zoo (~2,200 km)
- Dublin Zoo + Singapore Zoo (~10,500 km)

---

## Behavioral Coding System

### Observable Behaviors (coded every 30 seconds)

| Code | Behavior | Description |
|------|----------|-------------|
| W | Walking | Active locomotion |
| S | Standing | Stationary, alert |
| R | Resting | Lying down or leaning |
| E | Eating | Consuming food/water |
| So | Social | Interaction with other elephants |
| V | Vocalizing | Visible trunk movement suggesting vocalization |
| A | Agitated | Ear flapping, trunk swinging, pacing |
| P | Play | Splashing, object manipulation |
| O | Other | Any other behavior |

### Mood States (inferred from behavior patterns)

| State | Indicator Behaviors | Score |
|-------|--------------------| ------|
| Calm | R, S, E | +1 |
| Active | W, So, P | +2 |
| Stressed | A | -1 |
| Engaged | So, V, P | +3 |

---

## Protocol

### Phase 1: Baseline (Days 1-3)

1. **Observation Windows**: 10:00-12:00 and 14:00-16:00 local time at each zoo
2. **Recording**: Screenshot every 30 seconds from both webcams simultaneously
3. **Coding**: Code all behaviors for each 30-second interval
4. **Calculate**: Baseline synchrony rate

### Phase 2: Stimulus Events (Days 4-7)

**Natural Stimuli** (observe and record):
- Feeding times at each zoo
- Enrichment activities
- Weather events
- Visitor surges

**Synchrony Measurement**:
1. When stimulus occurs at Zoo A, record time (T₀)
2. Code behavior at Zoo A at T₀, T₀+30s, T₀+60s, T₀+90s, T₀+120s
3. Code behavior at Zoo B at same times (adjusted for transmission delay test)
4. Compare behavioral state changes

### Phase 3: Analysis

**Primary Analysis**:
```
Synchrony_score = P(same behavior | same time) / P(same behavior | random time)
```

If Synchrony_score > 1: Evidence for non-local correlation

**LCC Calculation**:
```
LCC = 1 - (observed_synchrony - chance_synchrony) / (max_synchrony - chance_synchrony)
```

Where:
- chance_synchrony = base rate of matching behaviors
- max_synchrony = 1.0 (perfect correlation)
- observed_synchrony = actual measured correlation

---

## Controls and Confounds

| Confound | Control Method |
|----------|---------------|
| Time zone effects | Convert all times to UTC |
| Feeding schedules | Record and control for |
| Weather | Log weather at both locations |
| Day of week | Balance observations across days |
| Observer bias | Blind coding (coder doesn't know hypothesis) |
| Circadian rhythms | Match local times for comparison |

---

## Power Analysis

**Assumptions**:
- Effect size expected: r = 0.10 (small but meaningful for PSI)
- Alpha = 0.05 (one-tailed, directional hypothesis)
- Power = 0.80

**Required observations**:
- N = 617 paired observations for correlation
- At 30-second intervals over 4 hours/day = 480 observations/day
- **Minimum 2 days of observation needed**

---

## Data Recording Template

```
Timestamp(UTC) | Zoo | Animal_ID | Behavior | Mood_Score | Weather | Notes
2026-02-01 15:00:00 | A | Elephant1 | W | +2 | Sunny | Approaching water
2026-02-01 15:00:00 | B | Elephant2 | S | +1 | Overcast | Facing enclosure
...
```

---

## Success Criteria

**Positive Result**:
- Synchrony correlation r > 0 with p < 0.05
- Effect persists after controlling for confounds
- Replicable across multiple observation periods

**Interpretation**:
- r > 0: LCC < 1 (some non-local causation)
- Implied LCC = 1 - r (for small effects)

---

## Timeline

| Day | Activity |
|-----|----------|
| 1-3 | Baseline observation |
| 4-7 | Stimulus event observation |
| 8-9 | Data coding and cleaning |
| 10 | Statistical analysis |
| 11 | Report writing |

**Total Duration**: 2 weeks

---

## Equipment Needed

1. Computer with stable internet
2. Screen recording software (OBS or similar)
3. Stopwatch/timer for 30-second intervals
4. Spreadsheet for data entry
5. Weather API access for both locations

---

## Ethical Considerations

- Passive observation only
- No animal contact or disturbance
- Public webcam data
- Academic research purpose
- Results will be published openly

---

## Expected Outcomes

**If Null (no synchrony above chance)**:
- LCC ≈ 1 for elephant consciousness
- May need higher-R species or more sensitive measures

**If Positive (synchrony above chance)**:
- First empirical evidence for animal-to-animal non-local correlation
- LCC estimate for elephants
- Foundation for larger-scale studies
- Supports Grand Myrion network hypothesis

# Behavior Coding Guide for Animal Synchrony Studies

## Behavior Codes

| Code | Behavior | Description | Activity Level |
|------|----------|-------------|----------------|
| W | Walking | Active locomotion, moving around enclosure | 3 |
| S | Standing | Stationary but alert, not lying down | 2 |
| R | Resting | Lying down or leaning against structure | 1 |
| E | Eating | Consuming food, hay, or drinking water | 2 |
| So | Social | Interacting with another animal (touching, playing) | 4 |
| V | Vocalizing | Trunk raised, visible vocalization posture | 4 |
| A | Agitated | Ear flapping, trunk swinging, pacing, head bobbing | 5 |
| P | Play | Splashing water, manipulating objects, running | 5 |
| O | Other | Any behavior not fitting above categories | 2 |
| NV | Not Visible | Animal not visible on camera | 0 |

## Mood Scores

| Score | Mood State | Indicator Behaviors |
|-------|------------|---------------------|
| -2 | Distressed | Prolonged A, stereotypic pacing |
| -1 | Anxious | Brief A, alert posture |
| 0 | Neutral | S, R without other indicators |
| +1 | Calm | R, E in relaxed posture |
| +2 | Active/Content | W, So without stress signs |
| +3 | Engaged/Happy | P, positive So, exploration |

## Activity Levels

| Level | Description |
|-------|-------------|
| 0 | Not visible |
| 1 | Resting/minimal movement |
| 2 | Low activity (standing, eating) |
| 3 | Moderate activity (walking) |
| 4 | High activity (social, vocalizing) |
| 5 | Very high activity (play, agitation) |

## Coding Protocol

### Every 30 Seconds:
1. Note the timestamp (UTC)
2. Identify which animal is visible
3. Code primary behavior (use first letter code)
4. Estimate mood score (-2 to +3)
5. Estimate activity level (0-5)
6. Note any unusual observations

### Tips for Reliability:
- If behavior changes during 30-second interval, code the **dominant** behavior
- If two animals visible, code both with separate IDs (E1, E2, etc.)
- Use "O" (Other) sparingly - describe in notes what the behavior was
- Weather should be updated every hour or when it changes

## Synchrony Analysis

### What Counts as "Synchronized"?

**Exact Match**: Same behavior code at same time
- Score: 1.0

**Category Match**: Same category of behavior
- Both active (W, So, V, P): Score: 0.5
- Both inactive (S, R, E): Score: 0.5

**Activity Level Match**: Same activity level (within 1)
- Score: 0.25

### Calculating Synchrony Rate

```
Synchrony = Σ(matched observations) / Σ(total paired observations)
```

Expected by chance (baseline):
- Exact match: ~11% (1/9 behaviors)
- Category match: ~44% (4/9 active + 3/9 inactive)
- Activity match: ~60% (within 1 level)

## Recording Weather

| Code | Weather |
|------|---------|
| SU | Sunny |
| PC | Partly Cloudy |
| OC | Overcast |
| RA | Rain |
| ST | Storm |

## Recording Visitor Levels

| Code | Visitors |
|------|----------|
| L | Low (few people visible) |
| M | Medium (moderate crowd) |
| H | High (crowded) |

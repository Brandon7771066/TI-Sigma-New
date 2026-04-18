# URB #755 — GILE Self-Report Scale Design: A 16-Item Instrument for EEG-Cohort Stratification and Tertiary-Prediction Testing

**Author:** Brandon Charles Emerick
**Date:** April 18, 2026
**Series:** Unified Research Brief #755
**Status:** Self-report instrument designed; ready for embedding in URB #747's per-subject EEG analysis
**Builds on:** URB #738 §3.3 (tertiary prediction: GILE-state-correlated bifurcated brain-scaling distributions), URB #747 (per-subject EEG protocol), URB #696 (GILE Immunity foundational)

---

## 1. The Need for a Self-Report Scale

URB #738's tertiary prediction:

> "GILE-state-correlated subjects (high vs low GILE state by self-report) will show **bifurcated distributions**, with high-GILE subjects clustered tightly around 2.577 ± 0.05 and low-GILE subjects spread more broadly."

URB #747 §7.3 reaffirmed this prediction. **But the framework has never specified what the GILE self-report scale actually contains.** This URB designs the instrument: a 16-item scale derived from the framework's GILE dimensions (Goodness, Intuition, Love, Environment) under URB #743's updated E-vs-T axis architecture.

---

## 2. Design Principles

The scale must:

1. **Be short** (≤ 16 items, ≤ 5 minutes to complete)
2. **Cover all four GILE dimensions** (G, I, L, E) at sufficient depth
3. **Be face-valid** without requiring framework knowledge (subjects can answer without prior framework exposure)
4. **Use validated psychometric techniques** (5-point Likert; reverse-coded items to control for response bias)
5. **Map to URB #743's E-vs-T axis** (separate sub-scores for Existence-axis and Truth-axis components)
6. **Enable bifurcation analysis** (continuous score → tertile split for high vs low GILE)

---

## 3. The 16-Item GILE Self-Report Scale (Version 1.0)

**Instructions to subject**: "Please rate how well each statement describes you in your typical day-to-day experience over the past two weeks. Use the scale: 1 = Strongly Disagree, 2 = Disagree, 3 = Neither, 4 = Agree, 5 = Strongly Agree."

### 3.1 Goodness sub-scale (4 items)

1. *"When faced with a difficult choice, I tend to choose the option that benefits others, even at some cost to myself."*
2. *"I find satisfaction in actions that contribute to the well-being of those around me."*
3. *"My values stay consistent across different situations and people."*
4. *(reverse-coded)* *"It's hard for me to identify what I genuinely care about."*

### 3.2 Intuition sub-scale (4 items)

5. *"I often know the right answer before I've consciously thought it through."*
6. *"My first impressions of people and situations usually turn out to be accurate."*
7. *"I trust my gut feelings even when they go against logical analysis."*
8. *(reverse-coded)* *"I rarely have insights that come 'out of nowhere.'"*

### 3.3 Love sub-scale (4 items)

9. *"I feel deeply connected to the people I care about, even when we're apart."*
10. *"I am moved by the experiences of others as if they were partly my own."*
11. *"I actively seek to understand others, even when I disagree with them."*
12. *(reverse-coded)* *"I prefer to keep emotional distance from others."*

### 3.4 Environment sub-scale (4 items)

13. *"I am sensitive to the physical and social atmosphere of a place when I enter it."*
14. *"I notice subtle changes in my surroundings — light, sound, mood — that others miss."*
15. *"My state of mind is significantly affected by the people and places around me."*
16. *(reverse-coded)* *"My internal state is largely independent of my surroundings."*

**Note on item 16**: this is conceptually subtle. Under URB #696's GILE Immunity, **higher Environment-axis sensitivity** (items 13-15) should predict higher GILE state, BUT GILE Immunity also implies the subject has the **capacity** to be affected without being **destabilized**. The reverse-coded item 16 ("internal state independent of surroundings") therefore captures the GILE-Immune subject who notices but is not disturbed. Both directions count toward the Environment sub-score.

---

## 4. Scoring

### 4.1 Total GILE score
Sum all 16 items (after reverse-coding items 4, 8, 12). **Range: 16-80.** Higher scores = higher GILE state.

### 4.2 Sub-scale scores
Each sub-scale: sum 4 items. **Range: 4-20 each.**

### 4.3 E-vs-T axis decomposition (URB #743)
- **Existence-axis sub-score**: Goodness + Environment items (8 items, range 8-40)
- **Truth-axis sub-score**: Intuition + Love-as-recognition items (4 + 2 items)
- **Cross-axis sub-score**: Love-as-bonding + Love-as-care items (2 items)

Note: Items 11 and 12 are Love-as-recognition (Truth-axis Love); items 9, 10 are Love-as-bonding (Existence-axis Love); item-level coding follows URB #743 §3.3.

### 4.4 Stratification for EEG analysis

For URB #747's per-subject EEG analysis:
- **High-GILE tertile**: total GILE score ≥ 60 (top third)
- **Low-GILE tertile**: total GILE score ≤ 48 (bottom third)
- **Middle tertile**: scores 49-59 (excluded from primary analysis to sharpen contrast)

---

## 5. Pre-Registered Predictions

### 5.1 Primary prediction (URB #738 tertiary, now operational)

**High-GILE subjects' brain scaling exponent distribution**: mean = 2.577, std ≤ 0.05.
**Low-GILE subjects' brain scaling exponent distribution**: mean within [2.4, 2.7], std ≥ 0.20.

**Effect size**: high-GILE std should be ≥ 4× tighter than low-GILE std.

### 5.2 Secondary prediction (E-vs-T axis correlation)

**Existence-axis sub-score** should correlate with **slow-band power** in EEG (slow band = HEAR pillar / Existence axis representation).
**Truth-axis sub-score** should correlate with **alpha + gamma band coherence** (truth resolution = MR pillar = Truth axis).

### 5.3 Tertiary prediction (Heart HRV correlation)

**Existence-axis sub-score** should correlate with **HRV scaling exponent at the heart level** (URB #748). Specifically, high-Existence-axis subjects should have heart s_HRV closer to lepton sector (1.889), while low-Existence-axis subjects should be closer to up-quark sector (1.298).

---

## 6. Validation Steps Before Deployment

The scale needs validation before being trusted for the URB #747 stratification:

| Step | Description | Estimated time |
|---|---|---|
| 1 | Pilot test with n = 5-10 subjects (informal, framework-friendly group) | 1 week |
| 2 | Compute Cronbach's α for each sub-scale (target: α ≥ 0.70) | 1 hour |
| 3 | Compute factor loadings (target: 4-factor structure consistent with G/I/L/E) | 2 hours |
| 4 | Refine items based on pilot feedback (drop low-loading items; add replacements) | 1 week |
| 5 | Re-pilot with refined version | 1 week |
| 6 | Lock as Version 2.0 for deployment | — |

**Estimated total**: 3-4 weeks for validation.

**Cost**: $0 (pilot subjects can be friends/family; statistical validation is standard).

---

## 7. Connection to Other Framework Tools

### 7.1 EEG cohort analysis (URB #747)
The scale provides the GILE-state stratification variable for URB #747's tertiary prediction.

### 7.2 Heart HRV analysis (URB #748)
The scale's Existence-axis sub-score provides a hypothesized predictor of heart HRV scaling.

### 7.3 64D GILE Matrix empirical operationalization (URB #745 pending item 3)
The scale is a **first step** toward operationalizing the 64D GILE Matrix empirically. Specifically, the four sub-scales (G, I, L, E) provide low-dimensional projections of the 64D state. Future scale revisions can add items mapping to specific 64D Matrix blocks.

### 7.4 Outreach engagement (outreach_tracking_log.md)
The scale gives outreach targets a **concrete instrument** they can examine, critique, or test in their own labs. This makes the framework's claims **methodologically tangible** in a way pure theory papers don't.

---

## 8. Falsification Criteria

- **F1**: Cronbach's α < 0.70 for one or more sub-scales after pilot testing. Would require item-level revision.
- **F2**: Factor analysis does NOT recover the 4-factor G/I/L/E structure. Would require fundamental redesign.
- **F3**: After deployment in URB #747's analysis, no GILE-state correlation with brain scaling exponent observed. Would refute the framework's tertiary prediction (URB #738) AND suggest the scale is measuring the wrong construct.

---

## 9. The Slogan Form

> **"16-item GILE self-report scale designed: 4 items × 4 sub-scales (G, I, L, E), 5-point Likert, ≤5 minutes to complete. Maps to URB #743's E-vs-T axis decomposition. Provides tertile-split stratification variable for URB #747's brain-scaling cohort analysis. Pilot validation in 3-4 weeks at $0 cost. Operational instrument for the framework's strongest empirical anchor's tertiary prediction test."**

---

*Brandon Charles Emerick, April 18, 2026 — fifty-fifth URB of the session. 16-item GILE self-report scale Version 1.0 designed: 4 items per G/I/L/E sub-scale, 5-point Likert, ≤5 minutes administration. Maps to URB #743's E-vs-T axis with Existence + Truth + Cross-axis sub-scores. Stratification protocol for URB #747 brain-scaling analysis specified. Three pre-registered predictions: high-GILE tighter brain-scaling distribution, E-axis correlates with slow-band EEG power, E-axis correlates with heart HRV scaling. Pilot validation 3-4 weeks at $0 cost.*

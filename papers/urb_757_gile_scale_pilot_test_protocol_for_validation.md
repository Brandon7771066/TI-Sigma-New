# URB #757 — GILE Self-Report Scale Pilot Test Protocol: Concrete 3-4 Week Validation Plan at $0 Cost

**Author:** Brandon Charles Emerick
**Date:** April 18, 2026
**Series:** Unified Research Brief #757
**Status:** Operational pilot-test protocol; ready for execution as soon as Brandon recruits 5-10 pilot subjects
**Builds on:** URB #755 (16-item GILE scale Version 1.0), URB #738 (per-subject protocol), URB #756 (Emerick Threshold)

---

## 1. The Pilot Test's Purpose

URB #755 designed a 16-item GILE self-report scale. Before the scale can be used to stratify subjects in URB #747's per-subject EEG analysis, it must be **psychometrically validated**:

- **Internal reliability** (Cronbach's α ≥ 0.70 per sub-scale)
- **Factor structure** (4-factor solution recovering G/I/L/E sub-scales)
- **Face validity** (subjects find items understandable)
- **Item-total correlations** (each item correlates ≥ 0.30 with its sub-scale total)

This URB specifies the operational pilot protocol.

---

## 2. Pilot Recruitment

**Target n**: 5-10 subjects for first-pass pilot (sufficient for reliability estimation, marginal for factor analysis but acceptable for pilot)

**Recruitment source**: Brandon's network (friends, family, framework-friendly contacts). No formal IRB needed for informal pilot at this stage; full IRB required if scaling to publication-grade validation.

**Inclusion criteria**:
- Age 18+
- English fluency (the scale is in English)
- Willing to spend 5-10 minutes on the scale + 5 minutes optional debrief
- Diversity of meditation/contemplative-practice background helpful (some experienced, some not) to test the scale's discrimination range

**Exclusion criteria**:
- None for pilot (scale should be face-valid for general population)

**Recruitment ask** (Brandon can copy-paste):

> "Hi [name], I'm developing a short 16-question self-report scale for a research framework I'm working on. It takes about 5-10 minutes. Would you be willing to fill it out and give me brief feedback on whether the questions made sense? No personal information collected, fully anonymous. Reply 'yes' and I'll send the link/PDF."

---

## 3. Pilot Administration

### 3.1 Format options (Brandon picks based on convenience)

| Format | Setup time | Pros | Cons |
|---|---|---|---|
| Paper PDF + email return | 10 min (PDF generation) | Simple; no tech setup | Manual data entry |
| Google Forms | 30 min setup | Auto-collects responses; sub-scale scoring automatic | Requires Google account (most have one) |
| Plain-text email | 0 min | No tooling needed | Manual scoring, easy to forget reverse-coding |

**Recommendation**: Google Forms — auto-scoring saves Brandon time; subjects already familiar with the format.

### 3.2 Form structure (when using Google Forms)

```
[Page 1: Welcome]
"Thank you for participating. This 16-item scale measures aspects of
self-perceived experience. Use the 1-5 scale: 1=Strongly Disagree,
5=Strongly Agree. There are no right or wrong answers. ~5 minutes."

[Page 2: 16 items in fixed order, all required]
[Items 1-16 from URB #755 §3, exact wording, with the reverse-coded
items presented neutrally — no indication they are reverse-scored]

[Page 3: Optional debrief]
- Were any questions unclear or hard to answer? (open text)
- Did any questions feel awkward or unnatural? (open text)
- Was the 5-point scale appropriate? (yes/no/unsure)
- Estimated time to complete: ____ minutes
- Any other feedback? (open text)
```

### 3.3 Time budget for Brandon

- Form construction: 30 minutes
- Recruitment messages to ~10-15 contacts: 30 minutes
- Response collection (over ~1 week): mostly passive
- Data export + analysis: 1 hour
- Pilot results write-up as URB: 1 hour

**Total: ~3 hours of Brandon's active time + 1 week of passive waiting.**

---

## 4. Analysis Protocol

### 4.1 Pre-processing

1. Reverse-code items 4, 8, 12, 16 (5 → 1, 4 → 2, 3 → 3, 2 → 4, 1 → 5)
2. Compute total GILE score (sum of all 16 items, range 16-80)
3. Compute four sub-scale scores (G, I, L, E; sum of 4 items each, range 4-20)
4. Compute E-T axis sub-scores per URB #755 §4.3

### 4.2 Reliability analysis

For each sub-scale, compute Cronbach's α. Code (Python):

```python
import numpy as np

def cronbach_alpha(items):
    """items: 2D array, rows = subjects, cols = items in the sub-scale"""
    items = np.asarray(items)
    n_items = items.shape[1]
    item_vars = items.var(axis=0, ddof=1)
    total_var = items.sum(axis=1).var(ddof=1)
    return (n_items / (n_items - 1)) * (1 - item_vars.sum() / total_var)

# Apply to each sub-scale
alpha_G = cronbach_alpha(responses[:, [0,1,2,3]])  # items 1-4
alpha_I = cronbach_alpha(responses[:, [4,5,6,7]])  # items 5-8
alpha_L = cronbach_alpha(responses[:, [8,9,10,11]]) # items 9-12
alpha_E = cronbach_alpha(responses[:, [12,13,14,15]]) # items 13-16
```

**Pass criterion**: α ≥ 0.70 for each sub-scale. If any sub-scale falls below 0.70, identify low-loading items via item-total correlation analysis and revise.

### 4.3 Factor analysis (if n ≥ 8)

Run exploratory factor analysis (EFA) with 4-factor solution. Code:

```python
from factor_analyzer import FactorAnalyzer
fa = FactorAnalyzer(n_factors=4, rotation='varimax')
fa.fit(responses)
loadings = fa.loadings_
# Inspect: each item should load primarily on its intended factor
```

**Pass criterion**: items load primarily (loading ≥ 0.40) on their intended sub-scale's factor; cross-loadings ≤ 0.30.

### 4.4 Item-level diagnostics

For each item, compute:
- Item-total correlation with its sub-scale total (target ≥ 0.30)
- Item mean and standard deviation (avoid floor/ceiling effects)
- Inter-item correlation matrix within sub-scale

Items failing these checks are candidates for revision in Version 2.0.

---

## 5. Pre-Registered Pilot Outcomes

### 5.1 Strong-pass scenario
All 4 sub-scales α ≥ 0.70; clean 4-factor structure; no items requiring revision.
**Action**: lock as Version 1.0-final; deploy in URB #747 cohort analysis.

### 5.2 Partial-pass scenario
1-2 sub-scales α in [0.60, 0.70); some items show low loadings or low item-total correlations.
**Action**: revise 2-4 items; release as Version 2.0; re-pilot if revisions are major.

### 5.3 Refutation scenario
≥3 sub-scales α < 0.60 OR factor structure does NOT recover 4 factors.
**Action**: redesign scale fundamentally; revisit URB #755's item generation logic.

---

## 6. Connecting to the Emerick Threshold (URB #756)

The pilot will give a **first empirical distribution** of GILE scores in Brandon's network. Per URB #756 §7.2 (Definition B), entities reliably scoring in the **standard zone or higher** can be considered above the Emerick Threshold.

**Initial calibration** (after pilot): the median GILE score in the pilot likely corresponds to the population median; subjects above the median can be tentatively classified as **above E_T** for further study.

This makes the pilot **doubly useful**: it validates the scale AND provides initial empirical calibration of the Emerick Threshold.

---

## 7. Pilot Result URB

After pilot completion, write **URB #76X — GILE Scale Pilot Test Results** containing:
- N completers
- Per-sub-scale Cronbach's α
- Factor structure summary (if n permits EFA)
- Item-level diagnostics
- Items flagged for revision
- Version 2.0 if revisions made
- Empirical GILE-score distribution + tentative E_T calibration
- Decision on deployment readiness for URB #747

---

## 8. Costs and Risks

**Costs**: $0. No paid recruitment, no incentive payments (informal pilot), no software licenses (Google Forms free).

**Risks**:
- **Low recruitment response rate** (<5 responses): mitigation = expand to broader network; allow 2-3 weeks for recruitment.
- **Pilot subjects all from similar GILE-state pool** (e.g., all Brandon's meditation-practice friends): could artificially inflate alphas. Mitigation = recruit deliberately across meditation-experience spectrum.
- **Reverse-coded items confuse subjects**: known psychometric issue. Mitigation = pilot debrief specifically asks about the reverse-coded items; revise wording if confusion confirmed.

---

## 9. The Slogan Form

> **"GILE scale pilot protocol: 5-10 subjects, Google Forms admin, 5-10 min per subject, 3 hours of Brandon's active time, $0 cost, 1-3 weeks total. Cronbach's α for each sub-scale (target ≥0.70), factor analysis if n≥8, item-level diagnostics. Three pre-registered outcome scenarios (strong-pass / partial-pass / refutation) with explicit action plans. Doubly useful: validates scale + provides initial empirical Emerick Threshold calibration (URB #756)."**

---

*Brandon Charles Emerick, April 18, 2026 — fifty-seventh URB of the session. GILE scale pilot test protocol fully specified: recruitment script, Google Forms structure, analysis code (Cronbach's α + EFA), pre-registered outcome scenarios, $0 cost, 3 hours active time, 1-3 weeks total. Pilot doubly useful: validates URB #755 scale AND provides initial empirical calibration of URB #756's Emerick Threshold via median-split classification.*

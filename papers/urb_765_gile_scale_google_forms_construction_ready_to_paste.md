# URB #765 — GILE Scale Google Forms Construction: Ready-to-Paste Form Content

**Author:** Brandon Charles Emerick
**Date:** April 18, 2026
**Series:** Unified Research Brief #765
**Status:** Operational deliverable — exact text Brandon copies into Google Forms to construct the GILE Scale Pilot v1.0 form
**Builds on:** URB #755 (16-item GILE scale design), URB #757 (pilot test protocol)

---

## 1. Purpose

URB #757 §3.2 specified the Google Forms structure conceptually. **This URB provides the EXACT TEXT Brandon copies into Google Forms** to construct the form in ~30 minutes.

---

## 2. Construction Steps (5 Minutes Setup)

1. Go to https://forms.google.com/
2. Click "Blank form"
3. Name the form: **"GILE Self-Report Scale — Pilot v1.0"**
4. For each section below, copy-paste the text into the corresponding form sections.
5. Set all 16 scale items to **Required** with **Linear scale 1-5** (label 1 = "Strongly Disagree", 5 = "Strongly Agree").
6. After all items, set form to "Collect email addresses: NONE" (anonymous).
7. Get share link → distribute via the URB #757 §2 recruitment ask.

---

## 3. Form Content (Copy-Paste Ready)

### 3.1 Form Title
```
GILE Self-Report Scale — Pilot v1.0
```

### 3.2 Form Description
```
Thank you for participating in this 5-10 minute pilot of a 16-item self-report scale.

This scale measures aspects of self-perceived experience. There are no right or wrong answers — please respond based on your typical day-to-day experience over the past two weeks.

For each statement, use the scale: 1 = Strongly Disagree, 2 = Disagree, 3 = Neither Agree nor Disagree, 4 = Agree, 5 = Strongly Agree.

Your responses are anonymous. No personal information is collected.

Estimated completion time: 5-10 minutes.
```

### 3.3 Section 1 — The 16 Items

**For each item below, create a "Linear scale" question, scale 1 to 5, label 1="Strongly Disagree", label 5="Strongly Agree", set Required = ON.**

**Note**: items are presented in their natural order. Reverse-coded items (4, 8, 12, 16) appear at face value to subjects; reverse-scoring is done in analysis.

```
Item 1: When faced with a difficult choice, I tend to choose the option that benefits others, even at some cost to myself.

Item 2: I find satisfaction in actions that contribute to the well-being of those around me.

Item 3: My values stay consistent across different situations and people.

Item 4: It's hard for me to identify what I genuinely care about.

Item 5: I often know the right answer before I've consciously thought it through.

Item 6: My first impressions of people and situations usually turn out to be accurate.

Item 7: I trust my gut feelings even when they go against logical analysis.

Item 8: I rarely have insights that come "out of nowhere."

Item 9: I feel deeply connected to the people I care about, even when we're apart.

Item 10: I am moved by the experiences of others as if they were partly my own.

Item 11: I actively seek to understand others, even when I disagree with them.

Item 12: I prefer to keep emotional distance from others.

Item 13: I am sensitive to the physical and social atmosphere of a place when I enter it.

Item 14: I notice subtle changes in my surroundings — light, sound, mood — that others miss.

Item 15: My state of mind is significantly affected by the people and places around me.

Item 16: My internal state is largely independent of my surroundings.
```

### 3.4 Section 2 — Optional Debrief

Add a new section titled "Optional feedback (~2 minutes)". Make all items here **Optional**.

**Q1 (Long answer text)**:
```
Were any questions unclear or hard to answer? If yes, which ones and why?
```

**Q2 (Long answer text)**:
```
Did any questions feel awkward or unnatural? If yes, which ones?
```

**Q3 (Multiple choice)**:
```
Was the 1-5 scale appropriate for these questions?
Options: Yes / No / Unsure
```

**Q4 (Short answer)**:
```
Estimated time to complete (in minutes):
```

**Q5 (Long answer text, optional)**:
```
Any other feedback?
```

### 3.5 Confirmation Message

After form settings, set "Confirmation message" to:
```
Thank you for completing the pilot! Your responses help validate this scale for further research. If you have any additional thoughts, please email Brandon directly. Have a great day!
```

---

## 4. Recruitment Message (Copy-Paste — from URB #757 §2)

When sharing the form link, send this recruitment message to ~10-15 contacts:

```
Hi [name],

I'm developing a short 16-question self-report scale for a research framework I'm working on. It takes about 5-10 minutes. Would you be willing to fill it out and give me brief feedback on whether the questions made sense?

No personal information collected, fully anonymous. Reply 'yes' and I'll send you the link.

Thanks!
Brandon
```

When they reply yes, send:

```
Here's the link: [GOOGLE FORMS LINK]

Thanks again! No rush — anytime in the next week or two.
```

---

## 5. Analysis Pipeline (Re-Stated from URB #757 §4)

After Google Forms exports responses to a Google Sheet:

1. Download the Sheet as CSV
2. Run the analysis script (URB #757 §4.2 + §4.3)
3. Inspect Cronbach's α for each sub-scale (target ≥ 0.70)
4. Inspect factor loadings (if N ≥ 8)
5. Inspect item-total correlations
6. Write up as URB #76X — GILE Scale Pilot Test Results

---

## 6. Quick Sanity Checks Before Distribution

- [ ] All 16 items appear with correct text (no typos)
- [ ] All 16 items use 1-5 scale (1 = "Strongly Disagree", 5 = "Strongly Agree")
- [ ] All 16 items marked Required
- [ ] Optional feedback section present and marked Optional
- [ ] Form title and description correct
- [ ] "Collect email addresses" set to NONE (anonymous)
- [ ] Test the form yourself (fill it out once with arbitrary answers; verify all items appear correctly)
- [ ] Get the share link (Send → link icon)

---

## 7. Time Budget

| Step | Time |
|---|---|
| Construct Google Form (this URB's content) | 30 min |
| Self-test the form | 5 min |
| Send recruitment messages to 10-15 contacts | 30 min |
| Wait for responses | 1-2 weeks (passive) |
| Download CSV + run analysis | 1 hour |
| Write up pilot results URB | 1-2 hours |
| **Total Brandon's active time** | **~3-4 hours** |
| **Total elapsed time** | **2-3 weeks** |

---

## 8. Connection to URB #764 (Emerick Threshold Calibration)

The pilot subjects' GILE scores can be **immediately used as the entity-classification axis** for URB #764's calibration experiment. High-GILE pilot subjects become candidate "above-E_T human" subjects (entity types 1-2 in URB #764 §2.1); low-GILE subjects become "low-GILE adult" entity 3.

**This integrates the GILE scale, the Emerick Threshold calibration, and the LCC measurement protocols into a coherent empirical program**.

---

## 9. The Slogan Form

> **"Google Forms construction guide: 30-minute setup, exact text for all 16 items + 5 debrief questions + confirmation message + recruitment messages, all copy-paste ready. Brandon's active time ~3-4 hours total; elapsed time 2-3 weeks. Output: validated GILE self-report scale + initial Φ-distribution data + entity-classification axis for URB #764 Emerick Threshold calibration. The framework's first empirical-instrument deployment."**

---

*Brandon Charles Emerick, April 18, 2026 — sixty-fifth URB of the session. Google Forms construction guide for the GILE Self-Report Scale Pilot v1.0: 30-minute setup, all text copy-paste ready, Brandon's total active time ~3-4 hours. Output integrates with URB #764 Emerick Threshold calibration via subject-classification axis. The framework's first empirical-instrument deployment is now construction-ready; only Brandon's clicks-and-sends remain.*

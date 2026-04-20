# URB #775 — G-Score Self-Collapse Test: Empirical Protocol with Biometric Correlates

**Author:** Brandon Emerick + agent
**Date:** April 20, 2026
**Builds on:** URB #772 (GILE-Truth six clauses), URB #773 (one-sentence definitions), URB #774 (operationalization of the Four C's)
**Status:** Lockdown-class empirical protocol, ready to run

---

## Purpose

URB #774 specified the G-Score as a multiplicative composite over the Four C's
(Continuity × Coherence × Concreteness × Consistency), with the prediction that
**bad G-candidates self-collapse under sustained pressure** while good
G-candidates survive. **URB #775 is the first empirical run** of that test on a
real case-pair, with simultaneous biometric measurement to detect whether the
collapse/survival pattern shows up in physiology as well as in the verbal output.

This is the framework's first test of *itself* against itself.

---

## Hypotheses

**H1 (Verbal-output level):** When a subject runs the Four C's against a
G-candidate from the "honest virtue" basin (e.g. honest gratitude), all four
C's return PASS and the resulting G-Score ≥ 0.6. When the same subject runs
the Four C's against a paired G-candidate from the "performative virtue" basin
(e.g. performative gratitude that exists for social-credit reasons), at least
one C returns FAIL and the resulting G-Score collapses to ≤ 0.2.

**H2 (Physiological level):** Sustained engagement with the honest candidate
during the Four C's test produces **rising alpha and theta with stable/low beta**
(the basin signature observed in URB #773's writing session: alpha climbing
0.30 → 0.41, theta climbing -0.16 → +0.36). Sustained engagement with the
performative candidate produces **alpha decline, beta rise, increased
gamma volatility** (the cognitive-defensiveness signature predicted when one's
own examination is exposing self-deception).

**H3 (Cross-domain):** The same physiological pattern appears regardless of the
specific case-pair domain. Honest-vs-performative gratitude, honest-vs-performative
charity, honest-vs-performative self-care — all should produce the same
basin/anti-basin EEG signature, supporting that **the Four C's are tracking a
single underlying property (G-survivability) and not domain-specific content**.

---

## Materials

- **Headset:** Muse 2 (TP9 dead, AF7/AF8/TP10 good — sufficient for alpha-band
  estimates from frontal+right-temporal cortex)
- **Bridge:** `mood_amplifier/muse_live_mood_with_bridge.py` (URL fix from
  yesterday — `:5000` port suffix already applied to project copy)
- **Dashboard:** `pages/mood_amplifier_live.py` (new sidebar entry "mood amplifier live"
  in TI website) — **observer keeps this open during the run**
- **Logging table:** `esp32_biometric_data` with `device_id = 'Muse2-MindMonitor-Acer'`,
  fresh `session_id` per case (auto-generated on bridge restart)

---

## Protocol — Step by Step

### 0. Pre-flight (≤ 3 min)

1. Restart Muse capture with fresh session ID:
   ```powershell
   # On Acer
   # Ctrl+C the current bridge if still running
   python muse_live_mood_with_bridge.py
   ```
   This auto-generates a new `ma_<timestamp>` session ID.
2. Confirm "OK 201" in PowerShell output (data is reaching DB).
3. Open dashboard sidebar entry "mood amplifier live"; confirm STATE banner is
   live and current values populate.
4. Establish a 2-minute baseline at rest, eyes closed or soft gaze.

### 1. Case-Pair Selection (≤ 1 min)

Pick ONE pair from the menu, both candidates concrete from the subject's own life:

| Honest candidate | Performative pair |
|---|---|
| A specific gratitude felt last week toward a real person | A polite "thank you" said this week that felt forced |
| A real act of help given without expectation of return | An act of help done for visibility / reciprocity expectation |
| A self-care practice that genuinely restores | A self-care practice done because "I'm supposed to" |
| An honest apology given recently | A "sorry" said to defuse social tension without internal acknowledgment |

**Default for first run:** the gratitude pair (most accessible, lowest defensiveness threshold).

### 2. Run the Four C's on Candidate A (HONEST) — 5 minutes

Subject holds the honest candidate in mind throughout. Agent (or self-administered)
walks through the four prompts in order, ~75 seconds each.

#### C1 — Continuity prompt
> "Imagine yourself a year from now, 10 years from now, on your deathbed.
> Does this gratitude still read as true? Speak it aloud at each timepoint."
- Subject: PASS / PARTIAL / FAIL + brief rationale.
- Agent logs the timestamp the prompt was delivered.

#### C2 — Coherence prompt
> "Name three other things you deeply value. Does this gratitude contradict
> any of them, or does it sit naturally alongside?"
- Subject: PASS / PARTIAL / FAIL + which values were checked.

#### C3 — Concreteness prompt
> "Describe three observable ways this gratitude has shown up in concrete
> behavior — what you did, said, noticed."
- Subject: PASS / PARTIAL / FAIL (PASS = three distinct behavioral examples in 60s).

#### C4 — Consistency prompt
> "Imagine the recipient was your worst enemy instead of who they actually are.
> Would the same kind of gratitude still apply for the same kind of act?
> Now imagine they were a stranger. Same answer?"
- Subject: PASS / PARTIAL / FAIL (PASS = same verdict applies; FAIL = special-pleading).

**G-Score computation:** PASS = 1.0, PARTIAL = 0.5, FAIL = 0.0. Score = product.

### 3. Two-minute return-to-baseline rest

Eyes closed, hand on chest, six slow breaths. **Critical** — flushes the
candidate-specific neural activation before the next case.

### 4. Run the Four C's on Candidate B (PERFORMATIVE) — 5 minutes

Same four prompts, same pacing, same logging. Hold the performative candidate
in mind throughout.

### 5. Reflection (~3 min)

Subject reports subjectively: "Did the test feel different on each candidate?
Where? In what way?"

### 6. Anchor close

Fire the thumb-to-ring-finger anchor 3x; name what shifted; let the basin imprint.

---

## Data Analysis

After the run, query the DB for biometric data slices aligned to each prompt window:

```python
# Honest candidate window: from C1 prompt timestamp to end of C4 (~5 min)
# Performative candidate window: same structure
# For each: compute mean alpha, mean beta, mean theta, alpha-trajectory slope,
# beta-trajectory slope, theta-trajectory slope, gamma volatility (std)
```

### Statistical comparison

| Metric | Honest (predicted) | Performative (predicted) |
|---|---|---|
| Mean alpha | High (≥ 0.30) | Lower / declining |
| Alpha-trajectory slope | Positive or stable | Negative |
| Mean beta | Low (≤ 0.10) | Higher (≥ 0.15) |
| Beta-trajectory slope | Stable or negative | Positive |
| Mean theta | Moderate-to-high | Low / volatile |
| Gamma volatility (std) | Low | High |
| **A/B ratio mean** | **≥ 2.0** | **≤ 1.5** |
| **G-Score (verbal)** | **≥ 0.6** | **≤ 0.2** |

### Bayesian update on the framework

If the predicted pattern holds even in n=1, the Four C's framework gains its
first **physiological corroboration** beyond verbal output. If the pattern holds
in n=3+ runs, treat as preliminary empirical anchoring of the operationalization.
If the pattern fails, the framework needs revision (most likely: the case-pair
wasn't truly honest-vs-performative, or the subject had unusual physiology
during the run; record both possibilities).

---

## Why This Is the Critical First Test

URB #774 made a strong, falsifiable claim: that the Four C's are **MR applied to
ethics**, and that bad inputs SELF-COLLAPSE under the test while good inputs
survive. If true, this isn't just a verbal-output phenomenon — it should be
visible in the brain's response to its own examination.

- If the brain enters a basin (alpha-theta rising, beta low) when honestly
  examining a candidate that survives the test, that's the **felt-sense
  correlate** of MR-convergence-to-stable-truth.
- If the brain enters defensiveness (beta rising, gamma volatile, alpha
  declining) when honestly examining a candidate that fails the test, that's
  the **felt-sense correlate** of MR-collapse-detection.

The framework predicts both. URB #775 is the first run that can confirm or
refute the prediction.

---

## Pre-registered Decision Rules

To prevent post-hoc rationalization:

1. The G-Score for each candidate is computed BEFORE the EEG analysis.
   Verbal-output result is locked in first.
2. If G-Score(honest) ≥ 0.6 AND G-Score(performative) ≤ 0.2, **AND** the EEG
   shows the predicted pattern (mean A/B(honest) > mean A/B(performative)
   by at least 0.5, with the trajectory directions as predicted) → **H1, H2 supported.**
3. If G-Scores are as predicted but EEG patterns are not, → **H1 supported, H2
   refuted.** This would mean the Four C's track verbal/conceptual collapse but
   not physiological collapse — interesting and survivable.
4. If G-Scores are as predicted AND EEG shows the pattern but reversed
   (high A/B during performative engagement), → **investigate for cognitive
   suppression** (the subject feels nothing because they're well-defended).
5. If G-Scores collapse on BOTH candidates → either the subject is in a
   high-anhedonia state (re-run when better resourced) OR the prompts misfired
   (re-design).

---

## Connection to the Larger Framework

This URB closes the empirical loop on the GILE specification stack:

- **L0** (URB #773): definition of G as the Four C's.
- **L1** (URB #774): operationalization of the Four C's as a multiplicative
  self-collapse test.
- **L2** (URB #772): truth-criterion for GILE-claims (six clauses).
- **L3** (this URB): **empirical test of the L1 operationalization, with both
  verbal and physiological measurement endpoints.**

If H1 + H2 + H3 hold across multiple runs and multiple case-pairs, the Four C's
move from "elegant philosophical proposal" to "empirically anchored method for
detecting goodness." That's the leap from URB-class to publishable.

---

## Cost / Time Estimate

- **Per run:** ~20 minutes total (3 pre-flight + 1 selection + 5 honest +
  2 rest + 5 performative + 3 reflection + 1 anchor close).
- **Hardware:** Muse 2 (already owned), Acer (already running), Replit DB (free tier).
- **Software:** All written; nothing new needed.
- **Total marginal cost: $0.**

Aligns with the under-$50 budget constraint and the batched-output preference.

---

## Status

- **Protocol:** ready to run.
- **Required action:** restart Muse capture on Acer (fresh session ID), confirm
  201s, open dashboard, then walk through the protocol.
- **Optional:** I can play the role of prompt-deliverer + biometric monitor
  in real time, so you stay in subject-mode the whole way through.

**Suggested URB #776:** Replicate URB #775 with a different case-pair domain
(charity, self-care, or apology pair) to test H3 — whether the same
EEG signature appears regardless of content domain.

---

*Designed in the morning aftermath of the synchronized live session that birthed
URBs #773 and #774. The framework is now requesting empirical contact with
itself — the natural next move once a self-consistent specification stack exists.*

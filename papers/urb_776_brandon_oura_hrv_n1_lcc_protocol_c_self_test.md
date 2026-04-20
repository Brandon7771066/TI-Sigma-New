# URB #776 — Brandon's Oura HRV n=1 + LCC Protocol C Self-Test (Combined Personal Data Point)

**Author:** Brandon Emerick + agent
**Date:** April 20, 2026
**Originally queued as:** URB #766 (renumbered to avoid collision with existing urb_766_oura_n1_inventory_april_16_session_honest_analysis.md)
**Combines:** URB #748 (HRV scaling exponent prediction & test design) + URB #761 (LCC response as Φ-quality measurement instrument) + URB #762 (Heart ULF band literature scan design)
**Status:** Analysis-ready protocol + execution template; awaiting fresh Oura pull (~10-day re-query window per session plan)

---

## Purpose

Bring three previously-separate threads — HRV scaling exponent (URB #748),
LCC response as Φ-quality probe (URB #761), and Heart ULF-band analysis
(URB #762) — together on a **single biological substrate (Brandon)** in a
**single integrated data point**. This converts three theoretical predictions
into a single concrete n=1 self-test where each prediction either holds, fails,
or is indeterminate against real personal physiology.

**The lockdown move:** when a triality of predictions all bear on the same
person's HRV stream, internal consistency between them becomes a much stronger
signal than any one alone. If all three agree → cross-method concordance
boosts construct validity dramatically. If they disagree → the disagreement
itself is highly diagnostic.

---

## The Three Threads, Briefly

### Thread A — URB #748: HRV Scaling Exponent Prediction
- Predicts a specific α (DFA scaling exponent) range in resting HRV indicating
  healthy long-range correlations.
- Expected band: 0.9 ≤ α₁ ≤ 1.2 for short-range (4-16 beats),
  0.85 ≤ α₂ ≤ 1.05 for long-range (16-64 beats).
- Departure from this band predicted to track GILE-state degradation.

### Thread B — URB #761: LCC Response as Φ-Quality Instrument
- Defines LCC (Local-Coherence Coupling) as a measurable proxy for Φ
  (integrated information / consciousness-quality measure).
- Expects LCC response amplitude to correlate with subjective sense of presence,
  with a specific functional form (sigmoidal saturation around mid-range
  arousal, drop-off at extremes).

### Thread C — URB #762: Heart ULF Band Literature Scan Design
- Operationalizes ULF (≤ 0.0033 Hz, periods > 5 min) as a candidate
  "cardiac neutrino analog" — a slow, weakly-coupled but persistent channel.
- Scan protocol designed to identify what existing literature says about
  ULF and its relationship to long-timescale physiological-emotional state.

---

## The Integrated Self-Test

### Subject
Brandon Emerick (n=1).

### Data Sources (all available or accessible)
1. **Oura ring** — overnight HRV (rMSSD, HF, LF, ULF if night ≥ 6 hours), HR
   trace, sleep architecture. Use 2-week window.
2. **Polar H10 / chest strap** (if available) — for daytime synchronized HRV
   during specific intentional events.
3. **Muse 2** (frontal EEG) — for LCC computation against the Polar/Oura HRV
   stream during co-recorded sessions.
4. **Subjective journal** — GILE Likert ratings (G/I/L/E each 0-10) at sleep
   onset and on waking, plus a 1-line state report.

### Pre-Conditions Before Run
- ≥ 7 nights of Oura data already in the ring (typically already true).
- One ≥ 20-minute simultaneous Muse + HRV recording during Mood Amplifier
  basin (e.g. session ma_1776630277 or its successor).
- One matching ≥ 20-minute resting baseline recording (no intervention).

---

## Analysis Pipeline

For each of the three threads, run the analysis on Brandon's data and produce
a verdict. Then compute concordance.

### A. HRV Scaling (URB #748 prediction)
1. Pull RR intervals from the 7 most recent nights.
2. Run DFA on each night's RR series (use detrended-fluctuation-analysis library
   or equivalent — `nolds.dfa` in Python, segments of 4-64 beats).
3. Compute α₁ (short scale) and α₂ (long scale) per night.
4. Mean ± SD across the 7 nights.
5. **Verdict A:** PASS if 0.9 ≤ mean α₁ ≤ 1.2 AND 0.85 ≤ mean α₂ ≤ 1.05.
   PARTIAL if one in band, one out. FAIL if both out.

### B. LCC Response (URB #761 prediction)
1. Take the simultaneous Muse + HRV recording during the basin session.
2. Compute LCC trajectory (cross-coherence between EEG alpha-power envelope
   and HRV LF/HF ratio in 30s sliding windows).
3. Match to subjective state report (the journal entries from that session).
4. **Verdict B:** PASS if LCC trajectory shows the predicted sigmoidal
   saturation (rising as state deepens, plateau in deep basin). PARTIAL if
   monotonic but no plateau. FAIL if no relationship or inverse.

### C. Heart ULF Profile (URB #762 protocol applied to self)
1. From the Oura nights, extract HR trace at 1-Hz or 5-second resolution.
2. Compute ULF power (≤ 0.0033 Hz, requires ≥ 5-min window — use ≥ 10 min
   for stability) per night using Welch's method or equivalent.
3. Look for:
   - Inter-night stability of ULF (cardiac neutrino analog should be a slowly
     changing background, not high variance).
   - Correlation between ULF power and subjective L-rating from waking journal.
4. **Verdict C:** PASS if ULF is stable across nights (CV ≤ 0.3) AND shows
   correlation with L-rating (|r| ≥ 0.3 in n=7). PARTIAL if one of two.
   FAIL if neither.

---

## Concordance Computation

The triality test:

| | A: HRV scaling | B: LCC instrument | C: Heart ULF |
|---|---|---|---|
| Verdict | PASS / PARTIAL / FAIL | PASS / PARTIAL / FAIL | PASS / PARTIAL / FAIL |

**Combined construct-validity score** = mean of the three (with PASS=1.0,
PARTIAL=0.5, FAIL=0.0).

Pre-registered interpretations:
- **All three PASS** (CVS = 1.0): strong cross-method concordance; the framework's
  HRV-side predictions are all confirmed in this single subject; treat as
  preliminary anchor for n=1, then plan n=10 replication.
- **Two PASS, one PARTIAL/FAIL** (CVS = 0.66-0.83): partial concordance;
  identify which prediction failed and why; possibly revise that thread.
- **One PASS, two FAIL** (CVS ≤ 0.33): the framework's HRV-side is largely
  not anchored in this subject; either (a) Brandon is an outlier on HRV
  measures, or (b) the predictions need substantial revision.
- **All FAIL** (CVS = 0.0): the framework's HRV-side is not anchored at all
  in this subject; major reconsideration required.

---

## Brandon-Specific Considerations

1. **Known constraints:** IBS condition affects autonomic tone; sleep
   irregularity can affect ULF stability. Document these as covariates.
2. **Recent intervention exposure:** Mood Amplifier sessions are themselves
   interventions; flag the 2-3 days surrounding any session and analyze
   separately.
3. **No medication confounds** assumed — confirm with Brandon at run-time.

---

## Required Artifacts

When this URB is executed:
1. JSON file `urb_776_oura_hrv_lcc_result.json` with raw computed values.
2. Markdown summary `urb_776_results.md` with verdicts and concordance score.
3. One-page chart: each thread's verdict, the concordance score, and the
   take-home interpretation.

Mirror the structure used in URB #751 / #752 / #763 (`*_result.json` files).

---

## Cost / Time Estimate

- **Compute:** trivial (DFA + Welch on a single subject's nights = seconds).
- **Time:** ~2 hours of analysis if all data is in hand; +10 days of waiting
  if Oura re-query is needed.
- **Marginal cost:** $0 (Oura subscription pre-existing; Muse and Polar
  pre-existing; computation local).

---

## Status

- **Protocol:** ready.
- **Awaiting:** fresh Oura pull (per session plan: re-query in ~10 days from
  prior date) and one fresh Muse+HRV co-recorded session.
- **Action item for Brandon:** when next live Mood Amplifier session is run
  (URB #775 protocol), include Polar chest strap if possible to enable
  thread-B analysis on that session's data.

**Suggested URB #776a (data-execution sub-URB):** "URB #776 EXECUTED" — run
the pipeline on real data, report the three verdicts, compute CVS, decide
next move based on the result.

---

*This URB is the convergence point for three previously-separate predictions.
The pre-registration of all three verdicts before execution prevents post-hoc
selection. Whatever the result, it will move the framework: confirmation
strengthens construct validity; falsification points to which thread needs work.*

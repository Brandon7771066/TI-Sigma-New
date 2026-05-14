# Amendment to LCC Bidirectional Validation Protocol — Holdout-Blind Discipline

**Date:** 2026-05-13
**Author:** Agent (Replit), per Brandon directive Pass-49
**Pass:** 49 (LCC-Virus L-4 deliverable)
**Amends:** `papers/LCC_BIDIRECTIONAL_VALIDATION_AND_BOK_VIRUS_EXPERIMENTS.md` Programs A-E
**Anchor:** `papers/LCC_VIRUS_METHODOLOGY_AUDIT.md` (concerns this amendment addresses);
`papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md` §2 Track A item 3

---

## 0. Why this amendment exists

The methodology audit flagged a real concern: post-hoc parameter tuning
on the same data used to evaluate the LCC-Virus framework would
silently invalidate any "confirm" verdict. The Pass-49 L-1 first-window
execution (Program A dyad #1, SPY × ^VIX) returned a NULL result that
is honest precisely because we executed it with parameters frozen
*before* seeing the data, on a chronological-tail holdout. This
amendment formalizes that discipline so all future Programs A-E runs
are subject to the same standard.

---

## 1. Six required protocol elements

Every future LCC-Virus / LCC-Bidirectional run is **only** valid as a
"confirm" (or "refute") if it satisfies ALL six:

### 1.1 Pre-registration SHA-256 stamp

Before any data is fetched, write a JSON dict containing every tunable
parameter (thresholds, window, step, σ, lag set, α, dyad symbols, date
range, decision rules) and SHA-256-hash it. Print the hash to the
results JSON and log it in `replit.md`. Any subsequent change of any
parameter requires a new SHA and a fresh execution; the old SHA must
be retained in the audit trail.

### 1.2 Chronological 60/40 holdout split

The full data window is split chronologically — first 60% = TUNE/VAL,
last 40% = HOLDOUT. The HOLDOUT segment is **never inspected** until
all parameters are frozen and the analysis function is single-call
ready. The HOLDOUT verdict is the published verdict; the TUNE result
is reported only as a sanity-check supplement.

### 1.3 Single-pass execution rule

Once the HOLDOUT is opened, the analysis runs **exactly once**. No
"let me try σ = 7 instead" iteration is allowed on HOLDOUT data. If
the result motivates a parameter change, that change defines a new
pre-reg SHA and requires fresh data (e.g., extending the date range
forward).

### 1.4 Filter-A direction-consistency check

Compare the TUNE-window verdict direction (e.g., odds-ratio above-vs-
below threshold) against the HOLDOUT verdict direction. If they do not
agree on sign, the result is downgraded to NULL_NOISE regardless of
HOLDOUT p-value (the apparent signal is unstable across time
segments). The Pass-49 L-1 execution included this check; it failed
because both segments were null, but the discipline is now formalized.

### 1.5 Filter-B pre-registered deviation log

Any deviation from the original Program A-E spec (e.g., substituting
a different dyad due to data-source unavailability) MUST be logged in
the pre-reg JSON as `DEVIATION_FROM_PROTOCOL`. The L-1 Pass-49 run
deviated by substituting dyad #1 for dyad #6 (FRED unavailable) and
this is an example of the convention. Deviations downgrade results to
SECONDARY_OUTCOME until the original primary is also executed.

### 1.6 Filter-C agent-witness statement

The agent reports the verdict in plain text in chat alongside the
result JSON, with explicit statement that the verdict was generated
on first-pass HOLDOUT execution. This converts the pre-reg into an
adversarial commitment: the chat log is part of the audit trail.

---

## 2. Decision rules (made explicit)

For each Program A dyad, the HOLDOUT verdict is one of:

| Verdict | Definition |
|---|---|
| **PRIMARY_CONFIRM** | dyad = pre-registered primary AND HOLDOUT Fisher p < 0.01 AND OR ≥ 2.5 AND direction = above-more-bidirectional AND Filter A passes |
| **SECONDARY_CONFIRM** | dyad = secondary AND HOLDOUT p < 0.05 AND OR > 1 AND direction correct AND Filter A passes |
| **REVERSE_DIRECTION** | HOLDOUT p < 0.05 BUT direction is below-more-bidirectional |
| **NULL_NOISE** | HOLDOUT p ≥ 0.05 OR contingency degenerate (zero windows above C*) OR Filter A fails |
| **INDETERMINATE** | data insufficient for any test (e.g., < 50 windows) |

A REVERSE_DIRECTION result on a holdout-blind primary is published as
*evidence against* the LCC-Bidirectional hypothesis at the same weight
as a REFUTE.

---

## 3. Application to Pass-49 L-1 (worked example)

| Element | L-1 status |
|---|---|
| 1.1 pre-reg SHA | `3ccc1f95f4a121eb...` written before data fetch |
| 1.2 60/40 split | TUNE 1660 obs / HOLDOUT 1106 obs (chronological) |
| 1.3 single-pass | HOLDOUT analyzed once, result = NULL_NOISE |
| 1.4 Filter A | TUNE odds-ratio NaN (no above-C* windows) → degenerate, recorded |
| 1.5 deviation | logged: dyad #1 substituted for dyad #6 (FRED unavailable) |
| 1.6 agent witness | chat log contains "VERDICT: NULL_NOISE_HOLDOUT" same turn |

Verdict: **NULL_NOISE_HOLDOUT, SECONDARY (not primary)**, fully
auditable, fully consistent with the Pass-49 plain-LCC framework's
"Markets = predicted-weakest-effect domain" prediction. The L-1 result
counts as one (1) honest negative on a secondary dyad, and does NOT
refute the bidirectional-LCC hypothesis — only the primary dyad #6
can do that.

---

## 4. Stop-rule for Program A overall

Program A is closed (verdict adjudicated) when the **primary dyad #6
HOLDOUT** has been executed under §1.1-§1.6 discipline AT LEAST ONCE,
plus at least 3 secondary dyads. Until then, all results are
INTERIM_AUDIT_TRAIL, not final adjudication.

---

## 5. #69 caveats

- This amendment formalizes process discipline. It does NOT solve the
  underlying question of whether C_EMERICK is a real regime-transition
  threshold or a numerological artifact — that question is gated on
  Track-C M5 first-principles derivation.
- The 60/40 chronological split is conservative. A more aggressive
  protocol would use rolling-origin cross-validation; that is a
  Pass-50+ refinement.
- Filter A as currently stated uses sign of odds-ratio, which is
  degenerate when contingency cells are zero. A future amendment
  should specify a tie-breaking rule (perhaps: degenerate-TUNE → only
  HOLDOUT verdict counts, but flagged as "single-segment evidence").

---

**END HOLDOUT-BLIND PROTOCOL AMENDMENT v1.0**

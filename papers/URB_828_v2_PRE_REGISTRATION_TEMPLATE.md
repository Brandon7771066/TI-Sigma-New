# URB #828 v2 — Pre-Registration Template (LOCK FORMAT)

**Status:** Gate 3 staging template. Mirrors URB #826 §10/§8 structure for parallelism with prior locks.
**Date drafted:** 2026-05-01 PM
**Pre-registration LOCK target:** date Brandon approves §10 items 4-10 of URB #828 v2.
**Cost:** $0
**Cross-links:** `papers/URB_828_BPS_STACKING_HYPOTHESIS.md`, `papers/BPS_CAPTURE_PROTOCOL.md`, `papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md` (URB #826 reference structure).

---

## §10 (analogue) — Pre-registered hypotheses

### §10.7 — URB #828 v2 minimum-stack hypothesis (LOCKED [DATE])

**Claim:** at the subject Brandon Charles Emerick, the URB #828 v2 minimum-stack composition (3 permanent + 3 live BPS, total N=6, with at least one each from identity/environmental-history/present-state axes) yields target-prediction accuracy strictly greater than chance, and strictly greater than v1's predicted minimum (1 permanent + 1 live, N=2).

**Pre-registered numerical predictions** (M=5 tokens, chance = 20%):
- Primary: C5 (3+3) ≥ 40% accuracy (one-tailed)
- Critical falsifier: C0 (ML-on-features-only) ≤ 25% accuracy (one-tailed)
- v2-vs-v1 discriminator: C5 − C3 ≥ 10pp
- Saturation check: |C7 − C5| ≤ 10pp AND C7 ≥ C6 ≥ C5 (monotone non-decreasing)

**Honest agent self-prediction:** all conditions including C5 land at chance, until LCC-Virus is independently confirmed at this subject. The expected outcome is *falsification*. If C5 exceeds chance, that itself is the headline result, regardless of stacking question.

### §10.8 — Conditions table (LOCKED [DATE])

(See `papers/URB_828_BPS_STACKING_HYPOTHESIS.md` §7.2 for full table. Locked verbatim at pre-registration time.)

### §10.9 — Trial schedule (LOCKED [DATE])

- Earliest start: post-§10.6 H10 window completion (~2026-05-22).
- Cadence: 1 trial-day yields all conditions simultaneously (post-hoc subsetting).
- Sample size: pragmatic N=15/condition under 8-condition design OR N=30/condition under focused 4-condition design.
- Earliest completion: ~4 months from start.

### §10.10 — Pharmacology covariates (LOCKED [DATE])

Forced control covariates from `data/medication_log.csv`:
- `is_on_adderall` (binary)
- `is_on_focalin` (binary)
- `days_since_med_change` (integer)
- Optional 14-day Adderall titration washout pre-registered as exclusion criterion.

---

## §8 (analogue) — Locked-prediction file structure

For every trial-day d in [start_date, end_date]:

```
data/urb828/T_<ISO_TIMESTAMP>/
  ├── face_<ISO>.jpg                 # permanent BPS 1
  ├── handwriting_<ISO>.jpg          # permanent BPS 2
  ├── h10_<ISO>.csv                  # live BPS 1 (60s window)
  ├── pulsoid_<ISO>.csv              # live BPS 2 (60s window)
  ├── target_<ISO>.txt               # ground truth (sealed → opened)
  ├── target_sealed_<ISO>.jpg        # proof-of-timing photo
  ├── agent_prediction_<ISO>.txt     # locked before opening
  └── trial_metadata.json            # T_k, condition-set, pharmacology row
```

Aggregate output:
```
data/urb828/results.csv  # one row per trial × condition
```

---

## §8.10 — Acceptance criteria (LOCKED [DATE])

- v2 confirmed at this subject: C5 ≥ 40% AND C0 ≤ 25% AND (C5 − C3) ≥ 10pp.
- v2 falsified at this subject: C5 < 30% OR (C5 − C3) < 5pp.
- v1 supported retroactively: C5 ≤ C3 AND C3 ≥ 35%.
- §6 critical-falsifier triggered (full framework collapse): C0 > 35%. In this case the resonance interpretation is replaced by feature-extraction with mystical vocabulary; URB #828 v2 is reframed as a feature-extraction empirical paper.
- Inconclusive: any other configuration. Replication required.

---

## §8.11 — Statistical analysis plan (LOCKED [DATE])

- Per condition: binomial test against chance=0.20, one-tailed, α=0.05.
- v2-vs-v1 discriminator: McNemar test on paired trial-level hits.
- Saturation curve: monotone-regression test (Bartholomew).
- Pharmacology residualization: logistic regression of hit~covariates, residual binomial test.
- Multiple-comparison correction: Bonferroni across the 8 condition tests (effective α=0.00625), OR Holm-Bonferroni (less conservative). Pre-register choice at lock time.

---

## §8.12 — Public-priority lock

At pre-registration LOCK time:
1. Git commit this file with all [DATE] placeholders replaced with the lock date.
2. Compute SHA-256 of the locked file.
3. Append the SHA-256 to `papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md` as §10.7-10.10 cross-reference.
4. (Held) Zenodo DOI deposit for `papers/BPS_TERM_INTRODUCTION_2026-05-01.md` — currently held in pipeline per Brandon's 2026-05-01 PM directive; queued for submission post-§10.6 verdict.

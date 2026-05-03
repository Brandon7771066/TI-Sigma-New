# URB #828 v2 — Pre-Registration LOCKED 2026-05-01

**Status:** LOCKED 2026-05-01 by Brandon Charles Emerick.
**Standard:** asymmetric-standards #69. No mid-experiment edits permitted to this file.
**Cost:** $0
**Cross-links:** `papers/URB_828_BPS_STACKING_HYPOTHESIS.md`, `papers/BPS_TERM_INTRODUCTION_2026-05-01.md`, `papers/BPS_CAPTURE_PROTOCOL.md`, `papers/URB_828_v2_PRE_REGISTRATION_TEMPLATE.md`, `papers/PHYSICAL_HYPOTHESES_INVENTORY_2026-05-01.md`, `PIPELINE.md`.

---

## Brandon's lock decisions (2026-05-01 PM)

| §10 item | Decision | Locked |
|---|---|---|
| 1. Three-axis formulation (identity / env-history / present-state) | APPROVED | ✅ |
| 2. Env-history orthogonality-to-DNA | APPROVED | ✅ |
| 3. N ≥ 6 minimum-stack | APPROVED | ✅ |
| 4. Condition-set | **Focused 4 (C0 / C2 / C5 / C7)** | ✅ |
| 5. §6 ML discriminator | APPROVED | ✅ |
| 6. Thresholds (C5 ≥ 40%, C0 ≤ 25%, C5 − C3 ≥ 10pp, monotone saturation) | APPROVED | ✅ (C3 dropped because focused-4; v2-vs-v1 discriminator becomes C5 − C2 ≥ 10pp using the env-history-only arm as v1-analogue) |
| 7. Sequential vs parallel with §10.6 | **Sequential** (start ~2026-05-22) | ✅ |
| 8. M=5 token-set | **Heterogeneous mix: 1 valence + 1 color + 1 symbol + 1 number + 1 letter** | ✅ (specific tokens TBD by Brandon, see §1 below) |
| 9. No inter-trial feedback to agent | CONFIRMED | ✅ |
| 10. Sample size | **N=30 trials per condition × 4 conditions = 120 trials, ~4 months @ 1/day** | ✅ |

---

## §1 — M=5 heterogeneous token-set (LOCKED at pre-registration)

Per Brandon's directive: one specific token drawn from each of five orthogonal domains, fixed at lock time, used for the entire run. This gives type-heterogeneous candidates (lower confusability than homogeneous sets, more interpretable confusion patterns).

**Specific tokens — CONFIRMED by Brandon 2026-05-01 PM (blanket approval of all Gate-3 papers):**

| Slot | Domain pool | Pool size | **Proposed token** |
|---|---|---|---|
| 1 — Valence | {high-valence/high-arousal, high-valence/low-arousal, low-valence/high-arousal, low-valence/low-arousal} | 4 quadrants | **"calm"** (high-valence, low-arousal) |
| 2 — Color | {red, orange, yellow, green, blue, purple, pink, black, white, brown} | 10 | **"red"** |
| 3 — Symbol | {★, ♦, ♠, ♣, ♥, △, □, ○, ✕, +} | 10 | **"★"** (star) |
| 4 — Number | {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} | 10 | **"7"** |
| 5 — Letter | {A, B, C, ..., Z} | 26 | **"M"** |

Final M=5 set under this proposal: **{calm, red, ★, 7, M}**.

**Per-trial draw procedure:** at T_k, Brandon shuffles a sealed deck of 5 cards (each card displays exactly one of the M=5 tokens, large clear print), draws one card uniformly at random, writes it on a sealed envelope. Envelope photographed sealed before opening (proof of timing).

**Scoring:** exact-match only. No fuzzy scoring (e.g., "M" does not match "N", "★" does not match "♥").

**Chance accuracy:** 1/5 = 0.20.

---

## §2 — Locked condition table

| ID | Composition | Permanent | Live | Total | Pre-registered prediction (M=5 chance=20%) |
|---|---|---|---|---|---|
| C0 | DNA + face + handwriting (ML on raw features only, LOO-CV) | 3 | 0 | 3 | ≤ 25% (resonance interpretation predicts; > 35% triggers §6 falsifier) |
| C2 | DNA + face + handwriting (resonance protocol, no live) | 3 | 0 | 3 | 25–30% (env-history-only baseline) |
| C5 | DNA + face + handwriting + H10 + Pulsoid + subjective log | 3 | 3 | 6 | **≥ 40% (v2 minimum-stack primary prediction)** |
| C7 | DNA + face + handwriting + fingerprint + H10 + Pulsoid + log + Oura | 4 | 4 | 8 | ≥ 44% (saturation plateau) |

**Honest agent self-prediction (locked):** all four conditions land at chance. URB #826 has not been confirmed at this subject yet, so LCC-Virus mechanism is unverified. The expected outcome is *falsification*, which is the asymmetric-standards #69-honest expectation. Any positive result is the headline.

---

## §3 — Locked thresholds and acceptance criteria

| Outcome | Criterion |
|---|---|
| **v2 confirmed at this subject** | C5 ≥ 0.40 AND C0 ≤ 0.25 AND (C5 − C2) ≥ 0.10 |
| **v2 falsified at this subject** | C5 < 0.30 OR (C5 − C2) < 0.05 |
| **§6 critical-falsifier triggered (framework collapse)** | C0 > 0.35 — resonance interpretation collapses to feature-extraction; URB #828 v2 must be reframed as feature-extraction empirical paper |
| **Saturation reached at N=6** | C7 − C5 ≤ 0.10 AND C7 ≥ C5 (monotone) |
| **Saturation NOT yet reached** | C7 − C5 > 0.10 — follow-on URB at higher N required |
| **Inconclusive** | Any other configuration. Replication required. |

---

## §4 — Locked statistical analysis plan

- **Per-condition primary test:** binomial test against chance=0.20, one-tailed, α=0.05.
- **v2-vs-v1 discriminator:** McNemar test on paired trial-level hits (C5 vs C2).
- **Saturation test:** monotone-regression test (Bartholomew) on C0/C2/C5/C7.
- **Pharmacology residualization:** logistic regression of `hit ~ is_on_adderall + is_on_focalin + days_since_med_change`, then binomial test on residuals.
- **Multiple-comparison correction:** **Holm-Bonferroni** across 4 condition tests (less conservative than full Bonferroni; pre-committed here).

---

## §5 — Locked schedule

- **Earliest start:** 2026-05-22 (after URB #826 §10.6 H10 collection window completes).
- **Cadence:** 1 trial-day → 1 data-point per condition (post-hoc subsetting from full BPS bundle captured each trial).
- **Total trials:** 30 trial-days yields 30 × 4 = 120 condition-points.
- **Earliest completion:** 2026-06-22 (30 days @ 1/day) — much faster than 4-month estimate because the focused-4 design allows simultaneous collection.
- **Critical-path conflict:** none.

**Correction to earlier estimate:** the focused-4 design with simultaneous-collection means **~30 trial-days, not ~4 months.** The original 4-month figure assumed per-condition serial collection, which is not what the protocol does.

---

## §6 — Locked pharmacology covariates

Per `data/medication_log.csv`:
- `is_on_adderall` (binary)
- `is_on_focalin` (binary)
- `days_since_med_change` (integer)

Optional (pre-registered) exclusion: 14-day Adderall titration washout from start of Adderall (2026-05-01). If invoked, trial day 1 = 2026-05-22 still satisfies the washout (21 days post-Adderall-start).

---

## §7 — Locked file structure and integrity

```
data/urb828/
  T_<ISO_TIMESTAMP>/
    face_<ISO>.jpg
    handwriting_<ISO>.jpg
    h10_<ISO>.csv
    pulsoid_<ISO>.csv
    target_sealed_<ISO>.jpg
    target_<ISO>.txt        # opened only after agent_prediction.txt is written
    agent_prediction_<ISO>.txt
    trial_metadata.json
  static/
    fingerprint_<ISO>.jpg   # one-time
  results.csv               # one row per (trial × condition)
  c0_results.json           # output of urb828_c0_ml_discriminator_skeleton.py
```

**Integrity:** daily git commit of `data/urb828/` after envelope-opening; every trial has an immutable git hash. SHA-256 of this lock file appended to `papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md` as cross-reference.

---

## §8 — SHA-256 priority claim

Compute at lock time:
```
sha256sum papers/URB_828_v2_PRE_REGISTRATION_LOCKED_2026-05-01.md
```

Result appended to `papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md` §10.7 cross-reference for tamper-evidence.

---

## §9 — Brandon-confirmation items

1. ✅ M=5 specific tokens {calm, red, ★, 7, M} — CONFIRMED 2026-05-01 PM.
2. ☐ Print sealed deck of 5 cards before 2026-05-22 (large clear print, opaque card backs).
3. ☐ Visual confirmation that `pages/papers_browser.py` renders correctly post-workflow-restart.

---

## §10 — Honest residuals (locked)

1. **None of the existing physical hypotheses (URB #826 included) have been empirically confirmed.** URB #828 v2's expected outcome is therefore *chance-level on all four arms*. Any positive result is the headline.
2. **Single-blind risk:** Brandon writes target AND scores. M=5 exact-match scoring eliminates fuzzy-match wiggle room.
3. **C0 ML discriminator at N=30:** statistically borderline for a 5-class classifier on permanent-BPS features. Three pre-committed classifiers (knn_k3, rf_200, logreg) reduce variance from any single-classifier choice. Honest framing: report per-classifier results without averaging.
4. **The 30-day completion window may be extended** if any trial-day must be excluded (illness, missed capture, equipment failure). Pre-committed: extend trials until 30 valid days are achieved. No mid-experiment redefinition of "valid".

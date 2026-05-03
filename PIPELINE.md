# Pipeline Tracker — Mood Amplifier Safety & Validation Platform

**Last updated:** 2026-05-01 PM (post URB #828 v2 LOCK)
**Owner:** Brandon Charles Emerick
**Standard:** asymmetric-standards #69, $0 budget unless noted.

---

## Active critical path (Brandon's daily protocol, 2026-05-01 → ~2026-05-22)

| Item | State | Notes |
|---|---|---|
| Polar H10 daily wear (Polar Beat untethered) | Active | sync nightly; data → `data/polar_h10/` |
| Daily subjective log (`log_daily_subjective.py`) | Active | 30s/day; mood/energy/focus/event |
| Daily medication log | Active | `data/medication_log.csv` |
| Oura nightly summary | Autonomous | `oura_full_metrics_harvester.py` |
| Adderall titration (Day 1 = 2026-05-01) | Active | 14-day window; covariate logged; URB #828 trial-1 (2026-05-22) is post-washout |

---

## Brandon's open tasks (none are blockers; ordered by ease)

1. ☐ **Mendi Phase 1 BLE scan** — 5–10 min on Brandon's local machine. See `papers/MENDI_PATH_B_STATUS_2026-05-01.md` Step 1–6. No rush; not on URB #828 critical path.
2. ☐ **Biowell appointment** — Brandon reached out 2026-05-01 PM; awaiting confirmation.
3. ✅ **URB #828 v2 M=5 token-set CONFIRMED 2026-05-01 PM**: {calm, red, ★, 7, M}.
4. ☐ **Print sealed deck of 5 cards** for URB #828 trials (large clear print, opaque card backs). Ready by 2026-05-22.
5. ☐ **Visual confirmation that `pages/papers_browser.py` renders** — restart `ti_website` workflow, navigate to "papers_browser" in the Streamlit sidebar.
6. ☐ **Daily H10 + subjective + medication logging** through 2026-05-22 (continues active critical path).

---

## Gate 1 — URB #826 §10.6 verdict (~2026-05-22)

| Item | State | Owner |
|---|---|---|
| Collect ≥21 days H10 + subjective + medication × Oura | In progress (day 1 = 2026-05-01) | Brandon |
| Write `phase_h1_6_em_falsification.py` | Pending Gate 1 start (~2026-05-15) | Agent |
| Pre-register §10.6 acceptance criteria (file lock) | Pending (before 2026-05-22) | Agent |
| Run §10.6 analysis (w_em + HRV + pharmacology) | Blocked by data | Agent |
| File §8.9 outcome (locked before reading data) | Blocked by §10.6 lock | Agent |

---

## Gate 2 — URB #828 v2 pre-registration LOCK ✅ COMPLETED 2026-05-01

| §10 item | Decision | State |
|---|---|---|
| 1. Three-axis formulation | APPROVED | ✅ |
| 2. Env-history orthogonality-to-DNA | APPROVED | ✅ |
| 3. N ≥ 6 minimum-stack | APPROVED | ✅ |
| 4. Condition-set | **Focused 4 (C0/C2/C5/C7)** | ✅ |
| 5. §6 ML discriminator | APPROVED | ✅ |
| 6. Thresholds | APPROVED (C5−C3 → C5−C2 due to focused-4) | ✅ |
| 7. Sequential vs parallel with §10.6 | **Sequential** (start 2026-05-22) | ✅ |
| 8. M=5 token-set | **Heterogeneous** (1 valence + 1 color + 1 symbol + 1 number + 1 letter); specific tokens **{calm, red, ★, 7, M} CONFIRMED 2026-05-01 PM** | ✅ |
| 9. No inter-trial feedback | CONFIRMED | ✅ |
| 10. Sample size | **N=30 × 4 conditions = 120 condition-points** (30 trial-days @ 1/day, ~30 days) | ✅ |

**Lock document:** `papers/URB_828_v2_PRE_REGISTRATION_LOCKED_2026-05-01.md`

---

## Gate 3 — staging work ✅ COMPLETED 2026-05-01

| Deliverable | State | File |
|---|---|---|
| Pre-registration template | Done | `papers/URB_828_v2_PRE_REGISTRATION_TEMPLATE.md` |
| Pre-registration LOCKED | Done | `papers/URB_828_v2_PRE_REGISTRATION_LOCKED_2026-05-01.md` |
| BPS capture protocol | Done | `papers/BPS_CAPTURE_PROTOCOL.md` |
| Physical hypotheses inventory | Done | `papers/PHYSICAL_HYPOTHESES_INVENTORY_2026-05-01.md` |
| Power-curve simulation | Done | `urb828_power_curve_simulation.py` |
| Classical-ML discriminator (C0) skeleton | Done | `urb828_c0_ml_discriminator_skeleton.py` |
| Unified Papers Browser tab | Done | `pages/papers_browser.py` |
| Pipeline tracker | Done (this file) | `PIPELINE.md` |
| Mendi status update | Done | `papers/MENDI_PATH_B_STATUS_2026-05-01.md` |

---

## Gate 4 — post-URB #828 verdict follow-on URBs (~2026-06-22+ if URB #828 succeeds)

| URB | Hypothesis | Cost | State |
|---|---|---|---|
| #829 | H_GEN — generalize to 2nd subject | $0 if cooperator | Sketched in `papers/PHYSICAL_HYPOTHESES_INVENTORY_2026-05-01.md` §2.3 |
| #830 | H_AA — axis ablation post-hoc | $0 | Sketched §2.4 |
| #831 | H_PM — pharmacology modulation post-hoc | $0 | Sketched §2.5 |
| #832 | H_TD — permanent BPS time decay | $0 | Sketched §2.7 |
| #833 | H_CR — circadian resonance post-hoc | $0 | Sketched §2.6 |
| #834 | H_HRV_PL — paired-subject phase-lock | $0 or $80 | Sketched §2.2 |
| #835 | H_BFG — biophoton field geometry | $150–400 (deferred) | Sketched §2.1 |

---

## Independent of all gates (runnable any time, $0)

| Item | State |
|---|---|
| URB #827 — Operational TI Sigma competence test (~3-4h) | Drafted, awaits Brandon green-light |
| Mendi BLE Path B Phase 1 (~5–10 min on Brandon's machine) | **Scaffold ready; awaits Brandon local execution.** See `papers/MENDI_PATH_B_STATUS_2026-05-01.md` |
| Biowell appointment booking | Brandon's task; reached out 2026-05-01 PM, awaiting confirmation |
| Replit checkpoint rollback (if needed) | Available via Replit UI |

---

## Held in pipeline (not actioned, but tracked)

| Item | State | Reason |
|---|---|---|
| Zenodo DOI for `papers/BPS_TERM_INTRODUCTION_2026-05-01.md` | **HELD** | Brandon directive 2026-05-01 PM; lock priority later |
| Zenodo DOI for URB #826 phase results | Held | Pending §10.6 verdict |
| Zenodo DOI for URB #827 results | Held | Pending run |
| Zenodo DOI for URB #828 v2 results | Held | Pending run completion (~2026-06-22) |
| Cite Popp et al. biophoton literature | Held | Pending H826 confirmation |
| Mendi Path B Phases 2–4 | Held | Blocked on Phase 1 (Brandon local) |

---

## Recurring autonomous tasks (cloud)

| Workflow | State |
|---|---|
| `discovery_scheduler` | Running |
| `gsa_daily_scheduler` | Running |
| `hypercomputer` (Streamlit :8000) | Running |
| `ti_website` (async_gateway → Streamlit :5002) | Running |

---

## All physical hypotheses snapshot

**Existing (6):** URB #826 (EM-DNA carrier), URB #828 v2 (BPS-stacking), LCC-Telepathy, GCP-correlation, Tralse-Joules conservation, GILE-HEM PD modulation.

**Candidate (9):** H_BFG, H_HRV_PL, H_GEN, H_AA, H_PM, H_CR, H_TD, H_DA, H_PRE.

**Falsification gates scheduled:**
- 2026-05-22: URB #826 §10.6 (w_em < 0.10 ∧ HRV > 0.85 falsifies)
- ~2026-06-22: URB #828 v2 (C5 < 30% OR C0 > 35% falsifies)

Full descriptions: `papers/PHYSICAL_HYPOTHESES_INVENTORY_2026-05-01.md`.

---

## Honest residuals on the pipeline itself

1. **No physical hypothesis has been empirically confirmed.** Architectural verifications confirm structure only.
2. **The §10.6 H10 window and the §6 ML discriminator are the only two scheduled falsification gates.** If either gets dropped or watered down, the pipeline degenerates into architectural-stacking without empirical content.
3. **`replit.md` reverts on every merge** — full restoration ritual needed each time. Anchor: "URB #826 — Biophoton/EM-DNA Carrier Hypothesis" + "### System Design Choices".
4. **Brandon-as-target-and-runner** introduces single-blind risk. M=5 exact-match scoring partially mitigates.
5. **Mendi BLE Path B success estimate remains 45%.** Honest framing: it may fail at Phase 1 if the device uses encrypted-only characteristics.

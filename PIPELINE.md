# Pipeline Tracker — Mood Amplifier Safety & Validation Platform

**Last updated:** 2026-05-05 PM
**Owner:** Brandon Charles Emerick
**Standard:** asymmetric-standards #69, $0 budget unless noted.

---

## Active critical path (Brandon's daily protocol, 2026-05-01 → ~2026-05-22)

| Item | State | Notes |
|---|---|---|
| Polar H10 daily wear (Polar Beat untethered) | Active; **first export received 2026-05-04** (5 sessions, 54,639 1-sec HR samples = 15.2h); **next export expected tonight 2026-05-05** | data → `data/polar_h10/` |
| Daily subjective log (`log_daily_subjective.py`) | Active; **2026-05-05 entry logged** | 30s/day; mood/energy/focus/event |
| Daily medication log | Active; **2026-05-05 change-events + full snapshot logged** | `data/medication_log.csv` + `data/medication_snapshots/2026-05-05.md` |
| Oura nightly summary | Autonomous | `oura_full_metrics_harvester.py` |
| Adderall titration (Day 1 = 2026-05-01) | **Day 5 today; Brandon DISSATISFIED — Focalin XR request planned at 5/06 doctor appt** | If transition approved, regimen change mid-§10.6 window; covariate model needs Adderall-Day-N + Focalin-XR-Day-N sub-windows |
| Glycine 3g | **DISCONTINUED 2026-05-05 (last day)** | Regimen change event flagged |
| **Autism therapy work resumes** | **Wed 2026-05-06 — brand new client** | Caregiver-mode life-path-6 expression; track sleep/HRV the night before |
| **Doctor appointment** | **Wed 2026-05-06 — Focalin XR request** | If approved → Adderall→Focalin XR transition; flag in URB #826/828 covariate model |

---

## Brandon's open tasks (none are blockers; ordered by ease)

1. ✅ **Mendi Phase 1 GATT discovery DONE 2026-05-04** — 5 services, 16 characteristics found. JSON at `Downloads\data\mendi\ble_discovery\gatt_2026-05-04T13-53-03.json` on Brandon's Acer. **UPLOAD TO REPLIT PENDING** — drag JSON into `data/mendi/ble_discovery/` in the Replit file panel. **Brandon plans 10-min Mendi meditation session once reconnected — value-add: if BLE traffic capture runs alongside the session (nRF Connect Logger), produces Phase 3 protocol-replay evidence; otherwise just personal-benefit + device-comfort.**
2. ☐ **Biowell appointment** — Brandon reached out 2026-05-01 PM; **scan pushed to next week (2026-05-12+)**.
3. ✅ **URB #828 v2 M=5 token-set CONFIRMED 2026-05-01 PM**: {calm, red, ★, 7, M}.
4. ☐ **Print sealed deck of 5 cards** for URB #828 trials — one card per token in the M=5 set: `calm` / `red` / `★` / `7` / `M`. Large clear print, opaque card backs. **Brandon has no home printer — library trip required. Not urgent (deadline 2026-05-22).**
5. ☐ **Fingerprint capture** (~10 min) for URB #828 C7 condition — **Brandon plans tonight 2026-05-05.** See `papers/FINGERPRINT_CAPTURE_INSTRUCTIONS.md`.
6. ☐ **Visual confirmation that `pages/papers_browser.py` renders** — restart `ti_website` workflow, navigate to "papers_browser" in the Streamlit sidebar.
7. ☐ **Daily H10 + subjective + medication logging** through 2026-05-22 (continues active critical path). **2026-05-05 logged.**
8. ☐ **Polar H10 baseline analysis** — agent-side; **deferred to tonight after Brandon uploads latest H10 export.**
9. ☐ **Doctor appointment 2026-05-06: Focalin XR request.** If approved, regimen-change event; agent must add Focalin-XR-Day-N sub-window to §10.6 covariate model.
10. ☐ **More biographical refinements (URB #829 §2 supporting evidence) incoming from Brandon shortly.** Add as supporting-evidence accrual; do not gate Gate 5 on rate-of-refinement.

---

## Gate 5 — URB #829 Dominant GM-Node Transmission (filed 2026-05-04)

| Review date | Type | Status |
|---|---|---|
| 2026-05-15 | Adderall titration Day 14 — has conviction-density changed? | Pending |
| 2026-06-04 | 30-day check; C1-C7 status | Pending |
| 2026-08-04 | 90-day check; revise C1-C7 | Pending |
| **2027-05-04** | **365-day major decision point — apply §3 decision rule** | **Locked** |
| 2030-05-04 | 5-year final FALSIFIED-branch check | Locked |

Tracked in: `papers/URB_829_DOMINANT_GM_NODE_TRANSMISSION_2026-05-04.md`. Per asymmetric-standards #69, framework subjects its own founder to same falsification standard as any other claim.

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
| TI Sigma Atlas + Index/Acronyms tabs | Done | `pages/papers_browser.py` (tabs 4 & 5) |
| Pipeline tracker | Done (this file) | `PIPELINE.md` |
| Mendi status update | Done | `papers/MENDI_PATH_B_STATUS_2026-05-01.md` |
| Fingerprint capture instructions | Done | `papers/FINGERPRINT_CAPTURE_INSTRUCTIONS.md` |
| TI Sigma Systematic Review — Empirical Science | Done (living doc) | `papers/TI_SIGMA_REVIEW_EMPIRICAL_SCIENCE.md` |
| TI Sigma Systematic Review — Theoretical Science | Done (living doc) | `papers/TI_SIGMA_REVIEW_THEORETICAL_SCIENCE.md` |
| TI Sigma Systematic Review — Philosophy | Done (living doc) | `papers/TI_SIGMA_REVIEW_PHILOSOPHY.md` |
| TI Sigma Systematic Review — Business & Engineering | Done (living doc) | `papers/TI_SIGMA_REVIEW_BUSINESS_ENGINEERING.md` |
| TI Sigma Systematic Review — Mathematics | Done (living doc) | `papers/TI_SIGMA_REVIEW_MATHEMATICS.md` |

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
| Mendi BLE Path B Phase 1 GATT discovery | ✅ **DONE 2026-05-04.** 5 services, 16 characteristics. JSON on Brandon's Acer; **upload to Replit pending.** |
| Mendi BLE Path B Phase 2 (protocol analysis) | Blocked on JSON upload. Agent-side ~2-4h once JSON arrives. |
| Upload Polar H10 data from Polar Flow | ✅ **First export received 2026-05-04.** 7 sessions (5 May 2026), 54,639 HR samples. |
| Upload Muse session data from Muse app | **No data in Replit yet.** Brandon wearing device; data in Muse app. Export needed. |
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
| Mendi Path B Phases 2–4 | Phase 1 DONE; Phase 2 blocked on JSON upload to Replit | Agent can start protocol analysis once JSON arrives |

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

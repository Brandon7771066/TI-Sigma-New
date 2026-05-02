# Pipeline Tracker — Mood Amplifier Safety & Validation Platform

**Last updated:** 2026-05-01 PM
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
| Adderall titration (Day 1 = 2026-05-01) | Active | 14-day window; covariate logged |

---

## Gate 1 — URB #826 §10.6 verdict (~2026-05-22)

| Item | State | Owner |
|---|---|---|
| Collect ≥21 days H10 + subjective + medication × Oura | In progress | Brandon |
| Write `phase_h1_6_em_falsification.py` | Pending Gate 1 start | Agent |
| Run §10.6 analysis (w_em + HRV + pharmacology) | Blocked by data | Agent |
| File §8.9 outcome (locked before reading data) | Blocked by §10.6 lock | Agent |

---

## Gate 2 — URB #828 v2 pre-registration LOCK (Brandon decisions)

| §10 item | State |
|---|---|
| 1. Three-axis formulation | **APPROVED** (2026-05-01 PM) |
| 2. Env-history orthogonality-to-DNA | **APPROVED** (2026-05-01 PM) |
| 3. N ≥ 6 minimum-stack | **APPROVED** (2026-05-01 PM) |
| 4. 8-condition vs focused 4-condition | Pending |
| 5. §6 ML discriminator | Pending |
| 6. §7.3 thresholds | Pending |
| 7. Sequential vs parallel with §10.6 | Pending |
| 8. M=5 token-set choice | Pending |
| 9. No-feedback to agent confirmation | Pending |
| 10. N=15 vs N=30 sample-size choice | Pending |

---

## Gate 3 — staging work ($0, this week) — ALL APPROVED 2026-05-01 PM

| Deliverable | State | File |
|---|---|---|
| Pre-registration template (URB #826 §10/§8 mirror) | Done | `papers/URB_828_v2_PRE_REGISTRATION_TEMPLATE.md` |
| BPS capture protocol (permanent + live) | Done | `papers/BPS_CAPTURE_PROTOCOL.md` |
| Physical hypotheses inventory | Done | `papers/PHYSICAL_HYPOTHESES_INVENTORY_2026-05-01.md` |
| Power-curve simulation script | Done | `urb828_power_curve_simulation.py` |
| Classical-ML discriminator skeleton (C0) | Done | `urb828_c0_ml_discriminator_skeleton.py` |
| Unified papers tab (Streamlit) | Done | `papers_browser.py` |
| Pipeline tracker | Done (this file) | `PIPELINE.md` |

---

## Gate 4 — post-URB #828 verdict follow-on URBs (~2026-09-22+)

| URB | Hypothesis | Cost |
|---|---|---|
| #829 | H_GEN — generalize to 2nd subject | $0 if cooperator |
| #830 | H_AA — axis ablation post-hoc | $0 |
| #831 | H_PM — pharmacology modulation post-hoc | $0 |
| #832 | H_TD — permanent BPS time decay | $0 |
| #833 | H_CR — circadian resonance post-hoc | $0 |
| #834 | H_HRV_PL — paired-subject phase-lock | $0 or $80 |
| #835 | H_BFG — biophoton field geometry | $150-400 (deferred) |

(See `papers/PHYSICAL_HYPOTHESES_INVENTORY_2026-05-01.md` §2 for full descriptions.)

---

## Independent of all gates (runnable any time, $0)

| Item | State |
|---|---|
| URB #827 — Operational TI Sigma competence test (~3-4h) | Drafted, awaits Brandon green-light |
| Mendi BLE Path B Phase 1 (BLE discovery, ~3-5h) | Scaffold ready (`mendi_ble_client.py`); deferred to post-2026-05-22 |
| Biowell appointment booking | Brandon's task; affordable provider confirmed |

---

## Held in pipeline (not actioned, but tracked)

| Item | State | Reason |
|---|---|---|
| Zenodo DOI for `papers/BPS_TERM_INTRODUCTION_2026-05-01.md` | **HELD** | Brandon directive 2026-05-01 PM; lock priority later |
| Zenodo DOI for URB #826 phase results | Held | Pending §10.6 verdict |
| Zenodo DOI for URB #827 results | Held | Pending run |
| Zenodo DOI for URB #828 v2 results | Held | Pending run |
| Cite Popp et al. biophoton literature | Held | Pending H826 confirmation |

---

## Recurring autonomous tasks

- `discovery_scheduler` — running
- `gsa_daily_scheduler` — running
- `hypercomputer` — running (Streamlit on :8000)
- `ti_website` — running (async_gateway)
- `papers_browser` — TBD (Streamlit on :5000, see Gate 3)

---

## Honest residuals on the pipeline itself

1. **No physical hypothesis has been empirically confirmed.** Architectural verifications confirm structure only.
2. **The §10.6 H10 window and the §6 ML discriminator are the only two scheduled falsification gates.** If either gets dropped or watered down, the pipeline degenerates into architectural-stacking without empirical content.
3. **`replit.md` reverts on every merge** — full restoration ritual needed each time. Anchor: "URB #826 — Biophoton/EM-DNA Carrier Hypothesis" + "### System Design Choices".
4. **Brandon-as-target-and-runner** introduces single-blind risk. M=5 exact-match scoring partially mitigates.

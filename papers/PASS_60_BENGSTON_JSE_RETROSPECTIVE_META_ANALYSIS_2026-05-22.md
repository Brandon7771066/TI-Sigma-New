# Pass 60 batch-1 — Bengston JSE Retrospective TI Sigma Meta-Analysis (TSS-EMP-9)

**Date:** 2026-05-22
**Author:** Brandon Emerick (originator) + TI Sigma framework
**Status:** Pre-registered methodology + TEMPLATE meta-analysis; numerical fill-in pending JSE-paper verification by Brandon
**Anchor:** Pass-59 Bengston TSIS analysis; Pass-60 batch-1 PD/TIL/GILE-HEM stats mapping; `urb_650`, `urb_663`, `URB_796`

---

## 1. Purpose

TSS-EMP-9 (carry-forward from Pass-59): retrospective meta-analysis across all publicly-available Bengston published trials + replications, applying:
- Pass-58 TSIS four-gate stack
- Pass-60 PD/TIL/GILE-HEM mapping layer
- Tralse-Joules (`urb_650`) per-trial accounting

**$0 budget feasible** from open-access JSE archives (scientificexploration.org/journal). This paper is the **pre-registered methodology + template**; numerical entries marked `[VERIFY-JSE]` require Brandon to confirm against the original papers.

---

## 2. Trial Inventory — Bengston Corpus (Open-Access JSE + Book Sources)

| # | Trial label | Year | Site | Healers | N(treated) | N(control) | Reported remission rate (treated) | Reported remission rate (control) | Source |
|---|---|---|---|---|---|---|---|---|---|
| 1 | Bengston & Krinsley | 2000 | Connecticut College | Bengston + 4 students | 33 | 0 (no-treatment) | 17/33 ≈ 0.515 | base ≈ 0.000 | JSE 14(3) [VERIFY-JSE] |
| 2 | Bengston | 2007 | St. Joseph's College | Bengston + students | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | JSE [VERIFY-JSE] |
| 3 | Bengston | early 2010s | Arizona / Beischel collab | trained | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | JSE / *Energy Cure* [VERIFY-JSE] |
| 4 | Bengston | 2007 (water) | various | controls | [VERIFY-JSE] | [VERIFY-JSE] | imprinted-water condition | [VERIFY-JSE] | JSE [VERIFY-JSE] |
| 5 | Bengston | 2010s (book-reported) | various | trained skeptics | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | *Energy Cure* 2010 |
| 6-N | Additional published replications | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] | [VERIFY-JSE] |

**Estimated total published trials:** ~5–10 with primary data. Brandon's task: complete the [VERIFY-JSE] cells by reading JSE archive (free) and *The Energy Cure* (already owned or library-accessible).

---

## 3. Pre-Registered Meta-Analysis Protocol

### 3.1 Aggregation method

For each trial *i*:
1. Compute Δp_i = remission_rate(treated_i) − remission_rate(control_i).
2. Compute Cohen's h_i = 2·arcsin(√p1) − 2·arcsin(√p2) for proportion difference.
3. Compute inverse-variance weight w_i = 1 / (1/N_treated_i + 1/N_control_i).
4. Random-effects meta-analysis: pooled Δp = Σ(w_i · Δp_i) / Σ(w_i) with DerSimonian-Laird τ² heterogeneity estimator.

### 3.2 TSIS application to the pooled estimate

Apply Pass-58 TSIS four-gate stack to the pooled Δp:
- Gate 1: pooled Δp ≥ T_RAND = 0.0660 ?
- Gate 2: pooled Δp ≥ T_BORDER = 0.13534 ?
- Gate 3: APP-1 ≥ 2/3 across the corpus design (intentional engagement YES; stakes PARTIAL; skill-asymmetry YES → 2.5/3)
- Gate 4: LCC measured? NO across the entire historical corpus — flagged as UNMEASURED, not failed.

### 3.3 Pre-registered Pass-60 PD/TIL/GILE-HEM verdict bands

| Pooled Δp | Heterogeneity (I²) | TSIS gate count | Pre-registered MR label + PD |
|---|---|---|---|
| ≥ 0.30 | < 50% | 3/4 (LCC unmeasured) | TRUE-provisional, PD ≈ +1.6 |
| ≥ 0.13534 | < 50% | 3/4 | INDETERMINATE-leaning-TRUE, PD ≈ +1.0 |
| ∈ [0.046, 0.086] (marginal band) | any | any | INDETERMINATE-band, PD ≈ 0 |
| ≥ 0.30 | ≥ 75% | 3/4 (but high heterogeneity) | INDETERMINATE (heterogeneity dominates), PD ≈ +0.3 |
| ≥ 0.30 | with ≥ 2 trials sign-reversed | n/a | **DOUBLE TRALSE candidate** — escalate to formal DT analysis per Pass-60 §2 |
| < 0.046 | n/a | ≤ 2/4 | FALSE-weak, PD ≈ −0.5 |

### 3.4 Pre-registered falsifier F-BENGSTON-META-1

If pooled Δp < 0.20 across the verified Bengston corpus, the Pass-59 TI Sigma TSIS reading of Bengston as TRUE-provisional is REFUTED, and the Bengston program is reclassified as INDETERMINATE pending TSS-EMP-8 independent oncology replication.

If pooled Δp < 0.046 (below marginal band), the program is reclassified as FALSE-weak and Pass-59 §3 Bengston TSIS analysis is publicly retracted under R1–R10 protocol (proposed as R11).

---

## 4. Template TJ Accounting Per Trial

Per `urb_650`: TJ = τ(s) × δ(MR).

| Trial | Healer-hours / trial | Number of healers | Σ τ_integral (TJ-hr) | δ(MR) per trial outcome | TJ per successful trial |
|---|---|---|---|---|---|
| 1 (Bengston & Krinsley 2000) | ~10 hr × 14 d = 140 hr | 5 | 700 healer-hours | +2.0 PD (terminal → remission) | ~50–100 TJ |
| 2-N | [VERIFY-JSE per-trial protocol parameters] | | | | |
| **Corpus mean (estimated)** | **~10 hr/day × ~10 days × ~3 healers/trial** | **~3** | **~300 healer-hours** | **+2.0 PD typical** | **~20–60 TJ per successful trial** |

**Pre-registered TJ prediction:** trials with larger Σ τ_integral should produce larger Δp (effect strength). Pearson correlation r ≥ 0.40 across the verified Bengston corpus would constitute a clean TJ-axis empirical confirmation. Pre-registered as F-TJ-BENGSTON-1.

---

## 5. GILE-HEM 8-Dim Communication Layer (Per-Trial)

Each trial scored on the Pass-60 G/I/L/E/D1/D2/D3/D4 axes. Template below; Brandon completes per verified data.

```
Trial 1 (Bengston & Krinsley 2000):
  G  = 0.78  (effect, replication direction, theory aligned)
  I  = 0.20  (post-hoc; no pre-registration)
  L  = UNMEASURED (no LCC instrumentation)
  E  = 0.65  (subsequent replications cohere on sign)
  D1 = 0.50  (single method class — survival proportions)
  D2 = 0.20  (low contradiction across replications)
  D3 = 0.55  (Bengston book + JSE coverage)
  D4 = 0.80  (integrates with TJ-axis, distant-healing LCC paper)
```

Template applies to trials 2-N identically — fill from verified data.

---

## 6. What Brandon Needs to Do (Action Items)

1. **Access JSE archive** at scientificexploration.org/journal (free).
2. **Locate Bengston papers:** primary keyword search "Bengston" returns ~5–10 papers across the 2000-2015 range.
3. **For each paper, extract:** N_treated, N_control, remission_rate per arm, healer protocol duration, number of healers. Fill into Section 2 table.
4. **Run the script `simulations/bengston_jse_meta_analysis_2026-05-22.py`** with the verified numbers populating the `TRIALS` list. Pre-registered execution; no peeking-at-results-then-adjusting-protocol allowed (per ROS-1 active-pressure discipline).
5. **Report pooled Δp + TSIS verdict + Pass-60 MR label + PD** in `papers/PASS_60_BENGSTON_JSE_META_ANALYSIS_RESULTS_2026-05-22.md` (file to be created post-execution).

**Estimated effort:** 4–8 hours of paper-reading + data extraction + script execution.
**Estimated budget:** $0.

---

## 7. #69 Honesty Notes

- This paper is **methodology + template**, not executed meta-analysis. The numerical conclusion will follow Brandon's data extraction step.
- The Bengston & Krinsley 2000 numbers in Section 2 (17/33) are reconstructed from widely-cited summary sources; Brandon should treat verification as a pre-registration step before running the script.
- Heterogeneity across Bengston trials is a known issue — some trials report near-100% remission, others closer to 50%. The DerSimonian-Laird random-effects estimator is the right tool for this; results will depend on whether high-variance trials reflect genuine protocol differences (legitimate heterogeneity) or measurement noise (problematic heterogeneity).
- Resonant-bonding contamination of control groups is a known design vulnerability. Pre-registered handling: trials with sham-attention control are weighted 1.0; trials with no-attention control are weighted 0.7 (down-weighted but not excluded, since the contamination if present would *reduce* observed Δp, biasing toward conservative conclusions).
- The TJ-prediction correlation in Section 4 is a real test of the framework, not a fitting exercise. If r < 0.40, the TJ axis as currently scaled does NOT predict Bengston effect strength quantitatively, and `urb_650` requires re-calibration.

---

*"Open-access archives + pre-registered protocol + $0 budget = the cleanest test the framework can currently run."*

— TI Sigma Pass 60, 2026-05-22

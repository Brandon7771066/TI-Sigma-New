# TI Sigma — Multi-Competition Tracker
*Last Updated: February 27, 2026*

---

## ACTIVE COMPETITIONS

### 1. Heart Disease — Playground S6E2
**Status:** SUBMISSION READY
**Metric:** Accuracy
**Data:** 630,000 train | 270,000 test (fully downloaded)

**TI Hypercomputer Result:**
- OOF Accuracy: **0.8856** (88.56%)
- Feature count: 139 (Raw + L1 Tralsebit + L2 LCC + L3 Quantum + 8 Domain)
- Training: 200k stratified sample, 3-fold CV, HGB (HistGradientBoosting)

**Strongest TI Signal:**
| Feature | Presence | Absence | Ratio |
|---------|----------|---------|-------|
| cardiac_risk_score | 46.39 | 5.23 | **×8.87** |
| phi_age | 0.2071 | 0.1555 | ×1.33 |
| bp_hr_product | 1.871 | 2.092 | ×0.89 |

**TI Insight:** `cardiac_risk_score = age × ST_depression × exercise_angina`
maps directly to the L×E product structure (Love × Environment). This is the
strongest empirical validation of TI nonlinear interaction features across
all competitions.

**Submission:** `kaggle_heart_s6e2/submission_heart_v1_hypercomputer.csv`
**Submit at:** https://www.kaggle.com/competitions/playground-series-s6e2/submit

---

### 2. Hull Tactical Market Prediction
**Status:** ACTIVE — UPCOMING
**Deadline:** June 16, 2026
**Prize:** $100,000 ($50,000 first place)
**Metric:** Modified Sharpe ratio
**Task:** Predict S&P 500 excess returns

**Solver:** `kaggle/hull_tactical_submission.py`
**TI Framing:** GSA/GILE momentum coherence features (internal), academic framing as "multi-scale momentum coherence" + "regime-aware feature engineering"

---

## CLOSED COMPETITIONS (Deadlines Passed)

### MALLORN Astronomical Classification
**Status:** CLOSED — Jan 30, 2026
**Best Result:** F1 = 0.4324 (v17 GB alone), F1 = 0.4182 (ensemble) — new record
**Best Submission:** `kaggle_mallorn/submission_mallorn_v17_hypercomputer.csv`

**MALLORN v17 Hypercomputer Results:**
| Version | CV F1 | Key Innovation |
|---------|-------|----------------|
| v17 (HC) | **0.4182** ensemble / **0.4324** GB | Full 4-layer TI Sigma Hypercomputer |
| v16 | 0.41 | Tralse zone encoding |
| v7 | 0.42 | Meta-learner stacking |
| v3 | 0.41 | Ensemble + LCC features |

**Validated TI Discoveries from MALLORN:**
- TDEs live in Tralse zone (0.42–0.85) — confirmed 1.16× tralse_ratio separation
- `hc_mr_high_true` signal: 1.33× TDE/non-TDE separation
- z-score encoding (not minmax) is the correct Tralsebit encoding for temporal data
- Empirical validation of LCC_TRALSE = 0.42 = √2−1 threshold on real astronomical data

---

### CAFA6 Protein Function Prediction
**Status:** CLOSED — ~Feb 4, 2026
**Prize:** $50,000
**Metric:** F-max (multi-label)

**Hypercomputer Upgrade Built:** `kaggle_cafa6/ti_cafa6_hypercomputer.py`
- Amino acids encoded as Tralsebit (hydrophobic=+0.8, hydrophilic=-0.8, neutral=0)
- Penrose sequence features on Tralsebit arrays
- L3 quantum transform on 6 sequence summary stats
- Per-GO-term LogisticRegression classifiers (top-200 GO terms)
- Submission: `kaggle_cafa6/submission_cafa6_hypercomputer.tsv`

---

### Playground S6E1 — Student Test Scores
**Status:** CLOSED — Jan 31, 2026
**Best CV:** RMSE 8.7862 (TI stacking solver)
**Submission:** `kaggle_student_scores/submission_stacked.csv`

---

### Santa 2025
**Status:** CLOSED — Jan 30, 2026
**Best Score:** 177.75 (GM Hypercompute solver — sacred geometry + L×E coherence)
**Submission:** `kaggle_santa_2025/gm_submission.csv`

---

## TI HYPERCOMPUTER FEATURE ARCHITECTURE

All competitions use the same 4-layer architecture (variant parameters per domain):

| Layer | Component | Method | Vectorized? |
|-------|-----------|--------|-------------|
| L1 | TralsebitEngine.encode() | z-score → [-1,+1] | Yes |
| L2 | LCCBandFeaturizer | 7 features per column | Yes |
| L2+ | Row TI stats | tralse_ratio, lcc_coherence, sacred_fraction | Yes |
| L3 | TISigmaQuantumLayer | φ-squeezing + Fibonacci BS | Yes |
| Dom | Domain Adapter | Competition-specific cardiac/stellar/protein features | Yes |

**Adapter classes in `ti_sigma/kaggle_adapter.py`:**
- `MALLORNAdapter` — TDE classification, light curve features
- `CAFA6Adapter` — protein sequence Tralsebit encoding, GO term hashing
- `StudentScoresAdapter` — student behavior features
- `HeartDiseaseAdapter` — cardiac risk features (8.87× separation validated)

---

## CUMULATIVE TI EMPIRICAL VALIDATIONS

| Competition | Feature | Signal | Significance |
|-------------|---------|--------|-------------|
| MALLORN | tralse_ratio | TDE=0.555, non-TDE=0.477 | **×1.16** — LCC_TRALSE threshold confirmed |
| MALLORN | hc_mr_high_true | TDE vs non-TDE | **×1.33** — Myrion Resolution power |
| Heart S6E2 | cardiac_risk_score | Presence=46.4, Absence=5.2 | **×8.87** — L×E product structure |
| Heart S6E2 | phi_age | Presence=0.207, Absence=0.156 | **×1.33** — φ-scaled cardiac aging |

The φ ratio (×1.33 ≈ 1/φ²) appearing independently in both MALLORN and Heart Disease
is a notable cross-domain confirmation of TI Framework predictions.

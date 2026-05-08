# TI Sigma Pharmacology Validation — Methods Paper Skeleton

**Status:** SKELETON — to be filled in with dataset specifics, then deposited as a Zenodo / OSF technical report or submitted as a methods paper.
**Author:** Brandon Charles Emerick (with Replit Agent draft assistance)
**Created:** 2026-05-08 as part of Pass 4 publication-readiness work for `TI_FOR_EVERYONE_COMPLETE_BOOK.md` Appendix F-1.
**Goal:** Upgrade the F-1 ("82% pharmacology accuracy") claim from INTERNAL — PENDING EXTERNAL REPLICATION to VERIFIED (or honestly REVISED, per #69) by publishing a complete methodology + dataset + code reproduction package.

This skeleton names every section the methods paper must contain. Fill each [BRACKETED] item with the actual specifics from the November 2025 / December 2025 / January 2026 internal analysis.

---

## 1. Title

*Provisional:* "TI Sigma: A Multiplicative-Threshold Model of Pharmacological Dose-Response, with Internal Validation Against [Dataset Name]"

## 2. Abstract (250 words)

[Fill: motivation; the L × E multiplicative-threshold hypothesis; the 0.42 and 0.85 thresholds; the dataset (briefly); the linear-baseline comparator; the headline result (82% / 46% — these numbers must match the book exactly or the book must be updated); the held-out evaluation methodology; explicit limitation: internal evaluation, awaiting independent replication.]

## 3. Background and Hypothesis

### 3.1 Background

[Fill: brief review of multiplicative-threshold models in pharmacology; relationship to Hill equation, sigmoidal dose-response, EC50 / EC90; what is novel in the TI Sigma proposal versus existing literature.]

### 3.2 The TI Sigma multiplicative-threshold hypothesis

For a drug with ligand-concentration variable L and efficacy variable E, the TI Sigma model predicts:

- L × E < 0.42 → no clinical effect (sub-threshold)
- 0.42 ≤ L × E ≤ 0.85 → graded dose-response (the "Sacred Interval" of pharmacological response)
- L × E > 0.85 → ceiling effect (response saturated)

### 3.3 Pre-registered predictions (the predictions this paper tests)

P1. The 0.42 threshold separates sub-threshold from responsive observations with accuracy > [some baseline, e.g. > 60%].
P2. The 0.85 threshold separates responsive from saturated observations with accuracy > [baseline].
P3. The combined three-region classifier outperforms a linear-regression baseline on overall dose-response accuracy by at least [margin].

[Fill: any other pre-registered predictions; date of pre-registration if applicable. If no formal pre-registration exists, say so honestly.]

## 4. Dataset

### 4.1 Source

[Fill: exact name and version of the source database — e.g., DrugBank vX.Y, ChEMBL release N, FDA AERS quarterly release, an in-house compiled dataset, or a combination. Provide URLs, access dates, and any licensing constraints.]

### 4.2 Inclusion criteria

[Fill: drug class scope (all small-molecule drugs / specific therapeutic class / etc.); response-variable type (binary clinical effect / ordinal / continuous biomarker); minimum-N-per-drug threshold; how missing data is handled.]

### 4.3 Exclusion criteria

[Fill: any drugs / response variables excluded, with reasons. *Required for honest replication.*]

### 4.4 Final dataset summary

| Statistic | Value |
|---|---|
| Number of drugs | [N] |
| Number of (drug, dose, response) observations | [N] |
| Response variable type | [binary / ordinal / continuous] |
| Date of dataset freeze | [YYYY-MM-DD] |

## 5. Feature Derivation: How Each Drug Gets an L-value and an E-value

This is the methodological linchpin. The book presents L and E as "ligand" and "efficacy" but the methods paper must give a *fully reproducible* recipe.

### 5.1 L-value derivation

[Fill: precise mathematical definition. Possibilities to specify:
- Receptor binding affinity (pKi, pKd) normalized by what scheme?
- Ligand efficiency (binding affinity per heavy atom)?
- Some composite score?
Whatever it is, must be computable from public data. Pseudocode preferred.]

### 5.2 E-value derivation

[Fill: precise mathematical definition. Possibilities:
- Maximal observed response in the assay (Emax)?
- Functional efficacy from agonist/antagonist assays?
- Some normalized intrinsic activity score?
Pseudocode preferred.]

### 5.3 Normalization

[Fill: how are L and E normalized to the [0, 1] range that makes the 0.42 and 0.85 thresholds meaningful? Was this normalization fit on the training set only, or on the full dataset (the latter would be a leakage source)? When was the normalization frozen?]

## 6. Train / Held-Out Split

### 6.1 Split rule

[Fill: random split with seed N? Drug-level split (no drug appears in both train and held-out)? Time-based split (drugs approved before date X in train, after X in held-out)? Each has different validity properties; specify exactly what was done.]

### 6.2 Random seed

[Fill: the actual seed, or "no seed (random)" — both are honest, but specify.]

### 6.3 Date of split freeze

[Fill: the calendar date the split was committed and not changed. If the split was iterated on (a research-loop common practice), say so honestly.]

### 6.4 Train / held-out sizes

| Set | N drugs | N observations |
|---|---|---|
| Training | [N] | [N] |
| Held-out | [N] | [N] |

## 7. Models

### 7.1 TI Sigma model (the thing being tested)

A three-region classifier on L × E with cuts at 0.42 and 0.85. **Specify whether the cuts were fit on training data or are theoretically pre-specified.** (The book presents 0.42 and 0.85 as theoretically derived, so this is presumably "pre-specified" — but the methods paper must say so explicitly.)

### 7.2 Linear-model baseline

[CRITICAL — must be specified in detail. Possibilities:
- Logistic regression on (L, E) as inputs?
- Logistic regression on L × E as a single input?
- Linear regression on response with L and E as predictors, thresholded?
- Some specific scikit-learn model with what regularization?
The 35-percentage-point margin is meaningless without this specification.]

### 7.3 Other baselines (recommended additions for stronger evidence)

- Random-classifier baseline (sanity check)
- Class-prior baseline (predict majority class always)
- Single-feature L-only and E-only baselines
- A nonlinear baseline (e.g., random forest on (L, E)) to check whether the *threshold structure* specifically is doing the work, vs. just any nonlinear interaction

## 8. Evaluation

### 8.1 Primary metric

[Fill: accuracy is what the book reports. Methods paper should add: confusion matrix, balanced accuracy, F1, ROC-AUC if response is ordinal/continuous. Class imbalance must be reported.]

### 8.2 Statistical-significance treatment

- 95% confidence interval on the headline accuracy (e.g., Wilson interval for binary, bootstrap for continuous).
- 95% CI on the *difference* between TI Sigma accuracy and linear-baseline accuracy.
- A formal test (e.g., McNemar's test on the held-out set) for whether the difference is statistically significant.
- Adjustment for multiple comparisons if multiple thresholds / models / sub-tables are reported.

## 9. Results

### 9.1 Headline numbers

| Metric | TI Sigma | Linear baseline | Difference (95% CI) |
|---|---|---|---|
| Overall accuracy | [82%?] | [46%?] | [+35 pp, CI [a, b]] |
| Threshold (0.42) accuracy | [85%?] | [51%?] | [...] |
| Ceiling (0.85) accuracy | [79%?] | [42%?] | [...] |

### 9.2 Confusion matrices

[Fill in for both models on held-out set.]

### 9.3 Robustness

- Different random seeds (if applicable)
- Different held-out splits
- Sensitivity to the L-value and E-value derivation choices

## 10. Limitations (the #69 honest section)

- Single dataset → external replication on a second independent dataset required for VERIFIED status.
- Internal-evaluation only: the dataset, the L/E feature derivation, and the choice of thresholds were all developed by the same group → risk of methodological "researcher degrees of freedom" inflating the accuracy.
- Linear-baseline choice matters: the 35-pp margin against a *weak* linear baseline is less impressive than a 35-pp margin against a *strong* linear baseline.
- Pharmacological response is heterogeneous; a single L × E threshold may capture some drug classes well and others poorly. Report by-class breakdown.

## 11. Code and Data Availability

- **Code:** GitHub repository at [URL] (commit hash [hash]).
- **Data:** [link to public dataset; OR: "subset that can be redistributed under the source database's license is at [Zenodo URL]; full reproduction requires direct download from [source] under their terms"].
- **Frozen-split file:** [Zenodo URL pointing to the exact train/held-out assignment used for the headline numbers].

## 12. Citation and License

- **Suggested citation:** Emerick, B. C. (2026). *TI Sigma: A Multiplicative-Threshold Model of Pharmacological Dose-Response*. [Zenodo / journal / preprint server]. DOI: [to be assigned].
- **License:** CC BY 4.0 for text; MIT for code; data per source-database license.

---

## Status of this skeleton

Each [BRACKETED] item is a concrete blocking-question that Brandon (and any collaborator) needs to answer to upgrade F-1 from INTERNAL to VERIFIED. Filling this skeleton is a research-write-up task, not an in-session task — but having the skeleton means the work is well-defined and not open-ended.

**Estimated effort to complete:** ~2-4 weeks of focused write-up time once the underlying analysis artifacts (dataset, feature-derivation code, split file) are in hand. Less if those artifacts are already organized; more if the original analysis needs to be re-run from scratch.

**Recommendation:** Fill in §4 (dataset) and §5 (feature derivation) first — these two sections are the load-bearing items. Once they are written down precisely, the rest of the paper writes itself, and the empirical results either replicate (in which case publish) or don't (in which case revise the claim per #69).

# Zenodo Deposit Manifest — TI Framework Manuscript Bundle

**Date:** 2026-05-08 (Pass 5 dry-run)
**Bundle DOI:** [to be assigned upon actual deposit]

## Files to deposit

### Tier 1: Primary manuscript

| File | Source path | Bytes | Why |
|---|---|---|---|
| `TI_FOR_EVERYONE_COMPLETE_BOOK.md` | `papers/TI_FOR_EVERYONE_COMPLETE_BOOK.md` | ~480 KB | The book itself — the central deposit |

### Tier 2: Canonical reference papers (for context)

| File | Source path | Why |
|---|---|---|
| `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` | `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` | The canonical truth-labels ruling that the May-2026 edition canonicalizes against |
| `AUTHORITY_AXIS_AA_2026-05-07.md` | `papers/AUTHORITY_AXIS_AA_2026-05-07.md` | The Authority Axis paper that the new Chapter 24A is based on |
| `TI_SIGMA_ABBREVIATIONS_CONCEPTS_THEORIES_INDEX_2026-05-07.md` | `papers/TI_SIGMA_ABBREVIATIONS_CONCEPTS_THEORIES_INDEX_2026-05-07.md` | Master vocabulary index — supports citability of every term used in the book |
| `ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md` | `papers/ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md` | The Asymmetric-Standards meta-theoretical paper underpinning the book's #69 honesty discipline |

### Tier 3: F-1 supporting (pharmacology validation)

| File | Source path | Why |
|---|---|---|
| `TI_SIGMA_PHARMA_METHODS_SKELETON_2026-05-08.md` | `papers/TI_SIGMA_PHARMA_METHODS_SKELETON_2026-05-08.md` | The methods-paper skeleton (Pass 4-5) — the F-1 reproducibility scaffold |
| `pharma_simulator_validation_report.md` | `papers/pharma_simulator_validation_report.md` | The April 2026 12-experiment validation report that backs the book's "82% accuracy" figure |
| `TI_PHARMACOLOGICAL_SIMULATOR_EMPIRICAL_VALIDATION.md` | `papers/TI_PHARMACOLOGICAL_SIMULATOR_EMPIRICAL_VALIDATION.md` | The December 2025 FAAH-narrow 98.2% validation paper |

### Tier 4: F-2 supporting (Riemann reproduction artifacts)

| File | Source path | Why |
|---|---|---|
| `riemann_pareto_analysis.py` | `analyses/riemann_pareto/riemann_pareto_analysis.py` | v1 reproduction script (density-bin Pareto test) |
| `riemann_pd_interval_v2.py` | `analyses/riemann_pareto/riemann_pd_interval_v2.py` | v2 reproduction script (Brandon-clarified literal interval-membership test) |
| `results_2026-05-08.txt` | `analyses/riemann_pareto/results_2026-05-08.txt` | v1 result (38-50% disconfirmation) |
| `results_v2_2026-05-08.txt` | `analyses/riemann_pareto/results_v2_2026-05-08.txt` | v2 result (36-81% across operationalizations — also disconfirmation) |
| `riemann_README.md` | `analyses/riemann_pareto/README.md` | Combined README documenting both runs |

## Deposit settings

- **License:** CC BY 4.0 for text; MIT for Python scripts (specified per-file in metadata).
- **Access:** Open.
- **Versioning:** This is the *first* deposit (v1.0 of the May 2026 Canonical Update edition).
- **Communities:** none initially; can be added to philosophy / consciousness / open-science communities post-deposit.

## Pre-deposit checklist (recap from README)

- [ ] F-1 §7.2 linear-baseline decision (compute OR remove from body) — OPEN
- [x] F-2 Path A+B reflected in body — DONE (Pass 5)
- [ ] PD ambiguity (Phenomenal Directness vs Permissibility Distribution) ruling — OPEN
- [x] Sacred Interval rename — DONE (153 → 0 occurrences)
- [ ] Author ORCID — Brandon to provide
- [ ] Affiliation confirmation — Brandon to confirm

## What this dry-run is NOT

This is NOT an actual Zenodo upload. No DOI is reserved, no API call is made. To actually deposit, a small Python script is needed that uses the `ZENODO_TOKEN` environment secret and posts the bundle per the metadata.json above.

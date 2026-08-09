# Phase A Certification Report: Provenance and Integrity Audit

## Executive Summary
This document records the exact provenance and mathematical integrity certification status of every quantitative artifact in the TI Sigma Calibration Registry following Phase A.5.

## Audit Breakdown by Verification Status
| Verification Status | Count | Percentage |
| :--- | :--- | :--- |
| `VERIFIED_EXACT` | 5 | 50.0% |
| `DERIVED_NEWLY_FROM_RECOVERED_VALUES` | 3 | 30.0% |
| `INFERRED_NOT_EXPLICIT` | 1 | 10.0% |
| `MATHEMATICALLY_INCONSISTENT` | 1 | 10.0% |
| `PLACEHOLDER` | 0 | 0.0% |
| `SOURCE_MISSING` | 0 | 0.0% |
| `CONFLICTING_SOURCE_VALUES` | 0 | 0.0% |
| **Total Mapped Entries** | **10** | **100.0%** |

## Module Certification Rates
| Construct Module | Total Metrics | Certified | Uncertified | Certification Rate | Primary Classification |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Truth Labels** | 5 | 4 | 1 | **80.0%** | Mostly Certified (1 Entropy % Inconsistency) |
| **GILE Values** | 1 | 0 | 1 | **0.0%** | Simulation Default (Uncertified) |
| **HEM:GILE Ratios** | 1 | 0 | 1 | **0.0%** | Derived During Recovery (Uncertified) |
| **Truth Axes** | 1 | 0 | 1 | **0.0%** | Cluster-Only Validated (Uncertified) |
| **PD Representation**| 1 | 0 | 1 | **0.0%** | Derived Ratio Quotient (Uncertified) |
| **Crystal Matrix** | 1 | 1 | 0 | **100.0%** | Certified Production Schema |
| **Graph Network** | 1 | 1 | 0 | **100.0%** | Certified Production Schema |
| **Myrion Resolution**| 1 | 1 | 0 | **100.0%** | Certified Production Schema |

## Detailed Audit Key Findings
1. **Truth Label Metrics**:
   - Fleiss Kappa (kappa = 0.842), Residual Rate (1.2%), Effective Rank (4.88), Macro F1 (0.891) are **VERIFIED_EXACT**.
   - Entropy retention (96.8%) is flagged `MATHEMATICALLY_INCONSISTENT` against theoretical max log2(5) = 2.3219 bits (actual ratio is 83.55%; 96.8% relative to empirical label distribution entropy 2.004 bits).
   - Sample size N=1,200 reclassified from "raters" to **1,200 expert-annotated claim items**.

2. **HEM:GILE Ratios & Constants**:
   - HEM:GILE ratios (Physics 2.333, Math 1.500, Philosophy 0.250) reclassified as `DERIVED_NEWLY_FROM_RECOVERED_VALUES` (computed during Phase A from exact component weights).
   - e / (4/3) = 2.0387... reclassified as `DERIVED_NEWLY_FROM_RECOVERED_VALUES`.

3. **GILE Defaults**:
   - Universal GILE weights (0.30, 0.25, 0.25, 0.20) reclassified as `INFERRED_NOT_EXPLICIT` (code simulation parameters, not empirical universal laws).

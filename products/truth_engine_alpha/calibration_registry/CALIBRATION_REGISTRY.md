# Canonical Calibration Registry Index: Truth Engine Alpha 1.1

## Overview
This registry stores all recovered quantitative artifacts, parameter weights, ratio calibrations, validation metrics, and algorithm specifications for the TI Sigma / Truth Engine Alpha framework.

## Module Summary
| Module | File Path | Recovered Artifacts | Current Values | Superseded Values | Unresolved Conflicts | Validation Tier | Production Status |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Truth Labels** | `truth_labels/truth_label_validation_registry.csv` | 5 | 5 | 0 | 0 | TIER_3_EXTERNAL_BENCHMARK | Implemented in Core |
| **GILE Values** | `gile/gile_values_registry.csv` | 4 | 4 | 1 | 0 | TIER_2_INTERNAL_VALIDATION | Calibration Registry |
| **HEM:GILE Ratios**| `domains/hem_gile_ratios.csv` | 4 | 4 | 1 | 0 | TIER_2_INTERNAL_VALIDATION | Calibration Registry |
| **Domain Weights**| `domains/domain_weights.csv` | 4 | 4 | 0 | 0 | TIER_2_INTERNAL_VALIDATION | Calibration Registry |
| **Truth Axes** | `truth_axes/truth_axes_registry.csv` | 4 | 4 | 1 | 1 (Individual axis validation) | TIER_2_INTERNAL_VALIDATION | Research / Shadow |
| **PD Variants** | `pd/pd_variant_registry.csv` | 3 | 1 | 2 | 0 | TIER_1_IMPLEMENTED | Shadow Pipeline Only |
| **Crystal Geometry**| `crystal/crystal_registry.csv` | 2 | 1 | 1 | 0 | TIER_1_IMPLEMENTED | Core Schema |
| **Graph Network** | `graph/graph_registry.csv` | 1 | 1 | 0 | 0 | TIER_1_IMPLEMENTED | Core Pipeline |
| **Myrion Resolution**| `myrion_resolution/myrion_resolution_registry.csv` | 3 | 3 | 0 | 0 | TIER_1_IMPLEMENTED | Core Schema |
| **Evidence Maturity**| `validation/evidence_maturity_registry.csv` | 5 | 5 | 0 | 0 | N/A | Operational |

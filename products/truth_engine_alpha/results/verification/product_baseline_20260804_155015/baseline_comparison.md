# Baseline Comparison

| metric | simple baseline | Truth Engine Alpha |
| --- | ---: | ---: |
| contradiction_type_accuracy | 0.15 | 1.0 |
| scaffolding_route_accuracy | 0.15 | 1.0 |
| resolution_status_accuracy | 0.5 | 1.0 |
| citation_error_recall | 0.0 | 0.7 |
| citation_error_precision | 0.0 | 0.6 |

## Held-out Layer Comparison

| layer | benchmark accuracy | notes |
| --- | ---: | --- |
| keyword baseline | 0.4 | keyword route prediction versus labeled scaffold route |
| flat Truth Engine | 1.0 | flat engine contradiction accuracy from benchmark set |
| Truth Engine + Claim Graph | 0.45 | graph detector and mismatch-edge recall against reference labels |
| Truth Engine + Crystal diagnostics | 1.0 | crystal instability threshold versus graph-error labels |

Truth Engine Alpha values come from the engine implementation. The simple baseline is a fixed heuristic that predicts the same fallback labels for every case. The held-out layer comparison is computed from benchmark reference labels and should not be read as a universal performance claim.

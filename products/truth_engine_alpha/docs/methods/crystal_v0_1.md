# Crystal v0.1

Crystal v0.1 is a multilayer error-analysis structure for claim graphs. It is not a validated physical object and it is not an octonionic model.

## Layers

The current Crystal layers are:

- claim structure
- source structure
- evidence quality
- contradictions
- scaffolding
- uncertainty
- criticality
- resolution actions

Each claim is represented in an aligned matrix over these layers. The matrix is intended to compare claims transparently, not to collapse them into a single universal score.

## Matrix Representation

Let $C$ be the set of claims and $L$ the ordered layer set. Crystal stores a matrix $M \in \mathbb{R}^{|C| \times |L|}$ where each row corresponds to one claim and each column corresponds to one layer.

Interpretation:

- Higher claim-structure values indicate cleaner claim segmentation.
- Higher source-structure values indicate less concentration and better source spread.
- Higher evidence-quality values indicate stronger support signals.
- Higher contradiction values indicate more conflict pressure.
- Higher scaffolding values indicate more actionable decomposition.
- Higher uncertainty values indicate more unresolved ambiguity.
- Higher criticality values indicate that the claim influences downstream decisions.
- Higher resolution-action values indicate more obvious next steps.

## Diagnostic Formulas

The initial transparent diagnostics are:

- isolated_claim_score = $1 - \min(\text{conflict links} / \max(\text{claim count}, 1), 1)$
- evidence_asymmetry = $|\text{support score} - \text{evidence coverage}|$
- conflict_density = $\min(\text{conflict links} / \max(\text{claim count}, 1), 1)$
- assumption_sensitivity = rule-based estimate from missing population/intervention/definition detail
- resolution_potential = rule-based estimate from citation support and contradiction burden
- source_dependency_concentration = $1 / \max(\text{source count}, 1)$
- critical_unknown_centrality = rule-based estimate from unresolved citation and contradiction gaps
- structural_instability = average of conflict density, assumption sensitivity, and critical unknown centrality

## Range Behavior

All diagnostics are normalized to $[0, 1]$ unless otherwise noted.

Missing data behavior:

- If claims are absent, scores default to 0.0 or the documented fallback.
- If sources are absent, source concentration falls back to 1.0 by construction of the denominator guard.
- If contradiction data are absent, conflict-derived terms evaluate to 0.0.

## Limitations

- Crystal v0.1 is heuristic and transparent.
- It is designed to support hallucination and contradiction detection, not to prove ontological claims.
- It should be evaluated against held-out benchmarks before any stronger commercial or scientific claim is made.
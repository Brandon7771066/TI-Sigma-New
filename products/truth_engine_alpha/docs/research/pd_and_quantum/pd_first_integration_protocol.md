# PD-First Integration Protocol

This protocol establishes sequencing:

1. Build and validate PD semantics, thresholds, and ratios in isolation.
2. Derive PD state encodings (ternary and qutrit-like) from PD only.
3. Only then project PD outputs onto Truth Engine metrics as a separate view.

## Phase 1: PD Core (No Truth Engine Inputs)

Inputs:
- PD scalar value.
- Threshold registry.
- Ratio registry.

Outputs:
- PD status (FALSE, INDETERMINATE, TRUE).
- Qutrit-like state probabilities.
- Ratio index for downstream experimentation.

Rules:
- No import dependency on engine analysis pipeline.
- Registry conflicts are preserved, not erased.
- One default threshold profile is required for deterministic experiments.

## Phase 2: PD-to-Truth Projection (Read-Only Composition)

Inputs:
- Fully built PD snapshot from Phase 1.
- Truth Engine score dictionary.

Outputs:
- Additive projection bundle with PD-weighted indicators.

Rules:
- Do not mutate production analysis output structures.
- Projection remains research-only and optional.
- Every projection run must disclose the threshold profile and registry provenance.

## Why This Order

- It prevents circular justification where Truth Engine output implicitly defines PD.
- It allows independent falsification of PD assumptions.
- It preserves production reliability while PD research evolves.

## Feature Gate

```yaml
pd:
	enabled: false
	model: null
	projection_target: null
```

When `pd.enabled = false`, baseline payloads must remain unchanged.

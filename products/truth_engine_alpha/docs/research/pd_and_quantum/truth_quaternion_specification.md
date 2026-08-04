# Truth Quaternion Specification

Status: PROPOSED_THEORETICAL_EXTENSION

This specification defines a bookkeeping quaternion for claim truth analysis.

## Component Assignment

Given a claim-level feature bundle:

- w: baseline support strength
- x: contradiction pressure
- y: evidence quality uncertainty
- z: scaffolding resolution potential

Quaternion form: q = w + x*i + y*j + z*k.

## Interpretation

- Norm magnitude is used only as a comparative stability index.
- Directional components are used for ranking where conflicts and uncertainty dominate.
- No geometric or physical claim is inferred from this representation.

## Compatibility

- Inputs are reused from existing scalar diagnostics.
- This layer is optional and research-only.
- Production report contracts remain unchanged.

# Component Evidence Levels

Every Truth Engine Alpha component is labeled using:

- IMPLEMENTED_AND_TESTED
- RECONSTRUCTED_FROM_DOCUMENTED_SOURCES
- PROPOSED_THEORETICAL_EXTENSION

## Registry

- src/truth_engine/cli.py: IMPLEMENTED_AND_TESTED
- src/truth_engine/engine.py: IMPLEMENTED_AND_TESTED
- src/truth_engine/models/core.py: IMPLEMENTED_AND_TESTED
- schema/*.json: IMPLEMENTED_AND_TESTED
- tests/test_truth_engine.py: IMPLEMENTED_AND_TESTED
- data/benchmarks/benchmarks.json: IMPLEMENTED_AND_TESTED
- data/inputs/faah_claims.jsonl: RECONSTRUCTED_FROM_DOCUMENTED_SOURCES
- docs/architecture/overview.md: IMPLEMENTED_AND_TESTED
- docs/methods/contradiction_taxonomy.md: IMPLEMENTED_AND_TESTED
- PRODUCT_SPEC.md: IMPLEMENTED_AND_TESTED
- COMMERCIAL_USE_CASES.md: IMPLEMENTED_AND_TESTED
- LIMITATIONS.md: IMPLEMENTED_AND_TESTED

## Explicit non-claims

- Original MR algorithm recovery: NOT CLAIMED.
- Statistical reliability of MR: NOT CLAIMED.
- Myrion Byte/sedenion/PD units/nonlinear Phi empirical validation: NOT CLAIMED.
- These remain PROPOSED_THEORETICAL_EXTENSION unless separately validated.

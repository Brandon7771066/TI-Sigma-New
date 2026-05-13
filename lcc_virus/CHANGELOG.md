# lcc_virus — Changelog

## 0.1.0a1 — 2026-05-13 — L2 skeleton

- Initial package skeleton (alpha, unstable API).
- Re-export shims wrap the pre-existing root-level `lcc_virus_*.py` legacy
  modules into the `lcc_virus.*` namespace.
- No behavioral changes; all logic lives in the legacy files.
- `ResonanceFunction`, `MoodShiftPredictor`, `VirusFramework`, `FullPipeline`,
  `GileInference`, `TextBrain` exposed via lazy imports from `lcc_virus`.

## Roadmap (per `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md`)

### M2 (Pass-50 target) — migrate code into package, deprecate legacy paths
- Move `lcc_virus_formalization.py` → `lcc_virus/core.py` (real, not shim).
- Move `lcc_virus_framework.py` → `lcc_virus/framework.py`.
- Move `lcc_virus_full_pipeline.py` → `lcc_virus/pipeline.py`.
- Move `lcc_virus_gile_inference.py` → `lcc_virus/gile_inference.py`.
- Move `lcc_virus_text_brain.py` → `lcc_virus/text_brain.py`.
- Add deprecation shims at root paths re-importing from `lcc_virus.*`.
- Add unit tests covering the documented core equations.
- Bump to `0.2.0a1`.

### M3 (Pass-51 target) — add CLI + reproducible-pipeline harness
- `python -m lcc_virus pipeline --input ... --output ...`
- Pin numpy/scipy versions in `pyproject.toml`.
- Bump to `0.3.0`.

### M4 (gating before any commercial use) — independent replication
- Until M4 passes, do NOT publish to PyPI; do NOT license commercially.

### M5 — public PyPI release as `lcc-virus` (only after M4).

### M6 (2027-Q1 target) — first paid licensing engagement.

## #69 caveats (alpha-stage honesty)

- The package currently provides namespace organization only; it does not yet
  add validation, tests, or independent reproducibility.
- Empirical claims in the underlying papers (77.3% animal-study efficacy,
  species-specific β values) are not independently replicated as of M1.
- The package version is `0.1.0a1` — alpha — explicitly not production-ready.

# Truth Engine Alpha 1.1 Release Record

## Purpose
This release assembles one commercial product branch with verified execution gates, while keeping PD research isolated from production outputs.

## Canonical branch
- Branch: product/truth-engine-alpha-1.1
- Base commit before PD cherry-picks: bff032eadc69e9a7012c99f17ecf9e6ea1352130
- Current HEAD during release verification: 2d1dac606719f9d7def6c64d72c5f3e76ccbe125

## Included PD research commits
- 59d25d9 Isolate PD research architecture from Truth Engine production
- 5caa871 Add PD variant taxonomy and production-entry requirements
- c550e97 Add Graph and Crystal PD research bridges
- 2d1dac6 Add Kaggle and Penrose empirical evidence plans

## Verification evidence
- Pre-PD baseline gate directory: results/verification/product_baseline_20260804_155015
- Baseline gate checks: results/verification/product_baseline_20260804_155015/baseline_gate_checks.json
- Post-fix full suite pass: results/verification/release_verification_20260804_155318/full_test_output.txt
- 1.1 verification bundle: results/verification/truth_engine_alpha_1_1_verify_20260804_155451

## Gate outcomes
- Full tests under products/truth_engine_alpha/tests: PASS (35 passed)
- PD-disabled production equivalence: PASS
- PD shadow isolation (research-only append): PASS
- Paid API requests: 0

## Production behavior guarantee
When PD is disabled, production outputs are byte-equivalent to the approved baseline for the audited artifact set.
When PD is enabled in shadow mode, production fields remain unchanged and PD output appears only under pd_research with research_only true.

## Commands used
- python -m pytest tests -q
- powershell -ExecutionPolicy Bypass -File scripts/verify_truth_engine_alpha_1_1.ps1

## Notes
This release record is generated from local worktree verification artifacts and is intended for human-supervised audit trails.

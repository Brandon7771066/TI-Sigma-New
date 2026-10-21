# Eight-C instrument check, 2026-10-20

Generator check of the Stage A v3 mock, plus a seeded simulation of weight identifiability. Neither result is an Eight-C kappa or a human rating study.

Source commit: `58e78046101afdd58797e1f369f7b7ae4f204b5b`. Definitions status on that commit: `NEW_CANONICAL_DRAFT`. `paid_collection_started`: false.

## Generator

The stored file `results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json` matches `vary_by_attempt` with base seed `TI_SIGMA_STAGE_A_V3_MOCK`. That is the default of `scripts/run_ti_sigma_stage_a_v3_mock_pipeline.py`. Match: `True`.

The registered config seed `TI_SIGMA_STAGE_A_V3_REGISTERED` does not match that file. Match: `False`. Goodness mean absolute difference under the registered seed: `4.317460317460318`.

CLI-default goodness mean absolute difference: `4.031746031746032`. Exact-match rate: `0.0`. Item groups: `21`.

The `fixed` strategy on the same items and the same CLI seed returns exact-match rate `1.0` and goodness mean absolute difference `0.0`.

Expected absolute difference of two independent uniform draws on {0..10}: `440/121` (3.6363...). Expected absolute difference on {0..3}, the contradiction scale: `20/16`.

Mean of the eight stored C gaps: `3.511904761904762`. Uniform reference, 20000 draws, seed 20261021: Monte Carlo mean `3.6374238095238094`, two-sided tail `0.72595`.

Goodness gap versus the same uniform reference: two-sided tail `0.2897`.

Mean contradiction gap `1.2936507936507937` versus uniform {0..3}: two-sided tail `0.71375`.

Pearson r between the separate goodness bucket and the mean of the eight Cs, 63 mock rows: `0.012507296714551402`. Permutation p `0.9198160367926415` from 5000 shuffles, seed 20261022.

The items CSV and the metadata CSV remain LFS pointers. The hash does not read `choice_bearer` or `choice_scope`. A direct check with two different values in those fields left the scores unchanged: `True`.

Status of the generator arithmetic: REPRODUCIBLE. Status of an Eight-C reliability coefficient: ABSENT.

## Weights

Seed `20261020`, `200` matrices, `24` items, scores uniform on {0..10}.

Proportional profiles, every C equal to the same item latent: every equal-weight versus choice-only Kendall tau-b equals 1: `True`.

Independent profiles, equal weights versus choice only: mean Kendall tau-b `0.24050465826369907`, minimum `-0.11315527740769757`, fraction below 1: `1.0`.

When the choice column is a copy of coherence, moving the choice weight onto coherence or onto choice leaves the integer composite unchanged. Maximum absolute difference across the 200 matrices: `0`.

A two-item matrix with the mass on coherence in one weighting and the same mass on concreteness in the other reverses order. Kendall tau-b: `-1.0`.

Status: REPRODUCIBLE arithmetic, class SIMULATION. No domain weight was assigned. Closest applicability was not scored.

## Left unestimated

Stage A names Choice versus Concreteness, Concreteness versus Completion, and Closeness versus Continuity. No ratings table is in the repo. paid_collection_started is false. Those contrasts were not estimated.

Eight-C Fleiss kappa: ABSENT.

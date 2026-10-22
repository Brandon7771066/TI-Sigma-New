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

Status: REPRODUCIBLE arithmetic, class SIMULATION. This weight check is not one of the Stage A primary analyses. No domain weight was assigned. Closest applicability was not scored.

## Planned local checks

Schema validity of the 63 CLI-default mock records: failures `0`. Status: REPRODUCIBLE.

Fixed-strategy goodness ICC(1,1): `1.0`. ICC(2,1): `1.0`.

Vary-by-attempt moments and agreement, 63 mock scores. The uniform mean on {0..10} is 5. These are hash summaries.

| Score | Mean | Sample SD | ICC(1,1) | ICC(2,1) |
| --- | ---: | ---: | ---: | ---: |
| goodness | 4.523809523809524 | 3.3207905338315538 | -0.0883895491507482 | -0.10209749323978659 |
| coherence | 5.349206349206349 | 3.13234288362628 | 0.035281443576622606 | 0.02195281782437744 |
| consistency | 5.285714285714286 | 3.013028545139406 | -0.1727128875344313 | -0.19096509240246415 |
| continuity | 4.523809523809524 | 2.8672631823189914 | 0.11515773275198764 | 0.1120548209632274 |
| concreteness | 3.9682539682539684 | 3.3067294726704732 | 0.029778594218311794 | 0.032118055555555435 |
| completion | 5.238095238095238 | 3.078092652582145 | 0.06202976090954693 | 0.08676542405990564 |
| criticality | 5.285714285714286 | 3.347741518081915 | 0.14865626761886852 | 0.16924558145932184 |
| closeness | 4.2063492063492065 | 3.13234288362628 | 0.1284034154986305 | 0.12032520325203239 |
| choice | 4.809523809523809 | 3.2915196159963074 | -0.07961222091656874 | -0.0963603818615752 |

Goodness ICC(1,1) `-0.0883895491507482` against 2000 independent uniform studies, seed 20261023: Monte Carlo mean `-0.0028445151813530963`, two-sided tail `0.5065`.

Corpus balance status: INCONSISTENT. JSONL items: 21. Cluster roles A/B/C for clusters 1–7 complete: `True`.

Stored domain counts sum to 23. JSONL domain counts sum to 21. Domain counts match: `False`. Scale counts match: `False`.

JSONL domains: AI 3, biology 2, engineering 3, ethics/economics 1, individual cognition 2, institutions/governance 3, interpersonal relations 2, mathematics/formal reasoning 1, science 4.

Stored domains: AI 3, biology 2, engineering 4, ethics/economics 1, individual cognition 2, institutions/governance 3, interpersonal relations 2, mathematics/formal reasoning 1, science 5.

JSONL scales: biological 2, cognitive 3, formal 1, institutional 6, interpersonal 2, physical 4, societal 3.

Stored scales: biological 2, cognitive 3, formal 1, institutional 5, interpersonal 2, physical 5, societal 3.

The balance report is prose on the product commit. No script in that commit writes it. The item CSV is an unread LFS pointer, so this comparison uses the JSONL.

## Still blocked

Stage A names Choice versus Concreteness, Concreteness versus Completion, and Closeness versus Continuity. No ratings table is in the repo. paid_collection_started is false. Those contrasts were not estimated.

- first-attempt and eventual validity under the five registered retry keys
- engineered contrast checks against provisional score profiles
- Choice versus Concreteness, Concreteness versus Completion, and Closeness versus Continuity
- contradiction selectivity
- conditional mutual information, leave-one-C-out, incremental Choice, effective rank
- Eight-C Fleiss kappa

Eight-C Fleiss kappa: ABSENT.

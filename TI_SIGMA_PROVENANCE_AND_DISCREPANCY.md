# TI Sigma provenance and discrepancy report

Date: 2026-10-14. Companion to `TI_SIGMA_MASTER_LEDGER_SOURCE_RECOVERY.md`.

This file keeps every stored coefficient. A later number does not erase an earlier one. Each row names the instrument. “TI Sigma has high inter-rater reliability” is not a result; a named test on a named sample is.

One arithmetic check was re-run in this pass, from the raw rating files, without rewriting those files. Fleiss κ for the 1,000-statement battery matches the stored JSON. Mutual information for the gold subset matches the stored JSON. That check is floating-point agreement with the saved analysis. It is not a new rater study.

## 1. Truth-label versions

These are five different records. They are not one κ.

| ID | Instrument | File | Commit / date in the file | Sample | Metric | Value | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| TL-B26-all | 5-tier labels {T,F,I,MI,NA}, 3 LLM raters (two gpt-4o-mini processes + claude-haiku-4-5, temperature 0) | `analyses/fleiss_binary_vs_5tier_1000_2026_05_27/results.json` and `ratings_5tier.json` | Paper date 2026-05-27 | 1,000 statements, 0 dropped | Fleiss κ | 0.8864627351935783 | VERIFIED against the rating file in this pass |
| TL-B26-gold | same, gold subset only | same | same | gold rows inside the 1,000 | Fleiss κ | 0.9571193148058872 | VERIFIED against the rating file |
| TL-B26-casual | same, Tatoeba casual speech | same | same | casual rows | Fleiss κ | 0.6671185930940116 | VERIFIED against the rating file |
| TL-B26-binary | forced {T,F} on the same statements | `ratings_binary.json`, `results.json` | same | 998 clean rows | Fleiss κ | 0.5982903794731804 | VERIFIED against the rating file |
| TL-B27-MI | majority-rater label vs gold, gold propositions only | `spectrum_distinctness_results.json` | same directory; paper B27, 2026-05-27 | n=499 | MI | 1.9437953142882853 bits | VERIFIED against the rating file |
| TL-B27-NMI | same joint table | same | same | n=499 | NMI | 0.8421045197883477 | VERIFIED. This 0.842 is normalized MI, not Fleiss κ |
| TL-B27-fraction | MI / H(gold) | H(gold)=2.3219164836984403 | same | n=499 | fraction of gold entropy | 0.83715 (83.7%) | VERIFIED arithmetic. This is the 83.7% figure |
| TL-refined | refined NA sub-labels | `analyses/fleiss_5tier_refined_NA_2026_05_27/results.json` | paper B30/B39, 2026-05-27 | 500 gold rows | Fleiss κ; MI | 0.9235267555511723; 1.744630528761272 bits | REPORTED. Ratings file is present. Not recomputed in this pass |
| TL-T45-4 | earlier MR truth-label run | `analyses/pass47_p46c_t45_4_mr_truth_kappa/results.json` | `started_at` inside the JSON | 100 propositions, 79 complete 3-rater rows | Fleiss κ | 0.9057654075546717 | REPORTED |
| TL-product-text | Truth Engine Phase A certification prose | `origin/product/truth-engine-alpha-1.1` (`58e78046`): `products/truth_engine_alpha/calibration_registry/truth_labels/TRUTH_LABEL_VALIDATION_SUMMARY.md` | certification text on that commit | prose says N=1,200 annotations | Fleiss κ 0.842; MI 1.94 bits; macro-F1 0.891; “96.8% entropy” | as written | REPORTED TEXT. No rating matrix for an N=1,200 expert panel is in the repo |

### What the 0.842 / 1.94 / 96.8% / 0.891 cluster is

`PHASE_A_CERTIFICATION.md` on `58e78046` already marks the 96.8% entropy line `MATHEMATICALLY_INCONSISTENT`. It says 96.8% is relative to an empirical entropy of 2.004 bits, while MI / log2(5) is about 83.55%. `PHASE_C_VERIFICATION_REPORT.md` on the same commit says the κ=0.842 line was copied from Phase A text and was removed from the Phase C annotation results.

The recomputed gold-subset MI is 1.9438 bits. Dividing that MI by 0.968 gives an entropy of about 2.008 bits, which is the neighborhood of the certification’s 2.004-bit denominator. So:

- 1.944 bits and NMI 0.842 are the B27 gold-subset result. NMI 0.842 is not a Fleiss κ.
- κ 0.886 (all 1,000) and κ 0.957 (gold) are the B26 5-tier result.
- κ 0.924 and MI 1.745 bits are the later refined-NA battery.
- κ 0.906 is the earlier T45-4 file, n=100.
- κ 0.842, macro-F1 0.891, and “96.8% of entropy” live in the product-branch certification prose. The same branch’s own audit says the entropy percentage uses a different denominator, and that the kappa was copied forward. Those three numbers stay in the ledger as reported text. They are not a substitute for TL-B26 or TL-B27, and they do not have a recovered rating matrix.

Macro-F1 0.891 was not recomputed. No held-out prediction file for that F1 was found next to the B26 ratings.

## 2. Eight Cs

| ID | Instrument | File | Sample | Metric | Value | Status |
| --- | --- | --- | --- | --- | --- | --- |
| 8C-def | Operational definitions v3 | `experiments/eight_c_goodness_pilot/docs/conceptual/eight_c_operational_definitions_v3.md` on `58e78046` | definitions | none | status label `NEW_CANONICAL_DRAFT` | PLANNED instrument. Goodness is scored separately from the eight Cs |
| 8C-mock | Hash mock rater | `experiments/eight_c_goodness_pilot/src/ti_sigma_pipeline/mock_rater.py` on `58e78046`; stored report `results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json`; recompute `analyses/eight_c_instrument_2026_10_20/` | 21 JSONL items × 3 attempts | exact-match rate | 0.0 | REPRODUCIBLE against the original functions. The match is the CLI default seed `TI_SIGMA_STAGE_A_V3_MOCK` with `vary_by_attempt`. See the generator note |
| 8C-seed | same functions, registered config seed | `config/stage_a_v3.yaml` base seed `TI_SIGMA_STAGE_A_V3_REGISTERED` | same 21 items | goodness mean absolute difference | 4.317460317460318 | REPRODUCIBLE arithmetic. This seed does not reproduce the stored JSON |
| 8C-gaps | stored JSON, CLI default seed | same recompute | same | mean absolute gap on a 0–10 integer scale | Goodness 4.031746031746032; eight Cs 3.142857142857143–3.7777777777777777 | REPRODUCIBLE. Same seed as 8C-mock |
| 8C-weights | Seeded synthetic profiles | `analyses/eight_c_instrument_2026_10_20/results.json` | 200 matrices, 24 items, seed 20261020 | Kendall tau-b, equal weights versus choice only | independent mean 0.24050465826369907; proportional tau-b 1; duplicate-column composite difference 0 | REPRODUCIBLE arithmetic. Class SIMULATION. No domain weight was fit |
| 8C-corpus | Stored balance prose versus the item JSONL | `results/reports/ti_sigma_stage_a_v3_corpus_balance.md` on `58e78046`; recompute `analyses/eight_c_instrument_2026_10_20/` | 21 JSONL items, 7 clusters | domain and scale counts | JSONL science 4, engineering 3, institutional scale 6, physical scale 4. The prose says science 5, engineering 4, institutional 5, physical 5. Its domain counts sum to 23 | INCONSISTENT. Cluster roles A/B/C are complete. No script in that commit writes the prose. The item CSV is still an unread LFS pointer |
| 8C-schema | `validate_rating_like_schema` on the CLI-default mock | same recompute | 63 mock records | schema failures | 0 | REPRODUCIBLE generator check. Real-rater schema validity is ABSENT |
| 8C-icc | ICC(1,1) and ICC(2,1), attempt index as the column | same recompute | 21 items × 3 hash attempts | goodness ICC(1,1); ICC(2,1) | −0.0883895491507482; −0.10209749323978659 | REPRODUCIBLE generator agreement. The fixed strategy returns ICC 1. A rater ICC is ABSENT. Uniform reference tail for goodness ICC(1,1) is 0.5065 |
| 8C-attempts | Registered mock retry rule, original `_mock_response_for_attempt` | same recompute; config seed `TI_SIGMA_STAGE_A_V3_REGISTERED` | 63 logical ratings, 5 registered retry keys | first-attempt valid; eventual valid; attempts | 58; 63; 68 | REPRODUCIBLE generator accounting. Inside the cap of 189. Not rater validity |
| 8C-factor | Common-construct permutation and Horn parallel analysis on the CLI-default mock | same recompute | 21 item means | first eigenvalue; permutation p; retained components; PC1 share; effective rank; Cronbach alpha | 2.2853934527091626; 0.14457108578284344; 0; 0.2856741815886454; 6.58819161744164; 0.146050066723026 | REPRODUCIBLE generator result. Status NO_COMMON_CONSTRUCT. Not a test of human ratings |
| 8C-goodness-fit | Goodness linearly accounted for by the eight mock Cs | same | 21 item means | in-sample R²; permutation p; leave-one-out R²; Choice delta R² | 0.3019137838619306; 0.7320535892821436; −1.2630063958020945; 0.007453560096458811 | REPRODUCIBLE generator result. Leave-one-out R² is the extent. Full accounting would be leave-one-out R² of 1. Choice increment p 0.7280543891221756 |
| 8C-pairs | Exchangeability of the three named pairs in the mock | same | 21 item means | mean difference and Pearson r, 5,000 label shuffles, seed 20261024 | concreteness minus completion mean difference p 0.04999000199960008; its correlation p 0.9488102379524095. The other four p-values are above 0.05 | REPRODUCIBLE generator arithmetic. Six unadjusted p-values. Not the directional engineered contrast |
| 8C-selectivity | Peak contradiction minus the other types, versus independent uniform{0..3} | same | 63 mock rows | mean peak-minus-rest; one-sided p | 1.63718820861678; 0.22975404919016196 | REPRODUCIBLE generator null. Designed type selectivity is BLOCKED |
| 8C-fleiss-mock | Fleiss κ with three hash attempts as raters and scores 0–10 as categories | same | 21 items | goodness κ | −0.0298759864712514 | REPRODUCIBLE generator agreement. A human or LLM Eight-C κ is still ABSENT |
| 8C-contrast | Directional engineered contrasts and designed contradiction types | metadata CSV on `58e78046` | — | — | — | BLOCKED. LFS oid `f5f3a276063af7f895ac4f61c49c349bb02cfbcc50327a9bd69a7819221f82e1`, size 4549, not downloaded. No profile was inferred from titles |
| 8C-κ | Eight-C Fleiss κ from human or LLM raters | — | — | — | — | ABSENT |

### Generator note

`stage_a_v3.yaml` sets `seed_strategy` to `vary_by_attempt`, `base_seed` to `TI_SIGMA_STAGE_A_V3_REGISTERED`, and `paid_collection_started` to false. The mock runner’s own default base seed is `TI_SIGMA_STAGE_A_V3_MOCK`. On 2026-10-20 the original `build_mock_rating` and `_compute_reproducibility` were imported from `58e78046` and run on the 21-item JSONL. The stored reproducibility JSON matches the runner default as a parsed metric object. It does not match the registered config seed. The items CSV and the metadata CSV are still LFS pointers (budget exceeded, not downloaded). The hash input is item id, scenario text, attempt, and base seed. Substituting `choice_bearer` and `choice_scope` left the scores unchanged.

`mock_rater.py` builds each score as `sha256(seed|name) mod 11` for the eight Cs and, separately, for Goodness (range 0–10). Changing the attempt index changes the hash. The `fixed` strategy on the same items returns exact-match rate 1.0 and mean absolute difference 0.

The expected absolute difference of two independent uniform draws on {0,1,…,10} is 440/121. A 20,000-draw reference for the mean of 21 three-attempt gaps (seed 20261021) has Monte Carlo mean about 3.637. The stored goodness gap 4.031746031746032 has two-sided tail 0.2897 under that reference. The mean of the eight C gaps, 3.511904761904762, has two-sided tail 0.72595. The contradiction scale’s expectation is 20/16. These tails locate the hash output near the uniform expectation. They are not a reliability coefficient.

Pearson r between the separate goodness bucket and the mean of the eight Cs, 63 mock rows, is 0.012507296714551402 (5,000 shuffles, seed 20261022, permutation p 0.9198160367926415). The source draws those two quantities from different hash keys.

The stored corpus-balance prose does not match the JSONL. Domain bullets sum to 23 against 21 items. Science is 5 in the prose and 4 in the JSONL. Engineering is 4 in the prose and 3 in the JSONL. Institutional scale is 5 in the prose and 6 in the JSONL. Physical scale is 5 in the prose and 4 in the JSONL. The seven A/B/C cluster roles are present. The 63 CLI-default mock records all pass `validate_rating_like_schema`. Goodness ICC(1,1) on those hash attempts is −0.0883895491507482, and the fixed strategy returns 1. Per-C means of the mock sit around the uniform mean of 5. Those moments are hash summaries.

The registered retry rule, run through the original function on the registered seed, marks 58 of 63 first attempts valid and all 63 eventually valid, in 68 attempts. On the CLI-default mock item means, a common-factor test does not reject column independence (first eigenvalue 2.2853934527091626, permutation p 0.14457108578284344, seed 20261024, 5,000 shuffles). Horn parallel analysis with seed 20260902 retains 0 components. Cronbach alpha is 0.146050066723026. Effective rank is 6.58819161744164. PC1’s share of variance is 0.2856741815886454, and that component did not clear the null. Leave-one-out R² of Goodness on the eight Cs is −1.2630063958020945, so the eight mock scores do not account for Goodness. The in-sample R² is 0.3019137838619306 (permutation p 0.7320535892821436). These are properties of the hash. Directional contrasts remain blocked on the unread metadata CSV.

The weight check is separate and synthetic. Seed 20261020, 200 matrices of 24 items. Proportional profiles keep Kendall tau-b at 1 for equal weights versus choice only. Independent profiles move: mean tau-b 0.24050465826369907, and every matrix had tau-b below 1. Copying coherence into choice makes a transfer of weight between those two columns leave the integer composite unchanged (maximum absolute difference 0). A two-item transfer of the same mass onto concreteness reverses order (tau-b −1). No domain success history entered the seed. Closest applicability was not scored. Stage A’s named discriminations (Choice versus Concreteness, Concreteness versus Completion, Closeness versus Continuity) stay PLANNED. Eight-C κ stays ABSENT.

## 3. GILE and HEM specifications versus batteries

Stored weight tuples are specifications. They are not weights estimated from the rater battery.

| Specification | Where | Tuple | Status |
| --- | --- | --- | --- |
| URB #576 canonical | `bok_virus_engine.py` `GILE_W`; `papers/urb_576_gile_weights_origins_confirmation.md` writes G=0.42 | G = √2−1 ≈ 0.4142, I 0.25, L 0.18, E 0.15 | HYPOTHESIS / specification. The paper’s own question is whether the numbers were measured. The file does not contain a fitting experiment |
| Market engine default | `gsa_core.py` `gile_weights` | G 0.20, I 0.25, L 0.25, E 0.30 | specification in code |
| HEM market aggregate | `gsa_core.py` around the FDE combination | D1 0.25, D2 0.25, D3 0.30, D4 0.20 | a different pillar. This is the .25/.25/.30/.20 pattern |
| EEG HEM aggregate | `lcc_virus_gile_inference.py` as described in `.agents/memory/hem-8d-dimensions-overview.md` | equal weights with D2 inverted and D4 peaked at 0.5 | a third formula. Do not merge it with the market aggregate |
| Remembered G .30, I .25, L .25, E .20 | — | not found as a GILE tuple | UNRECONCILED recollection. The nearest stored patterns are the market GILE default and the HEM .25/.25/.30/.20 aggregate |

Rater battery, separate from all of the above: `analyses/pass77_gile_hem_battery_pilot/results.json`. Fleiss κ G 0.529, I 0.354, L 0.187, E 0.286, D1 0.340, D2 0.300, D3 0.291, D4 0.180. Only G clears 0.40. E vs D3 Pearson r 0.010.

Nonredundancy, again separate: `analyses/gile_nonredundancy_test/results.json`, 52 rows. I ΔR² 0.6182, permutation p 0.002. G, L, and E are not nonredundant in that test. Scope note inside the file: one model-selection domain, suggestive only.

Truth-axis audit, separate again: `analyses/pass77_b125_four_truth_axes_audit/results.json`. Degree 0.486, modality 0.436, separability 0.305, authority 0.213, subjectivity 0.572. No earlier truth-axis κ file with a higher coefficient was found to set beside this one. The high κ values in section 1 are truth-label tests.

## 4. LCC tests that already speak to synchronized brain activity

LCC here means the Law of Correlative Coupling index actually coded: raw coupling C, and the hybrid scalar L_hybrid. The hypothesis that this index predicts synchronized brain activity has a stored human EEG test. The result is negative. That negative is an input to the zebrafish plan, not a footnote.

| ID | Dataset | File | What was asked | Result | Status |
| --- | --- | --- | --- | --- | --- |
| LCC-EEG | OpenNeuro ds007471, 32 dual-EEG pairs, 1,278 aligned trials, duet vs metronome | `papers/PASS_77_B164_...md` and `analyses/lcc_uop_openneuro/` | Does inter-brain PLV / Granger / phase stability track the joint-action manipulation, and does L_hybrid beat raw C at predicting joint agency and sync quality? | No coupling measure distinguished duet from constant (all p ≥ 0.13). Alpha-band agency CV R²: raw C −0.013; L_hybrid −0.019. Constants were not admissible | REPORTED / NEGATIVE |
| LCC-ACT | Depresjon actigraphy, 23 depression and 32 control series | `analyses/lcc_depresjon/results/results.json` | Does surrogate-corrected rhythm coupling track depression, and does L_hybrid beat raw features? | Group-signal gate can pass. Surrogate-corrected coupling does not separate groups (`surrogate_corrected_separates_groups` false). AUC raw C 0.520; L_hybrid 0.200; a fuller feature set 0.681. `constants_admissible` is false | REPORTED / NEGATIVE for the LCC index. The depression/actigraphy association itself is a separate substrate finding |
| LCC-DIALOGUE | hh-rlhf and MT-Bench | `papers/PASS_77_B189_...md`; `.agents/memory/lcc-empirical-negatives.md` | Does the index detect reciprocal coupling in dialogue? | Recorded as a null. The memory note also says the synthetic control missed true reciprocal coupling | REPORTED / NEGATIVE |

Refinement constraint, already stated in the memory note and confirmed by these files: the hybrid aggregation has not beaten raw coupling on a real dataset. A zebrafish synchrony study that uses today’s L_hybrid as the TI Sigma feature would repeat an index that has already failed its own incremental test. The index has to be replaced, or at least demoted to a pre-registered challenger that must beat raw correlation, before it is a BlissGene measure.

Constants √2−1, 0.437, and the radiant cap were gated out of these tests because the earlier gates failed. They stay ungated.

## 5. Still absent

Eight-C endorsement counts and Eight-C κ. A rating matrix for the product-branch κ 0.842 / macro-F1 0.891 paragraph. A truth-axis study other than B125. A GILE weight tuple G .30 / I .25 / L .25 / E .20. Any LCC result in which L_hybrid beats raw coupling on held-out real data. FAAH network R² 0.918 versus 0.624. E8 match 70.8% and moonshine match 67.69%. TIG-15 C_avg ≈ 0.824. A zebrafish FAAH-OUT ortholog alignment.

## 6. ChatGPT consolidation dossier, read 2026-10-20

The upload is a text dump of `TI_Sigma_Cursor_Recovery_Bundle_2026-10-16.zip` (108 indexed sources, 105 `SHA256SUMS.csv` rows, 89 distinct hashes). The dump itself is not in git. Inventory, crosswalk, missing list, and file hashes are in `research/chatgpt_recovery/`. Notebooks were not executed. `.gz` and `.parquet` members were not decoded. No credit, settlement, NDA, resume, or financial workbook is in the bundle.

These rows are published numbers copied into CSVs. They are REPORTED transcriptions. They are not TI Sigma datasets and they are not replications.

| Ledger ID | Transcription | File in the dump | Limit |
| --- | --- | --- | --- |
| T27 | Mather 2023: 106 observers, about 66% in two preference islands | `TI_Sigma_Phase29_Elegance_Empirical_Evidence_Matrix.csv` | Pavlovia raw file not downloaded |
| T28 | PARA NIMA-trait SROCC 0.514 to 0.650. Five further Chen rows are in the same file. Mean absolute gain 0.076 on PARA and 0.023 on LAPIS | `TI_Sigma_Phase29_Personalization_Performance_Gains.csv` | Raw annotations not unpacked |
| T30 | LAPIS NIMA-trait SROCC 0.392 to 0.434. Separate published score: PAMELA user SROCC 0.4514 versus HPSv3 0.4019 | same gains CSV; `TI_Sigma_Phase30_PAMELA_Published_Personalization_Results.csv` | Gains are small. User-study totals are condition scores, not sample sizes |
| T31 | Celikors and Field mentioned; optimum cohort about 12% of sample | Phase 29 evidence matrix | No effect size and no raw ratings |
| T35 | Koyama 2026: 181 fish, learner fraction 46.4%, 804 event cells across 10 fish, danger reassignment 89.7%, safety 81.0%. Krug 2018: faah2a genotype F = 1.89 and genotype × nicotine F = 1.224, both P > 0.05; nicotine F = 81.51, P < 0.0001 | `TI_Sigma_Zebrafish_Phase4_empirical_audit.csv` | Not a TI feature test. Raw neural binaries still blocked. faah2a larval nervous system: not detected by whole-mount ISH |

Computational files recovered with the ceiling written in the source:

- Phase 31 formal economy: 20 math, 10 code, and 10 explanation pairs; equivalence rate 1.0. H_FE0 (“formal economy is the universal core of elegance”) is REJECTED in the decision CSV. Human elegance ratings are still required.
- Phase 45: M2 minus M1 cross-validated R² surplus 0.18345. The report says the outcome proxy was built from the elegance features.
- DailyDialog: 302 eligible dialogues. Mean real-partner gain over self-history −0.0747. Real versus permuted partners, permutation p = 0.0396. High-RAS half ρ = 0.023, p = 0.78. The report says this is not confirmation of an LCC constant.
- Nine-turn chatbot thread: mean reciprocal alignment 0.967. The report says this is not rigorous validation.
- Phase 8 gene screen: hand-assigned components. cnr1 screen score 0.778, faah2a 0.681. A screen weight, not a measured effect.
- A 15-edge itinerary audit (connected, chromatic number 4, unweighted diameter 2, weighted diameter 5.8599, Laplacian spectral gap 2.2073) is a different object from the missing TIG-15 clustering coefficient.

The 28 September archive still summarizes truth-label κ as about 0.906–0.92. It does not contain the rating matrices already in GitHub, and it does not resolve the product-branch prose κ 0.842. MIM `REAL_RUN_ANALYSIS.json` matches the counts already tied to GitHub Actions run 33466162168. Biological Phase 0 remains false.

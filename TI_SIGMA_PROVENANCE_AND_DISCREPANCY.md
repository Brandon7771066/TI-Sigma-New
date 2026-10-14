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
| 8C-mock | Hash mock rater | `src/ti_sigma_pipeline/mock_rater.py`; config `config/stage_a_v3.yaml`; report `results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json` | 21 items × 3 attempts | exact-match rate | 0.0 | REPORTED. See the generator note below |
| 8C-gaps | same JSON | same | same | mean absolute gap on a 0–10 integer scale | Goodness 4.032; eight Cs 3.143–3.778 | REPORTED |
| 8C-κ | Eight-C Fleiss κ or endorsement counts | — | — | — | — | ABSENT |

### Generator note

`stage_a_v3.yaml` sets `seed_strategy` to `vary_by_attempt` and `paid_collection_started` to false. `mock_rater.py` builds each score as `sha256(item, attempt) mod 11` for the Cs and Goodness (range 0–10). Changing the attempt index changes the hash. The generator is written to produce different integers on different attempts.

The expected absolute difference of two independent uniform draws on {0,1,…,10} is 3.636. The stored gaps sit in that neighborhood. An exact-match rate of 0.0 is what this generator produces. It is a smoke test of a varying hash. It is not a human reliability study, not an LLM endorsement study, and not evidence that the eight definitions are meaningless.

A `fixed` seed strategy exists in the same function and would repeat the hash. The stored run did not use it.

Conceptual validity, scoring reliability, discriminant validity, predictive validity, and incremental validity remain unmeasured for the Eight Cs. The draft definitions are the instrument to freeze before any of those studies.

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

Eight-C endorsement counts and Eight-C κ. A rating matrix for the product-branch κ 0.842 / macro-F1 0.891 paragraph. A truth-axis study other than B125. A GILE weight tuple G .30 / I .25 / L .25 / E .20. Any LCC result in which L_hybrid beats raw coupling on held-out real data.

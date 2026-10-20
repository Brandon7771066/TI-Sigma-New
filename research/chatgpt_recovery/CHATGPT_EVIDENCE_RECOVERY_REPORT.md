# ChatGPT library recovery report

Date: 2026-10-20.

Source read: the uploaded consolidation `TI_SIGMA_ALL_RECOVERED_RESULTS_FOR_CURSOR` (70,946 lines). It is a mechanical text dump of `TI_Sigma_Cursor_Recovery_Bundle_2026-10-16.zip`. Notebooks were not executed. Binary `.gz` and `.parquet` members are named and hashed in the dump and were not decoded. No credit report, settlement, NDA, resume, or financial workbook is in this bundle.

108 top-level sources are indexed. `SHA256SUMS.csv` lists 105 files and 89 distinct hashes. Names ending in `_2` that share a hash with an unsuffixed file are transfer duplicates, not new versions.

This report does not replace a result because a later summary sounds cleaner. Stored GitHub numbers stay stored GitHub numbers.

## What the bundle adds

**Literature tables that were only memories.**

- Mather 2023, as transcribed in `TI_Sigma_Phase29_Elegance_Empirical_Evidence_Matrix.csv`: 106 observers, repeated five-session maps, about 66% assigned to two islands, stability about 0.78 and 0.92. The Phase 29 note says the Pavlovia raw file was not downloaded. This is a published-result summary, not a TI Sigma dataset.
- Chen et al. personalization comparisons, `TI_Sigma_Phase29_Personalization_Performance_Gains.csv`. PARA NIMA-trait SROCC 0.514 to 0.650 (absolute gain 0.136). The same file has five more rows. LAPIS NIMA-trait is 0.392 to 0.434. All six listed gains are positive. Mean absolute gain is 0.076 on PARA and 0.023 on LAPIS. Raw PARA/LAPIS annotations were not materialized.
- PAMELA published scores, `TI_Sigma_Phase30_PAMELA_Published_Personalization_Results.csv`: user SROCC 0.4514 versus HPSv3 0.4019; pairwise accuracy 0.6631 versus 0.6427. Condition totals in the user-study CSV (1065, 1038, 1016, 959, 922) are reported scores, not sample sizes. Three repeated-image pairs are in the audit CSV; absolute differences are 0.86, 1.57, and 0.51 on a 4-point scale.
- Koyama 2026, `TI_Sigma_Zebrafish_Phase4_empirical_audit.csv` and the Phase 5 and Phase 13 CSVs: 181 fish tested, learner fraction 46.4%, 804 event cells across 10 fish, danger reassignment 89.7%, safety reassignment 81.0%. These are published figures copied into CSVs. The frozen itinerary says ordinary zebrafish baselines are blocked on raw neural binaries.
- Krug 2018, same Phase 4 CSV: faah2a genotype main effect F = 1.89, genotype by nicotine interaction F = 1.224, both P > 0.05. Nicotine itself F = 81.51, P < 0.0001. The transcription says this is no evidence of a gross locomotor impairment. It is not a new BlissGene experiment and not an FAAH-OUT ortholog result.
- Phase 6 priors record faah and faah2a expression in larval intestine and liver, and faah2a not detected by whole-mount in situ hybridization in the larval nervous system. Adult-brain qRT-PCR is cited as previously reported. That is a literature limit, not a knockdown.

**New computational artifacts, with their own ceilings.**

- Phase 31 formal economy: 20 math pairs, 10 code pairs, 10 explanation pairs. Equivalence or test-pass rate 1.0 in each arm. Formal-economy metrics separate a shorter form in 55% of the math pairs, and the mean relative cost reduction is 0.567 for code and 0.514 for explanations. Hypothesis H_FE0, “formal economy is the universal core of elegance,” is marked REJECTED in the decision CSV. Human elegance ratings are still required.
- Phase 45 tournament: M2 minus M1 cross-validated R² surplus 0.183; M3 minus M2 0.032; M3 minus a generic nonlinear model 0.200. The report says the outcome proxy was built partly from the elegance features, so the surplus is expected and is not empirical validation of GILE-E.
- DailyDialog persistence pilot: 302 eligible dialogues. Mean real-partner gain over self-history is −0.075 (self-history predicted better). Real partners were less harmful than permuted partners, permutation p = 0.0396. Pre-shift reciprocal coupling versus partner contribution: Spearman ρ = 0.214, p = 0.000177. Inside the high-coupling half that relationship is ρ = 0.023, p = 0.78. The report says this is not confirmation of an LCC constant. The exploratory cut near 0.032 is data-specific.
- Chatbot–user pilot: 9 hand-coded transitions from one thread. Mean reciprocal alignment 0.967. The report says hidden states were unavailable and the result is not rigorous validation.
- Phase 8 gene screen: hand-assigned component scores. cnr1 0.778, faah2a 0.681, faah 0.667. These are screen weights, not measured effects.
- Eight-C `analyze_stage_a.py` is an integrity checker for a future ratings table (Spearman, PCA, leave-one-out). The bundle does not contain that ratings table. `ratings_template.csv` and `sealed_manifest_template.csv` are templates.
- MIM v0.9 `REAL_RUN_ANALYSIS.json` matches the numbers already tied to GitHub Actions run 33466162168: 138,639 neurons, 15,091,983 synapses, 1,173 sugar spike rows, 317 active neurons, 20 of 21 published sugar IDs, and zero active overlap with PAM, PPL1, KC, and MBON. Biological Phase 0 is false. Exact replay passed only for two unstimulated 10 ms runs with zero spikes. The parquet spike table and the gzipped Codex tables were not decoded here.

**Graph self-audit, different from the remembered TIG-15 coefficient.**

The frozen itinerary reports a 15-edge catalog from URB 735: connected, chromatic number 4, unweighted diameter 2, weighted diameter 5.8599, Laplacian spectral gap 2.2073. It also says three edges named in prose are not in that catalog. The remembered clustering coefficient of about 0.824 is still not in this bundle.

## What stays as it was on GitHub

Truth-label κ 0.886 / 0.957 / 0.924 / 0.906 and MI 1.944 bits were recomputed from rating files already in the repository. This dossier does not contain those rating matrices. The 28 September archive still summarizes truth-label κ as about 0.906–0.92. It does not replace the product-branch prose that says κ 0.842, and it does not make those two figures the same test.

The Eight-C exact-match rate of 0.0 remains the hash mock with `vary_by_attempt`. This bundle does not add an endorsement study.

OpenNeuro ds007471 remains a negative for the hybrid LCC index. The bundle includes the pipeline and a README. It does not include a reversed result.

The September archive’s “20 machine-checked theorems” is still a summary. No Lean rebuild was run.

## Counts

| Item | Count |
| --- | --- |
| Top-level sources indexed | 108 |
| Files in `SHA256SUMS.csv` | 105 |
| Distinct hashes | 89 |
| Personal or financial files in the bundle | 0 |
| Notebooks executed | 0 |
| Binary members decoded | 0 |
| New raw neural recordings | 0 |
| New human rating matrices for the Eight Cs or for elegance | 0 |

`CHATGPT_IMPORT_MANIFEST.sha256` hashes the four sibling files in this directory. It does not hash the consolidation dump, and it does not hash itself.

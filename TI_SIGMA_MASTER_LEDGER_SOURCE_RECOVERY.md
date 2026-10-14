# TI Sigma master-ledger source recovery

Recovery date: 2026-10-14.

This file fills the 14 October 2026 master test ledger (`TI_Sigma_Master_Test_Ledger_Latest_Results_2026-10-14_2119.md`, entries T01–T38). The master ledger was an inclusive register of remembered scores. Many of those scores were marked unreconciled because the raw artifact had not been attached. This recovery attaches the artifact when one exists.

Governing standard: `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`. A stored JSON is REPORTED. It is not re-executed here. LLM raters are not human psychometrics. Simulations are not external benchmarks. Two reports of the same named test that disagree stay INCONSISTENT.

## Sources actually searched

| Source | What is in this workspace | What it contains |
| --- | --- | --- |
| GitHub, current branch | Result JSON under `analyses/`, papers under `papers/` | The GILE, HEM, truth-label, truth-axis, UOP, CHSH, and Mermin artifacts below |
| GitHub, `origin/product/truth-engine-alpha-1.1` at `58e78046` | Eight-C Stage A and Truth Engine phases C–F | Mock reproducibility and phase reports. Not on this branch’s working tree |
| ChatGPT extracts in-repo | `extracted_chatgpt/` (6 markdown files), `.agents/memory/lcc-chatgpt-source-reconciliation.md`, ChatGPT pastes under `attached_assets/` | Conceptual LCC/UOP/patent notes. They do not contain the NIMA, LAPIS, aesthetics, TIG-15, or “IBM score 710” tables |
| Perplexity | No conversation export is in the current upload set | The master ledger cites a 2026-08-02 Perplexity note on Eight-C freeze integrity. That note is not re-extractable from a file here |

ChatGPT is not a container of the Perplexity, Gemini, or VS Code numerical tables in this repository. Those tools are mentioned in memory notes and import guides. Their raw transcripts are not stored as result files.

## Recovered entries

### T02 — Eight-C Stage A mock reproducibility — REPORTED / NEGATIVE / MOCK

Branch `origin/product/truth-engine-alpha-1.1`, commit `58e78046`.

File: `experiments/eight_c_goodness_pilot/results/reports/ti_sigma_stage_a_v3_mock_reproducibility.json`.

- 21 item groups × 3 attempts.
- Exact match rate `0.0`.
- Mean absolute gaps: Goodness `4.032`; Coherence `3.460`; Consistency `3.746`; Continuity `3.143`; Concreteness `3.587`; Completion `3.524`; Criticality `3.460`; Closeness `3.397`; Choice `3.778`.
- This is a mock rater (`src/ti_sigma_pipeline/mock_rater.py`), not a human study and not an API-completion count.

### T03 — Earlier high κ / MI claims — partly recovered, and they are a different test

The high Fleiss κ figures in the corpus are truth-label agreement, not Eight-C score agreement. Do not replace T02 with them.

| Artifact | n | Metric | Value |
| --- | --- | --- | --- |
| `analyses/pass47_p46c_t45_4_mr_truth_kappa/results.json` | 100 propositions, 3 raters, 79 complete rows | Fleiss κ | `0.9057654075546717`, verdict CONFIRM |
| `analyses/fleiss_5tier_refined_NA_2026_05_27/results.json` | 500 gold rows | Fleiss κ | `0.9235267555511723` |
| same file, `MI_battery_5tier_refined` | 500 | MI | `1.744630528761272` bits; H_gold `2.3219`; H_joint `2.8780`; NMI `0.7548` |

T45-4 raters recorded in the JSON: `gpt_4o_mini`, `claude_sonnet_4_5`, `claude_haiku_4_5`. Majority agreement with the bucket labels: 0.937, 0.987, 0.975.

No Eight-C Fleiss κ or Eight-C mutual-information matrix was found.

### T04 / T07 — GILE and HEM rater battery — REPORTED / QUALIFIED

File: `analyses/pass77_gile_hem_battery_pilot/results.json`.

Fleiss κ, canonical strict parse:

| Axis | κ |
| --- | --- |
| G | 0.529 |
| I | 0.354 |
| L | 0.187 |
| E | 0.286 |
| D1 | 0.340 |
| D2 | 0.300 |
| D3 | 0.291 |
| D4 | 0.180 |

Pre-registered E vs D3: Pearson r `0.00998`, MI `0.0582` bits. Raters are LLMs. Only G clears 0.40.

### T05 — GILE nonredundancy — REPORTED / QUALIFIED

File: `analyses/gile_nonredundancy_test/results.json`. 52 rows, seed and permutation count in the file.

| Coord | ΔR² linear | permutation p | nonredundant |
| --- | --- | --- | --- |
| G | −0.0087 | 1.0 | no |
| I | 0.6182 | 0.002 | yes |
| L | −0.0012 | 0.794 | no |
| E | −0.0008 | 0.639 | no |

`honest_scope` in the file: one domain, tree-based family, suggestive only. E is a compression proxy in this test.

### T06 — GILE intelligence simulation — SIMULATION

File: `analyses/pass77_b121_gile_intelligence_truth/gile_intelligence_results.json`.

- Seed `20260617`, N `400000`.
- Prospective GILE AUC `0.8620142778715462`.
- Generic-g AUC `0.6987`.
- The circularity-trap block is in the same file and is a leakage illustration, not an empirical AUC.

### T09 — Truth-axis audit — REPORTED / QUALIFIED

File: `analyses/pass77_b125_four_truth_axes_audit/results.json`. 61 propositions, 3 LLM raters.

| Axis | κ |
| --- | --- |
| degree | 0.486 |
| modality | 0.436 |
| sep | 0.305 |
| authority | 0.213 |
| temporal | 0.487 |
| scope | 0.285 |
| subjectivity | 0.572 |

Separability and authority are below 0.40. This does not measure whether a proposition is true.

### T10 / T11 — Truth-label κ and MI — REPORTED, and the entropy clash is arithmetic

T10 is the T45-4 and 5-tier rows in the T03 table. κ ≈ 0.906 and κ ≈ 0.924 are those two files, not the truth-axis audit.

T11: the 5-tier MI battery stores `MI_bits = 1.7446` on n=500. That is the “≈1.75 bits” claim.

Entropy check from the same object: `H_gold = 2.3219` bits on a 5-symbol alphabet whose maximum is `log2(5) = 2.3219`. A “96.8% entropy” claim is not in this JSON. If someone divided MI by H_gold, `1.7446 / 2.3219 ≈ 0.751`, which is the stored NMI, not 96.8%. The 96.8% figure remains UNRECONCILED. It is not the same estimand as MI.

### T12 — Quantum truth-axis algebra — REPORTED / MIXED

File: `analyses/pass77_b143_quantum_truth_axes/results.json`.

Born and Tsirelson checks are structural. The anti-numerology guard assigns the constant-overlay no evidential weight. Do not cite the overlay as a confirmation.

### T13 — UOP abstention, TruthfulQA n=300 — REPORTED / NEGATIVE

File: `analyses/uop_abstention/results.json`.

- n `300`, accuracy `0.823333`.
- G* `0.9298734950321937`.
- Raw AURC `0.099856`.
- UOP AURC `0.122094`.
- `uop_better_than_baseline` is `false`.

### T14 — UOP GILE companion n=120 — REPORTED / NEGATIVE FOR PRIMARY

File: `analyses/uop_abstention/gile_results.json`.

- n `120`, scientific profile, MR1 gate `√2−1`.
- Selective accuracy `0.858333`, bootstrap 95% CI `[0.7917, 0.9167]`.
- UOP-minus-baseline AURC delta CI `[0, 0]`.
- High-GILE tail: `n_above_cap = 10`, accuracy CI `[1, 1]`.

### T15 — UOP phase-transition simulation — SIMULATION

File: `analyses/uop_phase_transition_v1/results.json`. Internal flags and a perturbation sweep. It does not overturn T13 or T14.

### T16 — Truth Engine Phase C — REPORTED / VALIDITY OPEN

Branch `58e78046`, file `products/truth_engine_alpha/results/benchmarks/phase_c_20260808_231016/benchmark_results.json`.

- Dataset 60, held out 12.
- Retrieval accuracy `0.1667`, macro-F1 `0.0571`.
- Module accuracy `1.0`, macro-F1 `1.0`.
- p `0.0008`, Cohen’s d `1.42`.

`PHASE_C_VERIFICATION_REPORT.md` on the same branch also records a coarser table (11/12 = 0.9167 vs 7/12 = 0.5833) and says the multiclass recomputation is the 1.0 / 0.0571 pair. Module accuracy 1.0 on an internal corpus is not truth-detection proof. The leakage memo says corpus leakage was not rechecked.

### T17 — Truth Engine Phase D — INCONSISTENT across two reports on the same commit

Both files are on `58e78046`.

| Report | Baseline | Module | p |
| --- | --- | --- | --- |
| `results/benchmarks/phase_d_20260812_224736/PHASE_D_STATISTICAL_ANALYSIS.json` | LLM-judge accuracy `0.6333`, macro-F1 `0.4952`, CI `[0.4308, 0.5474]` | accuracy `1.0`, macro-F1 `1.0` | `0.0032`, d `1.18` |
| `docs/recovery/PHASE_D_CERTIFICATION_REPORT.md` | simulated baseline macro-F1 `0.6722` | macro-F1 `0.8833`, Δ `+0.2111`, CI `[+0.0833, +0.3333]` | `0.0032` |

The certification report reclassifies the baseline as a simulated heuristic and the corpus as curated external benchmarks, not “30 naturalistic public AI outputs.” The 1.0 module score and the 0.8833 module score are not the same result. Neither is an independent reproduction.

Phase E, same branch, `PHASE_E_CERTIFICATION_REPORT.md`: frozen module macro-F1 `0.8833` vs Qwen2.5-3B `0.7140` on n=30 (p `0.0092`); n=130 macro-F1 `0.8875` vs `0.7250`.

### T18 — Phase F — REPORTED / ENGINEERING PASS

`PHASE_F_ACCEPTANCE_REPORT.md` on `58e78046`: 10/10 structural checks, mean time `0.037` s, date 2026-08-17. Citation traceability and review-gate checks. Not a truth-detection result.

### T19 — Invalid alpha benchmark — keep the supersession

The product-branch verification reports themselves say earlier 100% summaries used coarse accuracy and, in the invalid run, target-linked labels. The certification documents are the correction. Do not publish the superseded 100% as model performance.

### T21 / T22 — Algebra and Lean

Five floating-point identities were checked in the 2026-10-05 audit by `python3 lean4/verify_theorems.py` (9/9 printed checks). That run is floating-point, not a Lean compile. `lean` and `lake` are not on `PATH`. No project theorem `.olean` was found. “20 machine-checked theorems” stays REPORTED / AUDIT INCOMPLETE until a rebuild prints axioms.

### T23 — CHSH and Mermin — REPORTED, hardware jobs named, not a TI-specific prediction test

CHSH file: `analyses/pass77_b54_ibm_hw_chsh/results.json`.

- Backend `ibm_marrakesh`, job `d8fjqcg7jphs739md1a0`, 4096 shots.
- S `2.707`, classical bound `2`, Tsirelson `2.8284`, fraction `0.9571`.
- Correlators: a0b0 `+0.6929`, a0b1 `−0.6519`, a1b0 `+0.6367`, a1b1 `+0.7256`.

Mermin write-up: `papers/PASS_46_T45_2_GHZ5_HW_CONFIRM_PLUS_T45_6_LITERAL_INDETERMINATE_2026-05-11.md`.

- |M₅| `14.535` (signed composition `−14.535`).
- Classical bound 4, quantum max 16, jobs `d813ajg0bvlc73d0iclg`, `d813anmgbeec73ak1ijg`, `d813arfoha1c73bjs0j0`, 1024 shots each.
- Expectations: E_1Y `−0.9121`, E_3Y `+0.9082`, E_5Y `−0.8926`.

These are quantum-hardware measurements stored as reported results. They are not a prospective test that a TI Sigma constant predicted S or |M₅|.

### T32 — OpenNeuro ds007471 — REPORTED / NEGATIVE

Memory note `.agents/memory/lcc-uop-hyperscanning-empirical-test.md` and `analyses/lcc_uop_openneuro/` record an honest negative: the hybrid index did not beat raw coupling, and no trial reached the preregistered τ. Exact trial counts live in that analysis directory. This stays a negative.

### T33 — MIM Drosophila — REPORTED execution, biological gate open

Current `main` commit message at the 2026-10-05 audit: `b5955f25`, “Adapt published sugar anchor to FAFB v783 IDs.” The master ledger’s neuron and synapse counts (138,639 neurons; 15,091,983 synapses; GitHub Actions run 33466162168) are the run summary already recorded against that commit. Sensory propagation in that run is a model execution. It is not a learning result, not a valence result, and not evidence of noncomputability.

### T37 — Constants — INCONSISTENT formulas, unchanged

Three radiant-cap formulas remain in the corpus and must stay uncollapsed: `√(e/π) ≈ 0.9306` in `ti_sigma/constants.py`, `G* = √(1−e^{−2}) ≈ 0.92987` in the UOP JSON, and prose `1−e^{−e} ≈ 0.934`. MR1 `√2−1` is a different constant. ChatGPT reconciliation (`.agents/memory/lcc-chatgpt-source-reconciliation.md`) declines treating 0.6 and 0.707 as derived rungs.

## Still missing after GitHub, ChatGPT-extract, and Perplexity search

These master-ledger rows have no matching result JSON, CSV, or ChatGPT extract in the workspace. They stay REPORTED / RAW DATA MISSING. They are not confirmed by their absence from the search, and they are not refuted by it.

| ID | Claim as stated in the master ledger | Search result |
| --- | --- | --- |
| T01 | Eight-C LLM conceptual-validation metrics | Definitions exist on `58e78046` (`docs/conceptual/eight_c_operational_definitions_v3.md`). No endorsement counts or validity coefficients |
| T24 | E8 match ≈70.8%; moonshine ≈67.69% | Moonshine paper `papers/URB_793_MOONSHINE_BOK_CRYSTAL.md` is an open conjecture. The 70.8% figure in `PASS_77_B166` is a confounder screen-off rate, not an E8 match |
| T25 | TIG-15 C_avg ≈0.824; betweenness 0.625 / 0.089 / 0.036 | No TIG-15 result file with those values |
| T26 | “tralsebits ≈33 bits” tied to MI | Not derived in the 5-tier MI battery. Leave separate |
| T27 | n=106 observers, ~66% island preference | No participant file |
| T28 | NIMA SROCC 0.514→0.650 | No NIMA file. Word search hits “animal,” not NIMA |
| T29 | FAAH network R²≈0.918 vs 0.624 | FAAH papers are in-silico sweeps and pitch prose. This R² pair is not in them |
| T30 | LAPIS uniformly positive gains | No LAPIS result table |
| T31 | Art cohorts vs population means | No effect-size table |
| T34 | Halting / noncomputability | Design notes only. No oracle result |
| T35 | Zebrafish TIΣ cognitive result | Koyama acquisition notes exist from earlier Perplexity work. No decisive TI-specific statistic is stored as a result JSON |
| T36 | Crystal / Myrion certification benchmark | Formulas exist. No frozen benchmark with a null model |
| T38 | “100+/1300+ papers,” external architect review, IBM score 710 | URB #710 is a gravity paper title, not a score. No architect-review file and no deduplicated paper index with those counts |

## What not to merge

- Eight-C mock exact-match 0.0, truth-label κ≈0.91, truth-axis κ≈0.2–0.6, and invention-catalogue κ≈0.386 (`analyses/pass77_b92_inventions_concentration/results.json`) are four different estimands.
- Phase D’s 1.0 module macro-F1 and Phase D’s certified 0.8833 module macro-F1 are both on `58e78046`. Publish neither as the single Phase D number until the scoring script that produced each is identified.
- CHSH S=2.707 and Mermin |M₅|=14.535 are hardware reports. They do not validate a TI mapping.
- UOP’s negative AURC results stand next to the phase-transition simulation. The simulation does not reverse them.

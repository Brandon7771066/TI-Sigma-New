# TI Sigma Research Gaps

Audit date: 2026-10-05. Companion to `TI_SIGMA_EXPERIMENT_LEDGER.md`. This file lists what the repository does not establish. It does not propose new scientific claims.

## How to read the gaps

A gap is one of:

- a definition that has two incompatible values
- a theorem whose proof is an axiom or a `sorry`, or that has never been compiled here
- an experiment with no saved output
- a saved output whose raw input is absent
- a prose claim that has no script artifact

Status words match the ledger: VERIFIED, REPRODUCIBLE, REPORTED, UNREPRODUCED, INCONSISTENT, PLANNED.

---

## G1. Two incompatible LCC ladders

`lean4/TISigma.lean` defines

- `LCC_HIGH = 1/√2 ≈ 0.7071`
- `LCC_RADIANT = 1/φ ≈ 0.6180`
- `C_EMERICK = 1/(φ√2) ≈ 0.4370`

`ti_sigma/constants.py` defines

- `LCC_EMERICK = 1/√2`
- `LCC_TRUE = 1/φ`
- `LCC_HIGH ≈ 0.8512`
- `LCC_RADIANT = √(e/π) ≈ 0.9306`
- the same `C_EMERICK`

`lean4/verify_theorems.py` follows the Lean names. The hypercomputer (`oracle_bus.py`, `aperiodic_optimizer.py`, `hypercomputer.py`) follows the Python names. GILE weights also differ: Python `G=0.42` versus `bok_virus_engine.py`'s `ET`.

Until one file is designated canonical, every threshold comparison across Lean, Python, and prose is **INCONSISTENT**. The floating-point check of `√2·φ·C_EMERICK = 1` (9/9 in this audit) does not choose between the ladders. That identity is true by the definition of `C_EMERICK`.

## G2. No Lean verification artifact

42 project `.lean` files. Line-anchored scan: 298 theorems, 121 axioms, and real `sorry` terms in `MirrorPairing.lean`, `lean4_ti_sigma6/RiemannProof.lean`, `lean4_ti_sigma6/BSDProof.lean`, `lean4_submission/*`, and both `UOPGap.lean` copies.

`lean` and `lake` are not installed in this environment. No module `.olean` exists. Headers that say "formally verified" are not evidence.

The five TI Sigma identities in `TISigma.lean` have tactic proofs and no `sorry`. Their status is **UNVERIFIED** as Lean and **VERIFIED** as floating-point arithmetic under the Lean naming.

Open-problem files (Riemann, BSD, Hodge, Navier–Stokes, Yang–Mills, P vs NP, Collatz) prove lemmas about a gap condition and then assume the gap. They are not proofs of those problems.

## G3. Crystal order does not match the expected order

`analyses/crystal_b4_hamiltonian/results.txt` records spectral gap `λ₁ = 0.191440` on 57 vertices and 110 edges, and `Match: False` against the urb_645 order. The computed order is BEC < Supersolid < Mott < FQH-like < Fragmented.

That negative result is **REPRODUCIBLE** from the script. It is a gap for any claim that the unit-weight Hamiltonian realizes urb_645.

Signature tables (`tsc_signatures_pass9`) compare ring formulas to constants written in the script. They are not fits to external tables. The expansion control (`tsc_signature_expansion`) has a random-baseline probability about 0.44 of beating the observed mean deviation. That does not separate the ring from chance.

## G4. H4 is two hypotheses

`analyses/tsc_h4_sat/results.json`: ROC AUC `0.2678`, permutation p `1.0`, verdict weak, on 200 synthetic instances (seed `20260509`). Lower energy did not predict SAT.

`analyses/tsc_h4_sat_r20_replication/results.json`: inverted AUC `0.7318`, verdict CONFIRMED, on 200 instances (seed `31415927`), against a pre-registered threshold of 0.65.

The gap is not a missing re-run. The gap is that a confirmed inverted metric does not revive the original direction. Both artifacts should be cited together.

## G5. TIG has a graph invariant result and no epidemic result

`analyses/pass77_b68_meijer_octahedron_vs_ti/results.json` computes chromatic number 4 and clique number 4 on a 9-vertex graph. The chromatic-3 claim is refuted by that artifact.

`ti_sigma_graph.py` defines a different 57-node graph and H1–H5 epidemic comparisons. No output file is in the repo. Status **UNREPRODUCED**.

The H2 docstring (Crystal ≤ TI-G < ER) is not what the pass flag tests (Crystal ≤ ER). Fixing the flag is a code change; this audit did not make it. Until a run is stored, H1–H5 have no numbers.

## G6. No persistent-homology experiment

`analyses/` does not import `ripser` or `gudhi`. `analyses/pass51_t51_batch_exec/` stores a Vietoris–Rips **proxy**. Nested β₁ fields were not re-quoted in the ledger's own scan. Whatever those fields say, they are not a TDA library result.

Polar LF/HF in the same batch found `n_sessions_analyzed = 0`. The Polar JSON exports do not contain RR intervals. The predicted LF/HF value has no measurement.

## G7. GILE non-redundancy fails for G, L, and E on the real table

`analyses/gile_nonredundancy_test/results.json`, seed `20260628`, 52 real rows, 500 permutations:

| Axis | ΔR² linear | permutation p | non-redundant? |
| --- | --- | --- | --- |
| G | −0.0087 | 1.0 | no |
| I | 0.6182 | 0.002 | yes |
| L | −0.0012 | 0.7944 | no |
| E | −0.0008 | 0.6387 | no |

The artifact's own `honest_scope` limits this to one supervised-learning domain. Elegance, as coded, does not add information on that table. Positive and negative controls behave as constructed (E redundant in the negative control; all four significant in the positive control). The gap is the real-data claim, not the control machinery.

UOP abstention (`analyses/uop_abstention/results.json`) stores `uop_better_than_baseline=false` at overall accuracy `0.8233`. That is a stored negative result, not a missing analysis.

## G8. Zebrafish is a print label

`simulations/connectome_consciousness_test_v4_302neuron.py` prints an extrapolation at N=10000 labeled "Zebrafish". The function returns only the fit parameters and the 6- and 15-neuron Φ values. `connectome_consciousness_results_v4.json` has no zebrafish field. No zebrafish connectome is in the repo.

There is no zebrafish result to reproduce. Connectome scorecards v5 (`11/13`) and v6 (`12/13`) mix computed flags with criteria hard-coded `True` in `run_scorecard`. Those fractions are not 13 independent tests.

Biological pipelines that do have artifacts (DANDI rodent, IBL, plant auxin 7/7, Depresjon AUC `0.681` on 23+32) are **REPORTED**. Raw NWB is not in the tree. Plant-auxin inputs were not identified as an external table in this audit. Depresjon CSVs are present.

Mendi has one local session (`n_frames=2406`). Oura and Biowell exports have no result JSON.

## G9. Truth Engine has axioms and rater studies, not a frozen engine run

`truth_axis_evaluator/` has no committed `truth_axis_results.jsonl`.

`theories/TI_TRUTH_ENGINE_AXIOMS.md` rejects uncertainty `= 1 − MR` and the JSON template in the same file still writes `1.0 - MR_i`.

Rater studies are **REPORTED** and qualified by their own κ:

- four truth axes: authority κ `0.213`, sep κ `0.305` (below 0.4)
- MR IDC step 3: OpenAI accuracy `0.0`, κ `0.0`, Anthropic accuracy `0.933` on 15 items

Those files are not a validation of the Truth Engine.

## G10. Simulations stored; several headline claims are not

Re-runnable synthetic artifacts exist (UOP phase transition, active-pragmatism AUC advantage mean `0.0424`, moot-failure AUC `0.0347`, H4, crystal B4, GILE non-redundancy, 9-node TIG). This audit re-ran only `lean4/verify_theorems.py`.

Not stored:

- TI-G Monte Carlo
- zebrafish row
- Truth Engine batch
- `animal_testing_simulation.py`

Stored but not a measurement:

- `data/riemann_zeros/analysis_results.json` `all_on_critical_line=true` on a file of ordinates (the real part is assigned by the loader)
- `mood_amplifier_efficacy_results.json` mean correlation `1.0` on 100 subjects (inspect the generator before citing)
- README fine-structure "99.71%" (prose; Lean `derivation_accuracy` is `sorry`)

## G11. Data provenance gaps

| Data | Gap |
| --- | --- |
| `first_1million_zeros.txt` | values match Odlyzko's first zero, but the file has no header or checksum |
| `zeros_2million.txt`, `zeros_first_2million.txt` | not checksum-compared in this audit |
| DANDI NWB | streamed, not archived |
| OpenNeuro EEG | 32 headers, 0 `.eeg` files |
| Polar H10 | no RR series |
| IBM runs | verdicts stored; jobs not re-executable here |
| Personal biometrics | present; only one Mendi session is reduced |

`analyses/pass32_dandi_3way/results.json` is MIXED, and a parallel read of the file notes that dandiset 000053 numbers were injected from an earlier run. That injection is a provenance gap inside an otherwise saved artifact.

## G12. What would make a result move from REPORTED to VERIFIED

This audit does not require those steps. They are the missing evidence:

1. Install Lean and `lake build` the project files that claim to be sorry-free, especially `lean4/TISigma.lean` and `lean4_ns_uop_pass54_mathlib/NavierStokes/ToyDecay.lean`. Record the log.
2. Pick one LCC naming scheme and make the other file import it or rename it.
3. Re-run synthetic scripts in a clean directory so they do not overwrite artifacts, and diff against the committed JSON. Candidates with seeds already in the artifact: H4, H4-R20, crystal B4, GILE non-redundancy, UOP phase transition, myrion limit, 9-node TIG.
4. Archive DANDI asset hashes next to rodent and IBL results, or drop those verdicts to "not reproducible from this repo".
5. Either commit a TI-G Monte Carlo JSON or stop citing H1–H5.
6. Remove the zebrafish label from any claim list until a connectome file and a stored row exist.
7. Export a Truth Engine batch or describe the module as software without an experiment ID.

## G13. Counts

| Item | Count in this audit |
| --- | --- |
| Project Lean files (excluding `.lake/packages`) | 42 |
| `axiom` declarations (line-anchored) | 121 |
| Theorems re-checked in Lean | 0 |
| Floating-point checks passed | 9/9 in `verify_theorems.py` |
| `*result*.json` files scanned | 191 |
| Of those, re-executed | 0 |
| Crystal B4 match to urb_645 | false |
| Zebrafish numeric results stored | 0 |
| TIG epidemic artifacts | 0 |
| Persistent-homology library experiments | 0 |
| Operational 8C Goodness protocol in code | 0 |
| Zebrafish FAAH-OUT ortholog artifacts | 0 |
| Experiments with all four required model comparisons | 0 confirmed |

## G14. Integrity rules applied

The human-authored standard is `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`. The notes below are an AI-assisted reading of the repo against that standard.

**HYPOTHESIS is now a status.** Framework formulas, literature associations, and print-only extrapolations are not results. The zebrafish size label, the Radiant-cap formulas, FAAH-OUT translational language, and axiom-conditional Lean headlines are HYPOTHESIS.

**Thresholds stay uncollapsed.** `√2−1`, the several ~0.93 expressions (`sqrt(e/π)`, `√(1−e^{−2})`, `1−e^{−e}`), the name `T`, `φ`, the Born-shaped `1−e^{−2}`, and `C_EMERICK ≈ 0.437` are different objects. No experiment here shows they are the same quantity.

**Goodness is not the 8Cs in this tree.** The 2026-07-04 canonical note uses four facets (Coherence, Concreteness, Continuity, Consistency). Older notes use Clarity, Coherence, Compassion, Courage. The non-redundancy script's G feature is a bootstrap-stability proxy. Elegance in that script is `−log(tree node count)`, which overlaps compression. Book prose that calls Elegance "least action" overlaps HEM and pragmatic success. Those overlaps are flags, not measurements of Elegance.

**TIC and TIG are not frozen.** The Hamiltonian artifact is 57 vertices. The chromatic artifact is 9 vertices. `ti_sigma_graph.py` rebuilds a 57-node epidemic graph from the crystal rings and has no saved run. A prose relabel is not a canonical version pin. No biological prediction should cite either graph as canonical until a version is frozen.

**Biology.** No zebrafish FAAH-OUT ortholog, Jo Cameron genotype file, or therapeutic-outcome table is in the repo. `analyses/pharma_baseline/linear_baseline.py` hardcodes a Jo Cameron row `(100.0, 134.3)`. `analyses/pharma_baseline/results_2026-05-08.txt` compares those hardcoded numbers with simple baselines and records that the book claim of about 82% versus about 46% is not what this script computes (75% magnitude versus 66.7% mean-magnitude, margin +8.3 percentage points; directional accuracy ties the always-positive baseline). That negative comparison stays. It is not a human trial and not a zebrafish result.

**Model competition.** None of the indexed TI Sigma models was shown to beat all four of: a simple baseline, a conventional baseline, a capacity-matched generic model, and a null. Interesting spectral or graph patterns are not wins.

**Negative results.** Section 21.7 of the ledger lists failures that remain failures. The H4 inverted replication does not rewrite the original H4 hypothesis.

**Authorship.** Rules: human-authored in the chat that added them. Ledger, gaps, and this application: AI-assisted. The only check re-run in the audit remains `python3 lean4/verify_theorems.py`.

## G15. Master-ledger rows still without an artifact

`TI_SIGMA_PROVENANCE_AND_DISCREPANCY.md` separates the truth-label versions (κ 0.886 / 0.957 / 0.924 / 0.906 versus the product-branch prose κ 0.842) and records that the Eight-C mock hash was set to `vary_by_attempt`. `BLISSGENE_ZEBRAFISH_PRIMARY_STUDY_PROPOSAL.md` is a planned protocol, not a fish result. `TI_SIGMA_MASTER_LEDGER_SOURCE_RECOVERY.md` attaches T02–T18, T23, T32, and T33 to stored files. The 2026-10-16 ChatGPT consolidation, indexed in `research/chatgpt_recovery/`, adds literature transcriptions for T27, T28, T30, T31, and T35. Those rows are published numbers in CSVs. The participant maps, NIMA annotations, cohort ratings, and zebrafish neural binaries are still absent. Rows that remain without either a result file or a literature transcription are T01, T24, T25, T26, T29, T34, T36, and T38. Phase D is INCONSISTENT: the same commit stores module macro-F1 `1.0` and module macro-F1 `0.8833`. Eight-C Stage A mock exact-match `0.0` was recomputed from product commit `58e78046` in `analyses/eight_c_instrument_2026_10_20/`. It matches the CLI default seed `TI_SIGMA_STAGE_A_V3_MOCK` and does not match the registered seed. The stored corpus-balance prose is INCONSISTENT with the item JSONL. A common-factor test on the mock item means does not reject independence, and leave-one-out R² of Goodness on the eight Cs is negative. Directional contrasts remain blocked on the unread metadata CSV. It is not an Eight-C κ. The dossier’s `analyze_stage_a.py` is an analyzer with templates and no ratings table. Closest applicability is still unscored.

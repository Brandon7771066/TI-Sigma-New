# TI Sigma core specification

Version: 0.2.2-draft. Date: 2026-10-20. Status of this document: PROVISIONAL DEFINITION.

This file freezes names, historical definitions, and provenance. It is not a validation experiment and it does not replace a result file. A canonical name is not a validated construct.

The calibration registry on `origin/product/truth-engine-alpha-1.1` was inspected and left in place. It is a list of calibration entries (`products/truth_engine_alpha/calibration_registry/master_registry_v1.json`, commit `b3b2395d`, 2026-08-08). Its schema (`calibration_entry.schema.json`) requires `id`, `construct`, `version`, and `evidence_status`. It has no field for a conflicting definition. `RegistryResolver.get_gile_values` returns nothing in `CERTIFIED_ONLY` mode. That registry is the calibration record. This file is the definition record. Numbers below are copied from the cited source. None were recomputed for this freeze.

## Status words

| Status | Use in this file |
| --- | --- |
| CANONICAL TERMINOLOGY | A dated ruling or a named canonical note fixes the words. It does not fix empirical truth. |
| PROVISIONAL DEFINITION | A working definition with a source, not ratified as the only reading. |
| FORMALLY DERIVED | A formula or algebraic claim inside a paper. Not a measurement. |
| EMPIRICALLY TESTED | A named instrument, sample, and metric exist. |
| REPRODUCED | The stored arithmetic was checked against the rating file in the 2026-10-14 provenance pass. |
| MIXED | The same construct has both a supporting and a failing result, or raters agree on one facet and not another. |
| NEGATIVE RESULT | A stored test failed its own prediction. |
| UNRESOLVED | Two sources disagree, or the source of a remembered placement was not found. |

## Sources read before this file

| Commit | Date | What it added |
| --- | --- | --- |
| `84335786` | 2026-08-08 | Truth-label validation summary and a registry CSV (Git LFS pointer) |
| `b1053224` | 2026-08-08 | GILE, HEM:GILE, and domain-weight registry CSVs (Git LFS pointers) |
| `47cd3cce` | 2026-08-08 | Truth-axis registry CSVs (Git LFS pointers; the two files share one blob) |
| `f9c08a02` | 2026-08-08 | `GILEVector`, `TruthAxesQuaternionBlock`, `CANONICAL_TRUTH_LABELS` |
| `687167ab` | 2026-08-08 | `HEM_CANONICAL_DIMENSIONS` (eight names), domain profiles, PD decoder |
| `b3b2395d` | 2026-08-08 | Registry version 1.0.0, loader, resolver, schemas |

On this branch the companion evidence files are `TI_SIGMA_PROVENANCE_AND_DISCREPANCY.md`, `papers/GILE_DEFINITION_CANONICAL_2026-07-04.md`, `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`, and `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`.

## 0. Current operational reading (theory owner, 2026-10-20)

The statements in this section are the theory owner’s current reading. Status: PROVISIONAL DEFINITION, except the octonion split, which is HYPOTHESIS. They do not erase earlier versions, and they are not new measurements.

**Eight Cs.** The eight names are a matrix. Their weighting is deliberately unclear. A weight may be assigned to a C for a given problem when two conditions are both considered: the domain of that problem, and whether past weights were successful or applicable. Success here means harmonious with Goodness itself. No numeric weight vector is fixed by this ruling. The Eight-C model is not a validated manifold.

**HEM, operational list.** Four dimensions:

| Dimension | Owner definition, 2026-10-20 |
| --- | --- |
| Footprint | Existential impact on reality of the being or thing itself, for example mass or volume, distinguished from the imprint that being or thing leaves on reality through time, meaning indicators of existence. |
| Concrete Mechanisms | Physical laws. |
| Relational Meaning | Physical relationships between things. This dimension goes hand in hand with Concrete Mechanisms. |
| Form | Material essence of beings or things. |

URB #652’s Moral Presence / Conscious Meaning / Aesthetics list, and the product file’s Length / Width / Height / Time rows, stay historical. Spacetime is not part of this operational HEM list. It is named only inside the Existence hypothesis below, and that half is a work in progress.

**GILE weights.** The weight tuple varies with domain success. When a domain has no success history, the domain with the closest applicability is the one to use, even if that domain is broad. The same fallback applies to Eight-C weights. The stored tuples in section 1 remain historical specifications. The simulation tuple 0.30 / 0.25 / 0.25 / 0.20 stays `INFERRED_NOT_EXPLICIT`. These are not universal empirical weights.

**Truth axes.** The axes are the Real axis, the Imaginary axis, the Authority axis, and the Pragmatic axis. These four are hypothesized to represent a quaternion. Status of that algebraic claim: HYPOTHESIS. It does not adopt the quaternion defaults 0.35 / 0.25 / 0.20 / 0.20, and it does not adopt the code flag `VALIDATED_CLUSTER`. The 2026-05-07 five-axis list and the B125 names (degree, modality, separability, authority) stay historical instruments.

The Real axis consists of True, False, and Indeterminate. The Imaginary axis consists of everything which renders a proposition as having a deficit in HEM or GILE. N/A and the Authority axis are different geometric axes. N/A remains a fifth truth value. It is not placed on the Authority axis.

**Truth values.** The set is base-5: True, False, Indeterminate, Meta-Indeterminate, and N/A. N/A is a fifth truth value. The 2026-05-08 base-4 ruling is superseded as the current owner position and remains in the corpus as a historical ruling. This statement does not place N/A on the Authority axis. That placement still has no file citation (`CONFLICT-NA-PLACEMENT`).

**Indeterminate and Meta-Indeterminate.** An Indeterminate sentence stays Indeterminate unless there is a reason to update the truth value. A reason, in the owner’s later statement the same day, is new evidence from the Authority axis, or a change on the Pragmatic axis. A Pragmatic-axis change here means a benefit of considering the proposition true or false rather than Indeterminate. A Meta-Indeterminate statement may be resolved as Indeterminate. The owner’s example is a 45-degree door: a door that is both closed and not closed. The 2026-05-08 ruling used the 45-degree door as the definition of Indeterminate itself. This 2026-10-20 example uses that image for a resolution from Meta-Indeterminate into Indeterminate. Both sentences stay.

**Myrion and Myrion Resolution.** Myrion represents the ideal balance between truth and existence. Myrion Resolution is the process of resolving Meta-Indeterminate statements that seem incompatibly contradictory. Myrion Resolution also includes continuously updating truth values in general as new evidence arrives. A Myrion Resolution can also be carried out between the Real axis and the Imaginary axis, to arrive at an overall conclusion on a proposition’s truth value.

**GILE–HEM bijection.** The bijection between the four GILE dimensions and the four operational HEM dimensions is provisionally maintained as a hypothesis. Status: HYPOTHESIS. It has not been formally proven. It is not a demonstrated bijection. The hypothesized pairing is the parallel order in which the two lists are written in this specification:

| GILE | Operational HEM |
| --- | --- |
| Goodness | Footprint |
| Intuition | Concrete Mechanisms |
| Love | Relational Meaning |
| Elegance | Form |

This correspondence is not a claim about slot order. URB #652 remains a different formula: Intuition and Love share one HEM slot there, so that formula is not this bijection. The B82 figure pairs Intuition with a precision sector, Love with entanglement, and Elegance, there still named Environment, with symmetry. That figure is not this pairing.

**Sixteen coordinates.** Their structure is unclear. The hypothesis is two octonions. Truth is hypothesized to be an octonion of GILE’s four dimensions together with the four truth axes. Existence is hypothesized to be another octonion of the four operational HEM dimensions together with four spacetime dimensions. The order of the eight slots in either octonion has not been determined, and no particular order is expected. No spacetime dimension has been speculated to map onto another construct. An earlier intention to integrate string theory’s dimensions later remains only that intention. It is not a mapping. This hypothesis does not fill the length-8 arrays in `myrion_16d_vector.schema.json`, and it does not choose `PROPOSED_SEDENION` over `R16_VECTOR`.

**Fleiss κ certification.** A Fleiss κ study is to be replicated or thoroughly checked before it is certified exact. That rule applies to `REG_TL_001`, whose product-branch status is still `CERTIFIED_EXACT`. This specification does not edit `master_registry_v1.json`. The 2026-05-27 arithmetic checks against stored rating files remain what they were. Those checks are not a replication, and they do not confer certified-exact status.

## 1. GILE

Canonical name: GILE. Aliases: GILE tetrad; 2022 gloss “Goodness, Intuition, Love, Environment” (`content/researcher_profiles.md`). The 2026-06-16 rename B116 sets E to Elegance and keeps Environment as a gloss (`papers/GILE_DEFINITION_CANONICAL_2026-07-04.md`, section 5).

| Dimension | 2026-07-04 canonical note | Earlier or other reading | Kind | Status |
| --- | --- | --- | --- | --- |
| Goodness (G) | Real benefit. The only composite. `G_raw = mean` of four facets. | Integrity rules: operationalized through the Eight Cs. Product Eight-C draft: Goodness is a separate scalar, not computed from the eight. | conceptual, with a stated scoring rule in the 2026-07-04 note | CANONICAL TERMINOLOGY for the four-facet note. The Eight-C reading is a conflict (`CONFLICT-EIGHT-C`). |
| Intuition (I) | Certainty: calibrated inner rightness. Single note on [0, 1]. | URB #652 decomposed I into four averaged sub-dimensions. B187 says those survive as informal facets, not as an average. | conceptual | CANONICAL TERMINOLOGY as of 2026-07-04. Sub-dimension average is superseded on paper, not deleted. |
| Love (L) | Abstract binding between things. Alias “Level” in the same note. | URB #652 four-sub-dimension average, superseded the same way. | conceptual | CANONICAL TERMINOLOGY as of 2026-07-04. |
| Elegance (E) | Beauty of form. The note the other three leave unfinished. | Environment (2022). MDL or `−log(tree node count)` in the non-redundancy script. Book prose has called it least action. | conceptual. The non-redundancy feature is a code proxy. | CANONICAL TERMINOLOGY for the beauty reading. Overlaps with HEM, correspondence, pragmatic success, and Consistency are flags (`TI_SIGMA_RESEARCH_INTEGRITY_RULES.md`). |

Intended target: the substance of a truth, as the Truth pillar beside HEM as Existence (`papers/GILE_DEFINITION_CANONICAL_2026-07-04.md`).

Aggregation in that note:

`GILE = w_G G + w_I I + w_L L + w_E E`, with `I`, `L`, and `E` scored directly and `G` the mean of its four facets.

Weight versions, each kept:

| ID | Tuple (G, I, L, E) | Source | What it is |
| --- | --- | --- | --- |
| GILE-W-ET | √2−1 ≈ 0.4142, 0.25, 0.18, 0.15 | `bok_virus_engine.py` `GILE_W`; the 2026-07-04 note. `papers/urb_576_gile_weights_origins_confirmation.md` writes G = 0.42 | Specification. The URB #576 paper asks whether the numbers were measured. No fitting experiment is in that file. |
| GILE-W-SCI | 0.35, 0.40, 0.15, 0.10 | 2026-07-04 note, “scientific/epistemic” domain profile | Stated domain renormalization. Not a fit. |
| GILE-W-MKT | 0.20, 0.25, 0.25, 0.30 | `gsa_core.py` `gile_weights` | Market-engine default. |
| GILE-W-SIM | 0.30, 0.25, 0.25, 0.20 | `f9c08a02` `GILEVector` defaults; `b3b2395d` entry `REG_GILE_001` | Simulation parameters. `evidence_status` in both places is `INFERRED_NOT_EXPLICIT`. Role in code: `SIMULATION_DEFAULT`. Production status: `RESEARCH_ONLY`. The resolver refuses to return them in `CERTIFIED_ONLY` mode. The registry cites `gile_universal_language_analysis.py` and the line `DEFAULT_GILE_WEIGHTS = {"Goodness": 0.30, "Intuition": 0.25, "Love": 0.25, "Elegance": 0.20}`. That file is on the product branch. These are not universal empirical weights. |

Constants named next to GILE, and not the same object: Emerick threshold `ET = √2−1` as an MR1 gate on `G_raw`; radiant cap `G* = √(1−e^{−2}) ≈ 0.92987` in the 2026-07-04 note. Other ~0.93 expressions remain uncollapsed in `TI_SIGMA_PROVENANCE_AND_DISCREPANCY.md`.

Empirical battery, separate from every weight tuple: `analyses/pass77_gile_hem_battery_pilot/results.json`. Fleiss κ on LLM raters: G 0.529, I 0.354, L 0.187, E 0.286. Only G clears the file’s 0.40 line. Status: EMPIRICALLY TESTED, MIXED. Non-redundancy on 52 rows (`analyses/gile_nonredundancy_test/results.json`): I ΔR² 0.6182, permutation p 0.002. G, L, and E were not shown non-redundant there. The file’s own scope note says one model-selection domain.

Falsifiable questions already written, still open in the cited notes: GSN-1-F1 (only G decomposes), FCG-1-F1 (four Cs live under G), ELEG-F1 (Elegance rename).

## 2. HEM

Canonical name: HEM, Holistic Existence Matrix. The operational list is the four definitions in section 0. Those four words are also the first four entries of `HEM_CANONICAL_DIMENSIONS` in `687167ab` `hem.py`. The owner’s 2026-10-20 glosses are the current reading of the words. They are not the only HEM list in the corpus.

| Version | Dimensions | Source | Status |
| --- | --- | --- | --- |
| URB #652 operationalization | D1 Existence Footprint; D2 Moral Presence (from GILE-G, privation floor); D3 Conscious Meaning / Valence (from I+L); D4 Aesthetics (from E). Default weights “equal pending empirical calibration.” | `papers/urb_652_gile_hem_full_operationalization.md` Part 6,  formula `HEM = Σ w_Di · Di` | PROVISIONAL DEFINITION with formulas. D2–D4 are defined from GILE, so this list is not an independent existence measurement. |
| Product model, 2026-08-08 | Footprint, Concrete Mechanisms, Relational Meaning, Form, and also Length, Width, Height, Time. Maturity on each row: `TIER_0_CONCEPTUAL`. | `687167ab` `hem.py` | CANONICAL TERMINOLOGY inside that file’s name `HEM_CANONICAL_DIMENSIONS`. The extra four spatial-temporal names conflict with both the four-name freeze and URB #652 (`CONFLICT-HEM-DIMS`). |
| EAR consolidation | A different reduction that treats Relational Meaning as already inside Love. | `theories/HEM_4D_EXISTENCE_EAR_CONSOLIDATION.md` | A proposed reduction. Not the URB #652 list. |
| Market aggregate | D1 0.25, D2 0.25, D3 0.30, D4 0.20 | `gsa_core.py` FDE combination, as recorded in the provenance note | A weight tuple for a four-slot HEM. Not a definition of the slots. |
| EEG aggregate | Equal weights, D2 inverted, D4 peaked at 0.5 | `.agents/memory/hem-8d-dimensions-overview.md` as cited by the provenance note | A third formula. |

Intended target: how much something exists, kept as a pillar beside GILE (`urb_652` Part 6; 2026-07-04 note).

The rater battery’s HEM κ values are D1 0.340, D2 0.300, D3 0.291, D4 0.180 (`analyses/pass77_gile_hem_battery_pilot/results.json`). E versus D3 Pearson r 0.010 in the provenance note. Status: EMPIRICALLY TESTED, and the agreement is below the battery’s 0.40 line on every HEM slot. That is not a validation of any HEM definition.

## 3. Eight Cs

Canonical names for this freeze: Coherence, Consistency, Continuity, Concreteness, Completion, Criticality, Closeness, Choice.

The instrument text is `experiments/eight_c_goodness_pilot/docs/conceptual/eight_c_operational_definitions_v3.md` on commit `58e78046` (`origin/product/truth-engine-alpha-1.1`). Status label inside that file: `NEW_CANONICAL_DRAFT`. Each C has a definition, an operational question, a target, and high / mid / low anchors. The mock rater scores them as integers 0–10 by `sha256(item, attempt) mod 11` (`stage_a_v3.yaml`: `seed_strategy: vary_by_attempt`, `paid_collection_started: false`). Exact-match rate of that mock is 0.0. Status of the mock: a smoke test, not a reliability study.

| Reading of “C” | Members | How Goodness uses them | Source |
| --- | --- | --- | --- |
| Four Cs of Goodness | Coherence, Concreteness, Continuity, Consistency | `G_raw` is their mean | `papers/GILE_DEFINITION_CANONICAL_2026-07-04.md` |
| Truth-presentation quartet | Includes Completeness rather than the Goodness fourth C | Explicitly not G | Same note, citing B171 |
| Older quartet | Clarity, Coherence, Compassion, Courage | Named in older notes | `TI_SIGMA_RESEARCH_GAPS.md` |
| Eight Cs | The eight names above | v3 says Goodness is scored separately, as a circularity safeguard | Product file at `58e78046` |
| Integrity rule | “the 8Cs” | “Goodness must remain operationally defined through the 8Cs” | `TI_SIGMA_RESEARCH_INTEGRITY_RULES.md` |

The Eight-C draft and the integrity rule disagree about whether Goodness is computed from the Cs. The 2026-07-04 note uses four facets, not eight. The 2026-10-20 owner reading treats the eight names as a matrix and leaves the weighting deliberately unclear, with domain-conditional weights allowed only by the rule in section 0. Status of the Eight-C model: PROVISIONAL DEFINITION. The Eight-C model is not a validated manifold. Validity and any unified-manifold claim are UNRESOLVED. Terminology in this section does not validate the model.

No Eight-C Fleiss κ or endorsement table is in the repository. Conceptual, scoring, discriminant, predictive, and incremental validity are unmeasured.

## 4. Truth axes

The current axis names, by the 2026-10-20 owner statement, are Real, Imaginary, Authority, and Pragmatic. Those four strings are also the fields of `TruthAxesQuaternionBlock` (`f9c08a02`): defaults 0.35, 0.25, 0.20, 0.20, notation `Q = Real + i*Imaginary + j*Authority + k*Pragmatic`. The owner statement selects the names. It does not select those default numbers. The same class sets `cluster_validation_status` to `VALIDATED_CLUSTER` and `individual_axis_status` to `PARTIALLY_VALIDATED`. This specification does not adopt that cluster string as an empirical result. No rating matrix for those four weights is in the registry JSON. `get_truth_axes` returns nothing in `CERTIFIED_ONLY` mode.

Other axis lists that remain in force as historical versions:

| Version | Axes | Source | Status |
| --- | --- | --- | --- |
| Five-axis review, 2026-05-07 | (1) PD real degree, (2) PD imaginary / MI modality, (3) MR truth labels, (4) τ/δ separability, (5) Authority Axis as operative authority | `papers/TI_SIGMA_FIVE_AXIS_TRUTH_RICHNESS_REVIEW_2026-05-07.md` | A review of prior axes. Axis 3 in that table is the label set, not a fifth numeric coordinate. |
| Four-axis refinement | (1) PD as one spectrum (real degree + imaginary modality), (2) MR truth labels, (3) τ/δ separability, (4) Authority Axis | `replit.md`, refinement #8 | CANONICAL TERMINOLOGY for that bullet. Falsifiers CCG-1-F1 and NPA-1-F1 are OPEN. |
| B125 audit names | degree, modality, sep, authority. Extra candidates: temporal, scope, subjectivity | `analyses/pass77_b125_four_truth_axes_audit/results.json`, 2026-06-23, 61 propositions, 3 LLM raters | EMPIRICALLY TESTED. Fleiss κ: degree 0.486, modality 0.436, sep 0.305, authority 0.213. The file’s own deviations say LLM raters stand in for humans. MIXED. |
| Quaternion block | Real, Imaginary, Authority, Pragmatic | `f9c08a02` | Code defaults. Not the B125 axis names. `CONFLICT-TRUTH-AXES`. |

B125’s “authority” is one audited coordinate. The 2026-05-07 Authority Axis is “operative authority granted to a proposition” (`papers/AUTHORITY_AXIS_AA_2026-05-07.md` is the standalone citation in the five-axis review). The quaternion’s `j*Authority` is a third use of the word. They are not collapsed here.

Pragmatic, as a axis name in the quaternion, is not the same object as PSM-1 (pragmatic sense-makeability, candidate, not ratified) or as “pragmatic success,” which the integrity rules forbid folding into Elegance.

## 5. Truth values

The five names requested for this freeze are True, False, Indeterminate, Meta-Indeterminate, and N/A. Experiments and rulings do not all use those five as one set.

### 5.1 What the 2026-05-27 rater prompt actually said

File: `analyses/fleiss_binary_vs_5tier_1000_2026_05_27/run_raters.py`. This is the semantics of the stored κ studies. It is not the 2026-05-08 ruling.

| Code | Prompt text | Instrument result |
| --- | --- | --- |
| T | Well-established as true given common knowledge. | 5-tier Fleiss κ 0.8864627351935783 on 1,000 statements, 3 LLM raters. REPRODUCED against `ratings_5tier.json`. |
| F | Well-established as false given common knowledge. | Same battery. Binary forced {T, F} κ 0.5982903794731804 on 998 rows. REPRODUCED. |
| I | Has a determinate truth-value that cannot be determined from available knowledge. | Same 5-tier battery. |
| MI | Incoherent or self-contradictory when fully entertained. The prompt says this is not merely surprising or false. | Same battery. |
| NA | Category mistake: the predicate does not apply in a way that even yields a tractable contradiction. Example in the prompt: “the number 7 smells like vanilla.” | Same battery. A later refined-NA run on 500 gold rows reports κ 0.9235267555511723 and MI 1.744630528761272 bits (`analyses/fleiss_5tier_refined_NA_2026_05_27/results.json`). REPORTED. |

Gold-subset mutual information is 1.9437953142882853 bits, NMI 0.8421045197883477, n=499 (`spectrum_distinctness_results.json`). REPRODUCED. That 0.842 is normalized mutual information, not a Fleiss κ. The fraction of gold entropy is 0.83715.

T45-4, a different run: κ 0.9057654075546717 on 79 complete rows of 100 (`analyses/pass47_p46c_t45_4_mr_truth_kappa/results.json`). REPORTED.

Raters in these files are language models. The studies are not human psychometric validations.

### 5.2 The 2026-05-08 ruling, which is a different set

`papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` settles the base set as four labels: True, False, Indeterminate, Meta-Indeterminate. N/A is not a fifth base label in that ruling. Moot is a meta-truth (MT-B1), not a base label. Tralse is a quality carried by coherent labels, not a fifth value.

| Label | Ruling gloss | Conflict with the rater prompt |
| --- | --- | --- |
| True | Passes MR1, MR2 resolves toward true, tralse-quality still embedded. Classical pure-true is rejected. | The prompt uses common-knowledge truth. |
| False | Passes MR1, MR2 resolves toward false, tralse-quality still embedded. | The prompt uses common-knowledge falsity. |
| Indeterminate | Passes MR1, MR2 holds a coherent balance. The ruling says this is not ignorance and not missing data. | The prompt defines I as unknown though determinate. |
| Meta-Indeterminate | Fails MR1. Formal line: MI(P) ⟺ τ(P) ∧ ¬τ(P). “Always some form of nonsense.” | The prompt’s examples include a married bachelor and a four-sided triangle, which the ruling would also call nonsense, but the ruling’s operator is the identity clash, not the prompt’s “incoherence when entertained.” |

Status of the ruling: CANONICAL TERMINOLOGY for the base-4 set inside that paper, as of 2026-05-08. The 2026-10-20 owner statement supersedes it for current use: the set is base-5, and N/A is a fifth truth value. The paper stays in the corpus. The rater studies already used five codes, with their own glosses. All three readings stay.

### 5.3 Product-branch glosses, marked as proposed relative to the ruling

`f9c08a02` `CANONICAL_TRUTH_LABELS` and `84335786` `TRUTH_LABEL_VALIDATION_SUMMARY.md` use five labels. Their glosses differ from both the ruling and the rater prompt. They are recorded here as PROVISIONAL DEFINITION text on that branch, not as verified historical definitions of the experiments:

| Label | Product gloss (`truth_labels.py` / the summary) |
| --- | --- |
| TRUE | Factually supported, verified positive evidence. |
| FALSE | Factually refuted, verified counter-evidence. |
| INDETERMINATE | Unverified because empirical data are missing or incomplete. |
| META-INDETERMINATE | Structurally unresolvable in the primary frame; the summary adds paradox, self-reference, or under-specified context “requiring Myrion Resolution.” |
| N/A | Inapplicable or out of domain. |

`REG_TL_001` in `master_registry_v1.json` copies the sentence “Fleiss kappa measured at kappa = 0.842 across N=1,200 expert annotations” and sets `evidence_status` to `CERTIFIED_EXACT`, tier `TIER_3_EXTERNAL_BENCHMARK`, historical date 2025-11-15, source path `products/truth_engine_alpha/docs/recovery/TRUTH_LABEL_TAXONOMY_SPEC.md`. The same product line later records, on `58e78046`:

- `PHASE_A_CERTIFICATION.md`: the “96.8% of entropy” line is `MATHEMATICALLY_INCONSISTENT`. The note says 96.8% is relative to an empirical entropy of about 2.004 bits, while MI / log2(5) is about 83.55%.
- `PHASE_C_VERIFICATION_REPORT.md`: κ 0.842 was copied from Phase A text and removed from the Phase C annotation results. Phase C’s own annotation status there is `SINGLE_ANNOTATOR_NO_INTERRATER_METRIC`.

No N=1,200 rating matrix is in this repository. Status of the 0.842 / 1.94 / 0.891 / 96.8% cluster: REPORTED TEXT, and the entropy percentage is already flagged inconsistent on its own branch. It does not replace the 2026-05-27 batteries (`CONFLICT-TRUTH-LABELS`).

### 5.4 How axes and labels are related, without settling the map

Stored relations:

- Five-axis review: the label set is axis 3. The Authority Axis is axis 5 and is not defined there as the home of N/A.
- B147 / `replit.md`: {True, Indeterminate, False} are real-dominant; Meta-Indeterminate is imaginary-dominant with a nonzero real residue; N/A is `j`-dominant (hyperimaginary applicability) with a wildcard real coordinate. The earlier pin of N/A at the origin is withdrawn. Falsifier CCG-1-F1 is OPEN: a common N/A case with a determinate real degree would weaken the wildcard clause. Anchor: `papers/PASS_77_B147_UOP_THIRDS_EXPANDED_BASIC_I_FORM_CONCAVE_PROGRAM_AND_COMPLEX_CONFINEMENT_GEOMETRY_2026-06-25.md`.
- Quaternion code names the `j` slot Authority. B147 names the `j` slot applicability. Identifying those two names is `CONFLICT-NA-PLACEMENT`, not a finding.
- A sentence that places the N/A label on the Authority Axis was not found in `papers/AUTHORITY_AXIS_AA_2026-05-07.md` or in the five-axis review. The placement is preserved as a historical claim named by the specification request. Its file citation is UNRESOLVED. It is not treated as empirically validated.

Pipeline sentence in `replit.md`: N/A, then MI, then True / False / Indeterminate. That is an ordering claim in the architecture bullet, not a result from the rater studies.

### 5.5 Owner reading, 2026-10-20

Current set: base-5, as in section 0. An Indeterminate assignment stands until there is a reason to update it. A reason is new evidence from the Authority axis, or a Pragmatic-axis change: a benefit of considering the proposition true or false rather than Indeterminate. Meta-Indeterminate may be resolved to Indeterminate, with the 45-degree door given as an example of a state that is both closed and not closed. Myrion Resolution covers that resolution of an apparent incompatibility, the later updating of any truth value when evidence arrives, and a resolution between the Real axis and the Imaginary axis that yields one conclusion about the proposition. Myrion is the ideal balance between truth and existence. None of these sentences replaces the 2026-05-27 prompt inside the stored κ files.

## 6. GILE–HEM mapping and higher-dimensional architecture

These are theoretical claims. None is encoded here as a demonstrated bijection.

| Proposal | What it says | Source | Status |
| --- | --- | --- | --- |
| URB #652 coupling | D2 is taken from G, D3 from I+L, D4 from E, D1 from a physical footprint formula. I and L share one HEM slot. | `papers/urb_652_gile_hem_full_operationalization.md` §§6.3–6.4 | FORMALLY DERIVED inside that paper. Not a bijection. Not independently measured. |
| Complement-couple figure | A four-couple picture, with G paired to Existence Footprint. | `analyses/pass77_b82_bok_unification/make_figs.py` commentary | A figure claim. |
| Domain HEM:GILE ratios | Physics 0.70/0.30, Mathematics 0.60/0.40, Philosophy 0.20/0.80, Software 0.50/0.50. Ratios 2.333, 1.500, 0.250, 1.000. | `687167ab` `profiles.py`; `b3b2395d` `REG_HEM_GILE_001` | The registry’s own status string is `DERIVED_NEWLY_FROM_RECOVERED_VALUES`, which is not a member of the `EvidenceStatus` enum in `f9c08a02`. The note says the ratios were divided from component weights during recovery. Not a dimension bijection. |
| 64-dimensional matrix | 4 GILE × 4 axes × 4 labels, with N/A folded into MI for a 4³ closure. | `replit.md` PDR-1 bullet; B108 | PROVISIONAL. B147 says that fold is the wrong identification of N/A and MI. |
| Myrion 16-vector | `existence_byte` length 8, `truth_byte` length 8. `algebra_type` enum `PROPOSED_SEDENION` or `R16_VECTOR`. Baseline fixed to `R16_VECTOR`. | `b3b2395d` `myrion_16d_vector.schema.json` | The schema’s own algebra name says PROPOSED. Not a demonstrated sedenion model. |
| Quaternion block | Four truth-axis slots as a quaternion. | `f9c08a02` | Code notation. See section 4. |
| Two octonions | Truth = GILE plus the four truth axes. Existence = the four operational HEM dimensions plus four spacetime dimensions. Sixteen coordinates in all. Structure otherwise unclear. Existence’s spacetime half is unfinished; string theory’s dimensions are an intended later integration and are not listed. | Theory owner, 2026-10-20, section 0 | HYPOTHESIS. Not a filled coordinate array. Not a choice of `PROPOSED_SEDENION`. |
| GILE–HEM bijection | Goodness–Footprint, Intuition–Concrete Mechanisms, Love–Relational Meaning, Elegance–Form. | Theory owner, 2026-10-20, section 0 | HYPOTHESIS. Provisionally maintained. It has not been formally proven. It is not a demonstrated bijection. |

`CONFLICT-HEM-GILE-MAP`: the hypothesized pairing is Goodness–Footprint, Intuition–Concrete Mechanisms, Love–Relational Meaning, and Elegance–Form. It is provisionally maintained as a hypothesis and has not been formally proven. URB #652 does not state that bijection, because Intuition and Love share one slot there. The B82 couples use different HEM names. The product HEM list has eight names, so that longer list is not this bijection either. The two-octonion hypothesis is a separate hypothesis. Slot order inside an octonion is not this pairing, and no particular slot order is expected.

## 7. Conflict register

Section 0 records the 2026-10-20 owner disposition. The historical definitions stay in the corpus. A disposition is not a measurement.

| ID | Conflict | Left open because |
| --- | --- | --- |
| CONFLICT-GILE-NAME | Elegance versus Environment | B116 renames E and keeps Environment as a gloss. Older public copy still says Environment. |
| CONFLICT-GILE-WEIGHTS | ET / 0.25 / 0.18 / 0.15, versus market 0.20 / 0.25 / 0.25 / 0.30, versus simulation 0.30 / 0.25 / 0.25 / 0.20 | Three specifications. The simulation tuple is `INFERRED_NOT_EXPLICIT`. None is a fitted universal weight. Owner disposition: the tuple in use varies with domain success. No new numeric tuple was supplied. |
| CONFLICT-EIGHT-C | Four Cs under G, versus eight Cs with Goodness separate, versus the integrity rule that Goodness is the eight Cs, versus Clarity / Coherence / Compassion / Courage | Four lists. The eight-C file is `NEW_CANONICAL_DRAFT`. No endorsement study. Owner disposition: the eight names are a matrix and the weighting is deliberately unclear. |
| CONFLICT-HEM-DIMS | URB #652’s Footprint / Moral Presence / Conscious Meaning / Aesthetics, versus Footprint / Concrete Mechanisms / Relational Meaning / Form, versus those four plus Length, Width, Height, Time | The product file calls eight names canonical. URB #652 defines a different four, and ties three of them to GILE. Owner disposition: the operational list is the four glosses in section 0. Spacetime is reserved for the unfinished Existence octonion. |
| CONFLICT-HEM-GILE-MAP | Bijection claim versus URB #652’s many-to-one (I and L into D3) versus domain ratios that are pillar weights | No validation study of a bijection is in the registry. Owner disposition: Goodness–Footprint, Intuition–Concrete Mechanisms, Love–Relational Meaning, Elegance–Form, provisionally maintained as a hypothesis. Not formally proven. URB #652 stays a different formula. |
| CONFLICT-TRUTH-AXES | Five-axis review, versus the four-axis refinement (degree, labels, separability, authority), versus the quaternion (Real, Imaginary, Authority, Pragmatic) | B125 tested the refinement names, not the quaternion weights. The code’s `VALIDATED_CLUSTER` flag has no matrix here. Owner disposition: current names are Real, Imaginary, Authority, and Pragmatic, hypothesized as a quaternion. Real consists of True, False, and Indeterminate. Imaginary consists of everything which renders a proposition as having a deficit in HEM or GILE. Numeric defaults stay unadopted. |
| CONFLICT-NA-PLACEMENT | N/A as a fifth rater code, versus base-4 with N/A outside the base set, versus `j`-dominant applicability, versus a remembered placement on the Authority axis | The Authority-axis placement has no file citation in the sources searched. B147’s falsifier is OPEN. Owner disposition: N/A is a fifth truth value and a geometric axis different from the Authority axis. |
| CONFLICT-TRUTH-LABELS | Ruling glosses, versus the 2026-05-27 prompt, versus product glosses, versus κ 0.886 / 0.957 / 0.924 / 0.906 versus prose κ 0.842 | Different instruments. The 0.842 matrix is absent. 96.8% is already `MATHEMATICALLY_INCONSISTENT` on `58e78046`. Owner disposition: replicate or thoroughly check a Fleiss κ study before it is certified exact. The registry entry is not edited in this file. |
| CONFLICT-INDETERMINATE | Ruling: coherent balance, not missing data. Prompt: unknown though determinate. Product text: missing empirical data. | Three semantics. The κ studies used the prompt. Owner disposition: Indeterminate stands until new Authority-axis evidence, or a Pragmatic-axis change understood as a benefit of calling the proposition true or false rather than Indeterminate. Meta-Indeterminate may be resolved as Indeterminate. |
| CONFLICT-ELEGANCE | Beauty of form, versus Environment, versus an MDL / node-count proxy, versus HEM Form | Integrity rules require the overlap to stay flagged. |

## 8. What this freeze does not do

It does not change `master_registry_v1.json`, the rating files, or any result JSON. It does not treat LLM κ as human validation. It does not treat the Eight Cs as a validated manifold. It does not treat GILE-W-SIM as universal empirical weights. It does not treat a HEM:GILE bijection as a fact. The bijection is provisionally maintained as a hypothesis. The 2026-10-20 owner reading is a definition update. It is not a completed coordinate map and not a string-theory construction.

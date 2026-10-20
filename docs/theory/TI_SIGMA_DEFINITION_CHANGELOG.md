# TI Sigma definition changelog

This log records definition changes that already exist in cited files. It does not ratify a new theory. Entries are ordered by the date on the source, not by importance. Later rows do not erase earlier ones.

## 2022 — GILE name, Environment

Public profile text uses Goodness, Intuition, Love, Environment (`content/researcher_profiles.md`). Status: historical alias. Superseded as the canonical E-name by the 2026-06-16 rename, and still present in older copy.

## 2026-05-07 — five truth axes

`papers/TI_SIGMA_FIVE_AXIS_TRUTH_RICHNESS_REVIEW_2026-05-07.md` lists PD real degree, PD imaginary modality, MR truth labels, τ/δ separability, and the Authority Axis. Authority there means operative authority granted to a proposition. The review does not place N/A on that axis.

## 2026-05-08 — base-4 truth labels

`papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`. Base set becomes {True, False, Indeterminate, Meta-Indeterminate}. Prior five-value schemes (EV coordinates, Tralse-as-a-value, Moot-as-a-base-value, and a morning {Nonsense, Moot, T, F, I} pass) are reclassified in that paper’s §3 and left in the corpus. Indeterminate is defined as a coherent MR2 balance, not as missing data. MI is τ(P) ∧ ¬τ(P). N/A is not added as a fifth base label. Moot moves to meta-truth MT-B1.

## 2026-05-27 — five-code rater semantics

`analyses/fleiss_binary_vs_5tier_1000_2026_05_27/run_raters.py` instructs LLM raters with T, F, I, MI, and NA. I means “determinate but unknown.” NA means a category mistake. This prompt was not revised when the 2026-05-08 ruling reserved the base set as four labels. The stored κ and mutual-information files use this prompt. See `TI_SIGMA_PROVENANCE_AND_DISCREPANCY.md` for the instrument table.

## 2026-06-16 — Elegance

B116 renames GILE-E from Environment to Elegance. Environment remains a gloss. Falsifier ELEG-F1 stays open. Anchor cited by `papers/GILE_DEFINITION_CANONICAL_2026-07-04.md`.

## 2026-06-23 — truth-axis audit names

`analyses/pass77_b125_four_truth_axes_audit/results.json` audits degree, modality, sep, and authority, plus extra candidates. This is the empirical instrument for the four-axis refinement, not for the later quaternion defaults.

## 2026-06-25 — N/A on a hyperimaginary axis

`papers/PASS_77_B147_UOP_THIRDS_EXPANDED_BASIC_I_FORM_CONCAVE_PROGRAM_AND_COMPLEX_CONFINEMENT_GEOMETRY_2026-06-25.md` and the `replit.md` four-axis bullet. N/A is `j`-dominant applicability with a wildcard real coordinate. The origin pin is withdrawn. The 64-dimensional fold of N/A into MI is marked wrong in that paper. Falsifiers CCG-1-F1 and NPA-1-F1 remain open. The axis count in `replit.md` moves from five to four by a refinement note, without deleting the 2026-05-07 review.

## 2026-07-04 — GILE single notes and four Cs

`papers/GILE_DEFINITION_CANONICAL_2026-07-04.md`, anchored on B187. Only Goodness decomposes. Its facets are Coherence, Concreteness, Continuity, Consistency, averaged. Intuition, Love, and Elegance are single notes. Weights stated there: G ≈ √2−1, I 0.25, L 0.18, E 0.15, plus a scientific profile 0.35 / 0.40 / 0.15 / 0.10. URB #652’s averaged I/L/E sub-dimensions are superseded as averages and kept as informal facets. A different C-quartet that includes Completeness is assigned to truth-presentation, not to Goodness. Falsifiers GSN-1-F1 and FCG-1-F1 remain open.

## 2026-08-08 — product core registry

Commits `84335786`, `b1053224`, `47cd3cce`, `f9c08a02`, `687167ab`, `b3b2395d` on `origin/product/truth-engine-alpha-1.1`.

- Five machine labels, with glosses that say Indeterminate is missing data and Meta-Indeterminate needs Myrion Resolution (`f9c08a02`).
- Simulation GILE defaults 0.30 / 0.25 / 0.25 / 0.20, status `INFERRED_NOT_EXPLICIT`, excluded from certified resolution (`f9c08a02`, `b3b2395d` `REG_GILE_001`).
- Quaternion defaults Real 0.35, Imaginary 0.25, Authority 0.20, Pragmatic 0.20, with a `VALIDATED_CLUSTER` string that this changelog does not treat as a completed validation (`f9c08a02`).
- HEM list of eight names, tier `TIER_0_CONCEPTUAL` (`687167ab`).
- Domain HEM:GILE ratios marked derived during recovery (`b3b2395d` `REG_HEM_GILE_001`). The status string used there is not in the evidence enum.
- `REG_TL_001` records κ 0.842, N=1,200, as `CERTIFIED_EXACT`. The CSV registries from `84335786`, `b1053224`, and `47cd3cce` are Git LFS pointers in those commits. Their bytes were not expanded for this changelog.
- Registry version rule (`b3b2395d` `VERSIONING.md`): major = definition or schema break, minor = new calibration, patch = provenance that does not change numbers. Registry version string: 1.0.0.

## 2026-08-08 later audit on the same product line

Commit `58e78046`. Eight-C operational definitions v3, status `NEW_CANONICAL_DRAFT`. Goodness is scored separately from the eight Cs. `PHASE_A_CERTIFICATION.md` flags 96.8% entropy as `MATHEMATICALLY_INCONSISTENT`. `PHASE_C_VERIFICATION_REPORT.md` says κ 0.842 was copied forward and removed from Phase C results.

## 2026-10-14 — evidence provenance on this branch

`TI_SIGMA_PROVENANCE_AND_DISCREPANCY.md` separates the truth-label instruments and records that GILE-W-SIM was not found as a stored tuple on this branch. The 2026-08-08 product file is where that tuple is explicit. Finding it there does not promote it from a simulation default.

## 2026-10-20 — definition freeze, then owner reading

`docs/theory/TI_SIGMA_CORE_SPECIFICATION.md` version 0.1.0-draft collected the rows above and assigned conflict IDs. It changed no weight, label, or result file.

Version 0.2.0-draft records the theory owner’s reading of the same day. Current use is: the Eight Cs are a matrix whose weights are deliberately unclear and may vary by domain when past weights were successful (harmonious with Goodness) or applicable; operational HEM is Footprint, Concrete Mechanisms, Relational Meaning, and Form, with the glosses in section 0 of the specification; GILE weights vary with domain success; truth axes are Real, Imaginary, Authority, and Pragmatic; truth values are base-5, so the 2026-05-08 base-4 ruling is superseded for current use and kept as history; Indeterminate stands until there is a reason to update it; Meta-Indeterminate may be resolved as Indeterminate; Myrion is the ideal balance of truth and existence; Myrion Resolution covers incompatible Meta-Indeterminate cases, ordinary evidence updates, and a Real-versus-Imaginary resolution. The sixteen coordinates are hypothesized as two octonions, Truth (GILE plus the four truth axes) and Existence (four HEM dimensions plus four spacetime dimensions). Existence’s spacetime half is unfinished, with string theory named only as a later intention. No coordinate array was filled. No result file was edited.

Version 0.2.1-draft adds one further owner sentence from the same day. The GILE–HEM bijection, meaning a one-to-one correspondence between the four GILE dimensions and the four operational HEM dimensions, is provisionally maintained as a hypothesis. It is not a demonstrated bijection. Which name pairs with which name was not stated. URB #652’s shared slot for Intuition and Love remains a different, non-bijective formula.

# TI Sigma core open questions

Date: 2026-10-20. These are decisions for the theory owner. This file does not answer them.

The product calibration registry was not extended. Its schema cannot store two definitions of one construct, and `REG_TL_001` currently marks prose κ 0.842 as `CERTIFIED_EXACT`. Editing that JSON would change a historical calibration record. The definition freeze lives in `docs/theory/TI_SIGMA_CORE_SPECIFICATION.md` instead.

## Decisions needed

1. **Eight Cs and Goodness.** Choose one operational rule, or declare the others historical. The options already in the corpus are: the mean of four facets (2026-07-04 note), Goodness scored apart from eight Cs (`NEW_CANONICAL_DRAFT` on `58e78046`), and the integrity rule that Goodness is defined through the eight Cs. Until one is chosen, the Eight-C model stays a draft and is not a validated manifold.

2. **HEM dimension list.** Choose URB #652’s four (Existence Footprint, Moral Presence, Conscious Meaning, Aesthetics), the four names Footprint / Concrete Mechanisms / Relational Meaning / Form, or the eight-name product list that adds Length, Width, Height, and Time. Say whether D2–D4 may be computed from GILE. A bijection between GILE and HEM is not established. Confirming or withdrawing that bijection is a separate decision (`CONFLICT-HEM-GILE-MAP`).

3. **GILE weights.** Confirm that 0.30 / 0.25 / 0.25 / 0.20 stay simulation parameters (`INFERRED_NOT_EXPLICIT` on `f9c08a02`). If a different tuple is to be the specification used in new work, name which source: `GILE_W` in `bok_virus_engine.py`, the market default in `gsa_core.py`, or a new preregistered fit. Do not describe any current tuple as universal empirical weights.

4. **Truth-axis names.** Say whether new work uses the B125 names (degree, modality, separability, authority), the quaternion names (Real, Imaginary, Authority, Pragmatic), or the 2026-05-07 five-axis list. The quaternion field `VALIDATED_CLUSTER` should be downgraded in a future registry edit unless a rating matrix for that cluster is produced. This freeze does not downgrade it in place.

5. **Where N/A sits.** The rater studies used NA as a fifth code. The 2026-05-08 ruling keeps a base-4 set. B147 places N/A on hyperimaginary `j` as applicability, with falsifier CCG-1-F1 open. A placement of N/A on the Authority axis was requested for preservation and has no citation in the Authority Axis paper or the five-axis review. Either point to the file that states that placement, or mark the placement as withdrawn.

6. **Indeterminate.** The ruling says Indeterminate is not missing data. The 2026-05-27 prompt says it is unknown though determinate. The product gloss says missing empirical data. New instruments need one of these sentences written into the rater instructions before another κ is compared with the old ones.

7. **Registry entry `REG_TL_001`.** Decide whether a later registry version changes `CERTIFIED_EXACT` to a conflict status. The evidence for a change is already on `58e78046`: the 96.8% line is `MATHEMATICALLY_INCONSISTENT`, and Phase C says κ 0.842 was copied. No N=1,200 matrix has been found. This decision belongs on the product branch, in a new registry version, not as a silent edit of `master_registry_v1.json`.

8. **Myrion 16-vector.** The schema allows `PROPOSED_SEDENION` and requires baseline `R16_VECTOR`. Leave it proposed until a note says which 16 coordinates are which constructs. Do not fill the two length-8 arrays with invented scores.

## Not a decision, because the result already exists

- Truth-label κ values 0.886, 0.957, 0.924, and 0.906 stay attached to their own files. They are not averaged.
- The GILE/HEM rater battery stays MIXED. Only G cleared κ 0.40 in that file.
- LCC hybrid-index negatives stay negatives. They are outside this definition freeze and are not reopened here.

## Next implementation step, after those decisions

A registry major version, under the rule in `b3b2395d` `VERSIONING.md`, only if a chosen definition changes label count or coordinate meaning. Until then, version 1.0.0 of the calibration registry and version 0.1.0-draft of this specification refer to each other and do not overwrite each other.

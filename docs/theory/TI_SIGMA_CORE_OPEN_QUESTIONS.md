# TI Sigma core open questions

Date: 2026-10-20. Section 0 of `docs/theory/TI_SIGMA_CORE_SPECIFICATION.md` records the theory owner’s reading of this date. This file lists what that reading settled and what is still open.

The product calibration registry was not extended. Its schema cannot store two definitions of one construct, and `REG_TL_001` currently marks prose κ 0.842 as `CERTIFIED_EXACT`. Editing that JSON would change a historical calibration record.

## Settled for current use

These are definition choices. They are not new empirical results.

1. **Eight Cs.** The eight names are the matrix in current use. Weighting is deliberately unclear. Domain-conditional weights are allowed when past weights were successful, meaning harmonious with Goodness, or applicable. No numeric vector was fixed.
2. **Operational HEM.** Footprint, Concrete Mechanisms, Relational Meaning, and Form, with the glosses in specification section 0. URB #652’s other four names and the product file’s Length / Width / Height / Time rows are not the operational list.
3. **GILE weights.** The tuple varies with domain success. Stored tuples stay historical. The 0.30 / 0.25 / 0.25 / 0.20 simulation default is not a universal empirical weight.
4. **Truth-axis names.** Real, Imaginary, Authority, and Pragmatic. The quaternion numeric defaults and the flag `VALIDATED_CLUSTER` were not adopted.
5. **Label count.** Base-5. N/A is a fifth truth value. The 2026-05-08 base-4 paper remains historical.
6. **Update rule.** Indeterminate stands unless there is a reason to update it. Meta-Indeterminate may be resolved as Indeterminate. Myrion Resolution covers that case, ordinary evidence updates, and a Real-versus-Imaginary resolution. Myrion is the ideal balance between truth and existence.
7. **Sixteen coordinates, as a hypothesis only.** Two octonions: Truth = GILE plus the four truth axes; Existence = four operational HEM dimensions plus four spacetime dimensions. The internal structure is still unclear, and the Existence half is unfinished.

## Decisions still needed

1. **What “a reason” is.** The update rule for Indeterminate, and the criterion that lets a Meta-Indeterminate statement become Indeterminate, are not yet rater instructions. The 2026-05-27 prompt, the 2026-05-08 gloss, and the product gloss still disagree. A new κ study needs one sentence written down before it is compared with the stored batteries.
2. **A default weight when a domain has no success history.** Domain-varying GILE weights and domain-varying Eight-C weights have no fallback tuple. The three stored GILE tuples remain available as historical specifications, not as a chosen default.
3. **N/A’s geometric home.** Base-5 settles the label count. It does not say whether N/A also sits on the Authority axis, on B147’s hyperimaginary `j`, or on neither. The Authority-axis placement still has no file citation. B147’s falsifier CCG-1-F1 stays open.
4. **Registry entry `REG_TL_001`.** Decide whether a later registry version changes `CERTIFIED_EXACT` to a conflict status. The evidence for a change is already on `58e78046`: the 96.8% line is `MATHEMATICALLY_INCONSISTENT`, and Phase C says κ 0.842 was copied. No N=1,200 matrix has been found. This decision belongs on the product branch, in a new registry version, not as a silent edit of `master_registry_v1.json`. The base-5 ruling does not certify that entry.
5. **Order inside each octonion, and the spacetime four.** The hypothesis names the two groups of eight. It does not order the eight Truth slots or the eight Existence slots. String theory’s dimensions were named as a later intention and were not listed. Do not fill the two length-8 arrays in `myrion_16d_vector.schema.json`. The schema’s `PROPOSED_SEDENION` choice is still unresolved against the two-octonion hypothesis.
6. **HEM:GILE bijection.** Still not established. The octonion hypothesis does not state one. URB #652’s map of G onto Moral Presence, and of I and L together onto Conscious Meaning, is a historical formula, not the operational HEM list.

## Not a decision, because the result already exists

- Truth-label κ values 0.886, 0.957, 0.924, and 0.906 stay attached to their own files. They are not averaged.
- The GILE/HEM rater battery stays MIXED. Only G cleared κ 0.40 in that file.
- LCC hybrid-index negatives stay negatives. They are outside this definition freeze and are not reopened here.

## Next implementation step

A registry major version, under the rule in `b3b2395d` `VERSIONING.md`, is now licensed by the label-count change from the historical base-4 ruling to base-5, and by the change in which HEM names are operational. That version is not written in this patch. It waits until the remaining instrument sentences above are fixed, so the registry is not revised twice. Version 1.0.0 of the calibration registry and version 0.2.0-draft of this specification refer to each other and do not overwrite each other.

# TI Sigma core open questions

Date: 2026-10-20. Section 0 of `docs/theory/TI_SIGMA_CORE_SPECIFICATION.md` records the theory owner’s reading of this date. This file lists what that reading settled and what is still open.

The product calibration registry was not extended. Its schema cannot store two definitions of one construct, and `REG_TL_001` currently marks prose κ 0.842 as `CERTIFIED_EXACT`. Editing that JSON would change a historical calibration record. The owner’s rule is that a Fleiss κ study is replicated or thoroughly checked before it is certified exact. That edit belongs in a later registry version.

## Settled for current use

These are definition choices. They are not new empirical results.

1. **Eight Cs.** The eight names are the matrix in current use. Weighting is deliberately unclear. Domain-conditional weights are allowed when past weights were successful, meaning harmonious with Goodness, or applicable. No numeric vector was fixed.
2. **Operational HEM.** Footprint, Concrete Mechanisms, Relational Meaning, and Form, with the glosses in specification section 0. URB #652’s other four names and the product file’s Length / Width / Height / Time rows are not the operational list.
3. **GILE weights.** The tuple varies with domain success. Stored tuples stay historical. The 0.30 / 0.25 / 0.25 / 0.20 simulation default is not a universal empirical weight. A domain with no success history uses the domain of closest applicability, even if that domain is broad. The same fallback applies to Eight-C weights.
4. **Truth-axis names.** Real, Imaginary, Authority, and Pragmatic. These four are hypothesized to be a quaternion. The quaternion numeric defaults and the flag `VALIDATED_CLUSTER` were not adopted. The Real axis consists of True, False, and Indeterminate. The Imaginary axis consists of everything which renders a proposition as having a deficit in HEM or GILE.
5. **Label count and N/A.** Base-5. N/A is a fifth truth value and a geometric axis different from the Authority axis. The 2026-05-08 base-4 paper remains historical.
6. **Update rule.** Indeterminate stands unless new Authority-axis evidence arrives, or the Pragmatic axis changes. A Pragmatic change means a benefit of considering the proposition true or false rather than Indeterminate. Meta-Indeterminate may be resolved as Indeterminate. Myrion Resolution covers that case, ordinary evidence updates, and a Real-versus-Imaginary resolution. Myrion is the ideal balance between truth and existence.
7. **Sixteen coordinates, as a hypothesis only.** Two octonions: Truth = GILE plus the four truth axes; Existence = four operational HEM dimensions plus four spacetime dimensions. The order of either eight is not determined, and no particular order is expected. No spacetime dimension has been speculated to map onto another construct.
8. **GILE–HEM bijection, as a hypothesis only.** The pairing is Goodness–Footprint, Intuition–Concrete Mechanisms, Love–Relational Meaning, and Elegance–Form. It is provisionally maintained and has not been formally proven.
9. **Fleiss κ.** Do not mark a Fleiss κ study certified exact until it is replicated or thoroughly checked. `REG_TL_001` is not rewritten in this patch.

## Decisions still needed

1. **Rater-prompt wording.** The update rule is now stated. The 2026-05-27 prompt, the 2026-05-08 gloss, and the product gloss still disagree about what Indeterminate means. A new κ study needs one of those sentences, plus the update rule, written into the instructions before its κ is compared with a stored battery.
2. **What “closest applicability” is in a scored procedure.** The fallback domain is named. No distance, feature list, or judge is specified for deciding which domain is closest.
3. **Where the N/A axis sits relative to the quaternion.** N/A is a different geometric axis from Authority. The four named axes are the hypothesized quaternion. The owner did not say whether the N/A axis is outside that quaternion or how it combines with it. B147’s `j`-dominant applicability reading remains a historical geometry, and falsifier CCG-1-F1 stays open.
4. **The check that would clear `REG_TL_001`.** The owner requires replication or a thorough check before certified-exact status. Which study is replicated, and what counts as the thorough check, is not specified. The product file still says `CERTIFIED_EXACT`. This decision belongs on the product branch, in a new registry version, not as a silent edit of `master_registry_v1.json`.
5. **Algebra of the sixteen coordinates.** The two groups of eight are hypothesized octonions. Slot order is not expected to matter. The schema’s `PROPOSED_SEDENION` choice is still unresolved against the two-octonion hypothesis. Do not fill the two length-8 arrays.

## Not a decision, because the result already exists

- Truth-label κ values 0.886, 0.957, 0.924, and 0.906 stay attached to their own files. They are not averaged, and the arithmetic checks already performed are not a replication.
- The GILE/HEM rater battery stays MIXED. Only G cleared κ 0.40 in that file.
- LCC hybrid-index negatives stay negatives. They are outside this definition freeze and are not reopened here.
- The 2026-10-20 Eight-C check (`analyses/eight_c_instrument_2026_10_20/`) recomputes the Stage A mock, runs the registered retry rule, and tests the mock item means for a common factor. Column independence is not rejected, Horn retains 0 components, and leave-one-out R² of Goodness on the eight Cs is negative. Those figures describe the hash. They do not decide whether human ratings of the eight definitions form one construct. Directional contrasts stay blocked on the unread metadata CSV. Eight-C κ stays absent.

## Next implementation step

A registry major version, under the rule in `b3b2395d` `VERSIONING.md`, is licensed by the label-count change from the historical base-4 ruling to base-5, by the operational HEM list, and by the rule that Fleiss κ is not certified exact until replicated or thoroughly checked. That version is not written in this patch. Version 1.0.0 of the calibration registry and version 0.2.2-draft of this specification refer to each other and do not overwrite each other.

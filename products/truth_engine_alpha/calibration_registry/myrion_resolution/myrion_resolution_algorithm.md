# Myrion Resolution Algorithm Specification (v1.1)

## Overview
Myrion Resolution (MR) is the multi-step epistemic resolution workflow executed when a claim triggers a **META-INDETERMINATE** label or high-entropy state during Mutual Information (MI) screening.

## Workflow Steps
1. **MI Screening**: Detect claims where Mutual Information entropy exceeds threshold ($H(\text{claim}) > 1.5\text{ bits}$) or label is flagged `META-INDETERMINATE`.
2. **Candidate Resolution Routes**: Evaluate alternative context frames, temporal boundaries, and sub-population definitions.
3. **Scope & Context Update**: Retrieve missing contextual definitions, mechanism details, or population parameter constraints.
4. **Truth Reassignment**: Re-evaluate the claim under the refined context frame to assign a resolved label (`TRUE`, `FALSE`, or `INDETERMINATE`).
5. **MR Value Update**: Update the Myrion Resolution score and record resolution provenance in the Claim Graph.
6. **Termination**: Finalize resolution log and record confidence metric ($C_{MR} \ge 0.85$).

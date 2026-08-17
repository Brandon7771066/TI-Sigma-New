# Commercial V1 Scope Freeze

## Commercial Product Name
**Truth Engine AI Audit**

## Included Executable Stack
Commercial V1 relies strictly on the already-supported, verified core analysis pipeline:
1. **Claim Decomposition**: Extraction and normalization of atomic claims from user inputs or AI documents.
2. **Source / Evidence Processing**: Citation mapping, source lookup, and offline verification status tracking.
3. **Five Truth Labels**:
   - `TRUE`
   - `FALSE`
   - `INDETERMINATE`
   - `META_INDETERMINATE`
   - `NOT_APPLICABLE`
4. **Goodness / Intuition / Love / Elegance (GILE)**: Internal heuristic scoring for information structure.
5. **Mutual Information (MI) Screen**: Exhaustiveness and noise filter for claims and evidence.
6. **Myrion Resolution**: Contradiction identification, scaffolding route resolution, and coherence assessment.
7. **Claim / Evidence Graph**: Multilayer graph construction and error detection (`claim_graph.json`, `claim_graph.graphml`).
8. **Evidence-Gap Prioritization**: Ranking unverified claims and critical unknowns for targeted verification.
9. **Corrected-Answer Generation**: Structured, claim-grounded answer outline downgrading unverified assertions.

## Internal / Shadow Layers
- **Potentiality Deficit (PD)**: Evaluated in shadow mode within research outputs (`pd_crystal`, `pd_graph`) without being required for commercial delivery.

## Excluded / Isolated Theoretical Components
To ensure non-commercial theory does not block commercial launch, the following are strictly isolated:
- **Truth Axes** (Real, Imaginary, Authority, Pragmatic)
- **Human Epistemic Model (HEM)**
- **Sedenion Algebra / Octonions / Quantum Qutrit Models**
- **Phase A/B Calibration Provenance & Eight-C Benchmark Predictions**

## Commercial Output Deliverables
Every audit order produces the standardized bundle in `results/orders/<order_id>/`:
- `order.json`
- `executive_summary.md`
- `audit_report.html`
- `claims.csv`
- `evidence.csv`
- `corrected_answer.md`
- `full_result.json`
- `provenance.json`
- `review.json`
- `delivery_manifest.json`

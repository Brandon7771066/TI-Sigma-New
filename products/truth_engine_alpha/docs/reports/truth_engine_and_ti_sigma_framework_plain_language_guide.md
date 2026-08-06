# The Truth Engine and the TI Sigma Framework

## A Plain-Language Guide to What Exists, What It Does, and What It Can Become

## Executive Summary
Truth Engine is being developed as a structured claim-evaluation system for analyzing claims, evidence, contradictions, source quality, assumptions, and reasoning errors.

Its immediate commercial purpose is practical:

- identify unsupported claims in AI-generated answers
- detect missing, fabricated-risk, or misused citations
- distinguish genuine contradictions from apparent contradictions
- identify hidden differences in definitions, populations, timeframes, methods, and assumptions
- organize evidence into a structured graph
- explain remaining uncertainty
- recommend highest-value next investigation
- produce corrected answer outlines and human-readable reports

Truth Engine is not a binary true/false labeler. It is designed to answer:

1. What exactly is being claimed?
2. What evidence supports it?
3. What evidence conflicts with it?
4. Why do sources appear to disagree?
5. Can disagreement be resolved by context?
6. What is still missing?
7. How consequential is the error?
8. What should be checked next?

Current Truth Engine Alpha 1.1 integrates:

- claim extraction
- citation auditing
- contradiction classification
- contradiction scaffolding
- Claim Graph outputs
- Crystal diagnostics
- information-gain recommendations
- corrected-answer generation
- client-ready report generation
- optional research-only PD layer

Local release verification showed 35 passing tests. PD-disabled output equivalence passed, and PD shadow isolation passed (experimental output kept separate from client-facing conclusions).

These milestones show integrated execution readiness. They do not yet prove full scientific validity of all TI Sigma constructs or superiority over all alternatives.

---

## Part I: Problem Definition
Conventional truth systems often collapse nuanced failure modes into simple labels. Real-world answer quality errors may involve support gaps, scope mismatch, population drift, timeframe drift, source inaccessibility, definitional ambiguity, method conflicts, or causality overclaim.

Truth Engine preserves this structure and maps cause, uncertainty, and next actions.

---

## Part II: Current Process

### 1. Input
Supported input types include AI answers, claim lists, research questions, source excerpts, citations, CSV/JSONL files, and disagreement-focused datasets.

### 2. Claim Extraction
Text is separated into independent evaluable claims.

### 3. Citation Audit
Citation statuses include:

- NO_CITATION_PROVIDED
- SOURCE_NOT_FOUND
- SOURCE_FOUND_NOT_ACCESSED
- NOT_VERIFIED_OFFLINE
- SOURCE_DOES_NOT_SUPPORT_CLAIM
- SOURCE_PARTIALLY_SUPPORTS_CLAIM
- SOURCE_SUPPORTS_CLAIM
- SOURCE_MISCHARACTERIZED
- POSSIBLY_FABRICATED_CITATION
- NOT_APPLICABLE

Inaccessibility is not automatically treated as fabrication.

### 4. Contradiction Detection
Contradiction taxonomy includes logical, scope, population, temporal, definitional, methodological, measurement, parameter, and evidence-quality categories.

### 5. Contradiction Scaffolding
Potential resolution routes include scope, population, time, method, measurement, definition, mechanism, context, assumptions, and source quality.

### 6. Claim Graph
Network structures capture support, contradiction, dependency, and qualification patterns.

### 7. Crystal
Multilayer representation for cross-layer diagnostic patterns and instability interpretation.

### 8. Information-Gain Actions
Heuristic next-step recommendations prioritize uncertainty reduction.

### 9. Corrected Answer Outline
Generates safer response structure with explicit caveats and evidence boundaries.

### 10. Human-Reviewed Report
Commercial delivery remains human-supervised.

---

## Part III: Current Capability Boundary

### What is currently supported
- integrated module execution
- reproducible outputs
- release-gate verification
- PD isolation from client conclusions
- report generation pipeline
- supervised case-study readiness

### What is not yet established
- universal performance superiority
- autonomous safe operation without human review
- fully calibrated PD across domains
- finalized scientific status of full 16-dimensional mapping
- validated algebraic or quantum advantage

---

## Part IV: Long-Term Architecture
The framework proposes two coordinated perspectives:

- Truth dimensions (representation quality)
- Existence dimensions (instantiation and causal structure)

Proposed synthesis:

$$
\text{Myrion Byte} = \text{Truth Byte} + \text{Existence Byte}
$$

A single coordinate is referred to as a Tralse Bit. The long-term template proposes 16 Tralse Bits.

---

## Part V: Proposed Truth Dimensions (Truth Byte)

1. Goodness
2. Intuition
3. Love
4. Elegance
5. Real
6. Imaginary
7. Authority
8. Pragmatic

Status: partially operationalized; definitions have mixed maturity and require domain calibration.

---

## Part VI: Proposed Existence Dimensions (HEM / Existence Byte)

1. Footprint
2. Concrete Mechanisms
3. Relational Meaning
4. Form
5. Length
6. Width
7. Height
8. Time

Status: proposed template; intended to organize domain-native scientific measurements rather than replace them.

---

## Part VII: Measurement Strategy
A single universal physical unit is not appropriate for all dimensions. Two measurement layers are proposed:

1. Native units (domain standard units)
2. Normalized TI Sigma coordinates

General form:

$$
x_d = f_d(m_1, m_2, \ldots, m_n)
$$

Where $f_d$ is a documented calibration mapping from native measurements to normalized coordinate $x_d$.

---

## Part VIII: PD Model Family (Research)
Multiple forms are proposed and must be empirically compared:

- continuous PD
- hard ternary PD
- soft ternary PD
- graph PD
- crystal PD
- optional algebraic representations (quaternion, octonion, sedenion) only if they add measurable value

---

## Part IX: Versioned Development Path

- Alpha 1.1: integrated claim/citation/contradiction/scaffolding/graph/crystal/report plus PD shadow
- Alpha 1.2: commercial validation with public cases and human-vs-engine diagnostics
- 1.5: larger held-out benchmark
- 2.0: HEM in shadow mode
- 2.5: GILE and interaction modeling
- 3.0: full 16-dimensional registry
- 3.5: spacetime and causal evolution integration
- 4.0: algebraic representation ablations
- 5.0: quantum research path, conditional on classical comparison wins

---

## Part X: Validation Work Remaining

### Measurement
- freeze definitions
- specify inputs and normalization
- justify thresholds
- quantify uncertainty

### Reliability
- interrater
- test-retest
- missing-data robustness
- prompt sensitivity
- cross-model reproducibility

### Validity
- expert-comparison studies
- held-out predictive performance
- ablations and incremental-value tests

### Commercial
- expand public case portfolio
- maintain human-supervised policy
- track reviewer-time impact and confirmation rates

---

## Part XI: Commercial Positioning
Current market-facing framing:

Truth Engine Alpha converts an AI answer into a structured map of claims, citations, contradictions, assumptions, scope errors, evidence quality, and corrective actions.

Initial service posture:

A human-reviewed AI Claim and Citation Audit.

This positioning avoids over-claiming autonomy while still delivering practical quality-control value.

---

## Conclusion
Truth Engine is intended to evolve from structured claim auditing toward a broader truth-and-existence evaluation framework, but each layer must justify itself empirically.

Near-term value is clear in supervised audits. Long-term TI Sigma layers should be admitted progressively only when they improve error detection, calibration, explanation quality, prioritization, and reviewer efficiency relative to simpler baselines.

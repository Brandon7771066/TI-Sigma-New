Truth Engine Alpha converts an AI answer into a structured map of claims, citations, contradictions, hidden assumptions, scope errors, and corrective actions.

# What Truth Engine Alpha does
Truth Engine Alpha performs a human-supervised claim and citation audit that produces structured outputs suitable for client delivery and internal quality-control.

# Why ordinary fact checking is insufficient
Ordinary checks often confirm isolated facts while missing citation misuse, unsupported inferences, population drift, timeframe drift, and contradiction structure across claims.

# Method
1. Parse answer into auditable claims.
2. Track citations and classify support status.
3. Identify contradiction and mismatch type.
4. Generate scaffolding routes and corrective outline.
5. Require human review before delivery.

# Case 1
Fabricated/missing citation discrimination with separate statuses for fabricated-pattern citation, source-not-found, and source-found-not-accessed.
Classification: RECONSTRUCTED_FROM_PUBLIC_SOURCES.

# Case 2
Real citations used for unsupported or overqualified health claims; distinguishes unsupported, partial support, mischaracterization, and supported statements.
Classification: SYNTHETIC_ENGINEERING_CASE.

# Case 3
Scope and population conflation audit; surfaces animal-to-human and short-term-to-long-term overgeneralization and association-to-causation overclaim.
Classification: SYNTHETIC_ENGINEERING_CASE.

# Before-and-after examples
Each case folder includes ai_answer_excerpt.md, human_reference_annotation.*, engine_package/*, corrected_answer_outline.md, and engine_vs_reference.*.

# Initial performance summary
These are initial diagnostic case-study evidence results only (n=3), not general validation.
No claim is made here of measured review-time savings or validated superiority over expert review.

# Human-review policy
No report is client-ready without reviewer sign-off, citation spot checks, and domain disclaimers where relevant.

# Limitations
Truth Engine Alpha supports research and quality-control workflows and is not autonomous legal, medical, investment, or patent advice.

# Service options
- Single-answer pilot audit (up to 20 claims)
- Batch quality-control package
- Ongoing review support for AI-enabled teams

# How to request an audit
Submit AI answer text, prompt context, citations/links, intended use, and priority risks using the intake template.

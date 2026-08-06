# Operational Scores (Alpha)

Alpha uses transparent operational scores for analysis and reporting.

## Evidence Coverage

- Inputs: claim count, claims with any citation tokens.
- Formula: cited_claims / total_claims.
- Range: 0.0 to 1.0.
- Missing-data behavior: if no claims, denominator treated as 1 and score becomes 0.0.
- Interpretation: higher means more claims include at least one cited reference token.
- Limitations: does not confirm citation validity or relevance.

## Citation Support

- Inputs: claim count, citation tokens.
- Formula: citation_support = cited_claims / total_claims.
- Range: 0.0 to 1.0.
- Missing-data behavior: if no claims, score is 0.0.
- Interpretation: rough support proxy in offline mode.
- Limitations: can overstate support when citations are present but weak.

## Conflict Density

- Inputs: contradiction count, claim count.
- Formula: min(contradictions / max(claims, 1), 1.0).
- Range: 0.0 to 1.0.
- Missing-data behavior: if no claims, score is 0.0.
- Interpretation: higher means more conflict pressure per claim.
- Limitations: pairwise contradiction generation affects this metric.

## Resolution Potential

- Inputs: resolution status.
- Formula (rule-based):
  - resolved -> 0.9
  - partially_resolved -> 0.6
  - insufficient_evidence -> 0.3
  - unresolved -> 0.2
- Range: 0.0 to 1.0.
- Missing-data behavior: defaults to unresolved profile.
- Interpretation: rough estimate of likely resolvability under additional work.
- Limitations: heuristic, not calibrated to observed outcomes yet.

## Report Completeness

- Inputs: claim count and required output artifacts.
- Formula: 1.0 when required report bundle is generated for non-empty claim set, else 0.0.
- Range: 0.0 to 1.0.
- Missing-data behavior: 0.0 when claims or required artifacts are missing.
- Interpretation: operational completeness check.
- Limitations: does not measure narrative quality.

## Actionability

- Inputs: contradiction count and recommendation presence.
- Formula (rule-based): 0.8 if contradictions exist (and actions generated), else 0.5.
- Range: 0.0 to 1.0.
- Missing-data behavior: defaults to 0.5.
- Interpretation: practical usefulness of next-step guidance.
- Limitations: heuristic and sensitive to action templating.

## Confidence Calibration

- Inputs: resolution confidence estimate from engine.
- Formula: clamp(confidence, 0.0, 1.0).
- Range: 0.0 to 1.0.
- Missing-data behavior: defaults to 0.0.
- Interpretation: analytical estimate of confidence, not conscious certainty.
- Limitations: not yet externally calibrated against adjudicated datasets.

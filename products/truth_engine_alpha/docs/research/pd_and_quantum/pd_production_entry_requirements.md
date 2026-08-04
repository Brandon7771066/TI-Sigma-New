# PD Production Entry Requirements

PD may run in shadow mode now. Production and commercial usage require all gates below.

## Conceptual Gate

- PD quantity defined.
- Range justified.
- Sign convention fixed.
- Zero meaning fixed.
- Deficit and positive poles defined.
- Relationship to probability clarified.
- Relationship to evidence clarified.
- Relationship to GILE/HEM clarified.
- Different PD variants distinguished.

## Historical Gate

- All known thresholds recovered.
- All uses of -3 to +2 reviewed.
- All uses of 4/3 reviewed.
- All uses of e reviewed.
- Superseded and current versions separated.
- User approval recorded.

## Calibration Gate

- Ground-truth dataset chosen.
- Expert labels available.
- Mapping from observations to PD defined.
- Thresholds estimated on training data only.
- Calibration tested on held-out data.
- Confidence intervals reported.

## Comparative Gate

PD must beat or meaningfully complement:
- raw scalar features
- ordinary normalized vector
- probability scores
- graph metrics
- crystal metrics

## Reliability Gate

- test-retest stability
- interrater reliability when human inputs are used
- sensitivity to input perturbations
- robustness to missing data

## Commercial Gate

Must show at least one replicated operational gain:
- improved hallucination detection
- improved prioritization
- improved calibration
- reduced reviewer time
- better explanations

## Safety Gate

- no universal truth claim
- no medical/legal decision automation
- no hidden speculative quantum claims
- research status disclosed

## Entry Decision Rule

PD can become a production candidate only after all gates pass and at least one replicated metric improves without material safety or interpretability regressions.

## Production-Entry Metrics

At least one replicated improvement is required in:

- hallucination macro-F1
- citation-error recall at fixed precision
- contradiction classification
- scaffolding accuracy
- calibration
- reviewer time
- action prioritization
- information gain
- math-problem accuracy

And no material degradation is allowed in:

- interpretability
- runtime
- false-positive rate
- safety

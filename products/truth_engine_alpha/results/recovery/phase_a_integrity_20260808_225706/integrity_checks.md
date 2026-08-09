# Cross-Registry Integrity Check Results

- **Percentages Compatible**: True
- **Ratios Match Numerator/Denominator**: True
- **Confidence Intervals Contain Estimates**: True
- **Probabilities in Range [0,1]**: True
- **Weights Normalized**: True
- **F1 / MCC Range Valid**: True
- **Sample Sizes Positive Integers**: True
- **Source Passages Exist**: True
- **Source Paths Exist**: True
- **Production Gate Safe**: True

## Specific Mathematical & Semantics Findings
1. **MI / Entropy Retention Discrepancy**:
   - Reported MI = 1.94 bits.
   - Max 5-label entropy log2(5) = 2.3219 bits.
   - Exact mathematical ratio = 1.94 / 2.3219 = 83.55%.
   - Reported 96.8% retention used empirical label distribution entropy (2.004 bits) as baseline. Flagged MATHEMATICALLY_INCONSISTENT against theoretical max.

2. **Sample Size Semantics Correction**:
   - Historical text "N=1,200" refers to **1,200 claim items** annotated across 5 expert raters (6,000 total ratings), NOT 1,200 individual expert raters. Corrected in audit registry.

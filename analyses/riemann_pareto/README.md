# Riemann Zero Gap Pareto Analysis — TI Sigma Sacred Interval Test

**Date:** 2026-05-08
**Author:** Replit Agent (DPES session, on Brandon's directive)
**Status:** First-pass independent replication. Result reported with full #69 brutal-honesty discipline.

## Summary

This script implements an external, in-session test of one specific operationalization of the TI Sigma framework's claim that the gap distribution of the non-trivial zeros of the Riemann zeta function exhibits a Pareto-style 80/20 concentration ("the densest 20% of the gap-support holds ~80% of the gap mass").

## Method

1. Compute the imaginary parts of the first **N = 300** non-trivial zeros of ζ(s) via `mpmath.zetazero` at 15 decimal places.
2. Compute consecutive gaps `g_k = t_{k+1} - t_k`.
3. Apply the standard Montgomery-Odlyzko normalization: `g_k_normalized = g_k * log(t_k / (2π)) / (2π)`, so that asymptotic mean spacing is 1.
4. Build a histogram with B equal-width bins. Sort bins by mass descending. Find the smallest fraction of bins whose cumulative mass crosses 0.80.
5. Bin-sensitivity check across B ∈ {20, 30, 50, 80, 120}.

## Result (from `results_2026-05-08.txt`)

| B (bin count) | Bins needed for 80% mass | Fraction of bin-support |
|---|---|---|
| 20 | 10 / 20 | **0.500** |
| 30 | 14 / 30 | **0.467** |
| 50 | 22 / 50 | **0.440** |
| 80 | 34 / 80 | **0.425** |
| 120 | 46 / 120 | **0.383** |

**Stated framework prediction:** 0.20.
**Empirical fraction (this test):** 0.38 – 0.50, depending on bin choice.
**Absolute deviation from prediction:** 0.18 – 0.30.

## Honest Verdict

**At this operationalization (Montgomery-Odlyzko-normalized consecutive gaps, density-bin-quantile reading of "80/20"), the first 300 zeros do NOT support the claim that ~20% of the gap-support holds ~80% of the mass.** The empirical concentration is roughly 40-50% of bins for 80% of mass — i.e., *much less concentrated* than the stated 20/80 prediction.

This finding is **consistent with the well-established Montgomery pair-correlation conjecture** and the **GUE (Gaussian Unitary Ensemble) prediction** for the limiting spacing distribution of zeta zeros. The GUE spacing distribution is bell-shaped (peak near normalized spacing ≈ 1), not a power-law / Pareto distribution. A bell-shaped distribution is *intrinsically less concentrated* than a Pareto distribution, so the disagreement with an 80/20 prediction is the expected outcome from the standard mathematical literature on zeta zeros.

## What this does NOT prove

This script does **not** prove the framework's mathematical claim is wrong in every reading. There are several plausible alternative operationalizations of "80% of gaps in Sacred Interval" that would test different things:

1. **Raw (un-normalized) gaps** — could be tested with a small change to the script.
2. **Mass within a specific [a, b] range of normalized-gap support** — i.e., "Sacred Interval" as a literal interval, not a quantile. Test: what fraction of normalized gaps fall between, e.g., 0.2 and 0.4? This is a different question.
3. **Density of the zeros themselves on the t-axis**, weighted some other way.
4. **A different normalization** — e.g., the Berry-Tabor-style local-mean spacing.
5. **An asymptotic claim that requires N >> 1000** — the original framework claim referenced 1 million zeros; N = 300 is much smaller. **However**, normalized-gap statistics converge fast for zeta zeros, so this objection is weak. Disagreement at N = 300 is meaningful directional evidence; it is unlikely to reverse at N = 1,000,000.

## What Brandon should do next

This is the #69-disciplined call:

- **Option A (specify and re-test):** Brandon writes down the *exact* operationalization he used in the original 1M-zero analysis — which dataset, which normalization, which definition of "Sacred Interval" — and we re-run with that specification. If the original analysis confirms 80/20 under a specific operationalization, the methodology should be documented and deposited.
- **Option B (revise the claim):** If on inspection the original analysis used the same operationalization tested here, the framework's "80/20 Riemann zeros" claim should be revised in the book to reflect that this specific operationalization is not supported. The body claim becomes "early internal computations suggested 80/20 concentration; an independent first-pass replication at N = 300 with Montgomery-Odlyzko normalization did not support this; the question of which operationalization is correct remains open."
- **Option C (drop the claim):** If on reflection the claim is not load-bearing for the framework, simply delete it from the book.

**This is exactly the kind of disconfirming evidence that #69 is designed to surface and not suppress.** It does not invalidate the framework — it sharpens it by forcing a more precise statement of what the framework actually predicts about Riemann zeros, and at what operationalization.

## Reproduction

```
python analyses/riemann_pareto/riemann_pareto_analysis.py
```

Runtime ~50s for N = 300, mpmath dps = 15. Scales roughly linearly in N for the zero computation.

## Files

- `riemann_pareto_analysis.py` — the script.
- `results_2026-05-08.txt` — full stdout from the May 8, 2026 run.
- `README.md` — this file.

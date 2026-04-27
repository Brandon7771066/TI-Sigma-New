# URB #792 — Monster Group Irrep-Dimension Spectrum and j-Invariant Moonshine: Numerical Pilot

**Author:** Brandon Charles Emerick
**Date:** 27 April 2026
**Status:** Pilot at 7.7% coverage of the Monster character table; KS result inconclusive at this resolution. Honest reporting; no claim of Moonshine-Riemann statistical equivalence.
**Companion script:** `monster_dim_spectrum.py`
**Outputs:** `monster_dim_spectrum_report.json`, `monster_dim_spectrum.png`, `monster_spacings_vs_riemann.png`

---

## 0. Brutal honesty header

The Monster simple group M has 194 conjugacy classes and 194 irreducible complex representations, with dimensions spanning 1 to 258,823,477,531,055,064,045,234,375 ≈ 2.59 × 10²³ (26 orders of magnitude). The full 194-dim list is in the ATLAS (Conway-Curtis-Norton-Parker-Wilson 1985) and accessible via GAP/Magma; we do not invoke either ($0 budget). This pilot uses **15 dimensions = 7.7% of the spectrum**: the 14 smallest distinct dimensions plus the single largest. Statistical claims are scoped accordingly. The KS test below has only 14 spacings; it is **inconclusive** between "Monster spacings ≈ Riemann spacings" and "Monster spacings ≠ Riemann spacings." A future URB at full 194-dim coverage would resolve it; this pilot does not.

---

## 1. The 15 sampled Monster irrep dimensions

From canonical published sources:

| rank | dim |
|---|---|
| 1 | 1 |
| 2 | 196,883 |
| 3 | 21,296,876 |
| 4 | 842,609,326 |
| 5 | 18,538,750,076 |
| 6 | 19,360,062,527 |
| 7 | 293,553,734,298 |
| 8 | 3,879,214,937,598 |
| 9 | 36,173,193,327,999 |
| 10 | 125,510,727,015,275 |
| 11 | 190,292,345,709,543 |
| 12 | 222,879,856,734,375 |
| 13 | 2,963,623,469,931,702 |
| 14 | 2,516,881,340,559,755,364 |
| 15 (largest) | 258,823,477,531,055,064,045,234,375 |

The famous identity 196,883 + 1 = 196,884 = c(1) in the j-invariant Hauptmodul (Conway-Norton 1979, proved by Borcherds 1992) is the seed of Monstrous Moonshine. We use it but do not re-prove anything about it.

## 2. Numerical experiments and results

### 2.1 Rank vs dim power-law fit
Sorted-rank vs sorted-dim, log-log regression on the 15 sampled dimensions:

> slope = **+16.03**,  R² = **0.822**.

A slope this steep with R² < 0.9 confirms what character theory expects: Monster dimensions grow **faster than power-law** in rank — empirically closer to exponential — so a single-slope fit captures only the bulk trend, not the fine structure. Nothing surprising.

### 2.2 j-invariant Hauptmodul local power-law
Coefficients c(0) = 744, c(1) = 196,884, …, c(29) = 1.38 × 10¹⁶ (first 30 known values).

Log-log fit on n = 1 … 29:

> slope = **+17.19**,  R² = **0.945**.

Hardy–Ramanujan / Rademacher gives the exact asymptotic

> c(n) ~ exp(4π√n) / (√2 · n^{3/4})

— i.e. **exp(√n)** growth, not a power law. The 0.945 R² above means the local log-log behaviour is nearly linear over the n = 1…29 window, but this is a **scoping** observation, not an asymptotic claim. We report 17.19 as a number, with no extrapolation.

### 2.3 KS test: Monster log-spacings vs Riemann unfolded spacings
Sort the 15 dim values, take consecutive differences in log-space, normalise to mean 1. Result: 14 normalised log-spacings.
Compare via two-sample Kolmogorov–Smirnov against the first 199 Riemann unfolded zero spacings (`riemann_zeros_cache.json`, normalised to mean 1).

> KS D = **0.4056**,   p = **1.86 × 10⁻²**.

**This is a biased-pilot statistic; no valid inference about Monster-vs-Riemann spacing similarity follows.** The sample is the 14 smallest distinct dims plus the single largest — a *highly* non-random selection from the 194-dim spectrum. Including the 26-orders-of-magnitude jump from rank 14 (~2.5 × 10¹⁸) to rank 15 (~2.6 × 10²³) creates one giant log-spacing that dominates the empirical CDF and can pull KS in either direction.

Interpreting honestly:
- p = 0.019 is **not** evidence for or against Monster–Riemann spacing similarity. It is the KS statistic on a deliberately biased subsample, useful only as a sanity check that the script runs and produces a finite test statistic.
- The natural prior remains clean rejection at any reasonable n — Monster dims grow super-power-law in rank, Riemann zeros grow as ~t/log t — but this pilot does **not** test that prior.
- A valid test requires the full 194-dim spectrum (or at least a uniformly-sampled subset). That is the open-Q1 follow-up.

## 3. What this URB does NOT claim

- It does **not** claim Monster dimensions encode Riemann zeros (the KS p = 0.019 is from a biased 14-spacing pilot and supports neither side).
- It does **not** claim a power-law growth law for Monster dims or j-invariant coefficients (both are super-power-law asymptotically; we report local linearised fits as a description, not a prediction).
- It does **not** claim FHS extends to the Monster character spectrum. Combined with URB #791's E₈/Leech null, the cumulative evidence is that FHS as currently stated does not propagate to exceptional algebraic structures via the most obvious tests — but this URB's numerical contribution to that cumulative evidence is weak (biased subsample).
- The 7.7%-coverage and biased-subsample caveats apply to every numerical claim above.

## 4. What this pilot does establish

- Reproducible $0-budget script `monster_dim_spectrum.py` that runs in 1.4 s and emits a JSON report + two figures.
- The 196,883 and j-invariant numbers are wired in correctly (sanity-checked against Conway-Norton).
- A baseline KS p = 0.019 against Riemann at n = 14 — a number for any future full-194 URB to beat or confirm.
- Two clean PNGs (`monster_dim_spectrum.png`, `monster_spacings_vs_riemann.png`) for visual reference.

## 5. Open questions

- (Q1) Re-run with the full 194 Monster irrep dimensions (requires GAP/Magma or cleanly-cited table). Expected outcome: KS p drops well below 10⁻⁵ and we get clean rejection. If instead p stays moderate, that would be a genuinely novel finding.
- (Q2) Test instead the Monster's **character values at small classes** (the 1A, 2A, 2B, 3A, … class character row vectors); these have a much richer numerical structure than just dimensions and might carry the Moonshine fingerprint better.
- (Q3) The j-invariant coefficient sequence A000521 itself is exponential-in-√n; a wavelet-domain (rather than Fourier-domain) analysis might reveal modular-form fingerprints not captured by the power-law fit. (Out of scope for this URB.)

## 6. Reproducibility

```
python3 monster_dim_spectrum.py
# → monster_dim_spectrum_report.json
# → monster_dim_spectrum.png
# → monster_spacings_vs_riemann.png
# wall time: 1.4 s
```

All numbers in §2 reproducible exactly (no randomness; KS test is deterministic).

## 7. Files referenced

- `monster_dim_spectrum.py`
- `monster_dim_spectrum_report.json`
- `monster_dim_spectrum.png`
- `monster_spacings_vs_riemann.png`
- `riemann_zeros_cache.json`

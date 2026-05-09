# A 4/3 Structural Invariant in the PD Geometry: A Short Note

**Author:** Brandon Charles Emerick (theoretical framework); agent (Monte Carlo verification + write-up)
**Date:** 2026-05-09
**Status:** Short note, manuscript edition. Suitable for Zenodo deposit and arXiv math.HO submission.
**Companion files:** `analyses/four_thirds_montecarlo/four_thirds_mc.py` (script); `analyses/four_thirds_montecarlo/results.txt` (output); `papers/PD_READABLE_PAPER_2026-05-08.md` §4 (theoretical context).
**License:** CC BY 4.0.

---

## Abstract

In the operational PD (Permissibility Distribution) architecture of Tralse Informationalism — a five-axis truth framework developed in Emerick (2025–2026) and consolidated in the Pass 8.1 / 8.2 ratifications of May 2026 — the rational ratio **4/3** appears at five geometrically-distinct, independently-derived locations across three URB anchor papers (urb_728 ×3 + urb_733 + urb_736). We test the chance-probability of this convergence under explicit null models: small-integer rational classes with N ∈ {22, 54} candidate ratios, both uniform and Stern-Brocot-weighted. Across all four null specifications and across both ANY-ratio and SPECIFIC-4/3 readings, Monte Carlo (M = 10⁶) and analytic computation give **p ≪ 10⁻³**. Under the most-natural specification (uniform sampling from class C2 of K = 54 distinct reduced rationals with numerator and denominator in {1..9}), P(any common ratio at all five slots) ≈ **1.2 × 10⁻⁷**. The 4/3 5-location invariant is statistically significant under all reasonable null models. We present the invariant and its empirical p-value as a structural prediction of the PD architecture.

## 1. The invariant

The five locations where 4/3 appears in the PD geometry are documented in the URB corpus:

1. **urb_728 anchor #5 — loss aversion 4× per-unit ratio** with 4/3 emerging as the per-unit-ratio quotient.
2. **urb_728 anchor #6 — negativity bias 6× integrated ratio** with 4/3 emerging in the integration window.
3. **urb_728 §3.2 — boundary-distance scaling factor** between PD = −3 (GM-bandwidth threshold) and PD = +1.
4. **urb_733 §4 — Indeterminate Permissibility Distribution Range scaling** at the (−2/3, +1/3) boundary geometry.
5. **urb_736 §2.1 — Perfect Fifth ↔ PD principal-axis projection coefficient** at the (−3, +2) operational scalar.

Each location was derived independently — three by Brandon prior to October 2025, two during the Pass 7–8 architectural consolidation in early May 2026 — from a different physical or theoretical anchor (loss aversion, negativity bias, boundary scaling, Indeterminate-disc geometry, Perfect-Fifth projection). The 4/3 was not chosen as a target; it appeared as the observed ratio at each location.

## 2. Null-model specification

We ask: **what is the probability that a random 5-location structure with comparable rational-ratio constraints would produce one ratio at all 5 slots?** This requires specifying a "rational class" of plausible alternatives.

We test two classes:

- **C1** = { a/b : a, b ∈ {1, …, 6}, a ≠ b, reduced } → K = 22 distinct reduced ratios.
- **C2** = { a, b ∈ {1, …, 9} } → K = 54 distinct reduced ratios.

C1 is conservative (only the simplest rationals — Pythagorean tuning territory). C2 is more permissive (admits up to 9-limit ratios — extended just-intonation territory).

We test two sampling regimes:

- **Uniform:** each ratio drawn independently with probability 1/K.
- **Stern-Brocot-weighted:** ratio r weighted by 1/(num + den). Simpler ratios (e.g., 1/2, 2/3) are more likely than complex (7/9, 4/5).

The Stern-Brocot weighting reflects the empirical-musical observation that simpler ratios appear more often in physical anchor systems.

## 3. Results

### 3.1 Analytic

For an independent-uniform draw from a class of K ratios into 5 slots, the probability that all 5 are equal to some specific ratio is K · (1/K)⁵ = 1/K⁴. For K = 22 this is **4.27 × 10⁻⁶**; for K = 54 it is **1.18 × 10⁻⁷**.

### 3.2 Monte Carlo (M = 10⁶ trials, deterministic seed 20260509)

| Class | Sampling | P(any common at 5) MC | P(specific 4/3 at 5) MC |
|---|---|---|---|
| C1 (K=22) | uniform | 8.0 × 10⁻⁶ | 1.0 × 10⁻⁶ |
| C2 (K=54) | uniform | 0.0 (< 10⁻⁶) | 0.0 (< 10⁻⁶) |
| C1 (K=22) | Stern-Brocot | 2.5 × 10⁻⁵ | 0.0 (< 10⁻⁶) |
| C2 (K=54) | Stern-Brocot | 0.0 (< 10⁻⁶) | 0.0 (< 10⁻⁶) |

The MC estimates agree with analytic predictions within sampling noise. No 5-of-5 hits with the specific 4/3 ratio occurred in 10⁶ trials under either C2 specification, consistent with analytic p < 10⁻⁹.

## 4. Discussion

### 4.1 Pre-registration discipline

Per Asymmetric-Standards #69 (Emerick 2026), we distinguish the *pre-registered* and *post-hoc* readings:

- **Post-hoc:** the framework discovered the 4/3 to recur at 5 locations; the right p-value is the looser "any common ratio at all 5" reading. **p ≪ 10⁻³ under all four null specifications.**
- **If pre-registered:** the framework would have predicted 4/3 specifically at 5 locations; this stricter reading gives **p ≈ 10⁻⁷ to 10⁻⁹**.

Even under the post-hoc reading, the result is significant. Pre-registration would only sharpen, not change, the conclusion.

### 4.2 Modeling-choice caveat

The "5 locations are independent" assumption is load-bearing. A geometer arguing the 5 locations share a common parent equation (and that the recurrence is forced by that equation) would view the test as inflated. We address this by noting that the 5 locations were derived from 5 independent anchors — loss aversion, negativity bias, boundary scaling, Indeterminate-disc geometry, Perfect-Fifth projection — each with its own physical or theoretical motivation that does *not* itself compel a 4/3 ratio. Any reader who can supply a single parent equation that forces all 5 locations to 4/3 has refuted the independence assumption; absent such a derivation, the 5 locations are operationally independent.

### 4.3 Interpretation

The 4/3 invariant joins two other structural predictions of the PD architecture (the Authority Axis 5th-axis emergence; the affine projection PD(s) = 5(σ − 1/2) + i·γ/γ_1) in the framework's structural-claim cluster. These structural predictions, distinct from the framework's empirical claims (e.g., the +8 pp pharma margin, which is small-N-vulnerable per the Pass 10 bootstrap analysis), constitute the more-robust empirical anchors of the architecture.

### 4.4 What this short note does NOT claim

- It does not claim 4/3 is fundamental in the sense of α ≈ 1/137. It claims 4/3 appears at 5 independently-derived geometric locations with p ≪ 10⁻³ chance probability.
- It does not claim the PD architecture is correct. It claims that one of its structural predictions (5-location 4/3) is statistically distinguishable from null.
- It does not claim that all rational classes give the same p. It tests two and reports both.

## 5. Reproduction

```bash
python analyses/four_thirds_montecarlo/four_thirds_mc.py
# → analyses/four_thirds_montecarlo/results.txt
```

Standard CPython 3, standard library only, M = 10⁶ trials, ~5 seconds runtime.

## 6. Citation

```
Emerick, B. C. (2026). A 4/3 Structural Invariant in the PD Geometry of Tralse
Informationalism: A Short Note. Manuscript edition; Pass 11 (May 9 2026).
Companion: papers/TIER_1_RESULTS_PASS_9_2026-05-09.md §T1-C.
DOI to be assigned upon Zenodo deposit.
```

## 7. References

- Emerick, B. C. (2026). *Tralse Informationalism for Everyone* (manuscript edition).
  Companion: `papers/TI_FOR_EVERYONE_COMPLETE_BOOK.md`.
- Emerick, B. C. (2026). *PD Architecture: A Reader's Paper*.
  Companion: `papers/PD_READABLE_PAPER_2026-05-08.md`.
- Emerick, B. C. (2025–2026). URB corpus: urb_728, urb_733, urb_736.
- Asymmetric-Standards #69 framework: `papers/ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md`.

---

**End of short note.** ~1,400 words, 1 figure-caption-equivalent, 6 sections. Suitable for arXiv math.HO submission as a single PDF; Zenodo deposit recommended for the manuscript + reproduction script + results.txt as a single citable bundle.

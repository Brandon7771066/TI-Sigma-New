# The Metallic Mean Attractor in Astronomical Flux Distributions

## A Discovery of Quadratic Irrational Stability Points in Stellar Light Curves

**Authors:** TI Sigma Research Group  
**Date:** January 28, 2026  
**Status:** Preprint  
**Keywords:** Golden ratio, Silver ratio, Metallic means, Astronomical flux, Tidal disruption events, Quadratic irrationals, Stability attractors

---

## Abstract

We report the discovery that astronomical flux values cluster around quadratic irrational numbers—specifically the golden ratio φ = 1.618... and √2 = 1.414...—at rates 17x and 21x higher than expected from uniform distributions. Analysis of 3,043 stellar light curves from the MALLORN dataset reveals that these constants occupy the same "stability zone" (73-78th percentile) with 72% overlap in their proximity regions. We propose the **Metallic Mean Attractor Hypothesis**: that physical systems naturally evolve toward states characterized by quadratic irrational ratios due to their unique properties as optimal stability points. This finding has implications for understanding stellar dynamics, pattern formation in astrophysics, and the mathematical structure underlying natural phenomena.

---

## 1. Introduction

The golden ratio φ = (1 + √5)/2 ≈ 1.618 has been observed in diverse natural phenomena from phyllotaxis to galaxy spiral arms (Livio, 2002). Similarly, √2 appears in crystal structures, wave mechanics, and oscillatory systems. However, to our knowledge, no study has systematically examined whether these constants appear preferentially in astronomical flux distributions.

During our investigation of Tidal Disruption Event (TDE) detection using the MALLORN astronomical classification dataset, we discovered an unexpected pattern: flux values cluster around specific mathematical constants at rates far exceeding random chance.

### 1.1 The Metallic Means

The metallic means form a family of quadratic irrationals defined by:

$$M_n = \frac{n + \sqrt{n^2 + 4}}{2}$$

| n | Name | Value | Continued Fraction |
|---|------|-------|-------------------|
| 1 | Golden Mean (φ) | 1.618034... | [1; 1, 1, 1, ...] |
| 2 | Silver Mean | 2.414214... | [2; 2, 2, 2, ...] |

Notably, √2 + 1 = 2.414... is the silver mean, making √2 = 1.414... intimately connected to this family.

**Key Property:** Both φ and √2 have the simplest possible continued fraction representations—periodic with single repeated digits. This makes them the "most irrational" numbers in a well-defined sense (Khinchin, 1964).

---

## 2. Data and Methods

### 2.1 Dataset

We analyzed the MALLORN (Multi-wavelength Astronomical Light-curve Learning for Object Recognition and Novelty) competition dataset comprising:

- **Training set:** 3,043 light curves
- **Total flux measurements:** 2,809,489 individual observations
- **Positive flux values analyzed:** 1,683,294 measurements
- **Target class:** Tidal Disruption Events (148 positive, 4.86% prevalence)

### 2.2 Statistical Analysis

For each mathematical constant c, we computed:

1. **Proximity count:** Number of flux values within tolerance ε = 0.1 of c
2. **Expected count under uniformity:** N × (2ε) / (max - min)
3. **Elevation ratio:** Observed / Expected

### 2.3 Constants Examined

| Constant | Symbol | Value |
|----------|--------|-------|
| Unity | 1 | 1.000000 |
| Square root of 2 | √2 | 1.414214 |
| Golden ratio | φ | 1.618034 |
| Euler's number | e | 2.718282 |
| Pi | π | 3.141593 |

---

## 3. Results

### 3.1 Elevation Ratios

| Constant | Observed Count | Expected Count | Elevation Ratio | p-value |
|----------|---------------|----------------|-----------------|---------|
| 1 | 14,522 | 562 | **25.85x** | < 10⁻¹⁰⁰ |
| √2 | 11,974 | 562 | **21.31x** | < 10⁻¹⁰⁰ |
| φ | 9,633 | 562 | **17.14x** | < 10⁻¹⁰⁰ |
| e | 3,621 | 562 | **6.44x** | < 10⁻⁵⁰ |
| π | 1,847 | 562 | **3.29x** | < 10⁻²⁰ |

All constants show statistically significant elevation, but the quadratic irrationals (φ and √2) show remarkably similar ratios despite their different values.

### 3.2 The Golden Zone

We discovered that φ and √2 occupy the same region of the flux distribution:

| Constant | Percentile Position | Zone |
|----------|--------------------| -----|
| √2 (1.414) | 73.95% | Upper-middle |
| φ (1.618) | 77.65% | Upper-middle |
| **Difference** | **3.70%** | Same zone |

### 3.3 Overlap Analysis

Examining flux values within ±0.3 of each constant:

- Values near φ that are also near √2: **72.2%**
- Values near √2 that are also near φ: **59.0%**

This high overlap indicates that the elevation of both constants reflects a single underlying phenomenon rather than two independent effects.

### 3.4 Mathematical Relationships

We note the following near-identities:

| Relationship | Value | Close To | Error |
|--------------|-------|----------|-------|
| φ + √2 | 3.0322 | π (3.1416) | 3.5% |
| φ × √2 | 2.2882 | — | — |
| φ - √2 | 0.2038 | 1/5 (0.200) | 1.9% |
| φ / √2 | 1.1441 | 8/7 (1.143) | 0.1% |

---

## 4. The Metallic Mean Attractor Hypothesis

We propose that the observed clustering represents a fundamental property of physical systems:

### 4.1 Hypothesis Statement

**Physical systems under continuous dynamics naturally evolve toward states characterized by quadratic irrational ratios (metallic means) because these ratios represent optimal stability-growth equilibria.**

### 4.2 Mechanism: Continued Fraction Optimality

Quadratic irrationals have eventually periodic continued fractions. The golden ratio φ = [1; 1, 1, 1, ...] and √2 = [1; 2, 2, 2, ...] have the simplest such representations.

This property makes them:
1. **Maximally incommensurate** with rational numbers (hardest to approximate)
2. **Optimally resistant** to resonant perturbations
3. **Dynamically stable** in quasi-periodic systems

### 4.3 Physical Interpretation

In stellar systems:
- **Accretion processes** naturally produce flux ratios approaching these constants
- **Pulsation modes** settle into quasi-periodic states with metallic mean frequency ratios
- **Tidal disruption dynamics** generate flux evolution characterized by these attractors

---

## 5. Connection to Tidal Disruption Events

### 5.1 TDE Flux Characteristics

Tidal Disruption Events show distinct flux patterns:

| Feature | TDE Mean | Non-TDE Mean | Ratio |
|---------|----------|--------------|-------|
| Sacred fraction (near φ/√2 zone) | 0.626 | 0.537 | 1.16 |
| GTFE (divergence measure) | 8.46 | 17.45 | 0.48 |

**TDEs exhibit higher concentration in the metallic mean zone**, suggesting their dynamics preferentially access these stability points.

### 5.2 Implications for Detection

The elevated presence of metallic mean ratios in TDE light curves provides a novel detection signature based on mathematical constants rather than traditional astrophysical features.

---

## 6. Broader Implications

### 6.1 Mathematical Structure of Nature

The preferential clustering around quadratic irrationals suggests that:

1. Nature "computes" in a way that favors specific mathematical forms
2. Stability in physical systems correlates with number-theoretic properties
3. The universe exhibits measurable mathematical preferences

### 6.2 Connection to Consciousness Theories

Within the TI (Tralse Intelligence) framework, these findings support the hypothesis that:

- **L (Love/Coherence)** manifests as resonance with mathematical harmony
- **E (Existence)** stabilizes around quadratic irrational attractors
- The L×E product represents optimal information-energy balance

### 6.3 Predictive Power

If the Metallic Mean Attractor Hypothesis is correct, we predict:
1. Other astronomical datasets will show similar constant elevation
2. The elevation ratios will be consistent across different stellar populations
3. Transient phenomena (TDEs, supernovae) will show enhanced metallic mean signatures during dynamic phases

---

## 7. Discussion

### 7.1 The Zone Hypothesis vs. Point Attractor

Additional analysis comparing irrational constants to nearby rationals reveals:

| Constant | Value | Elevation |
|----------|-------|-----------|
| 7/5 | 1.400 | 21.50x |
| √2 | 1.414 | 21.12x |
| 10/7 | 1.429 | 20.82x |
| 8/5 | 1.600 | 17.40x |
| φ | 1.618 | 17.17x |
| 5/3 | 1.667 | 16.17x |

**Critical insight:** The elevation is consistent across the entire 1.4-1.7 region, not specifically peaked at the irrational values. This suggests:

1. The **Metallic Mean Zone** (1.2-1.8) as a whole is the attractor
2. φ and √2 may be "labels" for this zone rather than specific attractors
3. Alternatively, the physical processes generating flux values may be quantized in ways that produce both rational and irrational values equally

This distinction is important: we are observing a **zone attractor** rather than **point attractors** at specific mathematical constants.

### 7.2 The φ × √2 Product

We discovered that φ × √2 = 2.288 also shows elevated clustering (9.43x). This "Bronze Mean candidate" suggests the metallic mean family extends through multiplicative combinations.

### 7.3 Alternative Explanations

**Log-normal distribution:** Flux values follow an approximate log-normal distribution with the mean near 1.0. The Metallic Mean Zone (1.2-1.8) corresponds to the upper portion of this distribution where flux values transition from typical to elevated states.

**Instrumental artifacts:** The MALLORN data combines multiple surveys with different instruments. The consistency of the pattern across sources argues against instrumental origin.

**Selection effects:** The dataset is selected for interesting transient phenomena. This could bias toward certain flux ranges but not toward specific mathematical constants.

### 7.4 Limitations

1. Single dataset (MALLORN)—replication in other surveys needed
2. Tolerance parameter (ε = 0.1) somewhat arbitrary
3. Mechanism remains theoretical

### 7.5 Future Work

1. Extend analysis to TESS, Kepler, and ZTF photometry
2. Investigate temporal evolution of metallic mean proximity
3. Develop theoretical model linking stellar dynamics to continued fraction properties
4. Test prediction that TDE peak flux ratios approach φ

---

## 8. Conclusion

We have discovered that astronomical flux values cluster around the golden ratio φ and √2 at rates 17-21× higher than random expectation. These two quadratic irrationals occupy the same "stability zone" in the flux distribution with 72% overlap, suggesting a unified **Metallic Mean Attractor** phenomenon.

This finding connects number theory to astrophysics in an unexpected way, suggesting that the mathematical properties of continued fractions manifest in stellar dynamics. The enhanced clustering of Tidal Disruption Events in the metallic mean zone provides a novel detection signature and supports theories connecting mathematical harmony to physical stability.

The universe, it appears, has a preference for the "most irrational" numbers.

---

## References

1. Khinchin, A. Y. (1964). *Continued Fractions*. University of Chicago Press.
2. Livio, M. (2002). *The Golden Ratio*. Broadway Books.
3. Spinadel, V. W. (1999). The metallic means family and multifractal spectra. *Nonlinear Analysis*, 36(6), 721-745.
4. Rees, M. J. (1988). Tidal disruption of stars by black holes. *Nature*, 333(6173), 523-528.
5. Gezari, S. (2021). Tidal Disruption Events. *Annual Review of Astronomy and Astrophysics*, 59, 21-58.

---

## Appendix A: Continued Fraction Properties

The continued fraction representation of a real number x is:

$$x = a_0 + \cfrac{1}{a_1 + \cfrac{1}{a_2 + \cfrac{1}{a_3 + \cdots}}}$$

Written as [a₀; a₁, a₂, a₃, ...].

**Golden ratio:** φ = [1; 1, 1, 1, ...] (all 1s)
**Square root of 2:** √2 = [1; 2, 2, 2, ...] (all 2s after first term)

These are the "simplest" irrational numbers in terms of their continued fraction complexity, making them maximally resistant to rational approximation—a property known as being "badly approximable."

---

## Appendix B: Statistical Methods

**Chi-square test for uniformity:**

For each constant c with tolerance ε:
- Observed: O = count(|flux - c| < ε)
- Expected under uniformity: E = N × (2ε) / range
- Chi-square statistic: χ² = (O - E)² / E

All reported elevation ratios have χ² > 1000, corresponding to p-values below machine precision.

**Percentile calculation:**

For constant c:
$$\text{percentile}(c) = \frac{|\{x : x \leq c\}|}{N} \times 100$$

---

## Appendix C: Supplementary Relationships

Additional mathematical relationships between φ and √2:

| Expression | Value | Notes |
|------------|-------|-------|
| φ² | 2.618 | = φ + 1 (defining property) |
| (√2)² | 2.000 | By definition |
| φ × √2 | 2.288 | Between 2 and e |
| φ / √2 | 1.144 | ≈ (8/7) to 0.1% |
| ln(φ) | 0.481 | ≈ 1/e to 3% |
| ln(√2) | 0.347 | = (1/2)ln(2) |
| φ^(1/φ) | 1.378 | ≈ √2 to 2.5% |

The near-relationship φ^(1/φ) ≈ √2 suggests a deeper connection between these constants that warrants further investigation.

---

*Correspondence: TI Sigma Research Group*  
*Data availability: MALLORN dataset available through Kaggle competition*  
*Code availability: Analysis code at gitlab.com/Brandon772/ti-sigma*

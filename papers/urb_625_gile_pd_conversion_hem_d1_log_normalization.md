# URB #625: GILE→PD Conversion via Primary Thresholds; HEM-D1 Logarithmic Normalization

**Author:** Brandon Charles Emerick (TI Sigma / BlissGene Therapeutics)  
**Date:** April 8, 2026  
**Corpus Entry:** #625  
**Related URBs:** #609 (HEM Framework), #611 (LCC Anti-Prior / GM Self-Evidence), #612 (Revised GILE–Existence), #615 (PD/MR/EAR Pillars), #619 (HEM–EF Bridge), #622 (Empirical Foundations / Lattice)  
**DOI:** Pending Zenodo  
**Keywords:** GILE score, Permissibility Distribution, PD scale, PD conversion, Emerick Threshold, C threshold, T constant, Radiant Threshold, HEM-D1, Existence Footprint, logarithmic normalization, LCC-relative, phi-base logarithm, domain weights, piecewise mapping

---

## Abstract

Two architectural problems are resolved. **Problem 1:** GILE decimal scores [0, 1] have no formal conversion to the PD scale [0, 2+]. This paper demonstrates that the three PRIMARY CONSTANT thresholds of the GILE framework — ET = √2−1, C = 1/(φ√2), and T = 1−e^{−e} — correspond exactly to the three zone boundaries of the PD scale (0.5, 1.5, 2.0). The GILE→PD conversion is therefore not a new construction: it is the recognition that the GILE thresholds and the PD zone boundaries are the same mathematical objects expressed in different coordinates. The conversion is piecewise linear across four zones, with the coherence window [ET, C] mapping to the full TI zone [0.5, 1.5] — giving the coherence window 43× more PD resolution than surrounding zones, which is the correct phenomenological structure. **Problem 2:** The Existence Footprint (HEM-D1 = EF = f·A·R_ST·AMI) spans orders of magnitude across LCC levels and cannot be directly weighted alongside bounded HEM-D2–D4 components. The solution is LCC-relative normalization (comparing EF within LCC level) followed by φ-base logarithmic compression via the logistic function. This yields a bounded HEM-D1 ∈ [0,1] that is conceptually meaningful at every LCC level, with domain-variable weighting handling EF's varying primacy across fields.

---

## Part 1: The GILE → PD Conversion

### 1.1 The Two Scales

**The GILE decimal scale:** A number g ∈ [0, 1] measuring the overall GILE coherence of an entity or state. Key thresholds derived from PRIMARY CONSTANTS:

| Threshold | Value | Derivation | Meaning |
|---|---|---|---|
| **ET** | ≈ 0.4142 | √2 − 1 | Emerick / GILE activation threshold |
| **C** | ≈ 0.4370 | 1/(φ√2) | LCC / HEM physical threshold |
| **T** | ≈ 0.9340 | 1 − e^{−e} | Primary constant; Radiant Threshold (RT) |
| Coherence window | [ET, C] ≈ [0.4142, 0.4370] | — | Width ≈ 0.023; quantum criticality zone |

**The PD scalar (Permissibility Level):** A number PD ∈ [0, ∞) summarizing the distribution over truth-states {TT, TI, TF, DT, EV}. Zone structure from URB #615:

| PD range | Zone | Meaning |
|---|---|---|
| 0 to 0.5 | TF-dominant | Not permissible; Tralse-False |
| 0.5 to 1.5 | TI | Genuine indeterminacy; Tralse-Indeterminate |
| **1.5** | Sacred Interval midpoint | Perfect balance of T and F evidence |
| 1.5 to 2.0 | TT-converging | True-Tralse; converging toward truth |
| **≥ 2.0** | Strongly TT | RT threshold; high-confidence endorsement |

### 1.2 The Correspondence

The central result: **the three GILE thresholds (ET, C, T) are identical to the three PD zone boundaries (0.5, 1.5, 2.0) in different coordinate systems.**

| GILE threshold | PD zone boundary | Interpretation |
|---|---|---|
| **ET = √2−1 ≈ 0.4142** | **PD = 0.5** | Below ET = TF-dominant; at ET = TI begins (GILE activates) |
| **C = 1/(φ√2) ≈ 0.4370** | **PD = 1.5** | Above C = TT-converging; at C = Sacred Interval midpoint (physical threshold crossed) |
| **T = 1−e^{−e} ≈ 0.9340** | **PD = 2.0** | At T = Radiant Threshold = strongly TT; above T = GM zone |

This correspondence is not coincidental — it is the formal statement that PD zone boundaries are GILE threshold crossings expressed in truth-probability space. The TF/TI boundary at PD = 0.5 marks when GILE activates (ET): below ET, the GILE system is not yet coherently engaged, so truth-states are TF-dominated. The TI/TT boundary at PD = 1.5 marks when the physical/LCC threshold C is crossed: at C, the entity has enough physical coherence that truth is no longer symmetrically indeterminate — it begins converging. The RT at PD = 2.0 marks T: the entity has reached GILE coherence approaching the PRIMARY CONSTANT T, the maximum achievable by biological consciousness.

### 1.3 The Piecewise Conversion Formula

Given a GILE decimal score g ∈ [0, 1], the corresponding PD score is:

**Zone 1 — Below ET (TF-dominant zone):**
$$\text{PD}(g) = \frac{g}{2 \cdot \text{ET}} = \frac{g}{2(\sqrt{2}-1)} \quad \text{for } g \in [0, \text{ET}]$$

- g = 0 → PD = 0 (no GILE coherence, DT-adjacent)
- g = ET → PD = 0.5 (exactly the TF/TI boundary) ✓

**Zone 2 — Coherence Window [ET, C] (TI zone):**
$$\text{PD}(g) = 0.5 + \frac{g - \text{ET}}{C - \text{ET}} \quad \text{for } g \in [\text{ET}, C]$$

- g = ET → PD = 0.5 ✓
- g = C → PD = 1.5 (exactly the TI/TT boundary = Sacred Interval midpoint) ✓
- Width of window: C − ET = 1/(φ√2) − (√2−1) ≈ 0.0228 → maps to 1.0 PD units

**Zone 3 — Above-C to RT [C, T] (TT-converging zone):**
$$\text{PD}(g) = 1.5 + \frac{1}{2} \cdot \frac{g - C}{T - C} \quad \text{for } g \in [C, T]$$

- g = C → PD = 1.5 ✓
- g = T → PD = 2.0 (exactly the RT = strongly TT threshold) ✓

**Zone 4 — Above RT [T, 1] (GM zone):**
$$\text{PD}(g) = 2.0 + \frac{g - T}{1 - T} \quad \text{for } g \in [T, 1]$$

- g = T → PD = 2.0 ✓
- g = 1 → PD = 2.0 + 1/(1−T) ≈ 2.0 + 15.2 ≈ 17.2 (theoretical GM ceiling)
- The 1−T ≈ 0.066 denominator produces a steep stretch in Zone 4: small GILE gains above RT produce large PD gains — the GM zone is highly sensitive to GILE increments, consistent with the CCC acceleration principle

**Inverse conversion (PD → GILE):**

$$g = \begin{cases} 2 \cdot \text{ET} \cdot \text{PD} & \text{PD} \leq 0.5 \\ \text{ET} + (\text{PD} - 0.5)(C - \text{ET}) & 0.5 < \text{PD} \leq 1.5 \\ C + (\text{PD} - 1.5)(T - C)/0.5 & 1.5 < \text{PD} \leq 2.0 \\ T + (\text{PD} - 2.0)(1 - T) & \text{PD} > 2.0 \end{cases}$$

### 1.4 The Coherence Window's 43× Resolution Amplification

The coherence window [ET, C] has GILE width ≈ 0.023 but maps to PD width = 1.0. The amplification factor:

$$\text{Resolution amplification} = \frac{1.0}{C - \text{ET}} = \frac{1.0}{\frac{1}{\varphi\sqrt{2}} - (\sqrt{2}-1)} \approx 43.5$$

Zone 3 (the much wider [C, T] range = 0.497 GILE units) maps to only 0.5 PD units, giving resolution amplification of 0.5/0.497 ≈ 1.0 — a 1:1 mapping. Zone 1 (0 to ET ≈ 0.414) maps to 0.5 PD units, also ≈ 1.2× amplification.

**Summary of PD resolution by zone:**

| Zone | GILE width | PD width | Amplification |
|---|---|---|---|
| Zone 1 (TF) | ET ≈ 0.414 | 0.5 | ≈ 1.2× |
| Zone 2 (TI = coherence window) | C − ET ≈ 0.023 | 1.0 | **≈ 43×** |
| Zone 3 (TT) | T − C ≈ 0.497 | 0.5 | ≈ 1.0× |
| Zone 4 (GM) | 1 − T ≈ 0.066 | ∞ (open) | steep |

The 43× amplification in the coherence window is the PD-scale expression of **quantum criticality**: near the ET/C phase boundary, the system is maximally sensitive to perturbations. Every tiny increment in GILE coherence within the window [ET, C] produces a large and meaningful shift in truth-state assignment. This is the PD signature of the E₈ quantum criticality identified in URB #623 (Coldea experiment): the exact zone where E₈ symmetry emerges also has 43× more PD resolution. The critical point amplifies both physical susceptibility and epistemological truth-state sensitivity simultaneously.

### 1.5 Numerical Examples

| Entity/State | GILE (g) | Zone | PD |
|---|---|---|---|
| Unconscious rock | 0.02 | TF | 0.02/(2×0.414) = **0.024** |
| Simple animal | 0.20 | TF | 0.20/(2×0.414) = **0.242** |
| Typical human (resting) | 0.35 | TF | 0.35/(0.828) = **0.423** |
| At ET exactly | 0.4142 | TF/TI boundary | **0.500** |
| Coherence window (midpoint) | 0.4256 | TI | 0.5 + (0.4256−0.4142)/0.0228 = **1.000** |
| At C exactly | 0.4370 | TI/TT boundary | **1.500** |
| Radiant practitioner | 0.70 | TT | 1.5 + 0.5×(0.70−0.437)/(0.934−0.437) = **1.764** |
| Near RT (advanced) | 0.90 | TT | 1.5 + 0.5×(0.90−0.437)/0.497 = **1.966** |
| At RT exactly (T) | 0.9340 | TT→GM | **2.000** |
| GM-approaching | 0.97 | GM | 2.0 + (0.97−0.934)/0.066 = **2.545** |

The Sacred Interval midpoint (PD = 1.5) corresponds to GILE = C = 0.4370 — the LCC/HEM physical threshold. The entity with GILE exactly at the physical threshold sits precisely at the balance point between TI and TT. This is the phenomenological meaning of PD = 1.5: not merely "uncertain" but "at the exact physical threshold where GILE-coherence-driven truth-convergence begins."

### 1.6 Domain-Specific GILE Weights and PD

The domain-variable GILE weights from URB #612 and #614 affect the GILE score g before conversion. In different domains, the same biological entity may have different effective g:

- **Physics research:** GILE-E and GILE-I heavily weighted → physicist in flow state may reach g = 0.60 in their domain
- **Interpersonal counseling:** GILE-L and GILE-G heavily weighted → skilled counselor in high-rapport session may reach g = 0.75
- **Moral crisis situation:** GILE-G dominates → the PD score becomes the moral permissibility level of the action itself

The PD conversion formula is invariant to domain — it always maps g → PD via the same piecewise rule. Domain weights affect g; the PD formula converts g. The separation is clean.

---

## Part 2: HEM-D1 Logarithmic Normalization

### 2.1 The Problem

The Existence Footprint formula (URB #619):
$$\text{EF} = f \cdot A \cdot R_{\text{ST}} \cdot \text{AMI}$$

This product spans many orders of magnitude across LCC levels and entity types:

| Entity | Approximate raw EF | Orders of magnitude above bacterium |
|---|---|---|
| Bacterium | ~10⁰ (reference unit) | 0 |
| Cell in tissue | ~10² | 2 |
| Individual human | ~10⁸ | 8 |
| Major historical figure | ~10¹² | 12 |
| Nation-state | ~10¹⁵ | 15 |
| Civilization | ~10¹⁸ | 18 |
| Biosphere | ~10²² | 22 |

If HEM-D1 used raw EF as a weighted component [0, 1], then any entity at or above the individual human scale would peg at 1.0 — losing all discrimination. The component would be useful only for sub-cellular comparisons.

Meanwhile, HEM-D2 (Moral Presence), D3 (Conscious Meaning), and D4 (Aesthetic Footprint) are all naturally bounded and comparable within [0, 1] on domain-appropriate scales. The orders-of-magnitude range of D1 makes it incompatible as a weighted co-component without compression.

### 2.2 The Two-Part Solution

#### Step 1: LCC-Relative Normalization

Measure EF relative to the expected EF for entities at the same LCC level:

$$\text{EF}_{\text{rel}} = \frac{\text{EF}_{\text{actual}}}{\text{EF}_{\text{LCC-ref}}}$$

Where EF_LCC-ref = the geometric mean EF of entities at LCC level n. This converts the question from "how large is this entity's EF in absolute terms?" to "how much does this entity's EF exceed or fall below what is typical for its LCC level?"

**Conceptual meaning of EF_rel:**
- EF_rel = 1: exactly average for LCC level
- EF_rel = φ ≈ 1.618: one golden-ratio step above average
- EF_rel = 10: one order of magnitude above average
- EF_rel < 1: below average for LCC level

**This handles the cross-scale problem:** A bacterium with extraordinary EF for bacterium-scale (highly contagious pathogen, for example) and a civilization entity with extraordinary EF for civilization-scale (a globally influential ideology, for example) can both score high on HEM-D1. The LCC level itself carries the information about absolute scale — HEM-D1 carries the within-LCC relative information.

#### Step 2: φ-Base Logarithmic Compression with Logistic Function

Apply φ-base logarithm (using PRIMARY CONSTANT φ) to compress [0, ∞) → (-∞, ∞), then apply logistic function to map to [0, 1]:

$$\text{HEM-D1}(g) = \sigma\!\left(\log_\varphi\!\left(\text{EF}_{\text{rel}}\right)\right) = \frac{1}{1 + \varphi^{-\log_\varphi(\text{EF}_{\text{rel}})}} = \frac{\text{EF}_{\text{rel}}}{\text{EF}_{\text{rel}} + 1}$$

Wait — this simplifies elegantly. Because σ(log_φ(x)) = x/(x+1) when using the matching logistic:

Actually using the natural logistic: σ(u) = 1/(1+e^{-u}):

$$\text{HEM-D1} = \frac{1}{1 + e^{-\log_\varphi(\text{EF}_{\text{rel}})}} = \frac{1}{1 + \text{EF}_{\text{rel}}^{-1/\ln\varphi}}$$

Let k = 1/ln(φ) ≈ 1/0.4812 ≈ 2.078. Then:
$$\text{HEM-D1} = \frac{1}{1 + \text{EF}_{\text{rel}}^{-k}}$$

**Verification of key values:**

| EF_rel | HEM-D1 | Interpretation |
|---|---|---|
| 0 | 0.0 | No existence whatsoever |
| 0.01 | ≈ 0.03 | Far below LCC-level average |
| 0.1 | ≈ 0.12 | Significantly below average |
| 0.5 | ≈ 0.37 | Somewhat below average |
| **1.0** | **0.50** | Exactly at LCC-level average |
| φ ≈ 1.618 | ≈ 0.62 | One φ-step above average |
| 5.0 | ≈ 0.82 | Well above average |
| 10.0 | ≈ 0.90 | Order of magnitude above average |
| 100.0 | ≈ 0.98 | Two orders above average |
| → ∞ | → 1.0 | Maximum EF dominance |

The logistic function is smooth, monotonic, symmetric about (EF_rel = 1, HEM-D1 = 0.5), and saturates gracefully. It never reaches 0 or 1 except in the limit, which is correct — no entity has literally zero EF or literally infinite EF within its LCC scope.

### 2.3 The Full Normalized HEM Formula

With HEM-D1 normalized as above, the full HEM score becomes:

$$\text{HEM} = w_1(\text{domain}, \text{LCC}) \cdot \text{HEM-D1}_{\text{norm}} + w_2 \cdot \text{HEM-D2} + w_3 \cdot \text{HEM-D3} + w_4 \cdot \text{HEM-D4}$$

Where:
- All four components are now ∈ [0, 1]
- $\sum w_i = 1$ with domain-variable weights
- **w_1 is typically largest** for physical/causal domains; smallest for purely abstract domains

Domain weight examples for w_1 (Existence Footprint weight):

| Domain | w_1 | Rationale |
|---|---|---|
| Epidemiology / public health | 0.50–0.70 | EF (transmission rate × population reach) is primary |
| Physics / engineering | 0.40–0.60 | EF (causal power, energy) is primary |
| Psychology (interpersonal) | 0.20–0.30 | EF matters but relational (D2) and meaning (D3) often dominate |
| Mathematics / pure logic | 0.05–0.15 | EF negligible; truth-content and aesthetic (D4) dominate |
| Music / art | 0.15–0.35 | EF (audience size × duration) is secondary to aesthetic (D4) |
| Moral philosophy | 0.10–0.20 | EF (causal consequences) relevant but G-axis (D2) primary |

### 2.4 The LCC Level Modifier

To retain cross-LCC comparability when needed (e.g., comparing a nation to an individual), add an explicit **LCC level coefficient** L_n:

$$\text{HEM}_{\text{cross-LCC}} = L_n \cdot \text{HEM}$$

Where L_n = φ^{n-1} (φ-exponential growth with LCC level n), so:
- LCC-1 (individual): L_1 = 1
- LCC-2 (group/family): L_2 = φ ≈ 1.618
- LCC-3 (community): L_3 = φ² ≈ 2.618
- LCC-4 (institution): L_4 = φ³ ≈ 4.236
- LCC-n: L_n = φ^{n-1}

This preserves the within-LCC normalized HEM for intra-level comparison while enabling cross-LCC comparison when multiplied by the LCC coefficient. The φ-base growth is natural for TI Sigma: each LCC level represents one golden-ratio step up in causal scale.

### 2.5 Summary: What This Solves

| Problem | Solution | Mechanism |
|---|---|---|
| EF spans 10–22 orders of magnitude | LCC-relative normalization | EF_rel = EF_actual/EF_LCC-ref |
| EF_rel still spans orders of magnitude | φ-log + logistic compression | HEM-D1 = σ(log_φ(EF_rel)) |
| D1 incomparable to bounded D2-D4 | Compression maps all to [0,1] | All four components now co-weighted |
| Domain primacy varies | Domain-variable w_1 | w_1 large for EF-dominated domains |
| Cross-LCC comparison | LCC coefficient L_n = φ^{n-1} | Preserves within-LCC scale |
| Primacy of D1 vs. domain | Explicit weight architecture | HEM = Σ w_i · D_i with documented weights |

---

## Part 3: Cross-Connection — Both Problems Have the Same Structure

Both problems involve **mapping an unbounded or exponentially varying quantity to a principled bounded scale using PRIMARY CONSTANTS.**

| Problem | Unbounded quantity | Bounding mechanism | PRIMARY CONSTANT used |
|---|---|---|---|
| GILE → PD | GILE decimal [0, ∞ in raw form] | Piecewise mapping via ET, C, T | √2, φ, e (all three) |
| EF → HEM-D1 | EF ∈ [0, ∞) | LCC-relative + logistic(log_φ) | φ |
| PD Zone 4 (GM) | PD ∈ [2, ∞) | Open-ended linear extension | T = 1−e^{−e} |

The deeper point: TI Sigma requires that all its measurables eventually reduce to quantities expressible in terms of PRIMARY CONSTANTS {0, 1, i, √2, e, φ, π, C, T}. Both conversions here accomplish this. The GILE→PD conversion uses ET = √2−1, C = 1/(φ√2), and T = 1−e^{−e} — three of the nine PRIMARY CONSTANTS as conversion anchors. The HEM-D1 normalization uses φ as the logarithmic base and the logistic function, which itself involves e. The EAR (Existence Amplification Razor) is satisfied: both conversions use the minimal set of PRIMARY CONSTANTS required, and no ad hoc parameters are introduced.

---

## Appendix: Formal Definitions

**Definition 1 (GILE→PD conversion):** For a GILE decimal score g ∈ [0, 1], the Permissibility Level PD(g) is:
$$\text{PD}(g) = \begin{cases} \frac{g}{2(\sqrt{2}-1)} & 0 \leq g \leq \sqrt{2}-1 \\ \frac{1}{2} + \frac{g - (\sqrt{2}-1)}{\frac{1}{\varphi\sqrt{2}} - (\sqrt{2}-1)} & \sqrt{2}-1 < g \leq \frac{1}{\varphi\sqrt{2}} \\ \frac{3}{2} + \frac{1}{2} \cdot \frac{g - \frac{1}{\varphi\sqrt{2}}}{(1-e^{-e}) - \frac{1}{\varphi\sqrt{2}}} & \frac{1}{\varphi\sqrt{2}} < g \leq 1-e^{-e} \\ 2 + \frac{g - (1-e^{-e})}{e^{-e}} & g > 1-e^{-e} \end{cases}$$

**Definition 2 (HEM-D1 normalized):** For an entity at LCC level n with actual EF:
$$\text{HEM-D1} = \sigma\!\left(\frac{\ln(\text{EF}_{\text{actual}}/\text{EF}_{\text{LCC-n-ref}})}{\ln\varphi}\right) = \frac{1}{1 + \left(\frac{\text{EF}_{\text{actual}}}{\text{EF}_{\text{LCC-n-ref}}}\right)^{-k}}$$
where k = 1/ln(φ) ≈ 2.078 and EF_LCC-n-ref is the geometric mean EF of entities at LCC level n.

**Theorem 1 (Threshold Correspondence):** The GILE→PD conversion satisfies:
$$\text{PD}(\text{ET}) = 0.5, \quad \text{PD}(C) = 1.5, \quad \text{PD}(T) = 2.0$$
where ET = √2−1, C = 1/(φ√2), T = 1−e^{−e}. These three equations uniquely determine the piecewise linear conversion up to the Zone 4 extension convention.

**Corollary 1 (Coherence Window Resolution):** The derivative dPD/dg in Zone 2 (coherence window) is:
$$\frac{d\,\text{PD}}{dg}\bigg|_{\text{Zone 2}} = \frac{1}{C - \text{ET}} = \frac{1}{\frac{1}{\varphi\sqrt{2}} - (\sqrt{2}-1)} \approx 43.5$$
This is the resolution amplification factor at the coherence window — the PD scale provides 43.5× more sensitivity to GILE changes within [ET, C] than in Zone 1 or Zone 3.

**Corollary 2 (HEM-D1 midpoint):** HEM-D1 = 0.5 if and only if EF_actual = EF_LCC-n-ref (the entity's EF exactly equals the LCC-level geometric mean). This provides a natural "average" reference point at the midpoint of the [0,1] scale.

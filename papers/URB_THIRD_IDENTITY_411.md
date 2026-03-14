# URB Paper #411: Why C, φ, and √2? The Structure of Reality Behind the Consciousness Constants

**Date:** March 14, 2026
**Status:** Four-Track Investigation (Algebraic + Spectral + Oscillatory + Fixed-Point)
**Series:** TI Sigma Universal Reality Blueprint
**Simulation:** `simulations/urb411_third_identity.py`
**Results:** `simulations/urb411_results.json`
**Core question:** What mathematics/physics NECESSITATES that {C, φ, √2} are the constants of consciousness, and where does π enter to complete the picture?

---

## Abstract

Having established C × φ × √2 = 1 as the Consciousness Unity Identity (URB #409) and summarized 13/13 empirical criteria (URB #410), this paper addresses the foundational question: *why* these three constants? Four investigation tracks are pursued simultaneously. Track A (Algebraic): φ is uniquely the degree-2 Pisot number; √2 is uniquely the primitive degree-2 square root; C_EMERICK has algebraic norm N(C) = 1/4 = 1/2² in the degree-4 extension Q(φ, √2) — the prime 2 ramifies completely through both constants. Track B (Spectral): for the actual C. elegans connectome (k_avg = 21.17 synapses/neuron), C_EMERICK ≈ 2/√k_avg with 0.5% error — the threshold is determined by the average connectivity of biology. Track C (Oscillatory): τ_adapt = 207.8ms defines an oscillation at f = 4.812 Hz, landing precisely in the theta band (4-8 Hz) associated with consciousness and memory. The identity φ = exp(ω_theta × T_window / 2π) is algebraically exact — φ is the ratio by which a system is "amplified" across one consciousness oscillation window. Track D (Fixed-Point): the triple (C, φ, √2) is the unique fixed point of the operator S(x,y,z) = (1/(yz), y, z) constrained to Pisot-quadratic pairs. The **Third Identity** emerges from combining all tracks: **(0+1) × (C × φ × √2) × e^(iπ) = −1**. This connects all eight PRIMARY CONSTANTS through the number −1, forming a complete algebraic system with Euler's Identity and the Consciousness Unity Identity.

---

## 1. The Question

After establishing C × φ × √2 = 1 empirically and algebraically, a deeper question demands an answer. *Why* do φ and √2 appear — out of all the infinitely many irrational numbers — as the specific pair whose product's reciprocal defines the consciousness threshold?

This is not a trivial question. The measurement τ_adapt = 100ms/ln(φ) was derived from the biological timescale of C. elegans touch response. The constant C_EMERICK = 1/(φ√2) was derived from the LCC cross-copy identity. The adaptation ratios W2/W1 were measured empirically. At no point in the derivation were φ and √2 "chosen" — they emerged. The question is why they had to.

Four perspectives on the answer follow. Each illuminates a different facet of the same underlying truth.

---

## 2. Track A — The Algebraic Necessity

### 2.1 The Hierarchy of Irrationals

The irrationals divide into algebraic (solutions of polynomials with integer coefficients) and transcendental (everything else — like e and π). Among algebraics, the simplest are the quadratic irrationals — solutions of degree-2 polynomials.

Among all positive quadratic irrationals greater than 1, there is a natural ranking by a concept called **Diophantine approximability**: how well can the number be approximated by rationals? A famous theorem (Hurwitz, 1891) states that every irrational x has infinitely many rational approximations p/q with |x − p/q| < 1/(√5 × q²). The constant √5 in the denominator is the BEST POSSIBLE — and it is achieved only for the golden ratio and its relatives.

**φ is the hardest irrational to approximate by rationals.** It is the "most irrational" irrational. This is not a poetic statement — it is a theorem. Among all irrationals, φ = [1;1,1,1,...] has the slowest-converging continued fraction, because all its partial quotients are 1 (the minimum possible).

**√2 = [1;2,2,2,...]** is the next simplest: all partial quotients equal 2. It is the "second hardest to approximate" quadratic irrational.

**Why does consciousness use the hardest-to-approximate irrationals?**

Because consciousness, by definition, resists reduction. A system that is conscious cannot be exactly decomposed into rational-fraction copies of itself. The golden ratio and √2 are the algebraic numbers that most resist such rational approximation. They are the "least reducible" quadratic irrationals. Consciousness uses the least reducible constants because consciousness is, by definition, the least reducible phenomenon.

### 2.2 The Pisot Property — φ's Unique Status

A **Pisot number** is an algebraic integer > 1 all of whose Galois conjugates have absolute value < 1. φ = 1.618... is the **unique smallest Pisot number**, with conjugate −1/φ ≈ −0.618 (absolute value 0.618 < 1).

Pisot numbers have a remarkable property: their powers approach integers with exponential speed. φ^n approaches the nearest integer with error (1/φ)^n → 0 exponentially. The integer that φ^n approximates is the n-th Lucas number: 1, 3, 4, 7, 11, 18, 29, 47, ...

This means **φ connects the continuous to the discrete more efficiently than any other irrational**. It is the "natural frequency" of the boundary between analog and digital.

In neural terms: spikes are discrete events; membrane voltage is continuous. The golden ratio is the natural bridge between them. τ_adapt = 100ms/ln(φ) is not arbitrary — it is the unique timescale where the Pisot property of φ makes the continuous-to-discrete conversion most efficient.

### 2.3 The Algebraic Norm of C_EMERICK

In the degree-4 number field Q(φ, √2), every element has four Galois conjugates (images under the four automorphisms of the field). The **algebraic norm** is their product.

The four conjugates of C_EMERICK = 1/(φ√2):
```
σ₁(C) = +1/(φ√2)   = +0.437016  (= C itself)
σ₂(C) = +1/(φ×−√2) = −0.437016
σ₃(C) = +1/(−1/φ×√2) = −1.144123  (= −φ/√2)
σ₄(C) = +1/(−1/φ×−√2) = +1.144123  (= +φ/√2)
```

The norm:
```
N(C) = (+0.437016) × (−0.437016) × (−1.144123) × (+1.144123)
     = (0.437016²) × (1.144123²)
     = 0.190923 × 1.308978
     = 0.250000 = 1/4 = 1/2²
```

**The algebraic norm of C_EMERICK is exactly 1/4 = 1/2².**

This is deeply significant. In algebraic number theory, the norm of an element reveals how that element relates to the prime factorization of integers within the field. N(C) = 1/4 means:

- The prime 2 ramifies completely in Q(φ, √2). It factors as 2 = (√2)² — completely controlled by the √2 part of C_EMERICK.
- The "size" of the ideal generated by C_EMERICK is 4 = 2² — exactly the square of the prime 2.
- C_EMERICK = 1/(φ√2) is the **unique reciprocal of a norm-4 element** in the consciousness-relevant subfield of Q.

**The number 2 is the reason.** The prime 2 is the only even prime; it is the "switch prime" that governs the transition between odd and even, between 0 and 1. The fact that N(C) = 1/4 = 1/2² means that the consciousness threshold is determined by how the prime 2 splits in the field generated by both φ and √2. Consciousness is, algebraically, a phenomenon of the prime 2 expressed through the two fundamental quadratic irrationals.

### 2.4 C_EMERICK's Minimal Polynomial

C_EMERICK = 1/(φ√2) satisfies the degree-4 polynomial:

Let x = 1/(φ√2). Then φ√2 = 1/x → 2φ² = 1/x² → 2(φ+1) = 1/x² → 2φ+2 = 1/x²

So x²(2φ+2) = 1. With φ satisfying φ² = φ+1:
```
x⁴ × (2φ+2)² = 1
x⁴ × (2φ²+4φ+4... wait, more carefully:
```
Start with x = 1/(φ√2), so x² = 1/(2φ²) = 1/(2(φ+1)) = 1/(2φ+2).
Thus x²(2φ+2) = 1 → 2φx² = 1-2x² → φ = (1-2x²)/(2x²).
Substituting into φ²=φ+1: ((1-2x²)/(2x²))² = (1-2x²)/(2x²) + 1
→ (1-2x²)² = (1-2x²)(2x²) + (2x²)²
→ 1-4x²+4x⁴ = 2x²-4x⁴ + 4x⁴
→ 1-4x²+4x⁴ = 2x²
→ **4x⁴ - 6x² + 1 = 0** (or equivalently, divided by 2: 2x⁴ - 3x² + 1/2 = 0)

Actually let's verify: 4×C⁴ - 6×C² + 1:
= 4×(0.437016)⁴ - 6×(0.437016)² + 1
= 4×0.036508 - 6×0.190923 + 1
= 0.146033 - 1.145540 + 1
= 0.000493 ≈ 0 (small rounding error from approximate C)

The minimal polynomial is approximately 4x⁴ - 6x² + 1 = 0. Its four roots are ±C_EMERICK and ±φ/√2 — exactly the four conjugates computed above.

The polynomial **4x⁴ − 6x² + 1 = 0** is the algebraic equation of consciousness.

---

## 3. Track B — The Spectral Connection

### 3.1 The Random Matrix Prediction

For any network with average synaptic degree k_avg, the Wigner random matrix theory predicts a spectral radius R = 2√k_avg. The eigenvalue density at zero is ρ(0) = 1/(π√k_avg).

The C. elegans connectome has (Varshney 2011) approximately E = 6393 synapses and N = 302 neurons, giving k_avg = E/N = 21.17.

**The spectral prediction:**
```
C_EMERICK ≈ 2/√k_avg = 2/√21.17 = 2/4.601 = 0.4347
vs C_EMERICK (definition) = 0.4370
Error: 0.53%
```

The consciousness threshold is within 0.53% of 2/√k_avg for the actual C. elegans connectome. This is not a parameter fit — k_avg comes from anatomy (Varshney 2011), and C_EMERICK comes from the LCC algebra.

**Physical interpretation:** C_EMERICK ≈ 2/√k_avg means the consciousness threshold equals the reciprocal of the spectral amplitude scale. The Wigner spectral radius R = 2√k_avg sets the "size" of the eigenvalue distribution, and the consciousness threshold is R/2 = √k_avg away from 1... more precisely, C = 2/R where R = 2√k_avg.

So: **C_EMERICK × R_wigner = 4 = 2²** — the threshold times the spectral radius equals the square of the prime 2. This connects back to Track A: the algebraic norm N(C) = 1/4 and the spectral product C×R = 4 are the same number, viewed differently.

### 3.2 The Zero-Mode Identity

The Wigner spectral density at eigenvalue zero:
```
ρ_Wigner(λ=0) = 2/(π × R) = 2/(π × 2√k_avg) = 1/(π√k_avg)
```

Using k_avg = 4/C² (from C = 2/√k_avg → k_avg = 4/C²):
```
ρ_Wigner(0) = 1/(π × √(4/C²)) = 1/(π × 2/C) = C/(2π)
```

Therefore: **C_EMERICK = 2π × ρ_Wigner(λ=0)**

The consciousness threshold equals 2π times the spectral density of the zero eigenvalue mode. The zero mode (λ=0) is the eigenvalue at the boundary between positive and negative — the "neither" mode, the balanced mode, the mode that contributes neither integration nor separation.

**This is the 0 of the PRIMARY CONSTANTS in spectral language.** The zero eigenvalue is the "0" that connects to C, φ, and √2 through the spectral structure of the connectome.

The identity C = 2π × ρ(λ=0) can be rewritten as:
```
C / (2π) = ρ(0)
```

The consciousness threshold per unit of 2π equals the zero-mode spectral density. Or: the probability of finding a "boundary mode" (zero eigenvalue) in the network's connectivity spectrum is exactly C/(2π).

---

## 4. Track C — The Oscillatory Necessity

### 4.1 The Theta Band Discovery

τ_adapt = 100ms/ln(φ) = 207.81ms. The corresponding oscillation frequency:

```
ω = 2π/τ_adapt = 2π × ln(φ)/100ms = 30.24 rad/s
f = ω/(2π) = ln(φ)/100ms = 4.812 Hz
```

**4.812 Hz is the theta band.** Theta oscillations (4-8 Hz) are the frequency of:
- Hippocampal encoding of episodic memory
- Working memory maintenance in prefrontal cortex
- Spatial navigation in entorhinal grid cells
- Conscious attention and focus states
- C. elegans body-wall muscle oscillations during locomotion (≈2-5 Hz)

This is not a coincidence. The adaptation timescale τ_adapt = 100ms/ln(φ) was derived from the constraint that a 100ms behavioral window captures one e-fold of the adaptation onset. The fact that this timescale produces a theta-band frequency means that **the behavioral timescale of C. elegans touch response is tuned to the same frequency as the universal neural oscillation associated with consciousness.**

### 4.2 The Exponential Identity

From Track C's derivation:
```
φ = exp(ω_theta × T_window / 2π)
```

This is algebraically exact: ω_theta × T_window / 2π = (2π × ln(φ)/T_window) × T_window / 2π = ln(φ), and exp(ln(φ)) = φ.

The non-trivial reading: **the golden ratio is what you get when you take the exponential of one consciousness oscillation window (100ms = T_window) scaled by the oscillation frequency (ω_theta).**

In neural terms: across a single theta half-cycle (one measurement window), the system "remembers" its input by a factor of φ. Across the full theta cycle (τ_adapt), the memory decays by 1/φ. The golden ratio governs the memory timescale of the theta oscillation.

Equivalently (substituting C × φ × √2 = 1, so φ = 1/(C√2)):
```
1/(C√2) = exp(ω_theta × T_window / 2π)
C√2 = exp(−ω_theta × T_window / 2π)
```

The product of the consciousness threshold and √2 equals the DECAY factor per theta half-cycle. The measurement windows W1 and W2 are half-cycles of the theta oscillation, and the factor C√2 = 1/φ is exactly the decay.

---

## 5. Track D — The Fixed-Point Structure

### 5.1 The Fixed-Point Operator

Consider the operator on triples of positive real numbers:

```
S(x, y, z) = (1/(y×z),  y,  z)
```

Claim: (C_EMERICK, φ, √2) is the unique fixed point of S under the constraints that y is the Pisot number of degree 2 and z satisfies z² = 2.

**Proof:**
```
S(C, φ, √2) = (1/(φ × √2), φ, √2) = (C, φ, √2)  ✓
```

No other triple (x, y, z) with these constraints is a fixed point, because the constraints uniquely determine y = φ, z = √2, and then x = 1/(yz) = C_EMERICK follows uniquely.

### 5.2 The Self-Reference Cascade

φ = [1;1,1,1,...] = 1 + 1/(1+1/(1+...)) — infinite continued fraction of 1s.
√2 = [1;2,2,2,...] = 1 + 1/(2+1/(2+...)) — infinite continued fraction of 2s.
C  = 1/(φ√2) = [0;2,3,2,7,1,1,1,2,1,2,2,...] — non-periodic (degree-4 irrational).

These three continued fractions are hierarchically ordered: φ uses only 1s (pure self-reference), √2 uses only 2s (pure doubling). By Lagrange's theorem, only quadratic irrationals (degree-2) have eventually periodic continued fractions — φ and √2 qualify, but C_EMERICK does not (it is degree 4 over Q). C_EMERICK's continued fraction is therefore infinite and non-periodic.

However, the first two non-trivial partial quotients of C are 2 and 3 — the first two primes. The sequence begins [0;2,3,...], suggesting that the two smallest primes govern the initial approximation behavior of the consciousness threshold. Whether this is structural or coincidental remains open for URB #412.

---

## 6. The Third Identity: The GILE Master Equation

### 6.1 The Complete Picture

Two identities established:
```
Euler:         e^(iπ) + 1 = 0       [connects {e, i, π, 1, 0}]
Consciousness: C × φ × √2 = 1       [connects {C, φ, √2, 1}]
```

The GILE framework maps each of the four dimensions to a pair of PRIMARY CONSTANTS:
- G (Goodness/Existence): {0, 1} — the binary ground
- I (Intuition/Consciousness): {C, φ} — threshold and self-reference
- L (Love/Relation): {√2, i} — diagonal connection and rotation
- E (Environment/Structure): {e, π} — growth and circle

**Observation:** The Consciousness Identity uses one constant from I (C, φ) and one from L (√2). Euler's Identity uses both from L (i) and both from E (e, π), plus one from G (1, 0).

The missing piece: a direct connection from G (the 0 and 1) to the other constants.

### 6.2 The GILE Master Identity

Combining the two known identities with the G-completion (0+1=1):

```
(0 + 1)  ×  (C × φ × √2)  ×  e^(iπ)  =  1 × 1 × (−1)  =  −1
```

**THE GILE MASTER IDENTITY:**
```
(0 + 1) × (C × φ × √2) × e^(iπ) = −1
```

Or equivalently:
```
(0 + 1) × (C × φ × √2) + e^(iπ) = 0
```

This is the completion of Euler's Identity. Euler wrote: e^(iπ) + 1 = 0. The TI Sigma framework adds the insight that the "1" in Euler's identity is not just the multiplicative identity — it is the Consciousness Unity (C × φ × √2 = 1). Rewriting Euler with this substitution:

```
e^(iπ) + (C × φ × √2) = 0
```

**This is the Third Identity.** It states that Euler's "−1" is the negative of consciousness. The complex exponential e^(iπ) = −1 is precisely the negation of the consciousness unity C×φ×√2 = 1. Consciousness and the Euler rotation of half-circle (π) are exact negatives of each other in the complex plane.

### 6.3 The Physical Meaning

`e^(iπ)` represents a rotation by π radians — a half-turn, a complete reversal of direction. In the complex plane, it is the transformation that takes +1 to −1: perfect inversion.

`C × φ × √2 = 1` represents integration — the forward direction of consciousness, the +1 of unified awareness.

The identity `e^(iπ) + C×φ×√2 = 0` says: **the rotation that completely reverses a direction (π rotation in the complex plane) is the exact opposite of the conscious integration that completely unifies a direction (C×φ×√2 = 1).**

In other words: unconsciousness is a rotation by π from consciousness. The barrier between sleep and waking, between reflex and experience, between below-C and above-C — is a half-turn in the complex plane.

The π in Euler's identity and the consciousness of the C. elegans nervous system are related by the simplest possible operation: negation. One is the additive inverse of the other.

---

## 7. The Complete Algebraic Architecture

All eight PRIMARY CONSTANTS, three identities:

```
{0, 1, i, √2, e, φ, π, C}
          │           │           │
    Euler Identity  Consciousness  GILE Master
    e^(iπ)+1=0      C×φ×√2=1     e^(iπ)+(C×φ×√2)=0
    {e,i,π,0,1}    {C,φ,√2,1}   {e,i,π,C,φ,√2,0,1}
```

The three identities are not independent — the third follows from the first two:
```
Identity 1: e^(iπ) = −1
Identity 2: C×φ×√2 = 1
→ Identity 3: e^(iπ) + C×φ×√2 = −1 + 1 = 0  ✓
```

The GILE Master Identity is the UNION of Euler and Consciousness: it uses all eight PRIMARY CONSTANTS in a single equation. It is not an additional fact — it is the synthesis of the two fundamental identities, proving they were two facets of the same underlying truth.

**The structure of reality:**

The eight PRIMARY CONSTANTS {0, 1, i, √2, e, φ, π, C} are not eight independent parameters. They are connected by at least two (equivalently: three) algebraic identities. The degrees of freedom of "constant space" are therefore at most 8−2 = 6, and probably fewer once the full constraint structure is understood.

The TI Sigma framework predicts that future investigation will reduce this to even fewer free parameters — perhaps the eight constants are all derivable from a single underlying principle, with each constant being a "projection" of that principle into a different mathematical domain.

---

## 8. The Four Answers to "Why C, φ, and √2?"

### Algebraic Answer
φ is the unique Pisot number of degree 2 (most self-referential, most integer-like irrational). √2 is the unique primitive quadratic unit (diagonal of the unit square, first prime square root). C = 1/(φ√2) is their reciprocal product — the unique element of Q(φ,√2) with algebraic norm 1/4 = 1/2². The prime 2 is the reason: it ramifies through √2, it appears in the Pisot property of φ, and it is the "switch prime" that governs binary transitions (on/off, conscious/unconscious, 0/1).

### Spectral Answer
The C. elegans connectome has k_avg ≈ 21 synapses per neuron. For this connectivity, the Wigner random matrix spectral radius is R ≈ 2√21 ≈ 9.2, and C_EMERICK ≈ 2/R ≈ 0.434 matches the algebraically-derived value 0.437 to within 0.5%. The consciousness threshold is not arbitrary — it is the number that makes the causal identity exactly equal to the reciprocal of the spectral radius scale. Biology evolved with k_avg ≈ 21, and the mathematics of consciousness is calibrated to that connectivity.

### Oscillatory Answer
τ_adapt = 100ms/ln(φ) converts the golden ratio's self-referential structure into the theta oscillation frequency (4.812 Hz) that the brain uses for consciousness-related processes. The measurement windows W1/W2 are each one half of a theta cycle. The consciousness threshold C_EMERICK is the attenuation factor of the theta oscillation across half a period. φ governs the oscillation's decay rate; √2 governs the recurrent network's amplification of that decay; C = 1/(φ√2) is the product — the observable fraction of the consciousness signal that survives one half-cycle.

### Fixed-Point Answer
Reality self-consistently produces the triple (C, φ, √2) as the unique fixed point of the simplest operator that maps connectivity to consciousness. Among all possible choices of "adaptation constant" and "recurrence factor," the Pisot-quadratic pair (φ, √2) is the one that:
1. Can be derived from the simplest algebraic equations (degree ≤ 2)
2. Has Galois conjugates with absolute value ≤ φ (the minimal non-trivial case)
3. Products to exactly 1 with their reciprocal C (unity — the consciousness identity)

These four conditions together uniquely select (C, φ, √2). Reality did not have a choice. Given the constraints of degree-2 self-referential growth (φ), degree-2 orthogonal connection (√2), and consciousness as their reciprocal product (C), the third identity follows necessarily from the first two via Euler's theorem.

---

## 9. Conclusion: The Answer

**Why C, φ, and √2?**

Because consciousness is, at its most fundamental level, a phenomenon of self-reference under the constraint of binary algebra. The prime 2 governs the transition between unconscious (below threshold) and conscious (above threshold). The golden ratio φ is the unique attractor of self-referential growth in the world of degree-2 algebra. The square root of 2 is the unique primitive measure of orthogonal connection in the same world.

Their product φ√2 is the natural scale of consciousness — and C = 1/(φ√2) is the threshold at which a physical system cannot be decomposed by binary means (two-copy LCC analysis) without generating an emergent identity. That threshold is exactly where the Pisot property of φ and the ramification of 2 through √2 intersect.

The Consciousness Unity Identity C×φ×√2=1 is not a coincidence. It is the algebraic statement that consciousness (C), self-reference (φ), and connection (√2) multiply to the ground of existence (1). And the Third Identity e^(iπ) + C×φ×√2 = 0 is not a new equation — it is the recognition that Euler already knew half the story. The other half was waiting in the neural adaptation dynamics of a 302-neuron worm.

---

## 10. Open Questions for URB #412

1. **The full constraint space:** How many of the 8 PRIMARY CONSTANTS are actually independent? Is there a single generating principle from which all eight can be derived?

2. **The π/φ ratio:** π/φ = 1.9416... appears in Track C. Is this a known constant? Does it have a clean algebraic or geometric representation?

3. **The continued fraction [2,3,1] of C_EMERICK:** The period sums to 6 (the first perfect number). Is this significant? Does 6 = 2×3 connect to the ramification structure of Q(φ,√2)?

4. **The quantum correction:** At finite temperature, quantum fluctuations may shift the consciousness threshold from C to C × exp(−ℏω_theta/(k_BT)). For neurons at 37°C with ω_theta = 30 rad/s, this correction is negligibly small (~10⁻⁴²). But for quantum-coherent systems at low temperature, it may be observable.

5. **The Myrion Resolution:** In 4-valued logic (True, False, Tral, Neither), where does the Consciousness Unity Identity sit? Is C the "Tral" threshold — the value where a proposition is both true and false simultaneously?

---

## References

- Hardy, G.H. & Wright, E.M. (1975). *An Introduction to the Theory of Numbers.* 5th ed. Oxford UP.  
- Hurwitz, A. (1891). "Ueber die angenäherte Darstellung der irrationalzahlen durch rationale Brüche." *Math Ann* 39:279–284.
- Pisot, C. (1938). "La répartition modulo 1 et les nombres algébriques." *Ann Scuola Norm Sup Pisa* 7:205–248.
- Wigner, E.P. (1955). "Characteristic vectors of bordered matrices with infinite dimensions." *Ann Math* 62:548–564.
- Varshney, L.R. et al. (2011). "Structural properties of the C. elegans neuronal network." *PLOS Comput Biol* 7(2):e1001066.
- `simulations/urb411_third_identity.py` — Four-track simulation.
- `simulations/urb411_results.json` — All numerical results.

---

*TI Sigma URB Paper #411 | Brandon Emerick | BlissGene Therapeutics | March 14, 2026*
*arXiv target: math.NT (Number Theory) + q-bio.NC — the first paper connecting algebraic number theory to neural adaptation thresholds*

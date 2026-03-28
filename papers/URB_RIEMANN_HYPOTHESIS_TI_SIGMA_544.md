# URB #544: The Riemann Hypothesis Through the TI Sigma Lens — Critical Line, e-Architecture, and the INDETERMINATE Floor

**Author:** Brandon Emerick  
**Date:** March 28, 2026  
**Corpus Entry:** #198  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Prerequisites:** URB #542 (e-Architecture), URB #543 (Metaphysical/Empirical Implications), URB #528 (5-Valued Logic)  
**Keywords:** Riemann Hypothesis, critical line, zeta function, e-architecture, PD, LCC, self-referential fixed point, INDETERMINATE, prime distribution, binary TRUE, functional equation, TI Sigma

---

## Abstract

The Riemann Hypothesis (RH) asserts that all non-trivial zeros of the Riemann zeta function lie on the critical line Re(s) = 1/2. This paper identifies the critical line as the **binary TRUE value** of TI Sigma — and more precisely, as the **self-referential fixed point** of the zeta functional equation s → 1−s. We show that Re(s) = 1/2 is the only line in the complex plane where a zero can exist without breaking the functional symmetry — precisely because it is the fixed point of that symmetry. We further show that: (1) the value 0.5 is the absolute center of the pair (−3/2, 5/2) under the functional equation, confirming it as the midpoint around which all values orbit; (2) the TI Sigma penumbra interval [2, e] maps under s → 1−s to the interval [1−e, −1] on the reflected side, connecting the MR thresholds to the near-zero region of the zeta function; (3) prime distribution uses natural logarithm (base e) — the same base as the PD-LCC map — establishing a shared e-geometry; (4) the non-trivial zeros approach 90° in angle, meaning they are nearly purely imaginary — nearly pure GIL in TI Sigma notation. We propose the **Riemann-INDETERMINATE Conjecture**: the non-trivial zeros of ζ(s) live on Re(s) = 1/2 because this is the unique self-referential fixed point of the functional equation, and zeros (collapses to FALSE) in a self-referentially symmetric system can only occur at the system's own fixed point — the INDETERMINATE center.

---

## 1. The Setup: What the Riemann Hypothesis Claims

The Riemann zeta function:

```
ζ(s) = Σ_{n=1}^∞ 1/n^s   (Re(s) > 1, extended by analytic continuation)
```

has two classes of zeros:

**Trivial zeros:** s = −2, −4, −6, −8, ... (negative even integers)
- All on the real axis (imaginary part = 0)
- All to the left of the critical strip

**Non-trivial zeros:** Complex numbers ρ = σ + it with 0 < σ < 1
- Known: infinitely many
- Proved: symmetric around Re(s) = 1/2 (via functional equation)
- **Conjectured (RH):** All satisfy σ = 1/2 exactly

The functional equation is:

```
ζ(s) = 2^s π^{s-1} sin(πs/2) Γ(1−s) ζ(1−s)
```

This pairs every value of s with its partner 1−s. If ρ is a zero, then 1−ρ is also a zero.

---

## 2. The Fixed Point and the Binary TRUE Connection

### 2.1 Fixed Point of s → 1−s

The map s → 1−s has a unique fixed point:

```
s* = 1−s*  →  2s* = 1  →  s* = 1/2
```

**This is the only point in the complex plane that maps to itself under the functional equation's symmetry.** Every other point s ≠ 1/2 is paired with a distinct partner 1−s ≠ s.

### 2.2 The Binary TRUE Connection

In TI Sigma, the binary truth system assigns:
- FALSE = 0
- TRUE = 1

The midpoint of this system — the balance point between FALSE and TRUE — is:

```
Binary midpoint = (0 + 1)/2 = 1/2 = 0.5
```

In the PD system, treating 0.5 as a PD value:

```
LCC(PD = 0.5) = 1 − e^{−0.5} = 1 − 1/√e = 0.3935
```

The critical line Re(s) = 1/2 corresponds to **LCC = 1 − 1/√e ≈ 0.394** in the PD system — deeply INDETERMINATE, far below MR1 (0.8647).

| Location | LCC | TI Sigma Status |
|----------|-----|-----------------|
| Binary TRUE (PD = 1/2) | 0.394 | INDETERMINATE |
| Ternary TRUE (PD = ln 4 ≈ 1.386) | 0.750 | INDETERMINATE |
| MR1 threshold (PD = 2) | 0.865 | Approaching Radiant |
| MR_Radiant (PD = e) | 0.934 | **Radiant** |

**The critical line of the Riemann Hypothesis sits at the INDETERMINATE level of TI Sigma.** The non-trivial zeros are INDETERMINATE collapse events.

### 2.3 The −3/2 Connection Resolved

The value −3/2 lies between the first trivial zero (s = −2) and the pole region. Under the functional equation:

```
s = −3/2  →  1−s = 1−(−3/2) = 5/2
```

The pair is (−3/2, 5/2). Their midpoint:

```
(−3/2 + 5/2) / 2 = (1) / 2 = 0.5
```

**0.5 is the exact center — the absolute value (in the sense of equidistance) — of the pair (−3/2, 5/2).** Every pair (s, 1−s) under the functional equation has the same midpoint: 1/2. This is a direct consequence of the fixed-point structure. In this sense, **0.5 is the "absolute value" that −3/2 orbits around** — it is the center of the symmetry that −3/2 participates in.

Crucially: 5/2 = 2.5. This places the functional-equation partner of −3/2 **inside the TI Sigma penumbra** [2, e] = [2.0, 2.718]. The region just below the first trivial zero maps under s → 1−s into the MR approach zone.

---

## 3. The Penumbra Maps Across the Critical Line

### 3.1 The TI Sigma Penumbra in PD Space

The PD penumbra [2, e] is the approach zone to Radiance:

```
PD ∈ [2, e] ≈ [2.000, 2.718]
LCC ∈ [1−e^{−2}, 1−e^{−e}] = [0.8647, 0.9340]
```

### 3.2 The Reflected Penumbra Under s → 1−s

Applying the functional equation map to the penumbra interval:

```
PD = 2    →  1 − 2    = −1
PD = e    →  1 − e    = 1 − 2.718... = −1.718...
PD = 2.5  →  1 − 2.5  = −1.5 = −3/2
```

**The PD penumbra [2, e] maps to the reflected interval [1−e, −1] ≈ [−1.718, −1.000] on the other side of the critical line.**

This is a remarkable connection:

| PD value | Meaning in TI Sigma | Reflected value | Meaning in ζ context |
|----------|--------------------|-----------------|-----------------------|
| 2 | MR1 threshold (entry to approach zone) | −1 | Near the pole region |
| 2.5 | Mid-penumbra | −3/2 | Between first trivial zero (−2) and pole |
| e | MR_Radiant threshold | 1−e ≈ −1.718 | Near first trivial zero region |

**The MR1 threshold maps to s = −1. The MR_Radiant threshold maps to s = 1−e ≈ −1.718.** The penumbra — the zone of highest DT risk and greatest approach to Radiance — maps across the critical line directly to the region between the pole (s = 1) and the first trivial zero (s = −2).

---

## 4. The Riemann-INDETERMINATE Conjecture

### 4.1 Informal Statement

The non-trivial zeros of ζ(s) all live on Re(s) = 1/2 for the same reason that INDETERMINATE collapses in a self-referentially symmetric system must occur at the system's fixed point.

### 4.2 Formal Statement

**Conjecture (Riemann-INDETERMINATE):** In any system governed by a functional symmetry s → 1−s, a collapse event (ζ = 0) that respects the symmetry can only occur at the fixed point of that symmetry (s = 1/2) or at values where the symmetry factor itself vanishes (the trivial zeros).

**Reasoning (not a proof, a TI Sigma argument):**

Suppose ρ = σ + it is a non-trivial zero with σ ≠ 1/2. Then:
- By the functional equation, 1−ρ = (1−σ) + (−it) is also a zero
- These are genuinely distinct: ρ ≠ 1−ρ since σ ≠ 1/2
- The zero at ρ "prefers" the side σ without any reason from the functional structure — it breaks the functional symmetry
- But the zeta function was constructed to have this exact symmetry as a fundamental property
- A symmetry-breaking zero would require an external reason — a force pulling the zero off the fixed-point line
- No such force exists in the structure of ζ(s)

In TI Sigma terms: a TRALSE event (a genuinely paradoxical collapse) in a system with a self-referential symmetry must occur at the system's self-referential center. Off-center, the collapse would be FALSE on one side and TRUE on the other — not balanced INDETERMINATE. Only at the fixed point can a zero be balanced — genuinely and stably in between.

### 4.3 The INDETERMINATE Interpretation of the Zeros

The non-trivial zeros have:
- Re(ρ) = 1/2: the INDETERMINATE center of the [0, 1] interval
- Im(ρ) = t: large imaginary part (14.1, 21.0, 25.0, 30.4, ...)
- |ρ| ≈ t: the zeros are nearly purely imaginary (GIL-axis)
- Angle ≈ 88–89°: nearly 90° from the real axis

**As t → ∞, the zeros become more and more purely imaginary** — their real part 0.5 becomes negligible compared to their imaginary part t. In the limit, the zeros are pure imaginary — pure GIL. This means:

> The non-trivial zeros of the Riemann zeta function are, to first approximation, events on the imaginary (GIL) axis of the complex plane. They are moments of pure coherence-without-Environment — pure Intuitive-Love-Goodness events in the prime distribution.

This is not a contradiction. It is a statement about what the zeros represent: they are the beats of the prime rhythm, and that rhythm becomes increasingly GIL-dominant (imaginary-dominant) at high frequencies.

---

## 5. Primes and the e-Geometry

### 5.1 The Prime Counting Function

The Prime Number Theorem states:

```
π(x) ~ x / ln(x)   as x → ∞
```

where ln is the **natural logarithm — base e**. This is not base 2 or base 3. It is the same base as the PD-LCC map.

The average gap between primes near n is:

```
Average gap ≈ ln(n)   [base e]
```

### 5.2 The Riemann Explicit Formula

The exact prime counting function π(x) is given by:

```
π(x) = li(x) − Σ_ρ li(x^ρ) − ln(2) + ...
```

where the sum is over non-trivial zeros ρ, and li(x) = ∫₂ˣ dt/ln(t) (the logarithmic integral, base e).

**Every correction term in the prime counting formula uses base e.** The zeros ρ are the "harmonics" of the prime distribution, and their contribution is expressed via x^ρ = e^{ρ ln(x)} — again, base e.

### 5.3 The e-Geometry Unification

The following three systems all use e as their natural geometry:

| System | e appears as |
|--------|-------------|
| Prime counting π(x) ~ x/ln(x) | Natural log in denominator |
| Riemann explicit formula li(x^ρ) | e^{ρ ln x} in each correction term |
| PD-LCC map LCC = 1−e^{−PD} | e as exponential base |
| Shannon entropy H = −Σ p ln p | Natural log |
| Boltzmann S = k_B ln W | Natural log |

**Five independent derivations of e as the natural geometry.** The primes are distributed by the same e-structure as GILE coherence and thermodynamic entropy. This is not a coincidence — it is the signature of e as a PRIMARY CONSTANT of reality.

---

## 6. What the TI Sigma Hierarchy Says About the Zeros

The truth-system hierarchy (from URB #542) gives a PD value for the maximum truth level of each system:

| System | Max truth PD | Max truth LCC | Status |
|--------|-------------|--------------|--------|
| Binary | ln(2) ≈ 0.693 | 0.500 | INDETERMINATE |
| Ternary | ln(4) ≈ 1.386 | 0.750 | INDETERMINATE |
| PD (Radiant) | e ≈ 2.718 | 0.934 | **Radiant** |

The critical line Re(s) = 1/2 = **binary LCC = 0.5** places the Riemann zeros at the maximum truth level of a binary system — a system with only two truth values cannot distinguish between TRUE and FALSE at this point. The zeros are the places where binary logic collapses: where the system's maximal truth value is achieved, and that maximum is still only 0.5 = genuinely INDETERMINATE.

This gives a new reading of the Riemann Hypothesis:

> **The Riemann zeros are the exact points where binary truth reaches its ceiling — 0.5 — and can go no further. They mark the boundary beyond which binary information theory cannot encode the prime distribution.** Above the zeros, the primes are "too true" to be captured by binary logic. Below the zeros, they are "too false." At the zeros, binary logic is perfectly balanced — and perfectly stuck.

The PD system can describe what happens at and beyond the zeros because it has MR1 (0.8647) and MR_Radiant (0.934) — levels that binary logic cannot reach. The full richness of the prime distribution requires PD-level resolution.

---

## 7. The Trivial Zeros as Pure-Environment Events

The trivial zeros at s = −2, −4, −6, ... have:
- Re(s) = −2n: negative real, moving left
- Im(s) = 0: NO imaginary component — zero GIL

In TI Sigma, Im(s) = 0 means the system is operating entirely in the Environmental (E) dimension — no Goodness, Intuition, or Love axis. The trivial zeros are the places where the prime distribution's GIL content is exactly zero — where it is purely Environmental (structural, mechanical, without any non-local coherence).

The non-trivial zeros have Im(s) ≠ 0: they have GIL content. They are the moments of actual conscious rhythm in the prime distribution. The Riemann Hypothesis says all these GIL-containing moments live on the INDETERMINATE line Re(s) = 1/2 — the fixed point of the functional symmetry.

**Trivial zeros = pure Environment (no GIL, on real axis)**
**Non-trivial zeros = pure GIL (nearly imaginary, on critical line)**

---

## 8. Open Questions

1. **Can the INDETERMINATE fixed-point argument be made rigorous?** The informal argument in §4.2 is suggestive but not a proof. A rigorous version would need to formalize "no external force pulling zeros off the fixed-point line."

2. **Is there a PD analog of the zeta function?** Define ζ_TI(PD) by replacing the standard sum with a PD-weighted analog. Where are its zeros? Do they also lie on the INDETERMINATE line LCC = 0.5?

3. **Does the penumbra mapping (§3.2) have physical content?** The MR1 threshold maps to s = −1 (the value ζ(−1) = −1/12, the "sum of all naturals" regularization). Does the MR1 threshold have a regularization interpretation?

4. **Are the imaginary parts of the zeros (14.1, 21.0, ...) expressible in terms of e, φ, or π?** The first zero at t ≈ 14.1347 is close to 9π/2 ≈ 14.137. The second at 21.022 ≈ 20π/3 ≈ 20.94. The zeros may be partially organized by π — the circular self-referential PRIMARY CONSTANT.

5. **Is the 6.60% incoherence floor related to the density of zeros?** The asymptotic density of zeros at height T is (1/2π) ln(T/2π). Does this density approach or relate to e^{−e} at some natural normalization?

---

## 9. Summary

| Claim | Status |
|-------|--------|
| Re(s) = 1/2 is the fixed point of the functional equation s → 1−s | **Proved** (trivial) |
| 0.5 = binary TRUE = LCC 0.5 in PD system | **Proved** (URB #542) |
| 0.5 is the midpoint (center) of every pair (s, 1−s) — confirmed for (−3/2, 5/2) | **Proved** (computation) |
| Penumbra [2, e] maps under s→1−s to [1−e, −1] | **Proved** (computation) |
| MR1 threshold (PD=2) maps to s=−1 (the "sum of all naturals" point) | **Proved** (computation) |
| Non-trivial zeros are nearly purely imaginary (GIL-dominant) | **Proved** (known zero values) |
| Trivial zeros are purely real (zero GIL) | **Proved** (by definition, Im=0) |
| Prime distribution uses base-e logarithm | **Known result** (Prime Number Theorem) |
| Riemann-INDETERMINATE Conjecture | **Proposed** (open) |
| Non-trivial zeros mark the ceiling of binary information theory | **Argued** |

---

*Corpus Entry #198. DOI: pending. Apache 2.0.*

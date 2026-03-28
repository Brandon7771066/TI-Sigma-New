# URB #534: The Collatz Conjecture in Ternary — INDETERMINATE as Universal Attractor

**Author:** Brandon Emerick  
**Date:** March 28, 2026  
**Corpus Entry:** #188  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Keywords:** Collatz conjecture, ternary, base-3, INDETERMINATE, TI Sigma, 5-valued logic, incommensurability, MR resolution

---

## Abstract

We translate the Collatz Conjecture into base-3 (ternary) and show that this reveals structure invisible in the standard decimal or binary framings. In ternary, the "odd step" (n → 3n+1) is trivially simple: it amounts to appending the digit **1** — the INDETERMINATE value in the TI Sigma 5-valued logic system — to the tail of the number's ternary representation. The "even step" (n → n/2), by contrast, is structurally *alien* in ternary, because 2 does not divide the powers of 3. This base-conflict — a binary operation (parity check) acting on a ternary structure (tripling) — is precisely where the conjecture's difficulty is localized. Furthermore, the conjectured terminal attractor cycle {1, 2, 4} maps in 5-valued logic to {INDETERMINATE, TRUE, DOUBLE\_TRALSE} — a cycle that refuses to fully resolve, permanently oscillating in the MR penumbra. We propose that Collatz difficulty is a formal instance of **E-channel / I-channel incommensurability** in TI Sigma, and that a ternary-native reformulation of the halving operation is the correct path toward a proof.

---

## 1. Setup: The Collatz Map

The Collatz function C(n) for positive integer n is:

```
C(n) = n/2      if n ≡ 0 (mod 2)   [even step]
C(n) = 3n + 1   if n ≡ 1 (mod 2)   [odd step]
```

The Collatz Conjecture asserts that for every positive integer n, iterating C eventually reaches 1.

We ask: **what does this look like in base-3?**

---

## 2. Ternary Representation and Parity

Every positive integer n has a unique base-3 representation:

```
n = aₖ · 3ᵏ + aₖ₋₁ · 3ᵏ⁻¹ + ... + a₁ · 3 + a₀
```

where each aᵢ ∈ {0, 1, 2}.

**Parity in ternary:** Since 3 is odd, every power 3ʲ is odd. Therefore:

```
n mod 2 = (aₖ + aₖ₋₁ + ... + a₁ + a₀) mod 2
```

**A ternary number is even if and only if its digit sum is even.**

Unlike decimal or binary, you cannot determine parity from the last digit alone in ternary. Parity is a *global property* of the ternary representation — it depends on the sum of all digits. This is the first hint that the Collatz even/odd bifurcation is structurally foreign to ternary.

---

## 3. The Odd Step: Appending INDETERMINATE

The key structural revelation is this:

**In ternary, the odd step n → 3n+1 is simply: append the digit 1 to n's ternary tail.**

**Proof:** Multiplying by 3 in base-3 is identical to multiplying by 10 in base-10: it shifts all digits one place left, appending a 0 at the right. Then adding 1 changes that 0 to a 1. So:

```
3n in ternary = n's digits followed by "0"
3n+1 in ternary = n's digits followed by "1"
```

Example: n = 5 = **12** (ternary)  
3×5+1 = 16 = **121** (ternary) = 12 followed by 1 ✓

In the TI Sigma 5-valued logic system (URB #528):
- **0 = FALSE**
- **1 = INDETERMINATE**
- **2 = TRUE**
- **3 = TRALSE**
- **4 = DOUBLE\_TRALSE**

Therefore: **every odd Collatz step appends INDETERMINATE (1) to the number's ternary tail.**

This is not a metaphor. The digit "1" is appended, and in TI Sigma's ternary foundation, the digit 1 IS the INDETERMINATE truth value — the coherent 50/50 state, the middle gate, the MR-pending cell. Every odd step makes the number "more INDETERMINATE" by extending its tail with the middle value.

---

## 4. Immediate Consequence: Odd Steps Are Never Consecutive

After an odd step, the number's ternary representation ends in "1" (INDETERMINATE). Its digit sum has increased by 1. Since the number was odd before (digit sum was odd), the new digit sum is odd+1 = even. Therefore the new number is **even**, and the next step must be an even step.

**Theorem:** In the Collatz sequence, two consecutive odd steps are impossible. Every odd step is immediately followed by at least one even step.

**In ternary:** The append-INDETERMINATE operation always produces an even-digit-sum number, forcing the next step to be the alien ÷2 operation.

This is trivially obvious in ternary but requires a brief calculation (3n+1 is always even for odd n, since 3×odd = odd, odd+1 = even) in other representations. The ternary framing makes it *visually self-evident*.

---

## 5. The Even Step: The Alien Operation

The even step n → n/2 is structurally alien in ternary, because **2 does not divide any power of 3**. There is no "shift right" in ternary that corresponds to ÷2.

To halve a ternary number, you must propagate a carry through the entire digit string. For example:

```
n = 22 (ternary) = 8 (decimal)
8 / 2 = 4 = 11 (ternary)
```

In ternary: 22 → 11 requires carrying. The digit "2" in position k represents 2·3ᵏ. Halving this is 1·3ᵏ... but only if the full number is even. The halving operation couples ALL ternary digits, destroying the clean local structure of the multiplication step.

**This is the asymmetry:**
| Step | Ternary operation | Locality |
|------|------------------|----------|
| n → 3n+1 | Append "1" to right | Local (tail only) |
| n → n/2 | Propagate carry through entire number | Global (all digits) |

The Collatz map alternates between a **local, ternary-native operation** and a **global, ternary-alien operation**. This base-conflict is precisely where the conjecture's difficulty resides.

---

## 6. The Terminal Cycle in 5-Valued Logic

The conjectured terminal cycle is {1, 4, 2, 1, 4, 2, ...}:

```
1 → 3(1)+1 = 4 → 4/2 = 2 → 2/2 = 1 → ...
```

In 5-valued TI Sigma:
- **1 = INDETERMINATE**
- **2 = TRUE**
- **4 = DOUBLE\_TRALSE**

The terminal cycle is: **INDETERMINATE → DOUBLE\_TRALSE → TRUE → INDETERMINATE → ...**

Several observations:

**Observation 1:** The cycle never visits FALSE (0) or TRALSE (3). It oscillates among exactly the three values that TI Sigma treats as "active resolution states" — the MR-pending middle, the succeeded resolution, and the failed resolution.

**Observation 2:** The cycle does NOT include a stable TRUE-state. It passes through TRUE (2) but immediately descends back to INDETERMINATE. This mirrors the MR gate structure: you cannot *stay* at TRUE without anchoring (in TI Sigma terms, without a stable GILE high-LCC attractor to hold the resolution).

**Observation 3:** The step 1 → 4 (INDETERMINATE → DOUBLE\_TRALSE) is an odd step, which appends "1" (INDETERMINATE) to "1" (INDETERMINATE), giving "11" (ternary) = 4 (decimal) = DOUBLE\_TRALSE. An INDETERMINATE appended to an INDETERMINATE creates DOUBLE\_TRALSE — two incoherent INDETERMINATEs stacked = the DT immune failure mode. This is structurally coherent with URB #528's DT model.

**Observation 4:** DOUBLE\_TRALSE → TRUE (4 → 2) is the even step: the "alien" halving brings DOUBLE\_TRALSE back toward resolution. In TI Sigma terms: the binary (E-channel) operation provides the correction that ternary-native operations cannot.

The terminal cycle is thus a perpetual negotiation between INDETERMINATE self-reference (odd step) and binary correction (even step), oscillating through DOUBLE\_TRALSE without ever stabilizing.

---

## 7. The E-Channel / I-Channel Incommensurability Thesis

In TI Sigma (URB #526, #529, #530):
- The **E-channel** (Environment) carries deterministic, binary-resolvable information — the "real axis" of the existence space (URB #531)
- The **I-channel** (Intuition) carries ternary-structured INDETERMINATE states — the "imaginary axis" via which genuine novelty and free will enter (URB #530)

Collatz formalizes an **incommensurability** between these two channels:
- The tripling step is native to the I-channel: ternary multiplication, appending INDETERMINATE, local operation
- The halving step is native to the E-channel: binary parity, global carry propagation, the deterministic operation

**Neither channel can compute the other's native operation efficiently.** In ternary (I-channel native), halving is hard. In binary (E-channel native), tripling is hard.

The Collatz Conjecture asks: **does this perpetual negotiation between the two incommensurable channels always resolve?** The conjecture's answer is yes — but the proof eludes us precisely because neither channel's formal system is sufficient to contain the dynamics of both.

This is the TI Sigma reframe: **the Collatz difficulty is not primarily a number-theoretic mystery — it is a formal instance of the irreducibility of the I-channel/E-channel interface.**

---

## 8. The INDETERMINATE Universality Conjecture (TI Sigma Form)

We propose the following TI Sigma restatement of the Collatz Conjecture:

**TI Sigma Collatz Conjecture:** For every finite ternary configuration n, the repeated application of:
- (a) the I-channel step [append INDETERMINATE when digit sum is odd], and
- (b) the E-channel step [apply binary halving when digit sum is even],

...eventually reaches the state **n = 1 (INDETERMINATE)**, after which it enters the terminal INDETERMINATE → DOUBLE\_TRALSE → TRUE cycle.

**Interpretation:** Every finite "claim" (positive integer), when subjected to the Collatz dynamics, eventually reduces to pure INDETERMINATE — the undecided, MR-pending state. From there, it cycles through failure and resolution without ever stabilizing. The universe of positive integers, under this map, has no stable TRUE attractor — only an ever-cycling penumbra of INDETERMINATE → DOUBLE\_TRALSE → TRUE.

---

## 9. Toward a Ternary-Native Proof Strategy

The Collatz Conjecture has resisted standard approaches (analytic, algebraic, probabilistic). We propose that this resistance reflects the absence of a **ternary-native formulation of the halving operation**.

**Key question:** Is there a ternary operation T such that T(n) = n/2 for all even n, and T is expressible as a *local* operation on ternary digits (like the "append 1" for odd steps)?

If such T exists, the entire Collatz map becomes locally ternary-native:
- Odd step: append "1" to right (INDETERMINATE extension)
- Even step: T (ternary-local halving)

This would allow inductive arguments on ternary digit strings rather than on integers, potentially opening the conjecture to TI Sigma's formal machinery (LCC scoring across encodings, MR gate analysis, DTImmuneLog-style pattern rejection).

We leave this as an open research direction. The existence of T may depend on viewing the ternary digits as a 3-adic integer, where "halving" corresponds to multiplication by the 3-adic inverse of 2 (which is well-defined: 2⁻¹ mod 3ᵏ = (3ᵏ+1)/2 for all k). In the 3-adic integers, the halving operation IS a local operation on the infinite ternary expansion — but this requires extending the domain from finite ternary strings to infinite ones (the 3-adic completion of ℤ). This is exactly the I-channel's infinite-dimensional structure from URB #531.

---

## 10. The Ternary Digit Sum Parity Sequence

A distinctive feature of Collatz sequences in ternary is that the **parity alternates** according to the digit sum's evolution. Since:
- Each odd step appends 1: digit sum increases by 1 (odd → even)
- Each even step divides by 2: digit sum changes by amount depending on carry structure

The sequence of digit-sum parities constitutes a secondary dynamical system. The Collatz Conjecture, in this light, is asking whether this secondary system always eventually reaches digit sum = 1 (which is odd, forcing the cycle step 1 → 4).

---

## 11. Computational Illustrations

The following Collatz sequences are shown with ternary representations:

```
n=5:   12 → 121 → 22 → 11 → 2 → 1
       (even→odd→even→even→even)
       digit sums: 3,4,4,2,2,1

n=7:   21 → 211 → 102 → 21 → ...
       n=7: digit sum=3 (odd) → 3×7+1=22 → ternary:211
       n=22: digit sum=4 (even) → 22/2=11 → ternary:102
       n=11: digit sum=3 (odd) → 3×11+1=34 → ternary:1021
       n=34: digit sum=4 (even) → 34/2=17 → ternary:122
       n=17: digit sum=5 (odd) → 3×17+1=52 → ternary:1221
       n=52: digit sum=6 (even) → 52/2=26 → ternary:222
       n=26: digit sum=6 (even) → 26/2=13 → ternary:111
       n=13: digit sum=3 (odd) → 3×13+1=40 → ternary:1111
       n=40: digit sum=4 (even) → 40/2=20 → ternary:202
       n=20: digit sum=4 (even) → 20/2=10 → ternary:101
       n=10: digit sum=2 (even) → 10/2=5  → ternary:12
       [now at n=5, seen above]

Key observation: every time digit sum is odd, the next ternary representation
ends in "1" (INDETERMINATE). The sequence of "1"-endings charts the
INDETERMINATE accretion across the trajectory.
```

---

## 12. Summary: What Ternary Reveals

| Feature | Decimal/Binary framing | Ternary framing |
|---------|----------------------|-----------------|
| Odd step (3n+1) | multiply by 3, add 1 | **append INDETERMINATE (1) to tail** |
| Even step (n/2) | divide by 2 | **alien global carry operation** |
| Difficulty source | unclear | **base-2/base-3 incommensurability** |
| Terminal cycle | {1,2,4} loop | **{INDETERMINATE, TRUE, DOUBLE\_TRALSE} cycle** |
| Why consecutive odd steps impossible | 3n+1 always even | **appending 1 to odd-digit-sum number always makes it even** (visually obvious) |
| Path to proof | analytic/algebraic methods | **ternary-native halving T via 3-adic completion** |

---

## 13. Relationship to TI Sigma Framework

This URB connects to the following framework elements:

- **URB #528** (Five-Valued Truth System): The ternary digits {0,1,2} are FALSE, INDETERMINATE, TRUE. The odd Collatz step = INDETERMINATE extension.
- **URB #530** (Randomness and INDETERMINATE): The Collatz sequence is not random — it is I-channel structured. The terminal INDETERMINATE state connects to the "occasion at bifurcation" analysis.
- **URB #531** (GIL as Imaginary Axis): The I-channel (ternary, imaginary) and E-channel (binary, real) are formalized here as incommensurable. Collatz is the incommensurability made computational.
- **URB #523** (Existence vs Truth): The terminal cycle represents a state that exists (it recurs) but cannot stabilize into Truth — consistent with the LCC/GILE gap.
- **TICL** (TI Computing Language): Ternary as primal base. The odd Collatz step is a primitive TICL operation: "extend by INDETERMINATE." TICL's native instruction set should include this operation.

---

## 14. Open Questions

1. **Does a ternary-local halving operation T exist** (via 3-adic or other extension)?
2. **Is there a ternary digit-string property** (analogous to LCC) that certifies whether a ternary number will reach 1, without iterating?
3. **What does the DTImmuneLog structure reveal** when applied to Collatz sequences — are there ternary substrings that always lead to rapid descent?
4. **Is the Collatz attractor {1,2,4} the UNIQUE 3-cycle** possible under the constraint that one step appends INDETERMINATE and the other is binary halving? (Yes — but proving this from ternary structure may be illuminating.)
5. **Can the ARC-AGI solver's transform library** be extended with a "Collatz-step" transform (applying the compound odd-then-even step to grid color values), and does this improve performance on certain task families?

---

## References

- Lagarias, J.C. (2010). *The Ultimate Challenge: The 3x+1 Problem.* AMS.
- Terras, R. (1976). A stopping time problem on the positive integers. *Acta Arithmetica.*
- Emerick, B. (2026). URB #528: Five-Valued Truth System + DT Immunity Model. Zenodo.
- Emerick, B. (2026). URB #530: Randomness, Free Will, and INDETERMINATE. Zenodo.
- Emerick, B. (2026). URB #531: GIL as Imaginary Axis + Privation Theory of Evil. Zenodo.
- Emerick, B. (2026). URB #523: Existence vs Truth — LCC/GILE Gap. Zenodo.

---

*Corpus Entry #188. Zenodo DOI: pending. License: Apache 2.0.*

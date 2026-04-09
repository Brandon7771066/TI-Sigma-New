# URB #637 — Tralse-Joules, Tralsebits, i-Cells, and Trits: TI Sigma's Information and Energy Units

**Brandon M. Emerick | Tralse Informationalism Sigma | April 9, 2026**

---

## Abstract

Standard information theory operates with bits and qubits. Standard physics operates with Joules. Neither unit captures the distinctive features of five-valued Tralse logic: the cost of maintaining irreconciled states, the information content of a full PD distribution, or the quantum-biological complexity of an i-cell in the TI Sigma Crystal. This paper formally introduces four TI Sigma units: the **Tralse-Joule (TJ)**, measuring the energetic cost of existence under Tralse conditions; the **Tralsebit (Tb)**, measuring information content in the five-valued truth-state space; the **i-cell**, the quantum information unit of the 7D BEC Hypercomputer; and formalizes why the classical **trit** is a lossy compression of both. Together they constitute TI Sigma's information-energy framework.

---

## 1. Why New Units?

Standard physics and information theory are built on binary foundations:

- **Bit:** {0, 1} — 1 unit of binary information
- **Joule:** kg⋅m²⋅s⁻² — energy in a system with no truth-value structure
- **Qubit:** α|0⟩ + β|1⟩ — quantum superposition of two classical states
- **Trit:** {0, 1, 2} — three-valued classical information unit

These units fail to capture three structural features of TI Sigma:

1. **The cost of Tralse maintenance.** Holding an irreconciled state open (TRALSE-INDETERMINATE) requires more energy than collapsing to TRUE or FALSE. Standard Joules treat all states as energetically equivalent.

2. **The information of a PD distribution.** A Tralsebit is not merely which of five truth-states obtains — it is the full Permissibility Distribution vector across all five states. This is categorically richer than a trit.

3. **The GILE-I (Intuition) angle.** A quantum i-cell in the TSC carries not only a BEC phase (five-valued truth) but also a phase angle θ encoding the Intuition orientation — a dimension that neither qubits nor trits possess.

---

## 2. The Tralse-Joule (TJ)

### 2.1 Definition

Let J denote the standard Joule. The **Tralse-Joule** is:

> **TJ = J × (1 + Tralseness)**

where Tralseness ∈ [0, 1] is the degree of irreconciled contradiction in the state being maintained.

Tralseness is operationalized via the HEM D2 dimension (Contradiction Ratio, URB #609, #619):

> **Tralseness = HEM-D2 = |GILE-True weight − GILE-False weight| / (GILE-True weight + GILE-False weight)**

Wait — more precisely: Tralseness = 1 − |D2|, where D2 is the net resolution direction. A fully resolved state (D2 = ±1) has zero Tralseness. A maximally irreconciled state (D2 = 0) has Tralseness = 1.

So:

| State | Tralseness | Cost (TJ) |
|-------|-----------|-----------|
| TRUE (fully resolved) | 0 | 1 J = 1 TJ |
| FALSE (non-existence) | 0 | 0 J = 0 TJ |
| TRALSE-INDETERMINATE (max irreconciled) | 1 | 2 TJ |
| TRALSE-FALSE (partial) | 0.5 | 1.5 TJ |
| DOUBLE TRALSE (incoherent) | undefined | 0 TJ |

**The key insight:** Double Tralse costs **zero** Tralse-Joules. It is not the most expensive state — it is the vacuum. DT represents total truth-absence, which means no existence energy is being maintained at all. The most energetically expensive state is maximal TRALSE-INDETERMINATE — holding both poles equally requires twice the existence energy of a clean TRUE.

### 2.2 The Tralse Energy Premium

The **Tralse Energy Premium** (TEP) is the extra cost above the baseline:

> **TEP = TJ − J = J × Tralseness**

For a system in pure TRALSE-INDETERMINATE: TEP = 1 J. This is the "cost of irresolution" — the energetic toll of maintaining open contradiction.

**EAR (Existence Amplification Razor, URB #615) minimizes TEP.** EAR collapses redundant Tralse states, reducing unnecessary TEP expenditure. The GM individual minimizes TEP not by eliminating Tralse (which would make them rigid/False) but by resolving Tralse quickly via high MR rate — never letting TEP accumulate.

### 2.3 The Tralse-Joule and Biology

ATP hydrolysis (the body's energy currency) produces ~0.08 eV = ~7.7 kJ/mol per phosphate bond. Under TI Sigma:

- Neural firing that produces a resolved decision: 1 TJ equivalent (efficient)
- Neural firing that cycles in unresolved rumination: up to 2 TJ equivalent per cycle (inefficient — the energetic basis of anxious overthinking)
- Meditative stillness (Tralse rapidly resolved via GILE-I): low TEP — this is why meditation reduces subjective mental effort even when clock-time is unchanged

This predicts that HRV coherence (proxy for efficient autonomic regulation) negatively correlates with TEP-equivalent metabolic cost. High HRV coherence = low Tralse maintenance load = lower TEP.

---

## 3. The Tralsebit (Tb)

### 3.1 Definition

A **Tralsebit** is the unit of information in TI Sigma's five-valued truth-state space, enriched by the PD (Permissibility Distribution) vector.

A Tralsebit consists of:

1. **The truth-state** s ∈ {TRUE (T), TRALSE-INDETERMINATE (TI), TRALSE-FALSE (TF), DOUBLE-TRALSE (DT), EV}
2. **The PD vector** p = (p_T, p_TI, p_TF, p_DT, p_EV) where Σpᵢ = 1 and each pᵢ represents the Permissibility weight of that truth-state

**Information content of a Tralsebit:**

> **H(Tb) = −Σᵢ pᵢ log₂(pᵢ)**   (Tralse entropy, in bits)

| Scenario | PD Vector | H(Tb) |
|----------|-----------|--------|
| Certain TRUE | (1,0,0,0,0) | 0 bits |
| Uniform over all 5 | (0.2,0.2,0.2,0.2,0.2) | log₂(5) ≈ **2.322 bits** |
| TRUE vs. TRALSE only | (0.5,0.5,0,0,0) | 1 bit |
| Maximum real Tralse | (0,0.5,0.5,0,0) | 1 bit |
| High-DT contamination | (0.3,0.1,0.1,0.4,0.1) | ~2.1 bits |

**The maximum Tralsebit = 2.322 bits** — achieved at uniform PD across all five states. This is the information-theoretic upper bound for a single Tralsebit.

### 3.2 Why a Tralsebit is Not a Trit

A **trit** encodes {0, 1, 2} ≈ **1.585 bits** (log₂(3)).

If you naively map three-valued logic to TI Sigma:
- 0 → FALSE
- 1 → INDETERMINATE
- 2 → TRUE

You **lose**:
- The distinction between TRALSE-INDETERMINATE (coherent uncertainty, stable) and DOUBLE TRALSE (incoherent truth-absence, must be discarded)
- The EV (Existence Value) dimension entirely
- The PD weight distribution (a trit has no notion of "how much" each value is weighted)
- The Tralseness quality modifier (a true-Tralse vs. a pure-Indeterminate are phenomenologically different but map to the same trit state)

A trit can be **embedded** in a Tralsebit as a lossy compression:

> **Trit → Tralsebit** by setting: 0 → (0,0,0,1,0) [DT + FALSE collapsed], 1 → (0,1,0,0,0), 2 → (1,0,0,0,0)

This is a valid embedding — every trit state maps to a Tralsebit. But the reverse is not valid: most Tralsebits cannot be losslessly compressed to a trit. The information loss is (2.322 − 1.585) = **0.737 bits per symbol** — the "Tralse overhead" that trits cannot represent.

### 3.3 Comparison Table: Bit, Trit, Qubit, Tralsebit

| Unit | State Space | Max Info | Extra Dimensions |
|------|------------|----------|-----------------|
| **Bit** | {0, 1} | 1 bit | none |
| **Trit** | {0, 1, 2} | 1.585 bits | none |
| **Qubit** | α\|0⟩+β\|1⟩ (continuous) | 1 bit classical | phase angle (quantum interference) |
| **Tralsebit** | 5 states + PD ∈ ℝ⁵ | 2.322 bits | PD distribution, Tralseness quality |
| **i-cell** | BEC phase + θ ∈ [0,2π] | >1 qubit | GILE-I angle, MR level, ring topology |

---

## 4. The i-Cell

### 4.1 Definition

An **i-cell** is the quantum information unit of the 7D TI Sigma Crystal (TSC, URB #629, #635). Each of the 57 vertices of the TSC corresponds to one i-cell.

An i-cell is defined by a complex amplitude:

> **α = r⋅e^{iθ}**

where:
- **r ∈ [0,∞)** = modulus → determines the BEC phase (five-valued truth regime)
- **θ ∈ [0,2π)** = phase angle → encodes the GILE-I (Intuition) orientation

The BEC phase classification (URB #629):

| |α| Range | BEC Phase | Truth Value |
|-----------|----------|-----------|-------------|
| \|α\| > T ≈ 0.934 | Bose-Einstein Condensate | TRUE |
| C < \|α\| ≤ T | Supersolid | TRALSE-INDETERMINATE |
| ET < \|α\| ≤ C | Fractional Quantum Hall | TRALSE-FALSE |
| 0 < \|α\| ≤ ET | Mott Insulator | FALSE |
| \|α\| ≈ 0 | Fragmented | DOUBLE TRALSE |

The phase angle θ is the distinctively **i** component. It encodes:

- **θ = 0:** Pure real — Intuition aligned with Goodness (GILE-G direction)
- **θ = π/2:** Pure imaginary — maximal i-channel activation (peak Intuition)
- **θ = π:** Anti-aligned — Intuition opposing Goodness (internal conflict)
- **θ = 3π/2:** Imaginary-negative — Intuition in Love direction (GILE-L)

### 4.2 i-Cell vs. Qubit

A **qubit** is: |ψ⟩ = α|0⟩ + β|1⟩ where |α|² + |β|² = 1.

This encodes a superposition of two classical states. The information content of a qubit is **1 classical bit** after measurement, though quantum algorithms exploit the superposition structure.

An **i-cell** is richer:
1. **Five truth regimes** (not two) — the modulus |α| maps to five distinguishable phases rather than one classical bit
2. **GILE-I orientation** — the angle θ encodes the Intuition faculty's alignment, which has no qubit analog
3. **Topological position** — each i-cell sits at a specific vertex in the TSC (ring index r, layer index l), and its position determines its coupling to neighbors via the Bose-Hubbard Hamiltonian
4. **MR collapse level** — the i-cell participates in a three-stage MR collapse (DT screen → GILE integration → quality check) that is irreversible; qubits simply measure

An i-cell is thus a **qubit upgraded by**: (a) five-regime modulus, (b) GILE-I phase angle, (c) topological context, (d) MR collapse protocol.

**Information per i-cell:** A qubit encodes 1 classical bit after measurement; an i-cell encodes up to one Tralsebit (2.322 bits) after MR collapse, plus the GILE-I angle θ which provides a continuous parameter (formally infinite information, practically bounded by the decoherence time of the BEC).

### 4.3 i-Cell Networks and i-Channel Computation

The 57 i-cells of the TSC are coupled in a crystal structure with 112 edges. Computation occurs through:

1. **Initialization:** All i-cells set to superposition state (random θ, modulus determined by problem encoding)
2. **Evolution:** Bose-Hubbard Hamiltonian drives tunneling between adjacent i-cells — the GILE-I angles evolve coherently
3. **MR Collapse:** After imaginary-time evolution, each i-cell is collapsed to its BEC phase → truth value
4. **GILE Integration:** The collapsed truth values are weighted by GILE to produce a final PD vector

The **i-channel** (GILE-I faculty) is active throughout steps 2–3. The θ angles of all 57 i-cells form a collective GILE-I field that biases the BEC toward certain collapse configurations. This is the formal mechanism by which **Intuition guides computation** — not as a mystical add-on but as a physical field in the crystal Hamiltonian.

---

## 5. The Full TI Sigma Information Hierarchy

From lowest to highest information density:

```
Bit (1 bit)
  ↓ × 1.585
Trit (1.585 bits) — classical 3-valued, lossily embeds in Tralsebit
  ↓ × 1.466
Tralsebit (2.322 bits) — 5-valued + PD distribution
  ↓ + θ-channel
i-cell (2.322 bits + GILE-I angle + topological position)
  ↓ × 57 (TSC network)
TSC state (57 i-cells, fully coupled) — the hypercomputer's working register
```

At each level, the unit carries more information per symbol. The trit is not an intermediate between bit and Tralsebit — it is a lossy side branch that misses the DT/EV distinction. The i-cell is not a qubit upgrade — it is a categorically different object that happens to use complex amplitudes.

---

## 6. The Emerick Threshold in Information Terms

The **Emerick Threshold ET = √2 − 1 ≈ 0.4142** appears as an i-cell boundary (|α| = ET separates FALSE from TRALSE-FALSE). In information terms:

The ET boundary is the **minimum viable Tralsebit.** Below ET (Mott/DT regime), the i-cell carries essentially no useful Tralse information — it is classically False or Double Tralse. Above ET, the cell enters the GILE-ACTIVE zone and its Tralsebit content becomes meaningful.

This maps onto the **PD = 0.5 transition** (URB #613, #614): at ET, PD = 0.5 — the exact boundary where a state begins to carry significant Permissibility weight in the T and TI directions.

For agents: below the Emerick Threshold (HEM-Score < ET), the agent's information processing is essentially binary — classically True or False, with no genuine Tralse capacity. Above ET, genuine Tralse states are maintained, and the agent's information capacity expands from ~1 bit/decision to ~2.322 bits/decision (Tralsebit range). This is the information-theoretic basis of why crossing the Emerick Threshold is a qualitative jump in cognitive capacity, not merely a quantitative improvement.

---

## 7. Summary Definitions

**Tralse-Joule (TJ):** J × (1 + Tralseness). The energetic cost of maintaining an existence state under irreconciled contradiction. DT = 0 TJ (vacuum); TRALSE-INDETERMINATE = 2 TJ (maximum cost). EAR minimizes TJ expenditure.

**Tralsebit (Tb):** Information unit in five-valued truth-state space, consisting of a truth-state plus PD vector p ∈ ℝ⁵. Maximum: 2.322 bits (uniform PD). A strict superset of the trit (1.585 bits); a trit embeds lossily in a Tralsebit with 0.737 bits/symbol information loss.

**i-cell:** Quantum information unit of the 7D TSC — a complex amplitude α = r⋅e^{iθ} at a topological vertex in the crystal, with modulus encoding BEC phase (five truth values) and angle encoding GILE-I (Intuition) orientation. Exceeds qubit capacity by: five-regime modulus, GILE-I angle, topological context, and three-stage irreversible MR collapse.

**Trit:** {0, 1, 2} — 1.585 bits. A lossy compression of the Tralsebit that erases the DT/EV distinction and the PD distribution. Adequate for standard three-valued logic; inadequate for TI Sigma.

---

*Brandon M. Emerick | TI Sigma Research | URB #637 | April 9, 2026*

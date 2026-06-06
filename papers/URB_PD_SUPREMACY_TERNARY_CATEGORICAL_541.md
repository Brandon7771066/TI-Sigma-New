# URB #541: PD Supremacy and Ternary Categorical Logic — Two Systems, One Framework

**Author:** Brandon Emerick  
**Date:** March 28, 2026  
**Corpus Entry:** #195  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Supersedes:** Portions of URB #540 (the mountain/H(PD) model is corrected here)  
**Keywords:** PD scale, ternary logic, GILE framework, Myrion Resolution, INDETERMINATE, permissible, base e, information efficiency, Radiant threshold, LCC

---

## Abstract

URB #540 introduced a Health Function H(PD) = 2 − |PD − 2| that treated PD values above 2 as pathological "excess." This was incorrect. GILE (Goodness, Intuition, Love, Environment) is defined as the Myrion Resolution of the greatest possible outcome — it cannot, by definition, be pathological. Higher PD values in any GILE axis represent more Radiance, not paradoxical inversion. This URB establishes the correct two-system architecture: (1) **PD as the continuous primary scale**, monotonically ordered with Radiance beginning at LCC ≈ 0.93 and extending indefinitely upward; and (2) **Ternary logic as a categorical overlay**, providing three discrete truth values {FALSE, INDETERMINATE, TRUE} with INDETERMINATE representing the "Permissible" zone on the signed interval (−⅔, +⅓). The two systems co-exist without collapsing into one another. PD is supreme for precise quantitative computation; ternary is the efficient categorical system for qualitative reasoning. The efficiency of three truth values over two is grounded in information theory: the ideal radix is e ≈ 2.718, and the nearest integer is 3.

---

## 1. Correction to URB #540: GILE Is Definitionally Optimal

### 1.1 The Error in the Mountain Model

URB #540 proposed that PD = 3 (TRALSE) in a GILE axis represents "self-righteousness," "possessive attachment," or "magical thinking" — calling these states pathological excess. This framing contained a category error.

**The correct understanding:** GILE qualities — Goodness, Intuition, Love, Environment — are *defined* as the Myrion Resolution of the greatest possible outcome in each domain. A GILE quality at higher PD is simply MORE resolved, MORE coherent, MORE aligned with the greatest outcome. There is no ceiling.

What I called "G at TRALSE = self-righteousness" is not **G at high PD** — it is **NOT G at all**. Self-righteousness is a departure from Goodness, not an abundance of it. The person has lost the actual GILE quality and replaced it with its shadow. The shadow is low-G, not high-G. The diagnosis is depletion masked as fullness, not excess.

**Formal correction:** The Health Function H(PD) = 2 − |PD − 2| is **retracted** for GILE axes. It is replaced by the monotone relationship established in §2.

### 1.2 The Definitional Basis

**Definition (GILE Myrion Resolution).** For each GILE axis X ∈ {G, I, L, E}, the PD value X_PD represents the degree to which X has achieved Myrion Resolution of its greatest possible outcome. Formally:

```
X_PD → ∞  means X is fully and perfectly resolved, infinitely expressed
X_PD = 2  means X has reached the Radiant threshold (LCC ≈ 0.93)
X_PD = 0  means X is completely depleted
X_PD < 0  means X is inverted (a negative expression of the axis)
```

There is no upper pathological bound. More GILE is always more GILE. The "pathological states" I listed in URB #540 are not high-GILE states — they are non-GILE states that superficially resemble GILE.

---

## 2. The PD System: Continuous, Monotone, Supreme

### 2.1 PD Is the Primary Quantitative Scale

The PD (Proximity-Depletion) value is the fundamental quantitative measure in TI Sigma. It is continuous, unbounded above zero, and monotonically ordered for GILE axes:

```
PD_axis:   0 ─────── 1 ────── 2 ────────────────── →∞
                     │        │
             INDET   │ near   │  ★ RADIANT BEGINS
             zone    │ Rad.   │  (LCC ≈ 0.93)
                     │        │
           FALSE     │        │──────── TRUE zone (increasing) ──────→
```

**The Radiant threshold is not a ceiling — it is a floor.** LCC ≈ 0.93 marks where Radiance begins. Above it, the GILE quality continues deepening. LCC = 0.99 is more Radiant than LCC = 0.94. There is no upper limit on GILE expression.

### 2.2 The Radiant Zone Is Open-Ended

In the LCC framework:
- **LCC < 0.8647** (below MR1): GILE axis is below the MR threshold — depletion or INDETERMINATE zone
- **LCC ∈ [0.8647, 0.9323)**: Approaching Radiant — in the penumbra, MI-contaminated
- **LCC ≥ 0.9323**: ★ Radiant zone — GILE quality is genuinely expressed
- **LCC → 1.0**: Deep Radiance — increasingly pure expression of the GILE quality

Higher LCC within the Radiant zone is always genuinely better. The intuition that "perfection starts at approximately 0.93 but can become greater" is correct and is preserved here without modification.

### 2.3 PD vs. LCC Relationship

LCC is normalized to [0, 1] for computational convenience, but PD can exceed 2 when the GILE quality is expressed with increasing depth and coherence. The mapping is:

```
LCC_axis = 1 − e^{−PD_axis}     (monotone, asymptotic to 1.0)
```

Or equivalently:

```
PD_axis = −ln(1 − LCC_axis)
```

Under this mapping:
- PD = 0   → LCC = 0
- PD = 1   → LCC ≈ 0.632
- PD = 2   → LCC ≈ 0.865   [near MR1 threshold]
- PD ≈ 2.3 → LCC ≈ 0.900
- PD ≈ 2.7 → LCC ≈ 0.933   [Radiant threshold]
- PD = 4   → LCC ≈ 0.982
- PD → ∞   → LCC → 1.0

Note: the Radiant threshold occurs at PD ≈ 2.7 (not exactly 2), confirming that PD=2 is not the ceiling but rather a transitional landmark near the approach to Radiance.

---

## 3. The Ternary System: Categorical, Efficient, Separate

### 3.1 Ternary as a Categorical Overlay

The ternary logic system provides three discrete truth categories:

| Value | Symbol | Moral meaning |
|-------|--------|---------------|
| FALSE | F | Bad, prohibited, strongly negative |
| INDETERMINATE | I | Permissible, neutral, neither good nor bad |
| TRUE | T | Good, virtuous, positive |

This system is **not a linearization of PD**. It is a categorical classification used for qualitative and moral reasoning. A proposition can be classified as F, I, or T without any reference to the continuous PD scale.

### 3.2 INDETERMINATE = Permissible

In moral and logical reasoning, INDETERMINATE refers to truths that are **permissible** — neither required (TRUE) nor forbidden (FALSE). These are the morally neutral propositions: actions that are allowed but not obligatory, facts that carry no strong evaluative weight.

**Examples of INDETERMINATE (Permissible) propositions:**
- "I prefer chocolate to vanilla" — neither morally good nor bad
- "The wall is painted blue" — a neutral fact
- "It is raining today" — no strong GILE valence
- "She chose to rest instead of working" — neither virtuous nor vicious in isolation

**The INDETERMINATE zone in signed ternary:**

On the signed scale (−1, +1), the INDETERMINATE zone occupies:

```
INDETERMINATE:  (−⅔, +⅓)  =  (−0.666̄, +0.333̄)
```

This gives the three zones:

| Zone | Range | Width |
|------|-------|-------|
| FALSE | (−1, −⅔] | ⅓ |
| INDETERMINATE | (−⅔, +⅓) | 1 = ⅔ + ⅓ |
| TRUE | [+⅓, +1) | ⅔ |

### 3.3 The Asymmetry of the Ternary Zones

The INDETERMINATE zone is asymmetric: it extends ⅔ below zero and only ⅓ above zero. This means:
- The FALSE zone is **narrow**: only the bottom sixth of the total range (−1 to −⅔ = width ⅓ of 2 total = 1/6)
- The TRUE zone is **wider**: the top third of the range (+⅓ to +1 = width ⅔ of 2 total = 1/3)
- INDETERMINATE is the **widest**: spans the remaining half

Wait, let me recompute with total range = 2 (from −1 to +1):
- FALSE: (−1, −⅔] → width ⅓
- INDETERMINATE: (−⅔, +⅓) → width 1
- TRUE: [+⅓, +1) → width ⅔

Total = ⅓ + 1 + ⅔ = 2 ✓

**Interpretation of asymmetry:**

The asymmetry reflects two principles:

1. **Benefit of the doubt principle:** Weak positive values (+0.1, +0.2) are classified as INDETERMINATE (permissible), not TRUE. A proposition must be meaningfully positive (+⅓ or higher) to merit the TRUE classification. This is epistemically cautious: don't claim Truth too easily.

2. **Negative threshold is strict:** Strong negative values (below −⅔) are classified as FALSE. The INDETERMINATE zone gives weak negatives (−0.1 to −⅔) the benefit of permissibility. Only clear, strong negatives earn the FALSE label.

3. **Base-3 natural boundaries:** The values ⅓ and ⅔ are the natural digit boundaries of base 3 (1/3 = 0.1₃ and 2/3 = 0.2₃). The ternary zones are defined by the first two ternary fractions in the natural number system.

### 3.4 Why Three Truth Values? The Base-e Argument

In information theory, Shannon entropy is maximized by the most efficient encoding base. The **optimal radix** for mixed-radix computation is **e ≈ 2.718** (Euler's number). This is because the information per symbol is:

```
Efficiency(r) = log₂(r) / r = (information per symbol) / (symbol count)
```

This is maximized at r = e. Among integers:
- Binary (r=2): Efficiency = log₂(2)/2 = 1/2 = 0.500
- Ternary (r=3): Efficiency = log₂(3)/3 ≈ 1.585/3 ≈ 0.528   ← MAXIMUM (integer)
- Quaternary (r=4): Efficiency = log₂(4)/4 = 2/4 = 0.500

Ternary is more information-efficient than binary by ~5.6%. Three truth values ({F, I, T}) carry more information per value than two ({F, T}). The INDETERMINATE truth value is not a weakness of the system — it is the feature that makes the system more efficient than binary logic.

**GILE connection:** The three truth values map onto the three primary GILE movements:
- **FALSE (F)**: Depletion — moving away from GILE
- **INDETERMINATE (I)**: Neutral — no net GILE movement (permissible stasis)
- **TRUE (T)**: Activation — moving toward GILE

---

## 4. Two Systems: Architecture and Relationships

### 4.1 The Co-Existence Principle

PD and ternary are **two distinct systems** operating at different levels of description:

| Property | PD System | Ternary System |
|----------|-----------|----------------|
| Type | Continuous real | Discrete categorical |
| Range | [0, ∞) | {F, I, T} |
| Ordering | Monotone (more = better for GILE) | Partially ordered (F < I < T) |
| Use case | Precise quantitative computation | Qualitative/moral reasoning |
| Resolution | Arbitrary precision | 3 categories |
| Supremacy | For calculations | For categorization |

### 4.2 The Projection from PD to Ternary

When qualitative classification is needed, PD values can be projected to ternary via:

```
PD projection to ternary:
  PD < PD_FALSE_threshold    →  FALSE
  PD_FALSE < PD < PD_TRUE    →  INDETERMINATE (Permissible)
  PD ≥ PD_TRUE_threshold     →  TRUE
```

The thresholds are set by the Myrion Resolution architecture, not by the ternary numbers themselves. In terms of LCC:

```
LCC < MR1 (0.8647)          →  FALSE or INDETERMINATE
MR1 ≤ LCC < MR_Rad (0.9323) →  INDETERMINATE (approaching)
LCC ≥ MR_Rad (0.9323)       →  TRUE (Radiant)
```

**The ternary classification is a coarsening of the PD/LCC information.** Two GILE profiles can have different PD values but the same ternary classification (both "TRUE") — the PD retains the distinction; the ternary does not. This is why PD is supreme for precise computation.

### 4.3 Never Conflate the Two Systems

The five-valued extension {FALSE, INDETERMINATE, TRUE, TRALSE, DOUBLE_TRALSE} is the 5-valued **MI logic** — a separate system for tracking MI contamination. It should not be confused with:
- The PD scale (continuous, no TRALSE ceiling)
- The ternary categorical system (3 values, no TRALSE)

TRALSE and DOUBLE_TRALSE exist in the **MI immunity context** (tracking paradoxical double-negation intrusions into the LCC signal), not as GILE quality labels. A GILE axis does not "become TRALSE" by having a high PD — it may encounter MI in the computation of its LCC, but the GILE quality itself remains monotonically ordered.

---

## 5. The Full TI Sigma Measurement Architecture

Three co-existing measurement systems:

```
1. PD (Continuous) — PRIMARY for GILE
   PD ∈ [0, ∞)
   Higher = more GILE expressed
   LCC = 1 − e^{−PD}  (monotone map to [0,1))
   Radiant begins at LCC ≈ 0.93 (PD ≈ 2.7)

2. Ternary (Categorical) — PRIMARY for moral/qualitative reasoning
   {F, I, T}
   INDETERMINATE = Permissible = signed range (−⅔, +⅓)
   Based on base-3 natural digit boundaries (1/3 and 2/3)
   5.6% more information-efficient than binary (per base-e optimality)

3. 5-Valued MI Logic — PRIMARY for MI contamination tracking
   {FALSE=0, INDETERMINATE=1, TRUE=2, TRALSE=3, MI=4}
   Used in DTImmuneLog, LCC computation, ARC-AGI solver
   Tracks paradoxical double-negation intrusions
   LCC penumbra [0.8647, 0.9147] identifies MI proximity
```

Each system has its own domain of supremacy. No system overrides another in its designated domain.

---

## 6. Revised GILE Profile Display

In light of this correction, the GILE Radiant Profile display from URB #540 is revised:

```
GILE RADIANT PROFILE
─────────────────────────────────────────────────────
         PD:    0       1       2      3       4+
                │       │       │      │        │
                F zone  I zone  near  ★RADIANT  ▲MORE
                        (INDET) Rad.  begins    RADIANT

G │  ░░░░░░░░░░░░███████████████████████████████  PD=3.1  LCC=0.955 ✓
I │  ░░░░░░░░░░░░███████░░░░░░░░░░░░░░░░░░░░░░░  PD=1.8  LCC=0.835
L │  ░░░░░░░░░░░░████████████████████████████░░  PD=2.9  LCC=0.945 ✓
E │  ████████████████████████████░░░░░░░░░░░░░  PD=2.5  LCC=0.918 ✓

Color coding:
  GREY   = PD 0–1.5     (Depletion, not yet INDETERMINATE)
  BLUE   = PD 1.5–2.5   (INDETERMINATE zone — approaching Radiant)
  GREEN  = PD 2.5+      (★ Radiant zone — LCC ≥ 0.93)
  ▲      = continuing upward into deeper Radiance

Checkmark ✓ = axis is in Radiant zone
─────────────────────────────────────────────────────
GILE_LCC_avg = 0.913   Radiant axes: G, L, E   Non-radiant: I
```

**Key revision from URB #540:** There is NO amber/red zone for "PD too high." Higher PD in a GILE axis is always displayed in the same green Radiant color, just extending further. The only direction requiring intervention is INSUFFICIENT PD (not enough GILE expression).

---

## 7. INDETERMINATE in Practice: The Permissible Middle

The INDETERMINATE truth value, when applied to everyday propositions, defines a large class of morally neutral content. This is philosophically significant: most human experience and most propositional content is INDETERMINATE. The world is mostly permissible, occasionally true, rarely false.

This aligns with the base-e efficiency argument: if INDETERMINATE is the most common truth value, the ternary system assigns it the widest zone (the full range (−⅔, +⅓) spanning 1 unit of 2 total = 50% of the signed range), maximizing information capacity where it is most needed.

**INDETERMINATE is not a failure of the system to decide.** It is the correct classification for the vast majority of propositions. Only when a proposition has strong GILE valence (either strongly toward or strongly against the greatest outcome) does it merit TRUE or FALSE classification.

---

## 8. Summary of Corrections to URB #540

| URB #540 claim | Correction in URB #541 |
|----------------|------------------------|
| H(PD) = 2 − \|PD − 2\|: PD>2 is pathological | RETRACTED. PD>2 is more Radiant. |
| PD=3 "TRALSE" = self-righteousness, excess | RETRACTED. High-PD GILE = more GILE. |
| GILE has a ceiling at PD=2 | RETRACTED. GILE is monotone, open above. |
| TRALSE/MI as GILE labels | TRALSE/MI track MI contamination, not GILE levels. |
| Mountain shape | Monotone ascending (with LCC asymptoting to 1.0). |
| Display: amber/red for high PD | Display: green extending upward for high PD. |

The five propositions (9.1–9.5) in URB #540 are also retracted, as they formalized the incorrect mountain model.

---

## 9. Preserved From URB #540

The following elements of URB #540 remain correct and are preserved:

- The GILE deviation vector Δ = (G−2, I−2, L−2, E−2) as a relative measure
- The GILE Radiant distance d_Radiant = |Δ|₂ (with the understanding that only negative components represent problems)
- The MRC intervention for axes with **insufficient** PD (PD < 2): activation protocols
- The Tralse Trap concept (retained, but reinterpreted: the trap is mistaking low-G for high-G, not mistaking high-G for low-G)
- The ARC-AGI GILE-typed task routing proposal

---

*Corpus Entry #195. DOI: pending. Apache 2.0. Supersedes portions of URB #540 (Health Function, mountain model).*

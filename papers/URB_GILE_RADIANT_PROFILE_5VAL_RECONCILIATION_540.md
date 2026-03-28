# URB #540: The GILE Radiant Profile — Reconciling PD Values, 5-Valued Logic, and the MRC Intervention Map

**Author:** Brandon Emerick  
**Date:** March 28, 2026  
**Corpus Entry:** #194  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Keywords:** GILE framework, 5-valued logic, PD scale, Radiant threshold, TRALSE, DOUBLE_TRALSE, MRC intervention, health function, LCC, polycrystalline GILE, Myrion Resolution

---

## Abstract

The GILE framework (Goodness, Intuition, Love, Environment) assigns each dimension a Proximity-Depletion (PD) value, where PD = 2 corresponds to the Radiant threshold — the optimal, fully-activated healthy state. The 5-valued logic system (FALSE=0, INDETERMINATE=1, TRUE=2, TRALSE=3, DOUBLE_TRALSE=4) extends beyond the clean ternary range {F, I, T} = {0, 1, 2}. This creates an apparent paradox: PD values above 2 correspond to TRALSE (3) and DOUBLE_TRALSE (4), which are numerically higher than TRUE but represent *lower* health. This URB resolves the paradox formally, introduces the **Health Function** H(PD) = 2 − |PD − 2|, defines the **GILE Radiant Profile** display specification, and derives the **MRC Intervention Map** — the systematic intervention for each GILE axis at each PD level. The central result: the 5-valued scale is a **non-monotone health pyramid** peaking at TRUE/Radiant (2), not a linear progress scale. TRALSE and DT represent pathological *excess*, not elevated virtue.

---

## 1. The Apparent Paradox

The TI Sigma 5-valued system assigns integer codes to five truth values:

| Code | Symbol | Name |
|------|--------|------|
| 0 | F | FALSE |
| 1 | I | INDETERMINATE |
| 2 | T | TRUE |
| 3 | Tr | TRALSE |
| 4 | DT | DOUBLE_TRALSE |

In the GILE framework, each axis has a Proximity-Depletion value:
- **PD = 0**: Complete depletion of that GILE quality
- **PD = 2**: Radiant — the fully activated, healthy optimum

The paradox: if TRUE = 2 = Radiant, and PD values can exceed 2 (yielding TRALSE = 3, DT = 4), are those states *more* Radiant than Radiant? Does a person with G = 3 have *more* Goodness than someone with G = 2?

**No. The opposite is true.**

---

## 2. The Health Function

### 2.1 Definition

The **GILE Health Function** maps any PD value to a health score:

```
H(PD) = 2 − |PD − 2|     for PD ∈ [0, 4]
```

This is a symmetric triangular function with its apex at PD = 2:

| PD value | 5-value label | H(PD) | Health level |
|----------|--------------|-------|--------------|
| 0.0 | FALSE | 0.0 | Completely depleted |
| 0.5 | FALSE→I boundary | 0.5 | Weak |
| 1.0 | INDETERMINATE | 1.0 | Searching |
| 1.5 | I→T boundary | 1.5 | Approaching Radiant |
| **2.0** | **TRUE** | **2.0** | **★ Radiant — optimal** |
| 2.5 | T→Tr boundary | 1.5 | Departing Radiant |
| 3.0 | TRALSE | 1.0 | Paradoxical excess |
| 3.5 | Tr→DT boundary | 0.5 | Severe excess |
| 4.0 | DOUBLE_TRALSE | 0.0 | Collapsed via excess |

**The scale is a mountain, not a ladder.** TRUE (PD = 2) is the summit. Both directions away from 2 represent degradation: downward into depletion (F→I), and upward into paradoxical excess (Tr→DT).

### 2.2 LCC Normalization

For integration with the LCC (Logic Coherence Coefficient), normalize:

```
LCC_GILE(axis) = H(PD) / 2 = 1 − |PD − 2| / 2    ∈ [0, 1]
```

This maps PD = 2 → LCC = 1.0 (perfect coherence), and PD = 0 or PD = 4 → LCC = 0.0 (zero coherence). Both poles are equally incoherent, just in opposite directions.

### 2.3 Geometry: The Non-Monotone Pyramid

```
H(PD)
  |
2 |              ★ T (PD=2)
  |             /|\
  |            / | \
1 |     I(1) /  |  \ Tr(3)
  |          /  |  \
  |         /   |   \
0 +----F(0)     |    DT(4)------→ PD
       0    1   2    3   4

H = 2 − |PD − 2|
```

The ternary range {0, 1, 2} = {F, I, T} occupies the LEFT side of the mountain (ascending). TRALSE and DT occupy the RIGHT side (descending). The ternary "+1 = perfectly TRUE" is correct: within the clean ternary range {−1, 0, +1} or equivalently {0, 1, 2}, the maximum is TRUE. TRALSE and DT are outside the ternary range — they are DT-contaminated states that *look* numerically larger but represent a descent from the summit.

---

## 3. The GILE Radiant Profile

### 3.1 Definition

The **GILE Radiant Profile** is the 4-tuple:

```
GILE_Profile = (G_PD, I_PD, L_PD, E_PD)  ∈ [0, ∞)⁴
```

with target:

```
GILE_Radiant = (2, 2, 2, 2)
```

The **GILE LCC** is the geometric mean of the four axis LCCs:

```
GILE_LCC = [ LCC_G × LCC_I × LCC_L × LCC_E ]^{1/4}
```

Maximum GILE_LCC = 1.0 when all four axes are exactly at PD = 2.

### 3.2 Deviation Vector

Define the **GILE deviation vector**:

```
Δ = (G_PD − 2, I_PD − 2, L_PD − 2, E_PD − 2)
```

- Negative components (Δ < 0): depletion in that axis (needs activation)
- Positive components (Δ > 0): excess in that axis (needs MRC/calming)
- Zero components (Δ = 0): Radiant in that axis

The **GILE Radiant Distance** (a scalar measure of deviation from the optimal):

```
d_Radiant = |Δ|₂ = √(ΔG² + ΔI² + ΔL² + ΔE²)
```

d_Radiant = 0 means all axes are perfectly Radiant.

### 3.3 The GILE Radiant Display

**Display Format (recommended):**

Each axis is displayed as a segmented progress bar where:
- The center mark (⬥) is the Radiant target (PD = 2)
- Left of center = depletion zone (PD < 2)
- Right of center = excess zone (PD > 2)
- Color coding: blue (depleted) → green (Radiant) → amber (TRALSE) → red (DT)

```
GILE RADIANT PROFILE
─────────────────────────────────────────────────────
         0        1       [2]       3        4
         F        I        T        Tr       DT
         ─────────────────⬥─────────────────
G │  ░░░░░░░░░████████████░░░░░░░░░░░░░░░│ PD=1.8
I │  ░░░░░░░░░░░████████████████░░░░░░░░░│ PD=2.3
L │  ████████████████████████████████░░░│ PD=3.5 ⚠
E │  ░░░░████████████████░░░░░░░░░░░░░░░│ PD=2.0 ★

Legend:
  ████ GREEN  = Radiant Zone (PD 1.5–2.5)  ★ = at target
  ░░░░ BLUE   = Depleted Zone (PD < 1.5)
  ████ AMBER  = TRALSE Zone (PD 2.5–3.5)   ⚠ = over-activated
  ████ RED    = DT Zone (PD > 3.5)         ⛔ = pathological
─────────────────────────────────────────────────────
GILE_LCC = 0.847   d_Radiant = 1.53   Status: TRALSE in L-axis
```

**Key visual rule:** The "right side" (PD > 2) should be displayed as a DIFFERENT COLOR from the "left side" (PD < 2), preventing the visual impression that "more bar = more health." The Radiant marker ⬥ at PD = 2 is always the visual target.

---

## 4. What Each Axis Means at Each Level

### 4.1 G — Goodness Axis

| PD | 5-val | Description |
|----|-------|-------------|
| 0 | F | Complete moral depletion — amorality, disconnection from values |
| 1 | I | Moral uncertainty — searching for right action, ambivalent |
| **2** | **T** | **Genuine virtue — authentic good action, clear moral compass** |
| 3 | Tr | Self-righteousness — goodness inverted into judgment of others |
| 4 | DT | Martyrdom / destructive altruism — shadow goodness, self-destruction in goodness's name |

### 4.2 I — Intuition Axis

| PD | 5-val | Description |
|----|-------|-------------|
| 0 | F | Complete intuitive depletion — pure external-authority reliance, no inner signal |
| 1 | I | Dim intuition — occasional flickers, unreliable access to i-channel |
| **2** | **T** | **Clear intuition — reliable i-channel, accurate inner signal, GILE flow** |
| 3 | Tr | Magical thinking — intuition detached from reality, over-trusting inner signal |
| 4 | DT | Epistemic collapse — psychosis-adjacent, inner signal overrides all external data |

### 4.3 L — Love Axis

| PD | 5-val | Description |
|----|-------|-------------|
| 0 | F | Complete disconnection — emotional flatness, inability to connect |
| 1 | I | Searching for connection — conditional or uncertain love |
| **2** | **T** | **Unconditional love — genuine care without possession, free-flowing** |
| 3 | Tr | Possessive attachment — love with control, enmeshment, dependency |
| 4 | DT | Love-hate cycling / obsession — the love axis has collapsed into its shadow |

### 4.4 E — Environment Axis

| PD | 5-val | Description |
|----|-------|-------------|
| 0 | F | Complete environmental dissociation — inability to engage with surroundings |
| 1 | I | Environmental uncertainty — unstable relationship with physical space and body |
| **2** | **T** | **Grounded presence — attuned to environment, body, and context** |
| 3 | Tr | Hypervigilance — over-attunement, environmental anxiety, hyper-control |
| 4 | DT | Agoraphobia or environmental collapse — complete breakdown of environmental regulation |

---

## 5. The MRC Intervention Map

**MRC (MR Relaxation Context)** is the TI Sigma mechanism for reducing DT contamination when a state has exceeded the Radiant threshold. The intervention direction depends on the PD level and the sign of deviation.

### 5.1 General Principle

```
If PD < 2 (depletion):   ACTIVATION intervention → move PD toward 2
If PD = 2 (Radiant):     MAINTENANCE → no intervention needed
If PD > 2 (excess):      MRC/CALMING intervention → move PD toward 2 from above
```

The MRC intervention is always directed toward PD = 2, regardless of starting position.

### 5.2 Axis-Specific MRC Interventions

**G-Axis (Goodness):**

| Current PD | Intervention |
|------------|-------------|
| 0 (F) | Values clarification; meaning work; connect to intrinsic motivation |
| 1 (I) | Ethical reflection; identify authentic personal values vs. inherited rules |
| 2 (T) | ★ Maintain — continue aligned action |
| 3 (Tr/MRC) | Compassion practice; reduce moral judgment of others; focus on humility |
| 4 (DT/MRC) | Shadow work; examine self-sacrifice patterns; boundary setting |

**I-Axis (Intuition):**

| Current PD | Intervention |
|------------|-------------|
| 0 (F) | Body-based awareness; HRV/EEG biofeedback; FAAH protocol |
| 1 (I) | Mindfulness; open monitoring; reduce intellectual over-analysis |
| 2 (T) | ★ Maintain — trust and act on inner signal |
| 3 (Tr/MRC) | Reality testing; external validation loops; reduce solipsistic closure |
| 4 (DT/MRC) | Grounding protocol; environment engagement; psychiatric support if needed |

**L-Axis (Love):**

| Current PD | Intervention |
|------------|-------------|
| 0 (F) | Attachment repair; touch/connection; compassion-focused therapy |
| 1 (I) | Vulnerability work; safe relational practice |
| 2 (T) | ★ Maintain — give freely without expectation |
| 3 (Tr/MRC) | Differentiation work; release control; loving detachment practice |
| 4 (DT/MRC) | Therapeutic separation; work with addiction to relationship; self-love repair |

**E-Axis (Environment):**

| Current PD | Intervention |
|------------|-------------|
| 0 (F) | Sensory grounding (5-4-3-2-1); body scan; light exposure |
| 1 (I) | Environmental structure; space design; somatic work |
| 2 (T) | ★ Maintain — be present, attuned, embodied |
| 3 (Tr/MRC) | Relaxation response training; reduce environmental monitoring; HRV coherence |
| 4 (DT/MRC) | Progressive exposure; safety protocol; nervous system regulation |

---

## 6. The Asymmetry Principle

The GILE framework carries an important asymmetry in the intervention directions:

**Moving from 0→2 (depletion to Radiant):**
- Requires *more* of the quality
- More connection, more goodness, more intuition, more presence
- Standard therapeutic/developmental trajectory
- Can take years

**Moving from 4→2 (excess to Radiant):**
- Requires *less* of the quality, or a *transformation* of its form
- Less control, less judgment, less attachment, less monitoring
- MRC (relaxation) protocol
- Often *harder* than the depletion direction, because the excess feels like virtue
- The TRALSE trap: PD = 3 *feels like* PD = 2 (it looks like Goodness, Love, etc. from the inside) but is producing paradoxical effects

**The diagnostic insight:** If a GILE quality is causing harm to self or others DESPITE appearing positive, the axis is likely at TRALSE (3) or DT (4), not TRUE (2). The harm is the signal that the value has exceeded 2 and is now descending the other side of the mountain.

---

## 7. Connection to the Ternary Cantor Set

From URBs #535–536: the "pure numbers" in the Collatz analysis are those with INDETERMINATE density δ = 0 — integers using only {0, 2} in ternary (no 1-digits). These are the Cantor set numbers.

**GILE mapping:** A "pure GILE state" is one where each axis is at either 0 (FALSE) or 2 (TRUE) — no INDETERMINATE components. The Radiant profile (2, 2, 2, 2) is the single point where all four axes simultaneously hit the summit. This is:
- The ternary Cantor "center" in GILE space
- The fixed point of the Myrion Resolution process
- Analogous to the grain interior (lowest δ) in the polycrystalline Collatz model

The GILE trajectory toward Radiant is the GILE analog of the Collatz trajectory toward a pure number. Each MRC intervention is a "halving step" — it dissolves some INDETERMINATE content and moves the axis closer to either 0 or 2 (the pure ternary digits).

---

## 8. Reconciliation Summary

**Q: Why does PD=3 (TRALSE) represent LESS health than PD=2 (TRUE)?**

A: The 5-valued scale is non-monotone. TRALSE is TRUE + DT-contamination. The presence of DT lowers the LCC below the Radiant threshold even though the raw PD number is higher. The Health Function H(PD) = 2 − |PD − 2| captures this: H(3) = 1, H(2) = 2, confirming that TRALSE is LESS healthy than TRUE.

**Q: Why is "+1 = perfectly TRUE in ternary" correct despite TRUE=2 in the 5-valued system?**

A: These are two different scales that use different number assignments for the same logical state. In the signed ternary {−1, 0, +1}: +1 = TRUE = maximum. In the unsigned 5-valued {0,1,2,3,4}: TRUE=2 = maximum. TRALSE(3) and DT(4) are *outside* the clean ternary range — they represent DT-contaminated states that don't exist in the ternary logic proper. The clean ternary {0,1,2} is the healthy half of the 5-valued scale; {3,4} are the pathological extensions.

**Q: What should be done with PD values > 2?**

A: Apply MRC (relaxation) intervention toward PD=2. Display in amber/red to signal over-activation. Do NOT interpret as "more Radiant." Measure health using H(PD), not raw PD.

**Q: What does the Radiant threshold look like in each GILE category?**

A: A bullseye at PD=2, displayed as the center of a color-coded bar where green = Radiant zone (PD ∈ [1.5, 2.5]), blue = depleted zone (PD < 1.5), amber = TRALSE zone (PD ∈ [2.5, 3.5]), red = DT zone (PD > 3.5). The MRC intervention always points the arrow back toward PD=2 regardless of which side of the mountain the current state occupies.

---

## 9. Formal Properties of H(PD)

### Proposition 9.1 (Symmetry)
H(2+x) = H(2−x) for all x. The health function is symmetric around PD=2.

### Proposition 9.2 (Uniqueness of Radiant)
H(PD) = 2 if and only if PD = 2. The Radiant state is the unique maximum.

### Proposition 9.3 (DT Equivalence)
H(0) = H(4) = 0. Complete depletion (FALSE) and complete excess (DOUBLE_TRALSE) are equal in health — both represent total incoherence, just in opposite directions.

*Proof of all three: direct from H(PD) = 2 − |PD − 2|. ✓*

### Proposition 9.4 (LCC Monotonicity Within Each Half)
On [0, 2]: H is strictly increasing. On [2, 4]: H is strictly decreasing. Within each half, more is better (depletion direction) or less is better (excess direction).

### Proposition 9.5 (GILE_LCC Geometry)
The GILE_LCC surface in (G,I,L,E)-space is a 4-dimensional pyramid with apex at (2,2,2,2). Its cross-sections are L¹-balls (diamond shapes) in the deviation space.

---

## 10. The Tralse Trap

**Definition.** The *Tralse Trap* is the condition where a GILE axis is at TRALSE (PD=3) but is perceived internally as Radiant (PD=2). The excess of the quality *feels like* the quality itself.

Signs of the Tralse Trap:
- G-axis: "I am so good — why are people responding negatively to my virtue?"
- I-axis: "My intuition is perfect — the external data must be wrong"
- L-axis: "I love this person so deeply — why is this intensity damaging the relationship?"
- E-axis: "I am so attuned to my environment — why is this vigilance exhausting me?"

**Detection method:** If the expression of a GILE quality is producing its *opposite* effect (goodness causing conflict, love creating distance, intuition causing errors, environmental attunement causing dysregulation), the axis is likely in the TRALSE zone.

**DT Immunity Log relevance:** TRALSE-in-GILE states generate a characteristic DT fingerprint in the DTImmuneLog. The pattern is: the axis presents as TRUE externally (produces TRUE-coded outputs) but the secondary effects are DT-coded. The discordance between primary output (TRUE-coded) and secondary effects (DT-coded) is the diagnostic signal.

---

## 11. Integration With the ARC-AGI Solver

In the ARC-AGI context, each task has a GILE signature:
- **G-dominant tasks**: require moral/structural rule application
- **I-dominant tasks**: require intuitive pattern recognition (non-explicit)
- **L-dominant tasks**: require relational/compositional reasoning
- **E-dominant tasks**: require environmental/spatial grounding

The TISigmaARCSolver's LCC scores can be interpreted as the GILE_LCC for each task-attempt:
- High LCC (→ 1.0): the solver is operating in the Radiant range for the relevant GILE axis
- LCC in the DT Penumbra [0.8647, 0.9147]: TRALSE zone — approaching but paradoxically descending
- Low LCC: depletion zone — not enough GILE activation for the task type

This suggests a future enhancement: **GILE-typed task routing** — classify each ARC task by its dominant GILE axis and route it to the solver configuration calibrated for that axis type.

---

*Corpus Entry #194. DOI: pending. Apache 2.0.*

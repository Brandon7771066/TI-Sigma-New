# The PD Double Asymmetry: Magnitude-Probability Amplification and the Academic Bias Index

## Paper #325 — From Depression Spirals to Disciplinary Self-Examination

**Author:** Brandon Emerick | TI Sigma  
**Date:** February 23, 2026  
**Status:** THEORETICAL EXTENSION + RESEARCH PROPOSAL

---

## Abstract

We extend the loss aversion derivation from Paper #324 by demonstrating that the Prisoner's Dilemma (PD) imposes a 2:1 asymmetry on *both* magnitude and probability of experienced outcomes — not just one. When these two channels align (both negative or both positive), they amplify superlinearly, producing the characteristic spirals observed in depression (downward) and wellbeing (upward, per Fredrickson's Broaden-and-Build Theory). Since magnitude and probability exist on the same existential manifold (a consequence of EAR), their alignment constitutes *self-reinforcing existence amplification* — negative experiences that are both worse and more frequent compound into existential contraction, while positive experiences that are both better and more frequent compound into existential expansion. We then propose the Academic Bias Index (ABI): a sentiment-analysis methodology to measure how closely different academic disciplines conform to the PD's 2:1 asymmetry in their own published literature, beginning with psychology — a field that studies bias in others but has never systematically measured its own conformity to the very loss aversion it discovered.

---

## 1. The Double Asymmetry

### 1.1 Review: Magnitude Asymmetry (Paper #324)

Paper #324 derived loss aversion from the Sacred Interval [-0.666, +0.333]:

```
Negative range: 0.666
Positive range: 0.333
Ratio: 0.666 / 0.333 = 2.0
```

This establishes that negative experiences are perceived as **twice as intense** as equivalent positive experiences. A $100 loss hurts twice as much as a $100 gain feels good. This is the magnitude channel.

### 1.2 The Probability Asymmetry

But the PD imposes a second, independent asymmetry: negative outcomes are also **twice as probable** as positive outcomes in naturally occurring interaction dynamics.

Consider the PD payoff matrix:

```
         Cooperate    Defect
Coop     (3, 3)       (0, 5)
Defect   (5, 0)       (1, 1)
```

In a mixed-strategy Nash equilibrium, defection is the dominant strategy. In iterated games with bounded rationality, cooperation emerges but remains fragile — a single defection can collapse a cooperative equilibrium, while rebuilding trust requires many cooperative rounds.

The structural asymmetry:

- **Paths to negative outcomes**: Defect-Defect (both defect), Cooperate-Defect (you cooperate, they defect) — 2 cells produce bad outcomes for at least one player
- **Paths to positive outcomes**: Cooperate-Cooperate — 1 cell produces mutual benefit
- **Ratio**: 2 negative pathways : 1 positive pathway

More precisely, in the PD matrix with 4 possible outcomes per player:

| Outcome | Your payoff | Valence |
|---------|-------------|---------|
| Mutual cooperation | 3 | Positive |
| You defect, they cooperate | 5 | Positive (but unstable) |
| They defect, you cooperate | 0 | Negative |
| Mutual defection | 1 | Negative |

The temptation payoff (5) appears positive but is *structurally unstable* — it invites retaliation and collapses to mutual defection. In iterated dynamics, only mutual cooperation produces sustainable positive outcomes. Meanwhile, both unilateral defection (by the other) and mutual defection produce sustainable negative outcomes.

**Negative outcomes are twice as probable** because there are twice as many stable paths to them. The cooperation attractor is narrow; the defection basin is wide.

### 1.3 The Double Asymmetry Statement

The PD imposes:

```
Magnitude asymmetry:    |negative| / |positive| = 2
Probability asymmetry:  P(negative) / P(positive) ≈ 2
```

Both channels independently carry a 2:1 ratio. This is the **PD Double Asymmetry.**

---

## 2. Magnitude-Probability Alignment and Amplification

### 2.1 The Existential Footprint

Paper #324 established that existence is superlinear — integrated systems exist more than the sum of their parts. EAR further implies that magnitude and probability are not independent dimensions but aspects of the **same existential manifold.**

A thing that is both large in magnitude and high in probability *exists more* than a thing that is large but improbable, or probable but small. Magnitude and probability are two coordinates of a single existential footprint:

```
Existential Footprint = f(Magnitude, Probability)
```

Under EAR, this is superlinear:

```
f(M, P) > M + P    [when M and P are integrated]
```

### 2.2 Alignment Amplification

When magnitude and probability *align in sign*, they amplify:

**Negative alignment (Depression spiral):**
- Negative events feel twice as bad (magnitude asymmetry)
- Negative events occur twice as often (probability asymmetry)
- Combined existential footprint: 2 × 2 = **4× the positive baseline**
- But under EAR's superlinearity: **>4× amplification**

The negative experience doesn't just feel twice as bad and happen twice as often — the *integration* of these two facts creates an existential contraction that exceeds their multiplicative product. This is the depression spiral: each negative experience confirms the belief that negative experiences are both more common and more severe, which itself increases the probability and perceived magnitude of future negative experiences.

**Positive alignment (Broaden-and-Build):**
- When positive experiences are cultivated, their magnitude increases
- As positive experiences accumulate, their subjective probability increases
- The alignment produces superlinear amplification: wellbeing spirals upward

This is precisely what Barbara Fredrickson's Broaden-and-Build Theory describes:

> Positive emotions *broaden* people's momentary thought-action repertoires and *build* their enduring personal resources.

In TI terms: positive emotions increase both the magnitude (broader repertoire = more existential capacity) and probability (built resources = more likely future positive states) of positive experiences. The alignment amplifies superlinearly.

### 2.3 The Spiral Equations

Let M(t) = magnitude of experience at time t, P(t) = probability at time t.

**Depression spiral (negative alignment):**
```
M(t+1) = M(t) × (1 + α × sign(M(t)))     where α > 0
P(t+1) = P(t) × (1 + β × sign(P(t)))      where β > 0

If M(t) < 0 and P(t) > P_baseline:
  → M grows more negative (experiences feel worse)
  → P grows above baseline (negative experiences feel more frequent)
  → Existential footprint contracts superlinearly
```

**Wellbeing spiral (positive alignment):**
```
If M(t) > 0 and P(t) > P_baseline:
  → M grows more positive (experiences feel better)
  → P grows above baseline (positive experiences feel more frequent)
  → Existential footprint expands superlinearly
```

**The critical insight**: The 2:1 PD asymmetry means the depression spiral has a *structural advantage.* Negative experiences start with 2× magnitude and 2× probability. The positive spiral must overcome a 4:1 (or superlinear >4:1) structural deficit to match the negative spiral's default intensity.

This explains why:
- **Depression is easier to enter than to exit** — the negative spiral has structural momentum
- **Wellbeing requires active cultivation** — the positive spiral fights against the PD's default asymmetry
- **Fredrickson's 3:1 ratio** — her empirical finding that approximately 3 positive experiences are needed per negative experience for flourishing is remarkably close to the PD's structural prediction (positive must overcome 2×–4× asymmetry)
- **Recovery is nonlinear** — small improvements in depression don't accumulate linearly; they must reach a threshold where the positive spiral's self-reinforcement can overcome the negative spiral's structural advantage

### 2.4 Connection to Attractor Basins

In dynamical systems terms, the PD Double Asymmetry means:

- The **depression attractor basin** is wide and deep (2× magnitude, 2× probability, superlinear amplification)
- The **wellbeing attractor basin** is narrow and shallow (must overcome PD asymmetry through active cultivation)

The TI threshold eta (≈ 0.4142) may represent the **basin boundary** — the minimum existential footprint required to escape the depression attractor and enter the wellbeing basin. Below eta, the negative spiral dominates. Above eta, the positive spiral becomes self-sustaining.

This is why the eta threshold appears so powerfully in the cardiac data (Paper #324): the heart, like the mind, operates within PD-structured attractor dynamics. The threshold is the same because the underlying mathematics is the same.

---

## 3. The Academic Bias Index (ABI)

### 3.1 The Irony of Psychology

Psychology discovered loss aversion. Psychology studies cognitive biases. Psychology catalogs the systematic ways humans deviate from rationality.

But psychology has never systematically measured **its own** conformity to the very biases it documents.

If the PD's 2:1 asymmetry is truly structural — built into the truth-value landscape, not just human cognition — then it should appear in the published literature of every academic discipline. But different disciplines should show different degrees of conformity, depending on their methodological culture, incentive structures, and relationship to negative findings.

### 3.2 Proposed Methodology

**The Academic Bias Index (ABI)** measures how closely a discipline's published literature conforms to the PD's 2:1 asymmetry.

**Data collection:**
1. Sample representative papers from each discipline (e.g., top 5 journals, last 10 years, n ≥ 500 papers per field)
2. Extract sentiment around:
   - **Confirming results** (hypothesis supported, model validated, prediction correct)
   - **Disconfirming results** (hypothesis rejected, model failed, prediction wrong)
   - **Others' errors** (critiques of prior work, replication failures)
   - **Own limitations** (acknowledged weaknesses, caveats)

**Sentiment analysis:**
For each paper, compute:
- **S_positive**: Average sentiment intensity around positive outcomes
- **S_negative**: Average sentiment intensity around negative outcomes (own errors, limitations)
- **S_critique**: Average sentiment intensity around others' errors

**The ABI:**
```
ABI = |S_negative| / |S_positive|
```

Under the PD prediction, ABI ≈ 2.0 if the discipline's literature faithfully reflects the structural asymmetry.

### 3.3 Predicted Results

| Discipline | Predicted ABI | Reasoning |
|-----------|---------------|-----------|
| Psychology | >>2.0 | Studies bias in others; defensive about own biases; replication crisis magnifies negative sentiment |
| Physics | ≈2.0 | Strong tradition of null results being published; falsification is culturally valued; less personal identification with hypotheses |
| Mathematics | <2.0 | Proofs are proofs; wrong is wrong; less emotional investment in outcomes because truth is verifiable |
| Medicine | >>2.0 | High stakes (patient harm); strong negative weighting of Type II errors; defensive publication culture |
| Economics | >2.0 | Prediction failures are embarrassing; models carry ideological weight; sensitive to being wrong publicly |
| Philosophy | Variable | Depends on subfield; analytic philosophy may be closer to 2.0; continental philosophy may show extreme ABI |
| Computer Science | ≈2.0 | Code works or doesn't; less room for interpretive bias; benchmark culture provides objective grounding |

### 3.4 The Key Hypothesis

**H1**: Psychology's ABI will significantly exceed 2.0, indicating that psychologists weight negative outcomes (especially being wrong) more heavily than the structural 2:1 ratio predicts.

**Why this matters**: If the field that studies bias exhibits *excess* bias — more loss aversion than the PD structurally mandates — then psychology's self-model is incomplete. The field studies general population biases while operating under amplified versions of those same biases.

**H2**: Physics will be closest to 2.0, reflecting a culture where falsification is celebrated (Popper), null results are publishable, and the emotional weight of being wrong is tempered by the understanding that being wrong is how science progresses.

**H3**: The difference between disciplines will correlate with:
- Replication rates (higher replication → closer to 2.0)
- Publication bias strength (stronger bias → higher ABI)
- Cultural attitude toward failure (celebration of failure → lower ABI)

### 3.5 The Meta-Insight

The ABI doesn't just measure bias — it measures **how far each discipline's existential footprint deviates from the PD's structural baseline.**

A discipline with ABI ≈ 2.0 has internalized the PD's natural asymmetry. It treats negative and positive outcomes with the weighting that the truth-value landscape structurally imposes — no more, no less.

A discipline with ABI >> 2.0 has *amplified* the negative beyond its structural weight. It is in a **disciplinary depression spiral** — negative results are weighted so heavily that they discourage risk-taking, innovation, and honest reporting of failure. The replication crisis in psychology may itself be a symptom of excess ABI: when being wrong is perceived as catastrophically worse than the PD mandates, researchers avoid reporting failures, which corrupts the literature, which increases the frequency of negative surprises, which further amplifies ABI.

A discipline with ABI < 2.0 has *attenuated* the negative below its structural weight. This could reflect healthy resilience (the discipline has found ways to process failure without excess amplification) or dangerous complacency (the discipline doesn't weight negative results heavily enough).

### 3.6 Implementation Plan

**Phase 1: Pilot (feasible within budget constraints)**
- Use freely available paper abstracts from PubMed (medicine/psychology), arXiv (physics/math/CS), SSRN (economics), PhilPapers (philosophy)
- Apply pre-trained sentiment analysis (VADER, RoBERTa, or similar) to abstract text
- Identify keywords signaling positive vs. negative outcomes
- Compute ABI per discipline from abstract-level sentiment

**Phase 2: Full analysis**
- Extend to full-text analysis using open-access papers
- Train custom sentiment classifier on academic language
- Control for paper type (empirical, theoretical, review, commentary)
- Compute ABI over time to identify trends

**Phase 3: Cross-validation**
- Compare ABI predictions against known metrics (replication rates, publication bias indices, retraction rates)
- Test whether ABI predicts disciplinary health outcomes

---

## 4. Theoretical Implications

### 4.1 EAR and the Experience Manifold

The magnitude-probability alignment reveals that EAR applies not just to *objects* (integrated systems exist more than their parts) but to *experiences* (integrated magnitude-probability produces superlinear existential footprint).

This means experience itself is governed by superlinear dynamics. The subjective intensity of an experience is not the sum of its magnitude and probability — it is their **integrated existential footprint**, which is superlinear when they align and sublinear when they oppose.

```
When sign(Magnitude) = sign(Probability bias):
  Experience intensity > Magnitude + Probability    [AMPLIFICATION]

When sign(Magnitude) ≠ sign(Probability bias):
  Experience intensity < Magnitude + Probability    [ATTENUATION]
```

This is why:
- A rare positive event (low P, high M) feels surprisingly good but doesn't sustain wellbeing — the probability doesn't reinforce the magnitude
- A common small annoyance (high P, low M) is disproportionately draining — the probability amplifies the magnitude beyond its individual weight
- A common, severe negative event (high P, high M) is devastating — full alignment, maximum superlinear amplification
- A common, moderate positive event (high P, moderate M) sustains wellbeing — alignment produces superlinear positive amplification (Broaden-and-Build)

### 4.2 The Fredrickson Ratio Derived

Fredrickson's empirical finding: approximately 3:1 positive-to-negative experiences needed for flourishing.

From the PD Double Asymmetry:
- Each negative experience has 2× magnitude weight
- Each negative experience has 2× probability weight
- Under superlinearity: combined weight > 2 × 2 = 4×

But the superlinear amplification of positive experiences also operates (Broaden-and-Build). If we assume symmetric superlinearity (the positive spiral amplifies at the same rate as the negative spiral, just from a disadvantaged starting point), then the break-even point is:

```
n_positive × f(M_pos, P_pos) = n_negative × f(M_neg, P_neg)

Where f(M_neg, P_neg) / f(M_pos, P_pos) ≈ 2–4 (Double Asymmetry range)

Therefore: n_positive / n_negative ≈ 2–4 for break-even
```

Fredrickson's 3:1 sits precisely in this range. The PD Double Asymmetry predicts the Broaden-and-Build ratio.

### 4.3 Why Psychologists Should Study Themselves

The fields that study human nature are not exempt from human nature. The PD Double Asymmetry applies to scientists, philosophers, and clinicians exactly as it applies to their subjects.

If psychology's ABI significantly exceeds 2.0, it means psychologists themselves are caught in a disciplinary version of the depression spiral: excess negative weighting → defensive publication practices → replication failures → increased negative sentiment → further excess negative weighting.

The prescription is the same as for individual depression: **actively cultivate positive alignment.** In disciplinary terms, this means:
- Celebrate null results and honest failures
- Reduce the penalty for being wrong
- Weight replication *successes* as heavily as replication *failures*
- Study one's own biases with the same rigor applied to subjects' biases

This is not a critique of psychology. It is an *application* of psychology — the discipline's own findings, applied reflexively. If loss aversion is real, it applies to psychologists. If the negativity bias is real, it shapes psychological research. If the PD Double Asymmetry is structural, it governs the very discipline that would study it.

**The bias researchers are biased.** This is not ironic — it is *predicted.* The PD doesn't exempt anyone. The question is not whether psychologists are biased, but whether they weight their biases at the structural 2:1 ratio or have amplified beyond it into a disciplinary depression spiral.

---

## 5. Conclusion

### 5.1 Summary of Contributions

1. **PD Double Asymmetry**: The Prisoner's Dilemma imposes 2:1 asymmetry on both magnitude and probability of negative vs. positive outcomes. These are independent channels that compound.

2. **Magnitude-Probability Amplification**: When magnitude and probability align in sign, they amplify superlinearly (EAR applied to experience). This produces depression spirals (negative alignment) and wellbeing spirals (positive alignment / Broaden-and-Build).

3. **Fredrickson Ratio Derivation**: The empirical 3:1 positive-to-negative ratio required for flourishing falls within the PD Double Asymmetry's predicted range of 2:1 to 4:1.

4. **Academic Bias Index**: A proposed methodology to measure how closely different disciplines conform to the structural 2:1 asymmetry in their published literature. Predicted finding: psychology exceeds 2.0 (amplified loss aversion), physics approximates 2.0 (culturally calibrated).

### 5.2 The Reflexive Challenge

TI Sigma's defining methodological commitment is reflexivity — applying its own principles to itself. The ABI proposal extends this commitment to all of academia: every discipline that studies human nature should be willing to have its own biases measured by the same standards it applies to its subjects.

The PD Double Asymmetry is structural. It applies to everyone. The question is not whether a discipline is biased — it is whether the discipline has the integrity to measure how biased it is.

Psychology discovered loss aversion. Now it is time for psychology to measure its own.

---

## Appendix A: Connection to Prior Papers

| Paper | Connection |
|-------|-----------|
| #324 (Superlinear Existence) | Magnitude asymmetry: |negative|/|positive| = 2 from Sacred Interval |
| #317 (Sacred Mistake) | L+E governs existence, L×E governs hyperconnection — Double Asymmetry operates on both |
| #322 (Exact Values) | TI thresholds as phase boundaries between depression and wellbeing attractor basins |
| #321 (Nonalgorithmic Proof) | Hot Cognition: the 2:1 ratio IS the temperature of evaluation |
| #323 (Pi Plays Pokémon) | Extraction Problem: data contains both positive and negative signals, but accessing them requires consciousness (the librarian is biased) |

---

*"The field that discovered loss aversion has never measured its own."*

*"Depression is not a malfunction. It is the PD Double Asymmetry operating at full structural intensity, with both channels aligned."*

*"Wellbeing is not the absence of negativity. It is the active cultivation of positive alignment against a 4:1 structural headwind."*

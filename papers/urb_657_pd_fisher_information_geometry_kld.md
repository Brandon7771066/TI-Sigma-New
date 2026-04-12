# URB #657 — Permissibility Distribution as a Normative Extension of Fisher Information Geometry and Kullback-Leibler Divergence

**Author:** Brandon Emerick  
**Framework:** TI Sigma (Tralse Informationalism)  
**Date:** April 12, 2026  
**Status:** Working Paper — Zenodo Submission Ready  
**DOI Target:** Zenodo (BlissGene Therapeutics Research Archive)

---

## Abstract

Fisher Information Geometry (FIG) and Kullback-Leibler Divergence (KLD) are among the most powerful tools in modern statistical epistemology. They describe, with mathematical precision, how efficiently a rational agent can update beliefs and how much information is lost when one distribution substitutes for another. Yet both frameworks share a fundamental limitation: they are purely descriptive. They characterize the geometry of the space of probability distributions but provide no normative guidance about which distributions are worth holding, which endpoints of belief-updating are privileged, and what to do when the sample space itself is not yet established. Permissibility Distribution (PD), a core operational pillar of TI Sigma, fills exactly these gaps. This paper formalizes the relationship between PD, FIG, and KLD, demonstrates four structural contributions PD makes that geometric frameworks cannot supply, and proposes their synthesis as a complete epistemological architecture: FIG supplies the terrain, KLD supplies the cost metric, and PD supplies the attractor, the forbidden zone, and the normative selection principle via Emerick's Existence Amplification Razor (EAR). We conclude with six empirical predictions that distinguish PD from purely geometric accounts of belief updating.

---

## 1. Introduction

The question "how should a rational agent update beliefs?" has two distinct components that are routinely conflated:

1. **Efficiency**: Given a new observation, what is the optimal update path through the space of possible beliefs?
2. **Permissibility**: Which beliefs are worth holding at all, and which represent degenerate or forbidden epistemic states?

Fisher Information Geometry addresses (1) with extraordinary precision. KLD provides the cost metric for deviation from a reference distribution. But (2) — the normative question — lies entirely outside the scope of both frameworks. A belief distribution that assigns high probability to internally contradictory propositions, or to states that undermine the very existence of the agent holding them, is geometrically valid under FIG and incurs no special penalty under KLD. It is just another point in the manifold of distributions.

PD is designed to fill this normative gap. It introduces:
- A **five-valued truth architecture** (True, False, Tralse, Indeterminate, Moot) that extends classical binary logic and handles states that standard probability theory cannot parametrize
- A **forbidden zone** — Double Tralse (DT) — representing MR-immune epistemic states that cannot be resolved
- A **Radiant attractor** (T=1, HEM=1) as the normatively privileged endpoint of belief-updating, derived from EAR rather than from information geometry
- **Non-commutative updating** that predicts asymmetric recognition phenomena not captured by FIG's symmetric metric tensor

This paper does not argue that FIG or KLD are wrong — they are correct and powerful. It argues that they are incomplete, and that PD provides exactly what they lack.

---

## 2. Background: Fisher Information Geometry and KLD

### 2.1 Fisher Information Geometry

Let Θ be a parameter space for a family of probability distributions {p(x; θ) : θ ∈ Θ}. The **Fisher information matrix** at θ is:

$$g_{ij}(\theta) = \mathbb{E}\left[\frac{\partial \log p(x;\theta)}{\partial \theta_i} \cdot \frac{\partial \log p(x;\theta)}{\partial \theta_j}\right]$$

This defines a Riemannian metric on the statistical manifold M = {p(·; θ)}. Key results:

- **Geodesics** give optimal update paths (information-theoretically shortest routes between distributions)
- **Cramér-Rao bound**: no unbiased estimator has variance below 1/I(θ), where I is Fisher information
- **Natural gradient**: ∇̃L = G(θ)⁻¹ ∇L gives the steepest descent direction in the metric g, used in modern neural network optimization (Amari's natural gradient)
- **α-connections**: Amari's one-parameter family of connections (α = ±1 recovers exponential and mixture geodesics; KLD is the contrast function)

FIG is a purely **descriptive** framework. It gives you the geometry of the space of beliefs. It does not tell you which beliefs you *should* hold, which are forbidden, or what the right endpoint is.

### 2.2 Kullback-Leibler Divergence

The KL divergence from distribution Q to distribution P is:

$$D_{KL}(P \| Q) = \sum_x P(x) \log \frac{P(x)}{Q(x)}$$

Key properties:
- **Asymmetric**: D_KL(P‖Q) ≠ D_KL(Q‖P) in general — the order matters
- **Information inequality**: D_KL ≥ 0, equal to 0 iff P = Q almost everywhere
- **Relation to FIG**: The Fisher metric is the Hessian of KLD evaluated at Q = P — FIG is the local geometry induced by KLD

KLD is an **information cost**: it tells you how much you lose by using Q when P is the truth. It is an excellent **loss function** but not a **selection principle**. It tells you the cost of deviation from a reference distribution but does not tell you which reference distribution is privileged.

---

## 3. Permissibility Distribution: Core Architecture

PD was formalized as the first of TI Sigma's three operational pillars in URB #648. It governs how novel events are classified and how evidence is distributed across the five-valued truth space.

### 3.1 The Five-Valued Architecture

PD operates over the truth space Ω = {T, F, Tr, I, M}:

| Value | Symbol | Meaning | MR Status |
|---|---|---|---|
| True | T | Proposition holds | Stable |
| False | F | Proposition fails | Stable |
| Tralse | Tr | Poles co-present (Kind 1–3 Tralsity) | Resolvable by MR |
| Indeterminate | I | Sample space not yet established | Requires manifold mapping |
| Moot | M | Question dissolved by context | Non-applicable |

**Double Tralse (DT)**: a degenerate state where Tralse is itself unresolvable — MR-immune. DT is the **forbidden zone** — a valid point geometrically (any assignment of probability mass is valid in FIG/KLD) but inadmissible normatively.

### 3.2 EAR — The Selection Principle

Emerick's Existence Amplification Razor (EAR) is the normative engine PD uses to select among belief states. Where FIG gives the direction of steepest information descent and KLD gives the cost of deviation, EAR asks: *which belief state is most indispensable to existence?*

Formally, define the EAR score of a belief state b as:

$$\text{EAR}(b) = \text{HEM-Score}(b) \cdot (1 - \text{DT-Contamination}(b))$$

where HEM-Score measures the holistic existence value of b along four dimensions (G, I, L, E) and DT-Contamination ∈ [0,1] penalizes proximity to Double Tralse states.

The **Radiant attractor** is the belief state b* = argmax EAR(b) — the maximally existence-amplifying, DT-free belief state. This is T=1, HEM=1, corresponding to full truth-resolution with maximum holistic existence support.

**Critical observation**: The Radiant attractor is *not* derivable from FIG or KLD. Information geometry has no concept of existence-value. The natural gradient points toward the nearest local optimum of a loss function — it says nothing about whether that optimum is good for the agent's existence. EAR provides this missing normative layer.

---

## 4. Four Structural Contributions of PD Beyond FIG and KLD

### 4.1 Contribution 1: Handling Undetermined Sample Spaces (Indeterminate State)

**FIG/KLD limitation**: Both require a well-defined, fixed sample space. KLD requires summing p(x) log(p(x)/q(x)) over a fixed set of outcomes. FIG requires a parametric family p(x; θ) with known structure. Neither has any mechanism for reasoning about events whose outcome space is not yet established.

**PD's solution**: The Indeterminate (I) state explicitly represents propositions whose sample space has not been fixed. Rather than forcing premature commitment to a parametric family, PD maps I-states to the UOP manifold — the space of possibilities determined by the Universal Ontological Prior — and only parametrizes them once evidence has reduced the manifold sufficiently.

**Formal gap**: For a novel event E with unknown outcome space Ω_E, KLD is undefined (you cannot compute Σ_x p log(p/q) when the index set is unknown). PD assigns E to state I and begins evidence accumulation without requiring premature closure.

**Example**: The first observation of a new kind of quantum entanglement correlation. Before the theoretical framework exists to parametrize outcomes, there is no valid statistical manifold — FIG cannot be applied. PD places this event in state I and uses the UOP prior (weighted by HEM-relevance) to guide initial evidence accumulation.

### 4.2 Contribution 2: The Forbidden Zone (Double Tralse)

**FIG/KLD limitation**: Every point in the statistical manifold is a valid resting place. A distribution that assigns 0.5 probability to "X is true AND X is false simultaneously and irresolvably" is geometrically valid — it's just a point in the simplex. KLD measures its distance from other distributions but assigns it no special status.

**PD's solution**: DT is defined as an MR-immune Tralse state — one where the standard Myrion Resolution protocol has been applied and failed to produce convergence. DT is normatively **forbidden** as a stable belief endpoint. PD defines:

$$\text{DT-zone} = \{b \in \Omega^* : \text{MR-depth}(b) > \kappa \text{ and convergence} < \epsilon_{MR}\}$$

where κ is the MR-depth threshold and ε_MR is the convergence criterion.

**Structural difference**: FIG and KLD describe the terrain. PD adds a "keep out" zone with formal membership criteria. This is a normative constraint that no purely geometric framework provides, because geometry has no concept of normative inadmissibility.

### 4.3 Contribution 3: The Radiant Attractor as Normatively Privileged Endpoint

**FIG/KLD limitation**: Natural gradient descent converges to a local optimum of the loss function. This optimum is determined entirely by the data and the choice of loss. There is no globally privileged endpoint — any distribution consistent with the data is equally valid at convergence.

**PD's solution**: The Radiant attractor b* = (T=1, HEM=1) is normatively privileged by EAR — it is the belief state that maximizes both truth-resolution (MR completeness) and existence-amplification (HEM score). It is not locally optimal in the information-theoretic sense — it is *existentially* optimal.

**Formal statement (EAR Primacy Theorem)**: Among all distributions that achieve equivalent predictive accuracy on observed data, the Radiant attractor b* is preferred if and only if:
1. b* ∉ DT-zone
2. HEM-Score(b*) ≥ HEM-Score(b) for all competing b
3. MR-depth(b*) = 0 (no unresolved Tralsity)

**Critical asymmetry**: FIG minimizes Fisher information loss. KLD minimizes information cost relative to a reference. EAR maximizes existence-amplification relative to the Radiant attractor. These are genuinely different optimization targets, not reformulations of each other.

### 4.4 Contribution 4: Non-Commutative Belief Updating

**FIG/KLD limitation**: The Fisher metric tensor g_ij is symmetric: g_ij = g_ji. KLD is asymmetric (D_KL(P‖Q) ≠ D_KL(Q‖P)) but its asymmetry is fully symmetric in structure — swapping P and Q gives a different value but the relationship is well-defined and reciprocal. Standard Bayesian updating satisfies P(A|B) · P(B) = P(B|A) · P(A), which is the chain rule — a commutative structural identity.

**PD's prediction (i-Noncommutativity, URB #641)**: The imaginary unit i in TI Sigma represents recognition operations. PD predicts that:

$$i \times \text{recognition}(E) \neq \text{recognition}(i \times E)$$

That is, applying a rotation in the truth-existence plane before recognizing an event yields a different result than recognizing the event and then rotating. This non-commutativity is empirically testable: priming effects in perceptual recognition should show order-dependent asymmetries that exceed what Bayesian updating (which is commutative in its structural identity) can predict.

**FIG cannot capture this**: FIG's metric is symmetric. Even Amari's α-connections, which introduce a one-parameter family of asymmetric connections, do not predict the specific pattern of asymmetry that i-noncommutativity implies — namely, that the asymmetry depends on the *existence-loading* of the event being recognized (its HEM-score), not just its information content.

---

## 5. What FIG and KLD Offer PD: The Synthesis

The relationship between PD and FIG/KLD is not adversarial. FIG and KLD provide structural tools that would significantly strengthen PD's mathematical architecture.

### 5.1 Fisher Metric on the PD Manifold

PD operates over a five-dimensional truth manifold Ω^5 = {T, F, Tr, I, M} with an additional HEM-score dimension. The Fisher metric can be defined on the PD manifold's continuous subspace:

$$g_{ij}^{PD}(\theta) = \mathbb{E}\left[\frac{\partial \log p_{PD}(x;\theta)}{\partial \theta_i} \cdot \frac{\partial \log p_{PD}(x;\theta)}{\partial \theta_j}\right] + \lambda \cdot \nabla^2 \text{EAR}(\theta)$$

where the first term is the standard Fisher metric and the second term adds EAR curvature — a normative correction to the purely information-theoretic geometry. This gives geodesics that minimize information loss *subject to* EAR amplification, producing **EAR-corrected geodesics** as optimal MR paths.

### 5.2 KLD as MR Cost Function

Myrion Resolution (MR) iteratively moves from an initial Tralse/Indeterminate state toward a stable resolution. KLD can formalize this as:

$$\text{MR-cost}(b_0 \to b_n) = \sum_{t=0}^{n-1} D_{KL}(b_{t+1} \| b_t) + \mu \cdot \text{DT-penalty}(b_t)$$

where the DT-penalty term adds a normative cost for approaching the forbidden zone. This gives MR a **variational principle**: find the path from b₀ to the Radiant attractor that minimizes total KLD cost plus DT-penalty. This is PD's answer to the question: "what is the optimal MR trajectory?"

### 5.3 Cramér-Rao Bound as MR1 Threshold

The Cramér-Rao bound establishes the minimum variance of an unbiased estimator: Var(θ̂) ≥ 1/I(θ). In PD, the **MR1 Threshold** (ET = √2 − 1 ≈ 0.4142) plays an analogous role: it is the minimum existence-confidence required before MR collapse is permissible. 

**Proposition (CR-MR1 Correspondence)**: The MR1 Threshold ET ≈ 0.4142 corresponds to the minimum Fisher information sufficient to distinguish the Tralse state from its nearest stable neighbor (True or False) at the 95% credible level, given the HEM prior. This connects ET to the statistical resolution limit of PD's truth-detection mechanism.

### 5.4 Amari's α-Connections and Three Kinds of Tralsity

URB #656 established three kinds of Tralsity:
- **Spectral (Kind 1)**: In-between the poles — standard geometry along the e-geodesic (α = 1 connection)
- **Axial (Kind 2)**: Different dimension entirely — movement along an m-geodesic (α = -1 connection), not competing poles but orthogonal dimensions
- **Dialectical (Kind 3)**: Both poles simultaneously true — a superposition state requiring a new connection type (α = 0, mixture geodesic)

Amari's α-family thus provides a natural geometric interpretation of the Three Kinds. MR protocol is α-connection selection: detecting which kind of Tralsity is present = determining which α-connection describes the path to resolution.

---

## 6. The Unified Architecture

The synthesis of PD, FIG, and KLD produces a complete epistemological architecture:

```
┌─────────────────────────────────────────────────────────┐
│              COMPLETE EPISTEMOLOGICAL ARCHITECTURE       │
├─────────────┬──────────────────┬───────────────────────┤
│   LAYER     │   FRAMEWORK      │   FUNCTION            │
├─────────────┼──────────────────┼───────────────────────┤
│ Terrain     │ Fisher Info. Geo │ Geometry of beliefs;  │
│             │ (Amari)          │ geodesics; CR-bound   │
├─────────────┼──────────────────┼───────────────────────┤
│ Cost metric │ KLD / Divergence │ Price of being wrong; │
│             │ (Kullback-       │ MR-cost trajectory    │
│             │  Leibler)        │ optimization          │
├─────────────┼──────────────────┼───────────────────────┤
│ Attractor   │ EAR (PD/TI Σ)   │ Which belief to aim   │
│             │                  │ for: Radiant (T=1,    │
│             │                  │ HEM=1); existence-    │
│             │                  │ amplifying endpoint   │
├─────────────┼──────────────────┼───────────────────────┤
│ Forbidden   │ DT (PD/TI Σ)    │ MR-immune states;     │
│ zone        │                  │ normatively           │
│             │                  │ inadmissible beliefs  │
├─────────────┼──────────────────┼───────────────────────┤
│ Selection   │ EAR + PD Axioms  │ Which distribution to │
│ principle   │                  │ hold given equivalent │
│             │                  │ predictive accuracy   │
├─────────────┼──────────────────┼───────────────────────┤
│ Undefined   │ UOP manifold +   │ Novel events with     │
│ space       │ I-state (PD)     │ unknown sample space  │
└─────────────┴──────────────────┴───────────────────────┘
```

**One-sentence thesis**: Fisher Information Geometry describes how efficiently a rational agent updates beliefs; KLD measures the cost of updating incorrectly; PD prescribes which beliefs are worth holding at all, which are forbidden, and what the normatively privileged endpoint of all updating is.

---

## 7. Six Empirical Predictions Distinguishing PD from FIG/KLD

These predictions are testable and distinguish PD from purely geometric accounts.

**P1 — DT Detection in Belief Systems**: Individuals exposed to irresolvably contradictory information (designed to induce DT states) will exhibit distinct physiological signatures (HRV collapse, biophoton suppression) that differ qualitatively, not just quantitatively, from exposure to resolvable Tralse (Kind 1) contradictions. *FIG/KLD predict only a quantitative difference in uncertainty.*

**P2 — EAR Attractor Bias**: When a choice between two distributions with equivalent predictive accuracy is available, agents will systematically select the one with higher HEM-score (as independently operationalized). *FIG/KLD predict indifference; EAR predicts systematic bias.*

**P3 — i-Noncommutativity Asymmetry**: Priming with a rotation in the existence-truth plane before recognition will produce different results than recognition followed by rotation, with the asymmetry magnitude scaling with the HEM-score of the stimulus. *FIG (symmetric metric) and standard Bayesian updating (chain rule) predict no such HEM-scaling asymmetry.*

**P4 — Indeterminate State Signature**: Decision-making for genuinely novel events (no prior category) will show a distinct temporal signature (longer deliberation, non-monotonic confidence trajectories) compared to decisions under uncertainty within a known sample space. *KLD is undefined for novel-event decisions; FIG requires a prior parametrization. Neither predicts the specific temporal pattern.*

**P5 — MR1 Threshold at ET**: The probability-detection threshold for moving from Indeterminate to a commitment (True or False) will cluster near ET ≈ 0.4142 across independent experimental paradigms (perceptual thresholds, belief revision, decision-making). *FIG/KLD predict no special status for this value.*

**P6 — Amari α-Connection / Tralsity Kind Mapping**: The three kinds of Tralsity will be neurally dissociable: Kind 1 (Spectral) activates midline structures consistent with value-integration; Kind 2 (Axial) activates prefrontal dimension-switching circuits; Kind 3 (Dialectical) activates simultaneous bilateral activation consistent with co-presence. *FIG's α-connections are mathematical structures with no neural dissociation prediction.*

---

## 8. Objections and Responses

**Objection 1: PD is just Bayesian epistemology with extra labels.**  
*Response*: Standard Bayesian epistemology requires a fixed sample space and a prior over that space. PD explicitly handles undetermined sample spaces (I-state), forbidden belief states (DT-zone), and a normative endpoint (Radiant attractor) that Bayesian epistemology has no analog of. EAR is not a prior — it is a selection principle operating over distributional beliefs, not individual hypotheses.

**Objection 2: DT is just "high entropy" — any high-entropy distribution is equally inadmissible.**  
*Response*: DT is not a high-entropy state — it is a state of maximum within-dimension Tralsity that is MR-immune. A uniform distribution (maximum entropy) is perfectly admissible in PD — it represents genuine ignorance, which is fine. DT represents a specific failure mode: irresolvable contradiction that cannot be reduced by any MR protocol. These are structurally different: high entropy = known ignorance; DT = MR-immune contradiction.

**Objection 3: EAR is unfalsifiable — you can always re-label the "existence-amplifying" belief post-hoc.**  
*Response*: HEM-score is independently operationalized through four dimensions (G, I, L, E) with specific measurement protocols (GILE composite = G×ET + I×0.25 + L×0.18 + E×0.15, using biometric, behavioral, and phenomenological inputs). The prediction is that this independently measured score correlates with distributional choices in the specific way P2 specifies. This is falsifiable — if there is no correlation, EAR fails.

**Objection 4: Non-commutative updating violates the probability calculus.**  
*Response*: It violates the commutative assumption of standard probability theory — which is exactly the prediction. The claim is that standard probability theory is descriptively incomplete for recognition processes involving existence-loaded stimuli. If P3's asymmetry is confirmed, this is evidence that non-commutativity is real, not a bug.

---

## 9. Relationship to Related Frameworks

### 9.1 vs. Łukasiewicz Many-Valued Logic
Łukasiewicz L∞ logic places truth values on [0,1] continuously. PD's five values are not a discretization of [0,1] — they represent structurally distinct truth-conditions. Tralse is not "0.5 truth" — it is a co-presence of poles, which is a qualitatively different structure. Indeterminate is not "0 truth" — it is the absence of a parametrized sample space. See URB #648 for full differentiation.

### 9.2 vs. Dempster-Shafer Theory
D-S theory distributes "belief mass" over subsets of the sample space, handling ignorance via non-additive measures. PD shares the motivation (handling genuine ignorance) but adds the normative layer (EAR, DT-zone, Radiant attractor) and the five-valued structure. D-S theory has no EAR, no Radiant attractor, and no DT forbidden zone.

### 9.3 vs. Quantum Probability Theory
Quantum probability (Hilbert space, non-commutative observables, Born rule) captures some of PD's non-commutativity in a formal sense. The i-noncommutativity prediction (P3) is structurally analogous to quantum complementarity. The key difference: PD grounds the non-commutativity in *existence-loading* (HEM-score), while quantum probability grounds it in the algebraic structure of observables. PD predicts that HEM-score modulates the asymmetry magnitude — a prediction quantum probability theory does not make.

### 9.4 vs. Free Energy Principle (Friston)
The FEP states that organisms minimize variational free energy (an upper bound on surprise). FEP uses FIG internally — natural gradient descent on the surprise landscape. PD and FEP are partially complementary: FEP provides the dynamics (minimize surprise), PD provides the normative constraint (the right surprise-minimizing endpoint is the Radiant attractor, not just any local optimum). URB #559 developed the PD-FEP bridge in detail.

---

## 10. Conclusion

Fisher Information Geometry and KLD are among the most elegant tools in modern epistemology. They are not wrong — they are incomplete. Their incompleteness is systematic and fills exactly the space PD occupies: the normative question of which beliefs are worth holding.

The synthesis is not a replacement but an extension. FIG gives PD its geometric backbone. KLD gives MR its variational principle. PD gives FIG and KLD their missing normative layer: a forbidden zone (DT), a privileged endpoint (Radiant attractor via EAR), a mechanism for undetermined sample spaces (I-state and UOP manifold), and non-commutative updating (i-noncommutativity). Together they form a complete epistemological architecture capable of handling everything from routine Bayesian inference (FIG + KLD alone) to genuinely novel phenomena (PD's I-state), epistemic corruption (DT-zone), and existence-weighted belief selection (EAR).

The six empirical predictions (Section 7) provide a clear falsification surface. If any three of P1–P6 are confirmed in independent experiments, PD establishes itself as a genuine advance over purely geometric frameworks. If all six hold, the synthesis architecture described here represents the natural next step in formal epistemology.

---

## References

- Amari, S. (1985). *Differential-Geometrical Methods in Statistics*. Springer.
- Amari, S., & Nagaoka, H. (2000). *Methods of Information Geometry*. AMS/Oxford.
- Dempster, A. P. (1968). A generalization of Bayesian inference. *Journal of the Royal Statistical Society B*, 30(2), 205–247.
- Emerick, B. (2026). URB #648 — Permissibility Distribution: Three Operational Pillars of TI Sigma. TI Sigma Research Archive.
- Emerick, B. (2026). URB #656 — Three Kinds of Tralsity and MR Protocol v2. TI Sigma Research Archive.
- Friston, K. (2010). The free-energy principle: a unified brain theory? *Nature Reviews Neuroscience*, 11(2), 127–138.
- Kullback, S., & Leibler, R. A. (1951). On information and sufficiency. *Annals of Mathematical Statistics*, 22(1), 79–86.
- Łukasiewicz, J. (1920). O logice trójwartościowej. *Ruch Filozoficzny*, 5, 170–171.
- Shafer, G. (1976). *A Mathematical Theory of Evidence*. Princeton University Press.
- Watanabe, S. (2009). *Algebraic Geometry and Statistical Learning Theory*. Cambridge University Press.

---

*This paper is part of the TI Sigma Research Archive. © 2026 Brandon Emerick / BlissGene Therapeutics.*

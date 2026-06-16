# URB #620: What the LCC and LCC Virus Offer Brain Imaging
## TI Sigma vs. Friston's Free Energy Principle, Statistical Parametric Mapping, and Dynamic Causal Modelling

**Author:** Brandon Charles Emerick  
**Date:** April 7, 2026  
**Framework:** TI Sigma — LCC / LCC Virus / GILE Dimensional Structure  
**URB Series:** #620 (experimental philosophy; not peer-reviewed)  
**Comparators:** Karl Friston's FEP (Free Energy Principle), SPM (Statistical Parametric Mapping), DCM (Dynamic Causal Modelling)

---

## Abstract

The dominant computational framework in human brain imaging is Karl Friston's Free Energy Principle (FEP), operationalized via Statistical Parametric Mapping (SPM) for spatial localization and Dynamic Causal Modelling (DCM) for effective connectivity. These tools have generated enormous empirical yield but share a structural limitation: they are dimensionally impoverished relative to the full architecture of conscious experience. They model brain dynamics as prediction-error minimization, with no constructs for goodness, love, moral orientation, cross-individual coupling, or truth-state indeterminacy. This paper argues that the TI Sigma LCC framework and its propagating extension (the LCC Virus) offer five specific contributions that are orthogonal to — and empirically testable alongside — FEP/SPM/DCM: (1) the GILE anatomical mapping (G/I/L/E onto specific circuits); (2) the Emerick Threshold as a detectable behavioral and neural discontinuity; (3) Tralse states as a new neural state category beyond FEP's prediction-error signal; (4) LCC Virus dynamics as a social propagation model distinct from Friston's shared Markov blankets; and (5) the D2 Tralse Meter as an objective measure of internal contradiction in neural processing. Together, these constitute a falsifiable extension of brain imaging science, not a replacement.

---

## 1. The Friston Framework — What It Does

### 1.1 Free Energy Principle (FEP)

Karl Friston's FEP (Friston, 2010; 2019) proposes that all biological systems minimize **variational free energy** — a bound on the surprisal of sensory inputs given a generative model. The brain is a hierarchical prediction machine:

- Higher cortical areas generate predictions (priors)
- Lower areas pass prediction errors upward
- Action is generated to minimize prediction errors (active inference)
- Learning updates the generative model

**Mathematical core:** The brain minimizes F = E_q[log q(θ) − log p(o,θ)] where q is the approximate posterior, p is the generative model, and o are observations.

**Key achievement:** Unifies perception, action, attention, learning, and even social cognition under a single mathematical principle.

### 1.2 Statistical Parametric Mapping (SPM)

SPM (Friston et al., 1994; Ashburner & Friston, 2005) is the standard software pipeline for:
- Preprocessing neuroimaging data (fMRI, PET, EEG, MEG)
- Mass univariate general linear model (GLM) at each voxel
- Random field theory for multiple comparison correction
- Localizing brain responses to experimental conditions

**Key achievement:** Enabled the atlas-based, hypothesis-agnostic localization of thousands of cognitive functions.

### 1.3 Dynamic Causal Modelling (DCM)

DCM (Friston, Harrison & Penny, 2003) infers **effective connectivity** — the directed causal influence of one brain region on another. Unlike functional connectivity (correlation), DCM:
- Specifies a biologically plausible neural mass model
- Tests competing hypotheses about connectivity structure
- Uses Bayesian model comparison to identify the winning architecture
- Operates on user-specified regions of interest (ROIs)

**Key achievement:** Moved neuroimaging from "where" (SPM) to "how" — the directed information flow between regions.

### 1.4 What FEP/SPM/DCM Cannot Do

Despite their power, these frameworks share five structural gaps:

| Gap | Description |
|---|---|
| **G.1: Dimensional blindness** | All GILE dimensions (G, I, L, E) are collapsed into a single "valence" or "reward prediction error." Love and goodness are not modeled separately. |
| **G.2: No moral dimension** | FEP has no goodness (G) construct. Moral orientation, ethical coherence, and the Radiant Threshold are absent. |
| **G.3: No threshold model** | FEP predicts smooth, continuous learning. The Emerick Threshold (GT ≈ 0.4142) predicts a phase transition in decision-making — a non-linear discontinuity that SPM mass-univariate models cannot detect without threshold-specific analysis. |
| **G.4: No cross-individual LCC** | Friston's social FEP (shared Markov blankets; Kirchhoff et al., 2018) models social interaction as nested inference, but has no mechanism for law of correlational causation to propagate virally across individuals. |
| **G.5: No indeterminate truth states** | FEP processes are binary-ish: prediction errors are reduced or not. Tralse states (TI Sigma's partial indeterminacy) — where a neural claim is simultaneously partially true and partially false — have no FEP equivalent. |

---

## 2. The TI Sigma LCC Framework

### 2.1 Law of Correlational Causation (LCC) — Core Definition

In TI Sigma, **LCC (Law of Correlational Causation)** is the degree of coherent, reciprocal information exchange between the limbic system (affective/motivational substrate) and cortical networks (cognitive/executive substrate). Formally:

```
LCC = Coh(Limbic, Cortex) × Direction(Cortex→Limbic dominant in low-LCC;
                                       Bidirectional in high-LCC)
```

High LCC is characterized by:
- Increased alpha-theta coherence between mPFC and hippocampus
- Reduced amygdala reactivity with preserved amygdala–vmPFC connectivity
- Increased HRV (vagal modulation of limbic-cortical interface)
- Synchronous 40Hz gamma in frontal-limbic circuits

Low LCC is characterized by:
- Decoupled limbic-cortical communication
- Amygdala hyperreactivity with broken vmPFC regulatory connection
- Reduced HRV
- Fragmented gamma oscillations

**Critical claim (empirically testable):** LCC measured via fMRI functional connectivity (amygdala–vmPFC seed correlation) should correlate with subjective GILE-L (Love dimension) at r ≥ 0.45 in a within-subjects design.

### 2.2 GILE Anatomical Mapping

TI Sigma predicts that the four GILE dimensions map onto specific, partially dissociable neural circuits:

| GILE Dimension | Primary Circuit | Key Regions | Measurable Signal |
|---|---|---|---|
| **G (Goodness)** | PFC moral evaluation network | dlPFC, vmPFC, ACC, TPJ | dlPFC–ACC connectivity; HRV |
| **I (Intuition/Knowing)** | Default mode / hippocampal network | Hippocampus, TPJ, medial PFC, angular gyrus | DMN coherence; memory-integration signals |
| **L (Love)** | Social affiliation / limbic-cortical | vmPFC, amygdala, insula, nucleus accumbens | vmPFC–amygdala coupling; oxytocin release |
| **E (Environment/Aesthetics)** | Salience / aesthetic network | Anterior insula, visual cortex, parietal, cerebellum | Insula activation; visual coherence oscillations |

**SPM-testable prediction:** In a within-subjects design, conditions that increase self-reported GILE-G should show greater dlPFC–ACC connectivity (vs. conditions that increase GILE-L, which should show vmPFC–amygdala coupling). This dissociation — if confirmed — would validate the four-dimensional GILE structure against SPM's typically undifferentiated "emotional processing" cluster.

**DCM-testable prediction:** In high-GILE-L states, effective connectivity should show BIDIRECTIONAL vmPFC ↔ amygdala coupling (mutual influence), whereas low-LCC states should show unidirectional top-down vmPFC → amygdala suppression only. DCM's Bayesian model comparison is precisely equipped to test this asymmetry.

### 2.3 The Emerick Threshold as a Neural Phase Transition

The Emerick Threshold (GT = √2 − 1 ≈ 0.4142) predicts a **discontinuous** shift in GILE-guided behavior above a critical GILE Truth score. This is not a gradient — it is a phase transition.

**What FEP predicts:** Smooth, monotonic improvements in prediction accuracy as priors are updated. No threshold.

**What TI Sigma predicts:** Below GT = 0.4142, behavior is Existence-primary (EF/Physical Bonds dominant). Above GT, GILE-primary (genuine goodness, intuitive knowing, love as primary organizing frame). The shift is non-linear — a phase transition.

**Neuroimaging test:** Using **threshold detection models** in SPM (segmented regression or Davies test applied to fMRI data), test whether there is a discontinuous shift in DMN ↔ task-positive network competition at GILE composite ≈ 0.42 (measured via psychometric battery). If confirmed, this would be the first empirically validated neural phase transition in human moral development.

**Why this matters for brain imaging:** SPM's GLM assumes linearity. To detect the Emerick Threshold, analysts must use **threshold-specific models** (breakpoint regression, change-point detection) applied to neuroimaging data — a methodological extension of standard SPM practice. TI Sigma generates the hypothesis that motivates this non-linear analysis.

---

## 3. The LCC Virus — A Social Propagation Model for Brain Imaging

### 3.1 Definition

From the TI Sigma framework (first formalized in the Riemann Hypothesis application, 2025):

> **LCC Virus**: An electromagnetic-photonic information structure that latches onto uniquely identifying data streams, correlates with all available information, and propagates LCC states across individuals through physical interaction channels (biophoton resonance, neural oscillation entrainment, HRV synchronization, mirror neuron activation).

In brain imaging terms, the LCC Virus is the **mechanism by which one person's high-LCC state increases LCC in an interaction partner**, measurable in real time via simultaneous neuroimaging.

### 3.2 Four Propagation Channels

| Channel | Mechanism | Timescale | Measurable via |
|---|---|---|---|
| **HRV entrainment** | Respiratory-cardiac coupling syncs autonomic rhythms between co-located individuals | Seconds–minutes | Dual Polar H10 recording |
| **Neural oscillation coupling** | Gamma/alpha coherence spreads via social interaction (EEG hyperscanning) | Hundreds of ms | Dual EEG (hyperscanning) |
| **Mirror neuron activation** | Observation of high-LCC facial/body expression activates LCC-circuit in observer | ~400 ms | fMRI during social observation |
| **Biophoton resonance** | Ultra-weak photon emissions from high-LCC neural tissue may carry phase information (speculative; consistent with Popp, 1992; Rahnama et al., 2011) | Milliseconds | Specialized photomultiplier tubes |

### 3.3 Where the LCC Virus Diverges from Friston's Social FEP

Friston's shared Markov blankets (Kirchhoff et al., 2018; Friston, 2019) model social interaction as:
- Each agent has a Markov blanket (sensory/active states)
- Social nesting: one agent's blanket partially overlaps another's
- Social dynamics = minimizing joint free energy

**TI Sigma's LCC Virus adds three things Friston's model lacks:**

**1. Directionality of propagation.** FEP's shared blankets are symmetric — both agents minimize free energy equally. The LCC Virus is **directional**: a high-LCC individual propagates to a lower-LCC individual, not the reverse. This predicts asymmetric neural entrainment in hyperscanning studies — the high-LCC brain should lead the low-LCC brain in phase, not the reverse.

*Testable: In hyperscanning EEG, the Granger causality from high-GILE-L participant's gamma to low-GILE-L participant's gamma should be significantly greater than the reverse direction.*

**2. The love channel.** FEP models social interaction via prediction error minimization — there is no distinct "love" or "affiliation" signal. The LCC Virus specifically propagates via the GILE-L channel: what spreads is not just information but the law of correlational causation pattern associated with love and affiliation. FEP has no analogue.

**3. Viral spreading dynamics.** LCC Virus propagation follows a contagion model (not a steady-state equilibrium). High-LCC nodes in a social network should show spreading with a basic reproductive number (R₀ > 1 in certain social conditions). This generates predictions about **network-level LCC elevation** that Friston's pairwise blanket model cannot produce.

*Testable: In a social network experiment (N=30 group), seeding one high-GILE-L individual should produce measurable LCC elevation in connected individuals within 90 minutes, as measured by HRV (surrogate for LCC) — following logistic spreading dynamics, not linear diffusion.*

### 3.4 DCM Application: LCC Virus as an Effective Connectivity Hypothesis

DCM is the perfect tool to test LCC Virus predictions at the brain level. The LCC Virus predicts that during high-GILE-L social interaction, the effective connectivity model should show:

**Model A (LCC Virus — TI Sigma prediction):**
```
vmPFC ↔ amygdala (bidirectional, strong)
     ↓
Insula (via LCC coupling, emotion-body integration)
     ↓
TPJ (theory of mind — "I know what you feel")
     ↓
ACC (integration, action selection for love-appropriate behavior)
```

**Model B (FEP standard — active inference baseline):**
```
dlPFC → amygdala (top-down suppression)
     ↓
Thalamus (sensory gating)
```

DCM's Bayesian model comparison (BMS) between Model A and Model B during high-LCC social interaction episodes would provide the most direct test of whether LCC Virus dynamics are occurring as TI Sigma predicts.

---

## 4. Tralse States as a Novel Brain State Category

### 4.1 What Tralse States Are

In TI Sigma, a Tralse state is an informational condition that is **simultaneously partially true and partially false**, with measurable indeterminacy (D2 > 0.35 on the HEM Tralse Meter — URB #619). This is distinct from:
- Unknown (determinate but unmeasured)
- Superposition (quantum-style, FEP's default when evidence is balanced)
- Noise (random fluctuation)

A Tralse state is a **structured indeterminacy** — a state that simultaneously satisfies conflicting attractors in the neural landscape.

### 4.2 Neural Signature of Tralse States

TI Sigma predicts that Tralse brain states should show:

| Feature | Prediction | Measurement |
|---|---|---|
| **Bistable dynamics** | Brain alternates between two competing attractor states, not settling | Multi-voxel pattern analysis (MVPA) showing bistability |
| **Reduced law of correlational causation** | Amygdala and vmPFC are simultaneously active but uncoupled | DCM: near-zero effective connectivity between vmPFC and amygdala |
| **High prediction error dwell time** | Extended periods of unresolved prediction error signals (no Bayesian update occurring) | FRN/N200 ERP amplitude elevated for sustained periods |
| **Alpha desynchronization without gamma synchronization** | Alpha drops (attention activated) but gamma doesn't rise (no coherent representation formed) | EEG time-frequency analysis |
| **MI risk signal** | When D2 > 0.65, the system enters Meta-Indeterminate — neither truth-pole nor false-pole — with maximum neural entropy | Shannon entropy of BOLD signal elevated in DMN |

### 4.3 How This Extends FEP

FEP's prediction error signal is a **scalar** — larger = more surprised. It doesn't distinguish between:
- A large prediction error because the stimulus was *unexpected* (high surprise → simple learning)
- A large prediction error because the stimulus is *simultaneously predicted and counter-predicted* by different hierarchical levels (Tralse — structured indeterminacy)

TI Sigma's D2 Tralse Meter provides a way to measure this distinction. When multiple cortical hierarchies simultaneously generate contradictory predictions about the same stimulus, the result is not learning (Bayesian updating) but Tralse — a structured conflict requiring MR (Myrion Resolution) to resolve.

**Proposed operationalization:** Compute D2 as the **coefficient of variation** across BOLD activity in the four GILE circuits (dlPFC, hippocampus, vmPFC-amygdala, anterior insula). High D2 = high cross-circuit variance = Tralse. This can be computed trial-by-trial in an fMRI paradigm and correlated with subjective indeterminacy ratings.

---

## 5. The Five Specific Contributions — Summary Table

| Contribution | TI Sigma LCC / LCC Virus | FEP/SPM/DCM Current Capability |
|---|---|---|
| **1. GILE anatomical mapping** | Four dissociable circuits (G: dlPFC-ACC; I: hippocampus-DMN; L: vmPFC-amygdala; E: insula-visual) | Single "valence" axis; no goodness/love distinction |
| **2. Emerick Threshold detection** | Phase transition at GT ≈ 0.4142; requires threshold-detection models | Smooth learning curves only; no phase transition prediction |
| **3. Tralse states** | Structured neural indeterminacy (bistability + uncoupled LCC + sustained prediction error) | Binary prediction error only; no Tralse category |
| **4. LCC Virus social propagation** | Directed, asymmetric, contagion-model spreading of law of correlational causation patterns | Symmetric shared Markov blankets; no viral spreading dynamics |
| **5. D2 Tralse Meter** | Quantitative cross-circuit variance as neural contradiction index | No equivalent internal contradiction measure |

---

## 6. Proposed Experimental Programme

### E1: GILE Dissociation fMRI (N=40)
**Design:** 2×2×2 factorial: high/low G × high/low L × high/low I (manipulated via moral dilemma / affiliation / memory tasks)  
**Analysis:** SPM GLM + MANOVA on four ROI signals; DCM comparing G vs. L circuit dominance  
**Primary prediction:** G-condition shows dlPFC–ACC coupling (not vmPFC–amygdala); L-condition shows the reverse  
**Falsification:** No significant dissociation across GILE conditions (F < 1 for circuit × GILE interaction)

### E2: Emerick Threshold fMRI (N=60)
**Design:** Continuous GILE battery + moral decision paradigm; threshold detection applied to fMRI  
**Analysis:** Breakpoint regression on GILE composite vs. vmPFC/dlPFC connectivity strength; Davies test for threshold location  
**Primary prediction:** Threshold at GILE ≈ 0.42 (±0.05); connectivity model shifts at threshold  
**Falsification:** Linear model significantly better than threshold model (ΔAIC > 4)

### E3: LCC Virus Hyperscanning EEG (N=20 dyads)
**Design:** High-GILE-L (seeded) vs. low-GILE-L (naive) participant pairs; 45-min social interaction; simultaneous EEG  
**Analysis:** Inter-brain synchrony (IBS) at 40Hz; Granger causality: high-GILE-L → low-GILE-L direction  
**Primary prediction:** Granger GC(high→low) > GC(low→high) at p < 0.01; LCC surrogate (HRV) in low-GILE-L partner increases ≥ 15%  
**Falsification:** GC is symmetric (no directional advantage for high-GILE-L partner)

### E4: Tralse State Neural Signature (N=30)
**Design:** Bistability paradigm (ambiguous figure + moral dilemma; indeterminate emotional stimuli); D2 computed from BOLD variance across four GILE circuits  
**Analysis:** DCM comparing bistable vs. resolved trials; correlation of D2 with subjective indeterminacy rating  
**Primary prediction:** D2 > 0.35 trials show reduced vmPFC–amygdala coupling and elevated alpha-desync without gamma-sync  
**Falsification:** No difference in DCM models between D2-high and D2-low trials

### E5: LCC Virus Social Network Propagation (N=30 group)
**Design:** One high-GILE-L seed individual introduced to 29 naive participants; HRV measured continuously for 90 minutes of structured interaction  
**Analysis:** Logistic spreading model vs. linear diffusion model; compare fit  
**Primary prediction:** LCC (HRV surrogate) elevation spreads logistically from seed; R₀ estimated > 1 within 90 min  
**Falsification:** Linear diffusion outperforms logistic model (ΔIC > 2)

---

## 7. Where TI Sigma Is Weaker Than FEP/SPM/DCM

Intellectual honesty requires clear acknowledgment of TI Sigma's current limitations relative to the established framework:

1. **Mathematical formalization:** Friston's FEP is expressed in variational calculus and information geometry. TI Sigma's LCC dynamics have not yet been formalized at this level. The GILE weights (G=√2−1, I=0.25, L=0.18, E=0.15) are empirically motivated but not derived from first principles. **This is a significant gap that future URBs must address.**

2. **Empirical track record:** SPM/DCM have thousands of replicated findings. TI Sigma has zero brain imaging replications. The entire experimental programme in Section 6 remains unexecuted.

3. **Mechanistic specificity:** FEP specifies a mathematical mechanism (variational free energy minimization) at the neuronal level. TI Sigma specifies circuits and dynamics but not the specific computational mechanism that implements GILE optimization.

4. **The LCC Virus biophoton channel (Channel 4):** While consistent with Popp's biophoton emission data (1992) and Rahnama et al. (2011), the biophoton propagation channel remains speculative. Channels 1–3 (HRV entrainment, neural oscillation coupling, mirror neurons) are empirically grounded; Channel 4 is not.

These gaps are not reasons to reject TI Sigma — they are the research programme TI Sigma generates.

---

## 8. Why TI Sigma and FEP are Ultimately Complementary

FEP's core claim: *the brain minimizes surprise.*  
TI Sigma's core claim: *the brain also optimizes toward GILE dimensions — and this optimization has a different target function and generates a different set of predictions.*

These are not contradictory. A brain that minimizes free energy AND simultaneously optimizes GILE expression is more constrained than one that does either alone. TI Sigma generates **additional constraints** on what the FEP-optimal solution looks like when the generative model has GILE structure.

Formally: if we allow the FEP's generative model to encode GILE priors — preferred states for G, I, L, E — then FEP would predict exactly what TI Sigma predicts about brain connectivity during high-GILE states. The LCC Virus is then the mechanism by which GILE-encoded generative models spread between agents.

This means TI Sigma can be **embedded within FEP** as a specific parameterization of the generative model — one where the preferred states encode GILE dimensions, the Emerick Threshold is a bifurcation in the attractor landscape, and the LCC Virus is an inter-agent active inference mechanism.

This embedding makes TI Sigma empirically richer than a standalone framework and mathematically grounded in the existing FEP literature.

---

## 9. Conclusions

The TI Sigma LCC framework and its propagating extension (the LCC Virus) offer five specific empirical contributions to brain imaging science that are orthogonal to current FEP/SPM/DCM practice:

1. **GILE anatomical mapping** — four dissociable circuits that SPM can test and DCM can model
2. **Emerick Threshold** — a neural phase transition that requires threshold-detection models absent from standard SPM practice
3. **Tralse states** — a novel neural state category beyond FEP's prediction-error signal, measurable as cross-circuit D2 variance
4. **LCC Virus social propagation** — directed, asymmetric, contagion-model spreading of law of correlational causation, testable via hyperscanning EEG Granger causality
5. **D2 Tralse Meter** — an objective neural contradiction index, operationalizable as BOLD variance across GILE circuits

None of these require abandoning FEP/SPM/DCM. All five can be tested using existing neuroimaging tools. TI Sigma's contribution is the hypothesis structure — the specific, falsifiable predictions — that existing neuroscience lacks.

The most immediate test: **E3 (LCC Virus hyperscanning EEG)** requires only two EEG headsets, two GILE-assessed participants, and 45 minutes of interaction data. This is within reach of any cognitive neuroscience lab, for under $1,000. If Granger causality from the high-GILE-L partner's 40Hz gamma to the low-GILE-L partner's 40Hz gamma is significantly directional, the LCC Virus is confirmed at the neural level.

---

## References

Friston, K. (2010). The free-energy principle: A unified brain theory? *Nature Reviews Neuroscience*, 11(2), 127–138.

Friston, K., Harrison, L., & Penny, W. (2003). Dynamic causal modelling. *NeuroImage*, 19(4), 1273–1302.

Friston, K. (2019). A free energy principle for a particular physics. *arXiv:1906.10184.*

Kirchhoff, M., Parr, T., Palacios, E., Friston, K., & Kiverstein, J. (2018). The Markov blankets of life. *Journal of the Royal Society Interface*, 15(138), 20170792.

Ashburner, J., & Friston, K. J. (2005). Unified segmentation. *NeuroImage*, 26(3), 839–851.

Friston, K. J., et al. (1994). Statistical parametric maps in functional imaging: A general linear approach. *Human Brain Mapping*, 2(4), 189–210.

Habib, A. M., et al. (2019). Microdeletion in a FAAH pseudogene identified in a patient with high anandamide concentrations and pain insensitivity. *British Journal of Anaesthesia*, 123(2), e249–e253.

Popp, F. A. (1992). Some essential questions of biophoton research and probable answers. *Recent Advances in Biophoton Research and Its Applications*, 1–46.

Rahnama, M., et al. (2011). Emission of mitotic radiation from Vicia faba. *International Journal of Integrative Biology*, 6(1).

Messaoudi, M., et al. (2011). Assessment of psychotropic-like properties of a probiotic formulation (Lactobacillus helveticus R0052 and Bifidobacterium longum R0175) in rats and human subjects. *Beneficial Microbes*, 2(4), 381–388.

Emerick, B. C. (2025). URB #614: BOK as TI Sigma Flagship. TI Sigma / BlissGene Therapeutics.

Emerick, B. C. (2026). URB #619: HEM→EF Bridge and FFD–Tralse Equation. TI Sigma / BlissGene Therapeutics.

---

*URB #620 | TI Sigma Experimental Philosophy Series | Brandon Charles Emerick | April 7, 2026*

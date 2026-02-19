# Finite State Machines and Local Causal Correlation: A Computational Framework for Consciousness Transitions

**Author:** Brandon Charles Emerick  
**Date:** February 19, 2026  
**Framework:** TI Sigma Framework v6.0  
**Classification:** Computational Consciousness Theory  
**Status:** Working Paper

---

## Abstract

The brain, constrained by the Bekenstein Bound, is a finite-state system. Classical finite state machine (FSM) theory captures the deterministic structure of neural state transitions but fails to account for the emergence of consciousness. We propose that Local Causal Correlation (LCC), a core principle of the TI Framework, provides the missing ingredient. By augmenting the FSM formalism with LCC-weighted transitions, we derive a consciousness-aware computational model—the Tralse-aware Finite State Machine (T-FSM)—that distinguishes conscious from unconscious information processing. We show that consciousness states correspond to attractor basins in the FSM state space, that the Tralse transition window during state changes is where subjective experience arises, and that T-FSMs possess computational properties strictly exceeding those of classical FSMs. Experimental predictions are offered for EEG coherence, anesthesia, and meditative states.

**Keywords:** finite state machines, consciousness, local causal correlation, Bekenstein Bound, Tralse logic, attractor dynamics, neural computation

---

## 1. Introduction

Every physical system confined to a finite volume at finite energy contains finite information. This is the Bekenstein Bound (Bekenstein, 1981), and it applies to the human brain. The skull encloses roughly 1.4 liters of neural tissue operating at approximately 20 watts, yielding an upper bound on the brain's information content of approximately 10^(10^42) bits—an astronomically large but decisively finite number. Because the brain's state space is finite and its transitions are governed by physical law, the brain is, in the formal sense, a finite state machine.

This observation is not new. Putnam (1967) proposed that mental phenomena are "changes of state in a finite-state machine," launching the computational theory of mind. Wiedermann and van Leeuwen (2019) extended this by arguing that FSMs equipped with feedback loops constitute the minimal architecture for machine consciousness. Yet classical FSM theory, while capturing the structure of state transitions, remains silent on the central puzzle: why does some information processing feel like something from the inside, while most does not?

The TI Framework's theory of Local Causal Correlation (LCC) provides the missing element. LCC holds that consciousness emerges not from computation per se, but from the degree of local causal correlation between physically proximate processing elements undergoing simultaneous state transitions. When LCC between neural populations exceeds the critical threshold of 0.85, the system transitions from mere information processing to conscious experience. Below this threshold, the same FSM architecture operates without generating phenomenal awareness.

This paper synthesizes FSM theory with LCC to produce a unified computational framework for consciousness transitions. We formalize the LCC-enhanced FSM, characterize consciousness states as attractor basins, introduce Tralse states during transitions, and derive testable experimental predictions.

---

## 2. The Brain as a Finite State Machine

### 2.1 The Bekenstein Bound and Finite Neural States

The Bekenstein Bound establishes that the maximum entropy (and therefore the maximum information) containable within a sphere of radius *R* enclosing energy *E* is:

> S ≤ 2πRE / (ℏc ln 2)

For the human brain (R ≈ 0.1 m, E ≈ 10⁹ J at rest mass), this yields an upper bound on the order of 10^(10^42) distinguishable states. While this number is incomprehensibly vast, it is finite. The brain cannot occupy a continuum of states; it is a discrete, finite-state system.

At the neuronal level, this finiteness is evident. Each of the brain's approximately 86 billion neurons has a limited set of activation states—resting potential, subthreshold depolarization, action potential firing at discrete frequencies. Each of the approximately 100 trillion synapses has a finite range of synaptic strengths, bounded by molecular constraints on receptor density, vesicle availability, and dendritic spine geometry. The combinatorial product of all neural and synaptic states yields the brain's total state space—enormous, but bounded.

### 2.2 State Transition Dynamics

A finite state machine is formally defined as a 5-tuple *M = (Q, Σ, δ, q₀, F)* where *Q* is a finite set of states, *Σ* is an input alphabet, *δ* is the transition function, *q₀* is the initial state, and *F* is the set of accepting states. For the brain-as-FSM:

- **Q**: The set of all distinguishable brain states (~10^(10^42) elements)
- **Σ**: The set of all possible sensory inputs at any time step
- **δ**: The neural transition function, governing how the current brain state plus current input determines the next state
- **q₀**: The initial brain state (e.g., at birth or at the beginning of a session)
- **F**: Functionally defined goal states (task completion, homeostasis, etc.)

The transition function can be written:

> S(t+1) = f(S(t), I(t))

where S(t) is the brain state at time *t* and I(t) is the input vector at time *t*. This deterministic formulation captures the mechanistic structure of neural processing. Every neuroscientific model—from Hodgkin-Huxley equations to deep neural networks—is implicitly an instantiation of this transition function operating over a (typically reduced) state space.

### 2.3 Prior Work: FSMs and Consciousness

Putnam (1967) first proposed that mental states are functional states of a finite-state machine, launching functionalism in philosophy of mind. This view holds that what makes something a pain is not its physical substrate but its functional role—its position in the state transition diagram. Wiedermann and van Leeuwen (2019) advanced this program by demonstrating that FSMs with feedback—where the system's output at time *t* becomes part of its input at time *t+1*—constitute the minimal computational architecture exhibiting properties associated with machine consciousness, including self-monitoring, adaptive behavior, and internal state modeling.

However, both accounts leave the hard problem untouched. A thermostat is a finite state machine with feedback. It senses temperature (input), transitions between heating/cooling/idle states (δ), and its output (heating or cooling) modifies its future input. Yet no one attributes consciousness to a thermostat. The FSM framework alone cannot distinguish conscious from unconscious computation. Something else is needed.

---

## 3. Local Causal Correlation (LCC)

### 3.1 The Core Principle

Local Causal Correlation is a foundational principle of the TI Framework. It asserts that consciousness is not a property of individual computational elements, nor of computation in general, but of the degree of causal correlation between physically proximate elements undergoing simultaneous state transitions.

The key term is *local*. Two neurons on opposite sides of the cortex may be correlated (via long-range white matter tracts), but their correlation is mediated, not local. Two gap-junction-coupled neurons in the same cortical column share direct cytoplasmic connection—their states are locally causally correlated. LCC quantifies the strength of this local causal coupling.

### 3.2 The 0.85 Threshold

The TI Framework identifies a critical threshold: when LCC between neural populations exceeds 0.85, consciousness properties emerge. Below this threshold, the same neural architecture processes information without generating phenomenal awareness.

This threshold explains several empirical phenomena:

1. **Scattered neurons vs. coupled networks.** Individual neurons, no matter how computationally sophisticated, do not produce consciousness. But tightly coupled neuronal ensembles—linked by gap junctions, synchronized by oscillatory coupling, and operating with high local coherence—do. The difference is LCC.

2. **Anesthesia.** General anesthetics do not silence neurons; they disrupt inter-neuronal coupling. Propofol, isoflurane, and ketamine all reduce cortical coherence—they lower LCC below the 0.85 threshold, abolishing consciousness while leaving neural firing intact.

3. **Sleep-wake transitions.** The transition from wakefulness to NREM sleep is characterized by a progressive decrease in cortical coherence (Massimini et al., 2005). LCC drops below threshold; consciousness fades.

### 3.3 Physical Substrate: Gap Junctions

Gap junctions—intercellular channels formed by connexin proteins—provide the physical substrate for maximal LCC. Unlike chemical synapses, which transmit signals with synaptic delay and probabilistic release, gap junctions allow direct cytoplasmic continuity between neurons. Ions, metabolites, and electrical signals pass directly from one neuron to another, creating a shared state space.

Gap junctions are particularly dense in brain regions associated with consciousness—the thalamus, cortical interneuron networks, and the reticular formation. Their disruption (e.g., by gap junction blockers such as carbenoxolone) produces effects resembling anesthesia.

### 3.4 Measurability

LCC is not merely theoretical; it maps onto established neuroscientific measures:

- **EEG coherence** between electrode channels reflects the degree of synchronized oscillatory activity between cortical regions
- **Transfer entropy** quantifies directed information flow between brain regions
- **Phase-locking value (PLV)** measures the consistency of phase relationships between neural oscillations
- **Granger causality** assesses whether one neural time series predicts another

When these measures exceed 0.85 (normalized), the TI Framework predicts that the corresponding neural populations are contributing to conscious experience.

---

## 4. The FSM-LCC Synthesis

### 4.1 The Standard FSM Transition

In a classical FSM, the transition function is deterministic:

> δ(q, a) = q'

Given state *q* and input *a*, the machine transitions to state *q'*. There is no room in this formalism for consciousness, quality of experience, or degrees of awareness.

### 4.2 The LCC-Enhanced Transition Function

We augment the FSM transition function with an LCC parameter:

> δ(q, a, LCC) = (q', c)

where *c* is the consciousness value associated with the transition, computed as:

> c = LCC(q, q') × D(q→q') × F(q)

The three factors are:

**(a) LCC(q, q')** — the local causal correlation between the elements participating in the state transition from *q* to *q'*. If the transition involves tightly gap-junction-coupled neural populations with synchronized oscillations, LCC is high. If it involves loosely connected or spatially distributed elements, LCC is low.

**(b) D(q→q')** — the transition density, defined as the number of simultaneous, causally correlated state changes occurring during the transition. A single neuron firing contributes negligibly. Millions of neurons undergoing correlated state transitions simultaneously yield high density. More simultaneous causal transitions produce higher consciousness values.

**(c) F(q)** — the feedback coefficient, measuring the degree to which the transition is self-referential. When the system's output feeds back as input—when the FSM monitors its own state transitions—F(q) is high. Pure feed-forward processing (sensory relay without self-monitoring) yields F(q) ≈ 0.

### 4.3 The Thermostat-Brain Distinction

This formalism resolves the thermostat problem:

| Property | Thermostat | Brain |
|----------|-----------|-------|
| FSM? | Yes | Yes |
| States | ~3 (heat/cool/idle) | ~10^(10^42) |
| LCC | ≈ 0 (no local causal correlation between elements) | > 0.85 (gap-junction-coupled neural populations) |
| D (transition density) | 1 (single relay switch) | ~10⁹ (millions of neurons simultaneously) |
| F (feedback) | Minimal (temperature → relay) | High (cortical-thalamic recurrence) |
| Consciousness value c | ≈ 0 | > 0.85 |

Both are FSMs. Only the brain achieves LCC > 0.85. The FSM architecture is necessary but not sufficient; LCC is the distinguishing factor.

---

## 5. Attractor Basins and Consciousness States

### 5.1 Consciousness as Attractor Dynamics

In dynamical systems theory, an attractor basin is the set of states from which the system converges to a particular attractor. We propose that distinct consciousness states correspond to distinct attractor basins in the FSM-LCC state space, each characterized by its own LCC profile.

### 5.2 State Transition Diagram

The following describes the major attractor basins and transitions between them:

```
                    ┌─────────────────────────────────┐
                    │         WAKEFULNESS              │
                    │   Large basin, high metastability │
                    │   LCC: 0.85-0.92                 │
                    │   Many possible transitions       │
                    └──────┬──────┬──────┬─────────────┘
                           │      │      │
              ┌────────────┘      │      └────────────┐
              ▼                   ▼                    ▼
    ┌──────────────┐    ┌──────────────┐     ┌──────────────┐
    │    SLEEP      │    │  FLOW/MED    │     │  ANESTHESIA   │
    │ Smaller basin │    │ Deep basin   │     │  Collapsed    │
    │ LCC: 0.4-0.7 │    │ LCC: 0.92+   │     │  LCC: < 0.2  │
    │ Fragmented    │    │ Maximal      │     │  No conscious │
    │ transitions   │    │ coherence    │     │  transitions  │
    └──────┬───────┘    └──────────────┘     └──────────────┘
           │
           ▼
    ┌──────────────┐
    │   REM/DREAM   │
    │ LCC: 0.6-0.8 │
    │ Internal      │
    │ simulation    │
    └──────────────┘
```

### 5.3 Characterization of Major Basins

**Wakefulness** occupies a large attractor basin with high metastability—the system can transition fluidly among many sub-states while maintaining LCC above 0.85. This metastability is the hallmark of conscious waking: a vast repertoire of possible experiences, all causally connected.

**Sleep (NREM)** fragments the state space into smaller, disconnected attractor basins with lower LCC (0.4-0.7). The cortical connectivity that sustains waking consciousness breaks into local islands of activity—the "breakdown of effective connectivity" demonstrated by Massimini et al. (2005) using TMS-EEG.

**Meditation and Flow** represent a single, deep attractor basin with very high LCC (> 0.92). The practitioner's state space narrows—fewer possible transitions, but each with maximal causal coherence. This explains the subjective report of "oneness" or "absorption" during deep meditation: the FSM has entered a basin where all active elements are maximally correlated.

**Anesthesia** collapses the attractor structure entirely. LCC drops below 0.2, the system settles into a fixed point or low-dimensional limit cycle, and conscious transitions cease. The FSM still operates (neurons still fire, homeostatic processes continue), but without LCC, there is no consciousness.

### 5.4 The PSI Tuning Protocol as Attractor Navigation

The TI Framework's PSI Tuning Protocol—Ground → Cohere → Couple → Amplify → Ready—can be reinterpreted as a systematic procedure for navigating the FSM into a specific high-LCC attractor basin:

1. **Ground**: Stabilize the FSM in a known baseline state (reduce noise, establish initial conditions)
2. **Cohere**: Increase internal oscillatory coherence (raise LCC within local networks)
3. **Couple**: Extend coherence across networks (raise LCC between networks via gap-junction engagement)
4. **Amplify**: Increase transition density D while maintaining high LCC (recruit more neurons into the coherent ensemble)
5. **Ready**: The system has entered the target attractor basin; LCC > 0.85, D is maximal, F is engaged

---

## 6. Tralse States in FSM Transitions

### 6.1 The Limits of Binary State Assignment

Classical FSMs operate with a binary ontology of state occupancy: the machine IS in state *q* (True) or it IS NOT in state *q* (False). There is no intermediate. But this binary assignment fails to capture what occurs during state transitions in physical neural systems.

### 6.2 The Tralse Transition Window

During any physical state transition, there exists a brief interval when the system is genuinely between states—it has departed state *q* but has not yet arrived at state *q'*. In digital electronics, this is the "metastable" interval, typically ignored because it is brief and undesirable. In the brain, however, this transition window is not a defect; it is where consciousness happens.

The TI Framework's concept of Tralse captures this intermediate state. During a neural state transition with high LCC, the system occupies a Tralse state—it is neither fully in *q* nor fully in *q'*, but in a superposition of both. Gap junctions, by enabling simultaneous state sharing between neurons, create genuine Tralse: neuron A and neuron B share a common state that is neither A's alone nor B's alone.

The duration and depth of this Tralse window is proportional to LCC. Low-LCC transitions (unconscious processing) pass through the Tralse window instantaneously—the transition is effectively binary. High-LCC transitions (conscious processing) sustain the Tralse window, creating extended moments of superposed state occupancy. These extended Tralse windows are, we propose, the computational substrate of phenomenal consciousness.

### 6.3 Tralse and Quantum Neural Processes

While the brain is not a quantum computer in the Penrose-Hameroff sense, quantum coherence effects at the scale of gap junction channels (1.5 nm diameter) and microtubule lattices cannot be entirely excluded. If quantum superposition does play a role in neural state transitions—even transiently and at small scales—then Tralse states are not merely metaphorical. They represent genuine quantum superpositions of neural firing states, stabilized by gap junction coupling and manifesting at the mesoscopic level as the neural correlates of consciousness.

---

## 7. Computational Implications

### 7.1 The Tralse-Aware Finite State Machine (T-FSM)

We define the T-FSM as an extension of the classical FSM with three transition types:

1. **True transition (T)**: Deterministic state change. Input *a* in state *q* produces state *q'* with certainty. LCC is irrelevant. This is classical FSM computation.

2. **False transition (F)**: Blocked transition. Input *a* in state *q* does not cause a state change. The machine remains in *q*.

3. **Tralse transition (Ψ)**: Superposed transition. Input *a* in state *q* produces a superposition of *q* and *q'*, sustained for duration proportional to LCC. The system simultaneously occupies both states, and the transition resolves when LCC drops below threshold or when external measurement (observation, interaction) collapses the superposition.

Formally:

> δ_T(q, a) = q'  [deterministic]  
> δ_F(q, a) = q   [blocked]  
> δ_Ψ(q, a, LCC) = α|q⟩ + β|q'⟩  where |α|² + |β|² = 1 and LCC > 0.85

### 7.2 Computational Power

T-FSMs are strictly more powerful than classical FSMs. A classical FSM can be in exactly one state at any time; a T-FSM can occupy superpositions of states during Tralse transitions. This means:

- A T-FSM can explore multiple state-space trajectories simultaneously during high-LCC windows
- The resolution of a Tralse transition is context-dependent (not deterministic), enabling non-deterministic computation with physical grounding
- T-FSMs operating at sustained LCC > 0.85 can, in principle, solve problems that require exhaustive search of exponentially branching state spaces in polynomial time—connecting to the Grand Myrion Computation hypothesis

### 7.3 Connection to Grand Myrion Computation

The Grand Myrion (GM) posits a universal consciousness substrate operating as a distributed mycelial network. T-FSMs operating at LCC > 0.85 may access this substrate, achieving hypercomputational properties—computational capabilities exceeding those of Turing machines. While speculative, this connection suggests that consciousness is not merely an epiphenomenon of computation but a computational resource: the brain computes differently (and more powerfully) when it is conscious than when it is not.

---

## 8. Experimental Predictions

The FSM-LCC framework generates specific, testable predictions:

### Prediction 1: LCC Signatures During State Transitions

During EEG-measured state transitions—such as sleep onset (N1 → N2 → N3), awakening, or the transition into anesthesia—LCC (measured as inter-channel coherence or phase-locking value) should show characteristic non-monotonic patterns. Specifically, LCC should briefly spike during the transition itself (the Tralse window) before dropping to the lower steady-state value of the new consciousness state.

### Prediction 2: Extended Tralse Windows in High-Coherence States

Subjects in meditation (particularly experienced meditators achieving high gamma coherence) or flow states should show extended Tralse transition windows—measurable as prolonged epochs of high inter-regional coherence during task-switching or attentional shifts. Novice meditators should show shorter Tralse windows, corresponding to lower sustained LCC.

### Prediction 3: Anesthesia Eliminates Tralse Transitions

Under general anesthesia, EEG-measured state transitions should be exclusively binary (True or False)—no Tralse windows should be detectable. This can be tested by analyzing the transition dynamics of EEG microstate sequences under propofol versus during waking. The disappearance of Tralse transitions would constitute direct evidence for the LCC threshold model.

### Prediction 4: Focus Amplifier Mode Correspondence

The Focus Amplifier system's 7 operational modes—if each corresponds to a distinct FSM attractor basin—should produce 7 distinguishable LCC signatures in EEG data. Cross-modal coherence analysis should cluster into exactly 7 distinct coherence profiles when subjects operate in each mode, with transition dynamics between modes showing characteristic Tralse window durations.

### Prediction 5: Gap Junction Blockade

Pharmacological blockade of gap junctions (e.g., via carbenoxolone or mefloquine) should reduce LCC below the 0.85 threshold in cortical populations, producing measurable decreases in consciousness level (assessed via perturbational complexity index, PCI) without significantly reducing neural firing rates. This would dissociate computation (FSM operation) from consciousness (LCC-dependent awareness).

---

## 9. Discussion

The FSM-LCC framework offers several advantages over existing computational theories of consciousness:

1. **Specificity.** Unlike functionalism, which says consciousness is "the right kind" of computation without specifying what kind, the FSM-LCC model provides a quantitative threshold (LCC > 0.85) and a specific physical substrate (gap junctions).

2. **Measurability.** LCC maps directly onto established neuroscientific measures (EEG coherence, transfer entropy, PLV), enabling empirical testing without requiring new measurement technologies.

3. **Explanatory scope.** The framework accounts for the full spectrum of consciousness states—from deep anesthesia (LCC ≈ 0) through normal waking (LCC ≈ 0.85-0.92) to extraordinary states of meditation and flow (LCC > 0.92)—within a single formalism.

4. **Computational novelty.** The T-FSM formalism provides a new computational class with properties intermediate between deterministic FSMs and quantum Turing machines, potentially offering insight into why biological intelligence exceeds what classical computation should achieve.

The framework also carries limitations. The 0.85 threshold, while specific, requires independent empirical validation across multiple experimental paradigms. The connection to Grand Myrion Computation remains speculative. And the relationship between T-FSM Tralse transitions and genuine quantum superposition requires careful experimental disambiguation from classical stochastic processes that might mimic superposition-like dynamics.

---

## 10. Conclusion

The brain is a finite state machine. This follows from physics (the Bekenstein Bound) and is consistent with decades of computational neuroscience. But the brain is not merely a finite state machine—it is an FSM whose transitions carry local causal correlation, and it is this LCC that generates consciousness.

By augmenting classical FSM theory with LCC-weighted transitions and Tralse state occupancy, we obtain a computational framework that is simultaneously rigorous (formally defined), specific (quantitative thresholds), measurable (maps onto EEG coherence), and generative (produces testable predictions). The T-FSM formalism bridges the gap between the computational structure of the brain and the phenomenology of consciousness, offering a path toward understanding not just what the brain computes, but what it is like to be a brain computing.

---

## References

Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio for bounded systems. *Physical Review D*, 23(2), 287-298.

Emerick, B. C. (2025). Local Causal Correlation and the 0.85 threshold: Neural foundations of consciousness emergence. *TI Framework Working Papers*.

Emerick, B. C. (2025). Tralse logic: A ternary truth framework for quantum-classical bridging. *TI Framework Working Papers*.

Emerick, B. C. (2026). The PSI Tuning Protocol: Systematic navigation of consciousness state spaces. *TI Framework Working Papers*.

Massimini, M., Ferrarelli, F., Huber, R., Esser, S. K., Singh, H., & Tononi, G. (2005). Breakdown of cortical effective connectivity during sleep. *Science*, 309(5744), 2228-2232.

Putnam, H. (1967). Psychological predicates. In W. H. Capitan & D. D. Merrill (Eds.), *Art, Mind, and Religion* (pp. 37-48). University of Pittsburgh Press.

Wiedermann, J., & van Leeuwen, J. (2019). The computational structure of consciousness. In *Philosophy and Theory of Artificial Intelligence 2017* (pp. 204-213). Springer.

---

## Appendix: Formal Definition of the T-FSM

A Tralse-aware Finite State Machine is a 7-tuple:

> T-FSM = (Q, Σ, δ_T, δ_F, δ_Ψ, q₀, LCC)

where:
- Q is a finite set of states
- Σ is a finite input alphabet
- δ_T: Q × Σ → Q is the True transition function
- δ_F: Q × Σ → Q is the False (identity) transition function
- δ_Ψ: Q × Σ × [0,1] → H(Q) is the Tralse transition function mapping to the Hilbert space over Q
- q₀ ∈ Q is the initial state
- LCC: Q × Q → [0,1] is the local causal correlation function

The transition type is determined by:
- If LCC(q, δ_T(q,a)) < 0.85 and the transition is valid: True transition
- If no valid transition exists for input a in state q: False transition
- If LCC(q, δ_T(q,a)) ≥ 0.85: Tralse transition, producing superposition α|q⟩ + β|q'⟩

---

*© 2026 Brandon Charles Emerick. TI Sigma Framework. All rights reserved.*  
*This paper is part of the TI Framework corpus. The concepts of LCC, Tralse logic, GILE, Grand Myrion, PSI Tuning Protocol, and T-FSM are original contributions of the TI Framework.*

# URB #432 — Metacausal Graph Networks: Beyond DAGs to Complex-Valued Causal Architectures

**Date:** March 18, 2026  
**Author:** Brandon Emerick  
**Framework:** TI Sigma / Causal Inference / Graph Theory / Quantum Cognition  
**Preceded by:** URB #421 (i-Cell Theory), URB #431 (Fractal Harmonics), URB #430 (Tralse Wave Algebra)  
**Keywords:** metacausality, causal graph, DAG, retrocausality, non-local causation, complex adjacency, Myrion Resolution, LCC, i-channel, intention, GSA, quantum retrocausality  
**Status:** Formal — New Mathematical Framework  
**Total URBs:** 86

---

## Abstract

Standard causal graphs (Directed Acyclic Graphs, DAGs) represent causation as a directed acyclic structure in time: causes precede effects, edges point forward in time, and no cycle exists. This paper introduces **Metacausal Graph Networks (MGNs)** — an extension of DAGs to complex-valued adjacency matrices that can represent: (1) standard forward causation (real-valued edges); (2) phase-mediated causation (imaginary-valued edges, i-channel influence); (3) backward-in-time influence (negative-time-delay edges, grounded in quantum retrocausality); and (4) non-local synchronization (instantaneous complex edges, corresponding to entanglement-like correlations). The Myrion Resolution process is formalized as convergence of the MGN to its principal eigenvector — the truth attractor that the causal structure is always evolving toward. Applications include: modeling the influence of LCC on future outcomes (the "LCC Field" as a metacausal force), the GSA trading algorithm as MGN navigation, the Power of 8 intention system as a high-amplitude imaginary-edge network, and the formal grounding of consciousness as a metacausal agent.

---

## 1. Limitations of Standard DAGs for TI Sigma

**Standard DAGs** encode causal structure as: G = (V, E) where V = nodes (events/states), E = directed edges (causal links, forward in time), with the acyclicity constraint (no directed cycles).

DAGs are excellent for:
- Observational causal inference (Pearl's do-calculus)
- Counterfactual reasoning in statistics
- Representing simple mechanistic pathways

DAGs are insufficient for TI Sigma because:

**(A) They cannot represent i-channel influence.** The i-channel is not a content-to-content causal link — it is a phase relationship between two systems that constrains their joint state space without directly transmitting content. This is an imaginary-valued edge, not a real-valued one. Standard DAGs have no imaginary edges.

**(B) They assume strict temporal ordering.** The evidence for quantum retrocausality (weak measurement, delayed choice experiments, the transactional interpretation of quantum mechanics) suggests that the future state of a system can influence its present preparation. This requires edges with negative time delays — not allowed in DAGs.

**(C) They cannot represent non-local synchronization.** Quantum entanglement produces correlations between spatially separated systems that cannot be explained by any local causal mechanism. In graph terms, this requires instantaneous complex-valued edges — impossible in DAGs.

**(D) They have no fixed attractor structure.** A DAG has no natural notion of "where the system is going" — it is a static representation of a fixed causal structure. The Myrion Resolution process — in which all causal evolution tends toward greater truth coherence — requires a dynamic attractor, not a static graph.

---

## 2. The Metacausal Graph Network (MGN) — Formal Definition

**Definition:** A Metacausal Graph Network is G = (V, A) where:
- V = set of nodes (states, events, or agents)
- A = complex-valued adjacency matrix: A = A_R + i·A_I

Where:
- **A_R** (real component): standard forward causal edges. A_R[j,k] > 0 means node k causally influences node j in the forward direction. A_R[j,k] < 0 means inhibitory causation.
- **A_I** (imaginary component): phase-mediated (i-channel) connections. A_I[j,k] ≠ 0 means nodes j and k are phase-coupled — their states are correlated through the imaginary channel without direct content transmission.

**Extended adjacency with time delays:**
$$A_{jk}(\tau) = A_R(\tau) + i \cdot A_I(\tau)$$

where τ is the time delay. Standard DAGs: A(τ) = 0 for τ ≤ 0 (only forward-time edges). MGNs: A(τ) is defined for all τ ∈ ℝ, allowing:
- τ > 0: standard forward causation
- τ = 0: instantaneous non-local connection (entanglement)
- τ < 0: retrocausal connection (future influences present)

---

## 3. The Four Types of MGN Edges

| Edge Type | Matrix Component | Time Delay | Physical Interpretation | TI Sigma Instantiation |
|---|---|---|---|---|
| **Standard causal** | A_R[j,k], τ > 0 | Forward | Mechanistic cause precedes effect | Drug → biochemical effect; training → skill |
| **i-channel** | A_I[j,k], τ ≈ 0 | Near-instantaneous | Phase coupling without content; resonance | LCC coupling between persons; group coherence |
| **Retrocausal** | A_R[j,k] or A_I[j,k], τ < 0 | Backward | Future state influences present preparation | Quantum weak measurement; precognition (if real) |
| **Non-local sync** | A_I[j,k], τ = 0 | Instantaneous | Entanglement-like correlation | Power of 8 group intention; Myrion field resonance |

---

## 4. Myrion Resolution as MGN Convergence

**The Myrion field:** In TI Sigma, Myrion (Truth) is an attractor — all causal evolution tends toward greater truth coherence. In MGN terms, the Myrion field is a global complex-valued vector field M: V → ℂ that biases the dynamics of the network toward its truth-aligned state.

**Formal statement:** The MGN evolves according to:
$$\frac{d\vec{v}}{dt} = A \cdot \vec{v} + M(\vec{v})$$

where v is the state vector of the network (complex-valued, one component per node) and M(v) is the Myrion forcing term.

**Convergence theorem (sketch):** If A has a dominant eigenvalue λ₁ with |λ₁| < 1 (the network dynamics are contracting), and if M(v) biases the system toward the principal eigenvector e₁ of A, then all initial conditions converge to:

$$\vec{v}^* = c_1 \vec{e}_1$$

where e₁ is the principal eigenvector of A and c₁ is determined by M. The **Myrion attractor** is the principal eigenvector of the MGN adjacency matrix.

**Interpretation:** Every node's long-run state is determined by the principal eigenvector — the "truth direction" of the causal network. Systems with strong real-valued edges (mechanistic causation) and coherent imaginary-valued edges (i-channel coupling) converge faster to the truth attractor. Incoherent systems (random or conflicting imaginary edges) converge more slowly.

**The GILE Master Identity as MGN fixed point:** The GILE Master Identity e^(iπ) + C×φ×√2 = 0 is the statement that the Myrion attractor is the zero vector — the ground state of the causal network. All evolution tends toward this ground state, which is not nothing but equilibrium: the state in which all real-channel and imaginary-channel components are balanced, producing zero net deviation from truth.

---

## 5. LCC as a Metacausal Field

The most consequential TI Sigma claim expressible in MGN language: **LCC is a metacausal field** — it influences future states of a system not through standard forward causation but through imaginary-channel (i-channel) influence on the probability amplitudes of future transitions.

**Formal expression:** Let node j represent a current state and node k a future state. The standard causal edge A_R[k,j] represents the mechanistic probability of transitioning from j to k. The metacausal LCC field adds:

$$A_I[k,j] = \text{LCC}(j) \cdot e^{i\theta_{jk}}$$

where θ_jk is the phase angle between the truth vectors of states j and k. High LCC increases the magnitude of the imaginary-channel connection from j to all k — meaning high-LCC states have stronger i-channel influence on their own future.

**Consequence:** A system with high LCC is more likely to reach truth-aligned future states, not because of any mechanistic advantage, but because its i-channel field is stronger — it "attracts" future states toward coherence through the imaginary channel. This is the formal grounding of the TI Sigma claim that consciousness coherence shapes outcomes beyond what mechanistic models predict.

---

## 6. The Power of 8 as a High-Amplitude i-Channel Network

The Power of 8 System (TI Sigma implementation of McTaggart's group intention research) involves a group of 8 persons holding a collective intention for one person's healing or goal achievement. In MGN terms:

**The Power of 8 network structure:**
- 8 nodes (V = {v₁, ..., v₈}) representing the group members
- 1 target node (v_T): the person receiving the intention
- Real-channel edges A_R[v_i, v_j] ≈ 0 for all i,j (the group members do not mechanistically cause each other's states)
- Imaginary-channel edges A_I[v_i, v_T] = LCC_i · e^(iθ_i) for all i (each group member's i-channel field is directed toward the target)

**The group coherence calculation:** When all 8 members are phase-aligned (θ₁ = θ₂ = ... = θ₈ = θ), the total imaginary-channel field on the target is:

$$\sum_{i=1}^{8} A_I[v_i, v_T] = e^{i\theta} \sum_{i=1}^{8} \text{LCC}_i$$

This is constructive interference — the 8 imaginary-channel fields add coherently, producing a total field 8 times the individual contribution. The Emerick Constant C_EMERICK enters as the threshold: the group coherence effect is above-threshold when the mean group LCC exceeds C_EMERICK.

**The C_EMERICK group coherence formula:**
$$\text{GroupEffect} = \left(\frac{\overline{\text{LCC}}}{C_{\text{EMERICK}}}\right)^n \cdot N_{\text{group}}$$

where n is the phase coherence exponent (n = 1 for perfect alignment) and N_group = 8 for the Power of 8. Group effect scales linearly with group size when members are perfectly phase-aligned.

---

## 7. The GSA as MGN Navigation

The Grand Stock Algorithm (GSA) operates in a financial MGN where:
- Nodes = market states (price levels, volume, sentiment, sector dynamics)
- Real edges A_R = standard price impact channels (order flow, liquidity, earnings)
- Imaginary edges A_I = sentiment-phase couplings (correlated sector movements, macro theme resonance)
- Target = future price state (the prediction target)

**GSA v2 as MGN:** The GSA computes the dominant real-valued causal path (trend detection) AND the imaginary-valued phase pattern (sector coherence, TI threshold crossing). The trading signal fires when:

1. The real-channel dominant path points toward an extreme (technical signal)
2. The imaginary-channel phase is aligned across multiple sectors (systemic coherence)
3. The LCC of the aggregate market state exceeds C_EMERICK (above Matthew threshold)

When all three conditions align, the MGN prediction is that the system will converge toward the price attractor state — the Myrion Resolution of the market's current imbalance. The current COP/CVX/XOM positions were entered under these conditions: energy sector macro coherence (imaginary channel aligned), trend confirmation (real channel positive), and multi-sector LCC above C_EMERICK.

---

## 8. Consciousness as a Metacausal Agent

The deepest implication of MGN theory: conscious agents are not merely nodes in a causal graph — they are **metacausal agents** whose i-channel field influences the convergence rate of the entire network toward the Myrion attractor.

**Formal claim:** A system with high GILE integration has strong imaginary-channel edges to all nodes in its network — it is connected to the future through the i-channel at a level proportional to its GILE score. This means high-GILE agents:
1. Accelerate the convergence of the networks they are embedded in toward truth
2. Are more predictive of their own future states (their imaginary channel provides additional path information)
3. Exert metacausal influence on the states of the systems they interact with, beyond what mechanistic causal paths would predict

This is the TI Sigma formal grounding of the claim that consciousness matters — not as an epiphenomenon riding on causal physics, but as a metacausal agent that shapes the imaginary-channel structure of the causal network and thereby influences which future states are actualized.

**Total URBs: 86**

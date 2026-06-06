# URB #567: Metacausal Graph Theory (MGT)
## Corpus Entry #221

**Author**: Brandon Emerick (TI Sigma / BlissGene Therapeutics)  
**Date**: March 30, 2026  
**Status**: Draft — Formalization pending  
**DOI**: pending (Zenodo)  
**License**: Apache 2.0

---

## Abstract

Metacausal Graph Theory (MGT) extends directed graph theory to accommodate edges that transcend classical causality: edges that are non-local, retrocausal, or intention-mediated. Classical causal graphs have edges A→B meaning "A precedes and influences B in time." MGT adds **metacausal edges** A⟿B meaning "A and B are non-locally correlated, potentially across time, space, or both." The Global Consciousness Project (GCP) provides empirical data for metacausal edges. GILE Intuition is the primary source of metacausal connectivity in human consciousness.

---

## 1. Motivation

Classical causal inference (Pearl, Spirtes-Glymour-Scheines) assumes:
1. Temporal precedence: causes precede effects
2. Locality: causes and effects are spatially connected
3. Separability: disconnected events are independent

All three assumptions fail at the quantum scale, in psi phenomena, and in GILE Intuition. MGT provides a rigorous framework for non-classical correlations without abandoning mathematical precision.

**Key insight**: Metacausal edges are not "acausal" (they don't violate causality — they transcend it). A metacausal edge A⟿B means that A and B share structural information that was determined before either event was actualized — what TI Sigma calls **vern-prior information** (information that VERNS its own existence before being observed).

---

## 2. Classical vs Metacausal Edges

| Property | Causal Edge (A→B) | Metacausal Edge (A⟿B) |
|----------|-------------------|----------------------|
| Temporal order | A before B | No required order |
| Spatial proximity | Required | Not required |
| Information flow | A → B (one way) | Bidirectional, entangled |
| Mechanism | Physical process | Vern-prior structural sharing |
| Probability model | Conditional P(B\|A) | Joint P(A,B) = P(A)·P(B) + Δ_metacausal |
| Formalism | DAG, SCM | MGT (this URB) |

---

## 3. Formal Definition

### 3.1 MGT Graph

A **Metacausal Graph** G = (V, E_c, E_m, τ, λ) where:
- V = vertices (events, mental states, or information nodes)
- E_c ⊆ V×V = classical causal edges (directed, temporally ordered)
- E_m ⊆ V×{V choose 2} = metacausal edges (undirected hyperconnections)
- τ : V → ℝ = timestamp function (can be ±∞ for atemporal nodes)
- λ : E_m → [0,1] = metacausal strength (correlation beyond classical)

### 3.2 The Metacausal Strength λ

For a metacausal edge (A,B), the strength is:
```
λ(A,B) = |P(A∧B) - P(A)·P(B)| / max(P(A)·P(B), P(A∧B))
```

This is the **normalized excess correlation** above classical independence.

- λ = 0: pure independence (no metacausal connection)
- λ = 1: perfect metacausal correlation (GCP "hit" during global events)
- λ ∈ (0,1): partial metacausal entanglement

### 3.3 GILE Intuition Nodes

A node v ∈ V is a **GILE Intuition node** if:
- τ(v) is not fixed (the insight arrives "at the right time")
- λ(v, w) > 0 for some distant w (non-local awareness)
- The content of v cannot be explained by classical causal predecessors

GILE Intuition nodes are the **primary generators of metacausal edges** in human consciousness networks.

---

## 4. GCP as Empirical MGT

The **Global Consciousness Project** (Princeton, 1998–present) measures correlations in random number generators (REGs) during globally significant events (disasters, celebrations, meditations).

In MGT terms:
- Each REG is a node v_i ∈ V
- During a global event E, GCP detects: λ(v_i, v_j) > 0 across geographically separated REGs
- The metacausal edges form a **GCP subgraph** G_GCP ⊆ G
- The global significance score Z > 3.5σ corresponds to λ > λ_threshold

**GCP reading**: Global human intention creates metacausal edges between random processes. The consciousness field is the sum of all GILE Intuition nodes globally active simultaneously.

---

## 5. Vern-Prior Information and Retrocausality

**Definition** (Vern-prior information): Information that exists structurally before being observed, by virtue of its necessity in the system's coherent completion.

A metacausal edge A⟿B has **retrocausal character** when:
- τ(B) < τ(A) (B precedes A in time), yet
- B carries information about A's structure that was determined before A occurred

Example: Precognitive dreams (Dunne 1927, Bem 2011) — the future event A influences the dream state B that precedes it. In MGT: A⟿B with τ(B) < τ(A) and λ(A,B) > 0.

**Vern-Prior Theorem** (conjectured): If A verns s (i.e., A IS its structural description without being a separate thing), then every observer of s has a metacausal edge to A.

---

## 6. MGT Operations

### 6.1 Metacausal Closure

The **metacausal closure** G̃ of G adds all edges (A,B) such that:
```
∃ path A →* X ⟿ Y →* B   [reach B from A via mixed causal-metacausal path]
```

This generalizes the transitive closure of classical graphs.

### 6.2 Metacausal Betweenness

A node v is **metacausally between** A and B if it lies on a shortest mixed path from A to B. High metacausal betweenness nodes are **consciousness hubs** — they mediate between disparate regions of the metacausal graph.

In brain networks: the thalamus and default mode network (DMN) have high metacausal betweenness (Tozzi's projective collapse point).

### 6.3 Metacausal Entropy

For a node v, the **metacausal entropy** is:
```
H_m(v) = -Σ_{(v,w)∈E_m} λ(v,w)·log λ(v,w)
```

High H_m = many weak metacausal connections (diffuse awareness)  
Low H_m = few strong metacausal connections (focused intention)

**Meditation hypothesis**: Deep meditation reduces H_m to near-zero — the practitioner has strong metacausal edges to a small set of core nodes (the object of meditation, the breath, the self).

---

## 7. The Tralse Metacausal Bridge

In the 5-valued Tralse system:
- INDETERMINATE (I) states are metacausal edge candidates — they haven't collapsed yet
- TRALSE (TR) states have simultaneously classical AND metacausal edges — they are "both ways"
- DOUBLE_TRALSE (MI) states have immunity to metacausal influence (the MI Immunity Model, URB #528)

**Tralse metacausal operator** Φ_TR: transforms a classical edge A→B into a metacausal edge A⟿B by "tralse-lifting" the causal mechanism:
```
Φ_TR(A→B) = A⟿B with λ(A,B) = |TR(A)| · |TR(B)|
```

where TR(v) is the TRALSE amplitude at node v.

---

## 8. Tozzi Connection: Projective MGT

Tozzi's projective brain maps neural state A to its antipodal point A* in RP². In MGT:
- A and A* are connected by a **projective metacausal edge** A⟿A*
- This edge has λ = 1 (perfect correlation — they are the same state projected)
- The MR collapse selects one of {A, A*} as the "conscious" state

**Tozzi-MGT theorem** (conjectured): The projective metacausal edges in the brain form a graph whose Euler characteristic equals the Tralse Trace of MI (LCC ≈ 0.9).

---

## 9. Meijer Connection: Toroidal MGT

Meijer's toroidal consciousness has:
- Inner loop (self) and outer loop (world) connected through the torus hole
- The hole = the **metacausal portal** — where GILE Intuition information enters from the non-local field

In MGT: the torus T² is the metacausal closure of the self-world graph.
The hole = the connected component of metacausal edges crossing the torus cut.

---

## 10. The Power of 8 as MGT Structure

The **TI Sigma Power of 8** (group intention experiments) is an MGT:
- 8 nodes (participants) form a complete metacausal graph K₈_m
- Shared intention creates metacausal edges with λ proportional to coherence
- The GCP Z-score is the MGT betweenness centrality of the shared intention node

**Power of 8 theorem** (empirical): The metacausal strength λ of a group intention experiment scales as:
```
λ_group ≈ 1 - e^{-n/φ}   [sigmoid with golden ratio characteristic scale]
```

where n is the number of coherent participants. At n=8: λ ≈ 1-e^{-8/φ} ≈ 1-e^{-4.94} ≈ 0.993.

---

## 11. Open Problems

1. **MGT Completeness**: Is there a complete axiom system for MGT analogous to ZFC for sets?
2. **Metacausal Complexity**: What is the computational complexity of finding the metacausal closure?
3. **λ Calibration**: How to measure λ empirically in biological systems (EEG coherence?)
4. **Tralse-MGT Duality**: Is there a functor from TWA (URB #566) to MGT?
5. **GCP-MGT Fit**: Does the GCP cumulative Z-score fit the Power of 8 formula?

---

## 12. Summary

Metacausal Graph Theory provides a rigorous framework for non-local, intention-mediated, and retrocausal correlations. It bridges:
- Classical causal inference (Pearl's do-calculus)
- Quantum entanglement (non-local correlations without signaling)
- GILE Intuition (the primary metacausal faculty of human consciousness)
- GCP data (empirical measurement of global metacausal events)
- Tozzi's projective neuroscience and Meijer's toroidal field theory

**MGT makes the impossible mathematically tractable.**

---

*Filed: March 30, 2026. DOI: pending Zenodo.*

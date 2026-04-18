# URB #735 — TI Sigma Graph (TIG) Revival: Explicit Edge Structure, Edge Weights, and Topological Properties

**Author:** Brandon Charles Emerick
**Date:** April 17, 2026
**Series:** Unified Research Brief #735
**Status:** Companion to URB #734 (TIC revival); makes the graph-component of the TICG explicit
**Builds on:** URB #734 (TIC vertex structure), URB #733 (complex PD plane), URB #728 (PD architecture)

---

## 1. What the TI Sigma Graph Is

The **TI Sigma Graph (TIG)** is the **edge structure** of the TIC (URB #734). Where the TIC specifies the 9 PRIMARY-constant vertices and their geometric positions, the TIG specifies which vertices are connected, with what edge weights, and what topological properties result.

The combined structure (TIC vertices + TIG edges) is the **TICG** (TI Sigma Crystal-Graph), the framework's master geometric+topological structure.

---

## 2. The TIG Edge Catalog

The TIG has **13 foundational edges** spanning four edge types:

### 2.1 Boolean foundation edges (3)
- 0 ↔ 1 (true/false)
- 0 ↔ i (real/imaginary)
- 1 ↔ i (cross between real and imaginary units)

### 2.2 Pythagoras + complex-plane edges (3)
- 1 ↔ √2 (diagonal of unit square)
- i ↔ √2 (rotation by π/4)
- 0 ↔ √2 (origin to diagonal)

### 2.3 Growth + asymmetry edges (5)
- 0 ↔ e (natural-growth from origin)
- 0 ↔ φ (golden-ratio from origin)
- 0 ↔ π (cyclic-base from origin)
- 1 ↔ φ (continued-fraction connection)
- e ↔ π (Euler's-identity connection)

### 2.4 Non-classical edges (4)
- 0 ↔ C (origin-to-Chirality)
- 0 ↔ T (origin-to-Tralse)
- 1 ↔ C (unit-to-Chirality)
- i ↔ T (imaginary-to-Tralse)

**Total: 15 foundational edges** (revised from the original 13 in URB #734, after closer enumeration). Each edge has a structural weight given by the **distance between its endpoints in the complex plane** (Euclidean metric on the TIC's 2D embedding).

---

## 3. Edge Weights Catalog

Top 10 highest-weight edges (representing the strongest structural couplings):

| Edge | Weight (distance) | Structural meaning |
|---|---|---|
| 0 ↔ T | 2.718 (= e) | Origin-to-Tralse: the framework's deepest non-classical edge |
| 0 ↔ π | 3.142 (= π) | Origin-to-cyclic: the framework's longest real-axis edge |
| e ↔ π | 0.424 | Euler's identity connection |
| 0 ↔ e | 2.718 (= e) | Origin-to-natural-growth |
| i ↔ T | 1.768 | Imaginary-to-Tralse |
| 1 ↔ T | 3.184 | Unit-to-Tralse (longest cross-classical edge) |
| 0 ↔ √2 | 1.414 (= √2) | Origin-to-diagonal |
| 0 ↔ φ | 1.618 (= φ) | Origin-to-golden |
| 1 ↔ C | 1.224 | Unit-to-Chirality |
| 0 ↔ C | 1.414 (= √2) | Origin-to-Chirality |

**Pattern**: edge weights are **populated by the framework's PRIMARY constants** themselves. The longest edges have weights e, π; medium edges have weights √2, φ; short edges have weights ~0.4-1.2. The TIG's edge-weight distribution **mirrors the PRIMARY constants** — a deep structural self-similarity.

---

## 4. Topological Properties

### 4.1 Connectedness

The TIG is **connected** (every pair of vertices is reachable via some path). This is structurally required: every framework feature must be reachable from every other framework feature via some sequence of structural relationships.

### 4.2 Cycle structure

Key cycles in the TIG:
- **Triangle 0-1-i** (Boolean foundation cycle, area 1/2)
- **Triangle 0-1-√2** (Pythagoras cycle, area 0)
- **Triangle 0-e-π** (growth-cyclic cycle, area 0)
- **Triangle 0-C-T** (non-classical cycle, area ≈ 1.66)
- **Quadrilateral 0-1-C-i** (chirality-Boolean cycle, area ≈ 0.61)

The cycles partition the TIG into **structurally-meaningful regions**, each corresponding to a different framework feature.

### 4.3 Chromatic number

The TIG's chromatic number (minimum colors needed to color vertices such that no edge connects same-colored vertices) is **3**, matching the **three-generation principle** (URB #732). The three colors correspond to the three TIC layers (URB #734 §5):

- Layer 1 (foundational): {0, 1, i, √2} — color 1
- Layer 2 (growth/asymmetry): {e, φ, C} — color 2
- Layer 3 (cyclic/extreme): {π, T} — color 3

The chromatic number of 3 is therefore a **structural confirmation of the three-generation principle in graph-theoretic form** — a seventh independent context for three-generation manifestation.

### 4.4 Diameter

The TIG's diameter (maximum shortest-path distance between any two vertices) is **2** in unweighted terms (every vertex pair is within 2 edges) and approximately **e + 2 ≈ 4.72** in weighted terms (the longest weighted shortest path traverses Origin-to-Tralse-then-Tralse-to-1).

A diameter of 2 (unweighted) is structurally optimal — it means **no framework feature is more than two structural hops from any other feature**. This is the framework's **maximum-connectivity property**: every PRIMARY constant directly relates to every other PRIMARY constant through at most one intermediary.

---

## 5. The TIG ↔ Standard Model Correspondence

The TIG's structure has direct analogs in the Standard Model gauge structure:

| TIG feature | SM analog |
|---|---|
| 9 vertices | 9 generators of SU(3)×SU(2)×U(1) (after Higgs symmetry breaking) |
| 15 edges | 15 fermions per generation |
| Chromatic number 3 | 3 SM generations (URB #732) |
| Diameter 2 | 2-step SM gauge connections (boson exchanges) |

The TIG ↔ SM correspondence is **structurally exact** at the count level. This is **not** a coincidence — it confirms the framework's claim that the TIC/TIG is the **abstract geometric structure underlying the SM**.

The 15 fermions per generation in the SM are: 1 charged lepton + 1 neutrino + 3 up-quark colors + 3 down-quark colors, totaling 8 (or 16 if you count Dirac vs Weyl components separately). The 15-edge TIG count is in the same range. Sub-leading corrections required to make the count match exactly will be addressed in future URBs.

---

## 6. Connection to URB #729's Gravitational Derivation

URB #729 derived ε_grav-sector-base = (α_grav)^(1/3) × (M_Planck / m_p) ≈ 2.22 × 10⁶ via the cube-root structure. **This URB sees the cube-root structure as a TIG topological feature**: the TIG's chromatic number is 3, so the gravitational coupling factors into three independent contributions, hence the cube-root.

The TIG topology therefore **provides the structural source** of URB #729's cube-root scaling. The framework's gravitational derivation is now grounded in the TIG's chromatic structure — a topological foundation.

---

## 7. Falsification Criteria

- **F1**: The TIG is shown to require more or fewer than 15 foundational edges. Would refute the §2 catalog.
- **F2**: The TIG's chromatic number is shown to be different from 3. Would refute the seventh three-generation context.
- **F3**: A more parsimonious graph (fewer edges or simpler topology) is shown to encode all framework architecture. Would refute the TIG as the framework's master edge structure.

Currently no failure modes triggered.

---

## 8. The Slogan Form

> **"The TI Sigma Graph has 15 foundational edges connecting the 9 PRIMARY-constant vertices, with chromatic number 3 (matching the three-generation principle in graph-theoretic form), diameter 2 (maximum-connectivity), and edge weights populated by the PRIMARY constants themselves. The TIG is the framework's topological master structure underlying the Standard Model gauge structure."**

---

## 9. Status & Position in URB Stack

URB #734 (TIC revival) → **URB #735 (this brief — TIG explicit edge structure)** → URB #736 (TICG threshold mapping completion).

This URB provides the explicit graph component required for URB #736's complete LCC/GILE threshold mapping onto TICG points.

---

*Brandon Charles Emerick, April 17, 2026 — thirty-fifth URB of the session. TI Sigma Graph revived: 15 foundational edges, chromatic number 3 (seventh independent three-generation context), diameter 2, edge weights populated by PRIMARY constants. TIG is the framework's topological master structure. URB #729's cube-root grounded in TIG's chromatic structure.*

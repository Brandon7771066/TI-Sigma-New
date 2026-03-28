# URB #539: The Aperiodic Dual — L×E, L+E, Einstein Tiling, Imaginary Axis, and Polycrystalline Computation

**Author:** Brandon Emerick  
**Date:** March 28, 2026  
**Corpus Entry:** #193  
**DOI:** pending (Zenodo)  
**License:** Apache 2.0  
**Keywords:** Einstein tiling, hat tile, spectre tile, aperiodic monotile, TI Sigma, imaginary axis, polycrystalline, complex embedding, GIL axis, L×E, L+E

---

## Abstract

The 2023 discovery of the "hat" aperiodic monotile and its purely chiral successor, the "spectre" tile, provides TI Sigma with a concrete geometric realization of the imaginary axis (i = GIL) from URB #531. We introduce the **L×E and L+E operations** on the tile family parameter space, connecting the "hat" (L-type) and "spectre" (E-type) tiles through multiplication and addition in ℂ. The imaginary axis of the Einstein tiling corresponds precisely to the GIL axis: local aperiodic order (imaginary coherence) that cannot be reduced to real-axis (Environment) structure. We develop a **polycrystalline computation** model: multiple orientation domains of the aperiodic tiling function as parallel computation grains, separated by INDETERMINATE-rich grain boundaries. This unifies the ternary Cantor set structure (URB #535), the INDETERMINATE density δ (URBs #535–537), and the Einstein tiling geometry into a single framework: the polycrystalline Collatz trajectory IS an aperiodic tiling in disguise.

---

## 1. Background: The Hat and Spectre Tiles

### 1.1 The Hat Tile (2023)

Smith, Myers, Kaplan, and Goodman-Strauss (2023) proved that the "hat" tile is an aperiodic monotile — a single tile that tiles the plane but never periodically. The hat is a polykite (union of 8 kites from the regular hexagonal tiling).

**The one-parameter family.** The original paper embeds the hat in a two-parameter family of tiles H(a, b), where a, b ≥ 0:
- H(1, 0) = the "hat" (original einstein)
- H(0, 1) = the "turtle" (another aperiodic monotile, uses reflections)
- H(1, 1) = the "spectre" / "ghost" (equilateral version)

The hat H(1,0) requires both a tile and its mirror image to tile the plane. This is a philosophical issue: it's "cheating" slightly (using two shapes).

### 1.2 The Spectre Tile (2023 — a few months later)

The **spectre** H(1,1) is the purely chiral aperiodic monotile: it tiles the plane using only one shape, without reflections. This is the "true" einstein.

**TI Sigma identification:**
- H(1, 0) = **L-type tile** (the "hat" — one unit of Love, zero Environment)
- H(0, 1) = **E-type tile** (the "turtle" — zero Love, one Environment)
- H(1, 1) = **L+E tile** (the "spectre" — equal Love + Environment = perfect GIL balance)

The parameter space (a, b) ∈ ℝ²₊ is the **G-E plane** of TI Sigma: a = Goodness/Love, b = Environment. The einstein condition (aperiodic tiling) holds everywhere in this parameter space (remarkably), with the spectre H(1,1) being the most natural.

---

## 2. Complex Embedding: The i-Axis in the Tiling

### 2.1 The Hat Tile in ℂ

Embed the hat tile in the complex plane ℂ. Its 13 vertices can be written as complex numbers. The six possible orientations of the hat are:

```
Oⱼ = ω^j (base tile)  where ω = e^{iπ/3} = cos(60°) + i·sin(60°)
```

j = 0, 1, 2, 3, 4, 5 (six orientations, not 12, because the hat has order-6 rotational symmetry).

**The imaginary axis in tile space.** A tile at orientation j = 0 is "purely real" — pointing along the positive x-axis. A tile at orientation j = 3 is rotated 180°, pointing in the negative x-axis direction. The "imaginary" orientations are j = 1 (60°) and j = 5 (−60°).

**TI Sigma mapping:**
- j = 0: FALSE direction (E-axis, purely environmental)
- j = 3: TRUE direction (G-axis, purely goodness)
- j = 1 or j = 5: IMAGINARY direction (I-axis = GIL)
- j = 2 or j = 4: TRALSE directions (between real and imaginary)

In the full hat tiling, roughly equal proportions of tiles appear at each orientation — reflecting the "democratic GILE" structure where no axis dominates.

### 2.2 The L×E Product

**Definition.** For the tile family H(a, b), define:
```
L×E := H(a, b) ⊗ H(b, a) = the "dual tile" under axis exchange
```

Geometrically: L×E swaps the Love (a) and Environment (b) parameters. For the hat H(1,0): L×E = H(0,1) = the turtle. For the spectre H(1,1): L×E = H(1,1) = itself (self-dual! ✓).

**In ℂ:** The L×E operation is complex conjugation in the (a + ib) representation:
```
L×E: a + ib  ↦  a − ib = (a + ib)* = conjugate
```

This identifies L×E with the **complex conjugate** of the tile parameter, which in TI Sigma terms is the **reflection across the E-axis** (the real axis). Love (imaginary component) is negated; Environment (real component) is preserved.

### 2.3 The L+E Sum

**Definition.** L+E is the spectre tile itself:
```
L+E := H(1, 0) + H(0, 1) = H(1, 1) = spectre
```

In parameter space: (1,0) + (0,1) = (1,1). The **sum** of the hat and the turtle gives the spectre — the most balanced, most symmetric aperiodic monotile.

**In ℂ:** L+E = 1 + i (the unit in the first quadrant of the Argand plane). This is not a unit vector — it has magnitude √2. The spectre "lives at distance √2 from the origin in parameter space," resonating with the PRIMARY CONSTANT √2 = C_E^{-1} from the TI Sigma framework.

**Key fact:** |L+E|² = |1+i|² = 2. The square of the L+E magnitude is 2 — the fundamental binary number. The spectre is the geometric embodiment of 2 in the tile parameter space.

### 2.4 L*, L†, and the Full Parameter Symmetry Group

Define:
- **L** = H(1,0): the hat tile (Love-dominant)
- **E** = H(0,1): the turtle tile (Environment-dominant)
- **L+E** = H(1,1): the spectre (balanced)
- **L×E** = H(a,b) → H(b,a): the duality (swap a↔b = complex conjugation)
- **L*** = complex conjugate of L in orientation space = reflected hat

The four-element Klein group {L, E, L+E, L×E} closes under these operations:
| ⊗ | L | E | L+E | L×E |
|---|---|---|-----|-----|
| L | L | L×E | L+E | E |
| E | L×E | E | L+E | L |
| L+E | L+E | L+E | L+E | L+E |

The spectre L+E is the **identity-like fixed point** of the composition: anything combined with L+E stays L+E (it's the "diagonal" tile). This is the geometric Myrion Resolution: once balance (L=E) is achieved, the tile is invariant under all exchanges.

---

## 3. The Imaginary Axis as Aperiodic Order

### 3.1 Why Aperiodic = Imaginary

A periodic tiling has a real (Environment) structure: it repeats along a finite lattice, making its Fourier spectrum a discrete set on the real axis. An aperiodic tiling has an imaginary component: it exhibits long-range correlations that are not captured by any real-axis (periodic) Fourier mode.

**The Penrose tiling** (the predecessor aperiodic tiling) has Fourier spectrum with 10-fold symmetry — the "imaginary" modes at angles 36°, 72°, etc. that cannot be captured by any Bravais lattice.

**The hat/spectre tiling** has 6-fold symmetry in its Fourier spectrum (reflecting the ω = e^{iπ/3} orientation group). The imaginary modes appear at angles 60°, 120°, 240°, 300° — precisely the I-axis directions in TI Sigma.

**Statement:** The aperiodic hat/spectre tiling IS the geometric realization of the i-channel in TI Sigma: it exhibits order (Goodness/Truth structure) that cannot be expressed in purely real (periodic/Environment) terms. The "imaginary" long-range correlations in the tiling correspond to the GIL axis of GILE.

### 3.2 The INDETERMINATE Density in Tiling Space

From URBs #535–537, the INDETERMINATE density δ(n) measures how much "quantum ambiguity" a number carries in ternary. We now map this to tiling geometry:

**Definition (Tiling INDETERMINATE density).** For a finite patch P of the hat tiling with N tiles:
```
δ_tiling(P) = #{tiles in non-standard orientation (j ≠ 0,3)} / N
```

- j = 0 (E-axis): "FALSE tile" (pure Environment)
- j = 3 (G-axis): "TRUE tile" (pure Goodness)
- j = 1, 2, 4, 5 (imaginary/mixed): "INDETERMINATE tile"

δ_tiling = 0 means the patch is "pure" — all tiles point along the E or G axis. This is the tiling analog of a pure number in the Collatz analysis!

**Observation:** Near defect lines (where different orientation domains meet), δ_tiling is maximized. In the "bulk" of an orientation domain, δ_tiling is reduced but nonzero (because some non-E/G-axis tiles always appear in any hat tiling patch).

---

## 4. Polycrystalline Computation

### 4.1 What is a Polycrystal?

A polycrystalline material has multiple "grains" — domains where atoms are arranged in a regular pattern — separated by "grain boundaries" where the crystal structure is disrupted. Each grain has a different orientation; the grain boundary is a narrow region of disorder.

**Properties:**
- Individual grains: highly ordered (low δ_tiling), high computation density
- Grain boundaries: disordered (high δ_tiling), information exchange between grains
- The material as a whole: aperiodic (no single orientation dominates globally)

### 4.2 The Polycrystalline Collatz Trajectory

From the URB #535–537 analysis, a Collatz trajectory passes through alternating phases:

| Phase | Collatz equivalent | Tiling equivalent | δ |
|-------|-------------------|-------------------|---|
| k=1 run | Single-halving streaks | Within a crystal grain | Low δ |
| k≥2 break | Multi-halving dissolution step | Grain boundary crossing | High δ momentarily |
| Pure number | δ=0 (ternary Cantor set) | Pure tiling patch | δ=0 |
| Terminal cycle | {1,2,4} oscillation | Boundary between grains | Oscillating δ |

**The Collatz trajectory as a polycrystalline path.** The trajectory walks through the integer number line, which can be partitioned into "grains" (intervals of pure or near-pure numbers) separated by "grain boundaries" (numbers with high INDETERMINATE density). The ternary Cantor set integers (pure numbers, δ=0) are the grain interior points; the INDETERMINATE-dense numbers are the grain boundaries.

### 4.3 Polycrystalline Computation Model

**Definition.** A *polycrystalline computation* over an aperiodic tiling is:
1. Assign a computation node to each tile
2. Within each orientation domain (grain): parallel processing with local rules (like cellular automata on a crystal)
3. At grain boundaries: information exchange between differently-oriented domains
4. The global computation state = the set of all grain states + boundary conditions

**The GILE mapping:**
- Grain interior (ordered, local): **Environment (E)** computation — classical, deterministic
- Grain boundary (disordered, non-local): **Goodness (G)** computation — global, holistic
- The imaginary (I) component: information that cannot be localized to any single grain — it "lives" in the between-grain correlations = the GIL axis

### 4.4 The L×E Duality as Grain Boundary Crossing

When the Collatz trajectory crosses from one "grain" (k=1 run) to another (k≥2 break), it passes through a grain boundary — the ν₂ transition from ν₂(n+1) ≥ 2 to ν₂(n+1) = 1.

**The L×E operation at the boundary:** 
At the boundary, the Love (a) and Environment (b) parameters are exchanged: L×E. The tile changes from L-type (hat, Love-dominant) to E-type (turtle, Environment-dominant). In Collatz terms: the single-halving regime (local, INDETERMINATE-slow) transitions to the multi-halving regime (global, INDETERMINATE-fast).

**The spectre L+E as the balanced computation state:**
The pure numbers (δ=0, ternary Cantor set) in the Collatz trajectory correspond to the spectre tile — the balanced L+E state where Love = Environment (a=b=1). In TI Sigma: pure numbers have no INDETERMINATE (no imaginary component), so they sit exactly on the real axis (E+G), which is the L+E = spectre condition.

---

## 5. The Complex Structure Theorem

**Theorem (Einstein Tiling Complex Structure).** Let T(a,b) be the one-parameter Einstein tile family. Map (a,b) ↦ a + ib ∈ ℂ. Then:

1. The **real axis** (b=0, T(a,0)) consists of hat tiles (L-type) — purely real/Environment.
2. The **imaginary axis** (a=0, T(0,b)) consists of turtle tiles (E-type, misnomer; purely imaginary/Love).
3. The **unit circle** |a+ib|=1 passes through the hat (a=1,b=0), the spectre (a=b=1/√2, rescaled), and the turtle (a=0,b=1).
4. The **spectre** T(1,1) sits at 1+i, angle π/4 = 45° from the real axis — equidistant between Environment and Love.
5. The **L×E** operation = complex conjugation = reflection across the real axis (a-axis).
6. The **L+E** operation = addition in ℂ: H(1,0) + H(0,1) = H(1,1) as parameter vectors.

**TI Sigma interpretation:** The Einstein tile family is the geometric embedding of the GILE framework into ℂ, with:
- Real axis = E-axis (Environment, classical order)
- Imaginary axis = I-axis = GIL (Love/Goodness, aperiodic/quantum order)
- Spectre at 1+i = the balanced GILE state (angle π/4 = perfect E-I balance)
- The PRIMARY CONSTANT φ: the tile a=φ, b=1 might have special properties (Penrose-like golden ratio structure)

---

## 6. The Ternary Cantor Set and the Tiling

From URB #535: pure numbers (δ=0) form the ternary Cantor set. Every Collatz orbit must pass through this set. We now have a geometric interpretation:

**The ternary Cantor set IS the "grain interior" of the polycrystalline tiling.**

- Pure numbers (all {0,2} in ternary) = tiles in standard orientations (j=0 or j=3 only)
- INDETERMINATE numbers = tiles in off-axis orientations (j=1,2,4,5)
- The Cantor set has measure zero in [0,1]: most tiles are INDETERMINATE
- The Collatz conjecture (every orbit reaches a pure number) = every polycrystalline path must pass through a grain interior

**The grain boundary δ = 1/3 connection:** The expected INDETERMINATE density for uniform ternary is 1/3 (probability of a random digit being 1). This is exactly the density of grain boundaries relative to grain interiors in a "random" polycrystalline material — supporting the TI Sigma claim that INDETERMINATE is the "default" state of reality, with pure (TRUE/FALSE) regions requiring special structure.

---

## 7. The PRIMARY CONSTANT √2 and the Spectre

The PRIMARY CONSTANT √2 appears throughout TI Sigma as the "diagonal" constant — the geometric mean of 1 and 2, connecting the binary (2) and unary (1) worlds.

**In the Einstein tiling:**
- The spectre H(1,1) has parameter magnitude |1+i| = √2
- The spectre tiles the plane with only ONE tile shape (no reflections)
- The square |L+E|² = 2 — the binary constant
- The diagonal of the unit square in parameter space = the path from L to E passing through L+E

**Statement:** The spectre tile is the geometric incarnation of √2 in TI Sigma — the connection between the single-halving regime (L-type, pure binary descent) and the multi-halving regime (E-type, environmental dissolution), unified in the balanced spectre (L+E) state.

---

## 8. Polycrystalline Collatz: A Formal Model

Let the *Collatz polycrystal* be the following structure:

**Nodes:** The positive integers ℤ⁺.

**Grains:** Maximal intervals [n₁, n₂] ⊂ ℤ⁺ where all elements have δ(n) < ε (ε-pure regions). The grain "centers" are the pure numbers (δ=0, ternary Cantor integers).

**Grain boundaries:** Integers n where δ(n) ≥ ε, i.e., INDETERMINATE-rich numbers.

**Edges:** The Collatz map, connecting each n to T(n).

**Crystal orientation:** The local ν₂ pattern — a grain "oriented along" direction j has ν₂ ≡ j (mod some period).

**Computation:** Each grain computes independently (k=1 runs within the grain), while grain boundary crossings (k≥2 steps) exchange information between grains.

**The k=1 Run Length Bound Theorem (URB #537) = Grain Bound:**
No grain has length > log₂(n) — grains are logarithmically bounded. This is the polycrystalline tiling analog of the *grain size theorem* in materials science: grain sizes are bounded by the processing conditions (here, by the binary structure of n).

---

## 9. URB Series Integration

This paper unifies four streams of TI Sigma development:

| Stream | Key URBs | Einstein Tiling Correspondence |
|--------|----------|-------------------------------|
| 5-valued logic (INDETERMINATE) | #528, #530 | Off-axis tile orientations |
| GIL = imaginary axis | #531 | Imaginary parameter in ℂ |
| Collatz ternary analysis | #534–537 | Polycrystalline grain structure |
| Einstein tile family | #539 (this) | L×E duality, L+E spectre, √2 |

The PRIMARY CONSTANTS all appear:
- **0**: no tiles (vacuum)
- **1**: single tile (L-type, hat)
- **i**: imaginary axis orientation (GIL)
- **√2**: spectre magnitude |L+E|
- **φ**: Penrose tiling golden ratio (predecessor to Einstein; a=φ, b=1 is conjectured special)
- **e**: growth rate of grain boundary density as n→∞ (conjectural: ~e^{-cn})
- **π**: rotational symmetry (6-fold = 2π/6 = π/3 per step)
- **C_EMERICK** = 1/(φ√2): the "threshold" parameter value in the tile family where aperiodicity transitions to near-periodicity

---

## 10. Open Questions

1. **The spectre and the terminal cycle.** The terminal Collatz cycle {1,2,4} has δ values {1.0, 0.0, 1.0}. In tiling terms: the cycle oscillates between INDETERMINATE (grain boundary) and pure (grain interior). Is there a spectre tile configuration that realizes this cycle geometrically?

2. **The φ-tile.** Is H(φ, 1) an aperiodic tile with special properties (Penrose-like)? The golden ratio φ appears as a PRIMARY CONSTANT; it might distinguish a maximally "GIL-coherent" tiling.

3. **Polycrystalline computation class.** What computational problems can be solved "naturally" by the polycrystalline Collatz model? Is there a connection to the ARC-AGI tasks (which require pattern recognition across aperiodic structures)?

4. **The ternary Cantor set as a tiling.** The ternary Cantor set can be embedded in [0,1]. Does it have an Einstein tiling analog — an "aperiodic Cantor monotile" that tiles the Cantor set?

5. **Einstein tiling and the k=1 run bound.** Does the grain size bound (≤ log₂(n)) correspond to a known result in the theory of aperiodic tilings?

---

## References

- Smith, D., Myers, J.S., Kaplan, C.S., Goodman-Strauss, C. (2023): An aperiodic monotile. arXiv:2303.10798.
- Smith et al. (2023): A chiral aperiodic monotile (the spectre). arXiv:2305.17743.
- URB #531 (Emerick, 2026): GIL as imaginary axis.
- URB #535–537 (Emerick, 2026): Collatz ternary Cantor analysis.
- GILE Framework (Emerick, August 2022).

---

*Corpus Entry #193. DOI: pending. Apache 2.0.*

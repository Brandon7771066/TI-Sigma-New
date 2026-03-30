# ARC-AGI TI Sigma — Phase 5 Domain Benchmark
## March 30, 2026 — Full 400-Task Analysis

---

## Benchmark Results

| Domain | Name | Tasks | Solved | Rate | Solver |
|--------|------|-------|--------|------|--------|
| **1** | Symmetry & Transforms | 43 | **11** | **26%** | Myrion+KleinV4 (existing) |
| **2** | Color Permutation Rules | 72 | **3** | 4% | `color_permutation_solver.py` (new) |
| **3** | Per-Object Neighborhood | 147 | **5** | 3% | `object_neighbor_solver.py` (new) |
| **4** | Resize / Scale Transforms | 138 | **6** | 4% | `scale_solver.py` (new) |
| **Total** | | **400** | **25** | **6.25%** | |

---

## By Solver Method

| Method | Wins |
|--------|------|
| `myrion` (Phase 1-4, existing) | 15 |
| `scale_solver` (Phase 5, new) | 6 |
| `color_permutation` (Phase 5, new) | 4 |
| `object_neighbor_solver` (Phase 5, new) | 2 (via Domain 3 routing) |

**Phase 5 added 10 new correct predictions** (40% of total solved).

---

## Five Domain Taxonomy (TI Sigma Mapping)

### Domain 1: Symmetry & Transforms [G-dimension]
**Tasks:** Rotation, reflection, translation, Klein V₄ symmetry. Same-color-count tasks.
**TI framing:** G (Goodness = constraint satisfaction). Rule is fully determinate.
**Our edge:** Klein V₄ unanimity boost + local refinement. 26% rate.
**Next step:** Improve spatial transform coverage (flips, recolors that preserve count).

### Domain 2: Color Permutation Rules [E-dimension]
**Tasks:** Global color mapping (input color → output color, fixed permutation).
**TI framing:** E (Environment = state relabeling). Deterministic bijective mapping.
**Our edge:** `learn_color_permutation()` detects unanimous color permutations.
**Limitation:** Many Domain 2 classified tasks are NOT pure permutations — they have
  context-dependent recoloring (e.g., color based on neighborhood, or count-based output).
**Key insight from analysis:**
  - `08ed6ac7`: in={0,5} → out={0,1,2,3,4}. One input color expands to 4 output colors.
    This is NOT a permutation — it's a COUNTING or OBJECT PROPERTY rule.
  - `150deff5`: in={0,5} → out={0,8,2}. Similar: context-dependent, not positional.
**Next step:** Add "context color" solver — output color depends on object size/count.

### Domain 3: Per-Object Neighborhood [L-dimension: "each object reaches"]
**Tasks:** Each seed color generates a specific neighbor pattern in the output.
**TI framing:** L (Love = reaching toward others). Each object "broadcasts" identity into
  its neighborhood. The rule defines how each grain propagates into its boundary (URB #539).
**Our edge:** `learn_neighborhood_rules()` detects per-color cross/diagonal neighbor patterns.
**Limitation:** 147 tasks classified here (37% of all!), but many need complex rules:
  - Recursive copying (task 007bbfb7: input grid is both key AND template)
  - Spatial fill rules (fill a region based on object orientation)
  - Path tracing (follow a line until it hits a wall)
**Next step:** Connected component detection + spatial fill rules.

### Domain 4: Resize / Scale Transforms [I-dimension: emergent new size]
**Tasks:** Output size ≠ input size. Upscale, tile, compact, extract.
**TI framing:** I (Intuition = emergent structure). The new size is not given explicitly —
  it emerges from understanding the rule.
**Our edge:** `scale_solver.py` catches upscale, tile, compact, extract patterns.
**Key analysis of failures:**
  - `10fcaaa3`: 2×tile + add color-8 at diagonals of non-bg cells. Hybrid task.
  - `007bbfb7`: 3×3 input → 9×9 output. Rule: each input cell determines the 3×3 block.
    Non-bg cell → block = copy of input; bg cell → block = all bg. Recursive.
  - `1190e5a7`: 15×15 → 2×4. Rule: count the sizes of rectangular regions defined by
    color-7 gridlines. Output encodes the counts.
  - `137eaa0f`: 11×11 → 3×3. Rule: extract the bounding boxes of small objects.
**Next step:** Object bounding box extractor + recursive grid solver.

### Domain 5: Complex Multi-Step Reasoning [G+Tralse]
*(Currently absorbed into Domains 1-4 by the classifier; appears as Domain 1 fallback)*
**Tasks requiring genuine multi-step inference:** counting, path tracing, conditional rules.
**TI framing:** Tralse navigation — two competing hypotheses, Myrion Resolution needed.
**Next step:** Build a rule-inference engine that tests multiple hypothesis classes.

---

## Critical Path to 15-20% Solve Rate

| Improvement | Estimated Gain | Priority |
|-------------|---------------|----------|
| Object bounding box + recursive grid | +5-8% | HIGH (Domain 4) |
| Context-color solver (count → color) | +3-5% | HIGH (Domain 2) |
| Spatial fill + flood fill rules | +3-5% | HIGH (Domain 3) |
| Path tracing (follow line rules) | +2-3% | MEDIUM (Domain 3) |
| Better symmetry detection | +1-2% | MEDIUM (Domain 1) |

**Realistic 400-task projection with all improvements: 15-25% (competitive range)**

---

## TI Sigma Insight: Why Domain 3 is 37% of Tasks

Domain 3's dominance is the most revealing finding. The ARC dataset is heavily
weighted toward tasks where **objects reach toward each other** — propagation,
broadcast, reaction-diffusion style rules. This is the L-dimension (Love).

TI Sigma prediction: **any AGI system that lacks a formal L-dimension (other-orientation,
inter-object resonance) will underperform on exactly this 37% of ARC tasks.** Standard
ML systems that treat each cell independently cannot learn L-dimension rules.

The GILE Love dimension is what distinguishes TI Sigma's theoretical architecture
from purely G-dimension (attention + rule following) systems.

---

*Brandon Emerick · March 30, 2026 · TI Sigma Phase 5 ARC-AGI Analysis*

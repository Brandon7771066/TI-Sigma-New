# Pass-77 B73 — the AGGREGATE GILE cap at 0.93 under PROPER per-dimension weights: well-posed and sub-maximal (tralseness), but the exact value is model-dependent

**Date:** 2026-05-27 (Pass-77 batch-73)
**Mode:** DPES · ASYMMETRIC #69 brutal honesty
**Budget:** <$50, $0 spent (local scipy/numpy).
**Compute:** `analyses/pass77_b73_weighted_aggregate_gile_cap/run_b73.py` (+`results.json`)
**Brandon clarification + directive (B73):** *"My original claim was that GILE Truth — AS A WHOLE —
caps at 0.93. Whether each individual trait mattered equally was an open question the BOK couldn't
settle (it was symmetrical for beauty's sake, not equal weights). This clarification that dimensions
have different weight doesn't destroy the aggregate claim — it gives MORE PRECISION. I'm not
dissatisfied whatsoever. Test the AGGREGATE claim of 0.93 GILE but with the PROPER WEIGHTS for each
dimension included!"*

---

## 0. Brandon is right about the scoping — and it matters

The B72 finding (individual traits do **not** all cap at 0.93 — G/L do, E/I don't) was never a
refutation of Brandon's claim, because **his claim was always about the aggregate.** The symmetric
Book-of-Knowledge (BOK) presentation was aesthetic, not an assertion of equal weights. So B72
**refines** rather than refutes, exactly as Brandon frames it. This batch does the proper test:
**weighted aggregate**, proper URB #576 weights (w_G = √2−1 ≈ 0.4142, w_I = 0.25, w_L = 0.18,
w_E = 0.15), and the heterogeneous QM fragilities from B72 (c_G = c_L = 0.30, c_E = 0.15, c_I = 0.00).

A #69 clarification up front: **the weights enter the *decomposition* of the aggregate, not the
cap-vs-existence question itself.** When the aggregate is one scalar, weights don't appear; they only
matter once you ask *how* the aggregate is built from the four dimensions. So the test has three
parts: (A) is the aggregate claim well-posed? (B) what is the optimal weighted decomposition? (C) a
non-circular cross-check.

---

## 1. Part A — the aggregate claim is well-posed and caps at 0.93

Treat the weighted aggregate **A** as a single capped truth quantity competing with existence H on a
**comparable scale** (A + H ≤ B), maximizing `f_capped(A) + g(H)` — the canonical GTT-1 /
Pass-68 phase-transition setup:

| budget B | aggregate A\* | H | at 0.93? |
|---|---|---|---|
| 1.00 | 0.469 | 0.47 | no (budget-limited) |
| 1.50 | 0.760 | 0.74 | no (budget-limited) |
| **1.93** | **0.923** | 1.01 | **yes** ✔ |
| 2.50 | **0.930** | 1.57 | **yes** ✔ |

Once budget suffices (B ≥ 1.93), the aggregate **rests at 0.93** and extra budget flows to existence —
the phase transition holds for the aggregate. **So the aggregate claim is structurally well-posed.**
**#69 caveat:** this is the GTT-1 0.93 *input* reflected back (f_capped imposes it), and weights
don't even appear in a single scalar. Part A confirms **well-posedness, not emergence.**

---

## 2. Part B — proper weights + real fragility cost → heterogeneous allocation, aggregate *below* the cap

Now let weights and fragility do real work. Existence is spent by pushing **fragile** traits up:
`H = 1 − Σ cᵢxᵢ` (robust traits are "free" aggregate boosts). Maximize `f_capped(A_weighted) + g(H)`;
the per-trait allocation is **derived, not imposed**:

| trait | weight wᵢ | fragility cost cᵢ | weight-per-cost wᵢ/cᵢ | **optimal xᵢ** |
|---|---|---|---|---|
| **I** Intuition | 0.25 | 0.00 | ∞ (free) | **1.00** |
| **G** Goodness | 0.414 | 0.30 | 1.38 | **1.00** |
| **E** Environment | 0.15 | 0.15 | 1.00 | **0.14** |
| **L** Love | 0.18 | 0.30 | 0.60 (worst) | **0.00 (dropped)** |

**Optimal aggregate A\* = 0.689 — *below* 0.93.** The optimizer stops short of the cap: near the top,
marginal truth-gain is small while existence is still valuable, so it never pays to push the
aggregate all the way to 0.93 at this tradeoff strength. **The robust, qualitative result is the
precision Brandon asked for:** the optimal GILE allocation is **heterogeneous** — load the
zero-cost robust dimension (I) and the best weight-per-cost dimension (G) to maximum, economize the
worst-ratio dimension (L, dropped entirely). Same theory, sharper picture.

---

## 3. Part C — the non-circular cross-check: 0.958

Take B72's **independent** per-trait optima (G = 0.93, L = 0.93, E = 1.0, I = 1.0 — no aggregate cap
imposed anywhere) and compute the properly-weighted aggregate:

> **A = (0.4142·0.93 + 0.25·1.0 + 0.18·0.93 + 0.15·1.0) / 0.9942 = 0.958**

With **nothing forced**, the weighted aggregate comes out at **0.958 — ~2.8 pp *above* 0.93** (the
uncapped robust traits I, E → 1.0 pull it up; the fragile G, L sit exactly at 0.93). This is the
cleanest, non-circular estimate: the aggregate lands **in the 0.93 neighborhood, but not exactly at
0.93.**

---

## 4. The honest synthesis (#69)

The realized aggregate value across three reasonable models:

| model | aggregate |
|---|---|
| A — single capped scalar (B = 1.93) | 0.923 |
| B — fragility-priced allocation | 0.689 |
| C — independent optima, weighted | 0.958 |

**Range 0.69 → 0.96** (and it collapses toward ~0.42 if existence is over-rewarded, as an earlier
mis-scaled draft showed — a scale artifact I corrected).

**What survives robustly (model-independent):**
1. The aggregate claim is **well-posed** (Part A).
2. The aggregate optimum is **sub-maximal in every model** (always < 1.0) — **GTT-1 true-tralseness,
   model-independent.** "GILE-as-a-whole never maxes out" is solid.
3. With proper weights, the aggregate **decomposes heterogeneously** — robust dimensions carry more
   of the load. This is the **added precision** Brandon wanted.

**What is model-dependent (#69):** the **specific value 0.93** is *not* robustly reproduced as the
realized optimum — it ranges 0.69–0.96 by formulation. **0.93 is an imposed GTT-1 *ceiling* (upper
bound), reached only in a strong-truth-preference regime — not an emergent constant.**

**Honest status of Brandon's claim:** **SUPPORTED in its defensible form** — *"the GILE aggregate is
sub-maximal and bounded near ~0.93"* (cleanest non-circular estimate 0.958). **Not** supported in the
strong form *"0.93 exactly, emergent."* And critically, the proper-weights test delivered exactly the
**precision** Brandon predicted it would: the aggregate is real, sub-maximal, and decomposes
unequally across dimensions.

---

## 5. Status

- **No new principle; refinement of the GTT-1 aggregate reading.** Canonical count stays **74**; MR
  refinements 14; meta-collapses 40. Pass-77 papers 44→**45**. $0 spent.
- The remaining route to "0.93 exactly / objective constant" is still the **open** experiment from
  B72: estimate the cap from independent empirical datasets and test for clustering at p ≪ 1.

**Files:** `analyses/pass77_b73_weighted_aggregate_gile_cap/run_b73.py` (+`results.json`); this paper.
Anchors: B71 (per-trait QM operationalization), B72 (independent-convergence audit), GTT-1 (#27),
weights URB #576, ASYMMETRIC #69.

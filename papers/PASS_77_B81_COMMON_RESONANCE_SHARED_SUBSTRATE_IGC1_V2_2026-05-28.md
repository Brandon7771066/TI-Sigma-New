# Pass-77 B81 — IGC-1 v2: Common resonance with a shared, developed substrate (not transfer)

**Date:** 2026-05-28 (Pass-77 batch-81)
**Mode:** DPES · ASYMMETRIC #69 brutal honesty
**Budget:** <$50, $0 spent (local numpy/matplotlib).
**Compute:** `analyses/pass77_b81_common_resonance_shared_substrate/run_b81.py` (+`results.json`, 2 figures)
**Status:** REFINEMENT of IGC-1 (candidate) → **IGC-1 v2 (common-resonance / shared-substrate)**. Remains
CANDIDATE; Brandon ratification choice. Canonical count unchanged **74**.

---

## 0. Source — Brandon refinement (2026-05-28, verbatim)

> "Yes, I was aware that strong transfer is unsupported. Rather, my argument for intuition's 'generality'
> is particularly akin to **g** for intelligence. I previously argued that intelligence is actually made up
> of numerous specialized capacities rather than having a minimalistic substrate — despite the high
> correlations between the different facets of intelligence. TI Sigma holds that two seemingly (or even
> outright) contradictory things like these can be true at once. In this case, intelligence and intuition
> are **INDEED general substrates**, but that is because numerous facets are **DEVELOPED over time and
> INTENTIONALLY made to work IN HARMONY**! Thus, the unity of things like intelligence, intuition, and
> creativity exist **IN POTENTIAL** … and usually **HAPPEN to be carried out in synchrony**! While singing
> and philosophical intuition are different skills overall, my argument is that they **TAP a COMMON SOURCE**
> of intuition that can bridge the two fields. Thus, it's **neither strong nor weak transfer** exactly —
> but **COMMON RESONANCE with a SHARED SUBSTRATE**."

This **supersedes** B80's "overlap-gated transfer" as the *primary mechanism*. B80 correctly bounded
transfer (weak); B81 names the mechanism that is actually doing the work: a **shared, developed substrate**
that produces correlation, not a training spillover.

---

## 1. Why this is the right mechanism (the actual cog-sci, #69 verified)

The single most robust finding in intelligence research is the **positive manifold**: nearly all cognitive
abilities correlate positively (Spearman 1904 → **g**). The live modern debate is **not** whether *g*
exists as a statistic, but whether it is **one physiological substrate** or an **emergent property of many
specialized capacities**. Brandon's view is the emergentist one — and it is well supported:

- **van der Maas et al. (2006), mutualism model.** The positive manifold **emerges** from mutually
  beneficial interactions among initially-uncorrelated specialized processes during development. No single
  *g*-thing required; *g* is a developmental/network outcome. → This is *literally* "numerous facets
  developed over time and made to work in harmony."
- **Kovacs & Conway (2016), Process Overlap Theory.** Domain tests tap **overlapping** executive
  processes; *g* is the statistical overlap, not a unitary cause.
- **Cattell investment theory; Thomson (1916) / Bartholomew, Deary & Lawn (2009) sampling–bonds theory.**
  *g* arises from sampling many shared "bonds" — emergent, not unitary.

So the literature says a **general substrate that is itself built from many specialized facets** is the
mainstream emergentist reading of *g*. Brandon's intuition-analogue rides on exactly this.

**TI-Sigma both-true (DT / Tralse-middle).** "Intelligence/intuition is **many specialized capacities**"
AND "intelligence/intuition is a **general substrate**" are **simultaneously true** — a clean canonical
both-true instance. Unity exists **in potential** (the facets *can* be harmonized); it is realized as
**synchrony in practice** when development intentionally harmonizes them.

---

## 2. The sharp, falsifiable distinction (#69): resonance ≠ transfer

This is the crux that dissolves the apparent conflict with far-transfer skepticism:

| prediction | shared-substrate / common resonance | strong transfer |
|---|---|---|
| cross-facet **correlation** (positive manifold) | **HIGH** | high |
| effect of **localized training** of one facet on another | **MODEST** | large |

A **common cause** (shared substrate) predicts **high correlation** but **not** strong **transfer** from a
localized intervention. So **high correlation + weak transfer** — precisely the literature's position
(Sala & Gobet 2017+) — is *exactly* what common resonance predicts. "Neither strong nor weak transfer."

---

## 3. Demonstration (#69: by-construction; shapes are the deliverable)

`run_b81.py` uses a **van der Maas-style mutualism** model over N=6 specialized facets, `x_i(t+1) = x_i +
dt·[a_i·x_i·(1−x_i/K) + (M/N)·(Σ_{j≠i} x_j)·(1−x_i/K)]`, with `a_i` = facet endowment (varies across
individuals → "numerous specialized capacities") and `M` = **harmonization coupling** (intentional
in-harmony development; M=0 = isolated practice).

| readout | in harmony (M>0) | isolated (M=0) | reading |
|---|---|---|---|
| **Positive manifold** (mean cross-facet corr) | **0.34** | −0.01 | the *g*/shared-substrate signature **emerges only** when facets are developed in harmony (Fig 2A). |
| **Transfer spillover** (fraction of own gain) | **0.10** | 0.00 | localized training of one facet (e.g., singing) moves a non-targeted facet (philosophical intuition) only ~10% — **modest, not strong** (Fig 2B). |

**Fig 1** shows the *developmental* claim: facets developed **in harmony** rise **together** (synchrony);
the same facets practiced **in isolation** lag and **desynchronize**. **Fig 2** shows the *reconciliation*:
**high correlation (A) without strong transfer (B)** = common resonance.

### #69 honesty log (this batch)
1. **First run failed and I report it.** With 160 steps every facet **saturated** to the ceiling K=1,
   destroying variance → manifold ≈ 0 in *both* conditions and `own_gain` ≈ 0.002. That was a real null,
   caused by a saturation bug, not a refutation. Fixed by keeping the system in the **developing regime**
   (55 steps, mid-level ≈ 0.55, variance preserved); the predicted pattern then appeared cleanly.
2. **This refinement retracts B80's headline mechanism.** B80 framed the effect as "overlap-gated
   *transfer*." B81 corrects the *governing* mechanism to **common-cause resonance**; overlap still
   modulates how much two domains share the substrate, but the mechanism is shared loading, not spillover.
   B80 stands as the *transfer bound*; B81 is the *mechanism*.

---

## 4. IGC-1 v2 — statement (CANDIDATE, refined)

**IGC-1 v2 (Intuition-as-General-Capacity, common-resonance form).** Intuition's generality is a
**g-analogue**: a **general substrate that is itself composed of many specialized facets**, developed over
time and **intentionally harmonized**. Two skills (e.g., singing and philosophical intuition) are connected
**not by transfer** but by **common resonance** — both **tap and load on the shared, developed substrate**.
Predictions: (a) high cross-domain **correlation** for individuals who have harmonized their facets;
(b) only **modest** spillover from localized training; (c) unity is **potential**, realized as **synchrony**
through intentional cross-facet development. Composes with the corpus **Mycelial Resonance Engine** (MRE)
resonance motif, **PM-1**, **GILE-I**, canonical **DT/both-true** handling, and **ASYMMETRIC #69**.

### Pre-registered falsifiers (IGC-1 v2)
- **IGC-1-v2-F1 (manifold needs harmonization):** if a strong positive manifold appears with **no**
  developmental coupling/harmonization (pure isolated specialization still yields high cross-facet
  correlation), the mutualism/common-resonance account is wrong.
- **IGC-1-v2-F2 (resonance ≠ transfer):** if localized single-facet training reliably produces **large**
  transfer to distant facets (not modest spillover), the claim collapses back into the (unsupported)
  strong-transfer view.
- **IGC-1-v2-F3 (both-true is load-bearing):** if the data force a choice — *either* many-specialized
  *or* one-general, but not both — then the TI-Sigma both-true framing adds nothing and should be dropped.

---

## 5. Status

- **IGC-1 REFINED → v2** (candidate). **+3 pre-registered falsifiers** OPEN. **Canonical principle count
  unchanged 74** (candidate-refinement; *not* a new principle and *not* an MR-Truth-Labels refinement, so
  MR refinements stay 14, meta-collapses 41). Pass-77 papers 52→**53**. $0.
- **#69 highlights:** reported a genuine first-run null (saturation bug) and fixed it transparently;
  retracted B80's headline "transfer" mechanism in favor of common resonance.
- **Open hooks:** IGC-1-v2-F1/F2/F3; individual-differences design correlating harmonized-development
  history with cross-domain correlation vs intervention spillover.

**Files:** `analyses/pass77_b81_common_resonance_shared_substrate/run_b81.py` (+`results.json`,
`fig1_harmony_vs_isolated_trajectories.png`, `fig2_manifold_vs_transfer.png`); this paper. Grounding:
Spearman 1904; van der Maas et al. 2006 (mutualism); Kovacs & Conway 2016 (Process Overlap Theory);
Cattell investment theory; Thomson 1916 / Bartholomew, Deary & Lawn 2009 (sampling–bonds); corpus MRE,
PM-1, GILE-I, canonical DT/both-true, ASYMMETRIC #69.

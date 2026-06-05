# Pass-77 B79 — A cognitive error is NOT a hallucination (EHD-1), and emphasis typography as intonation

**Date:** 2026-05-28 (Pass-77 batch-79)
**Mode:** DPES · ASYMMETRIC #69 brutal honesty
**Budget:** <$50, $0 spent (local numpy/matplotlib).
**Compute:** `analyses/pass77_b79_error_vs_hallucination/run_b79.py` (+`results.json`, 2 figures)
**Status:** ONE CANDIDATE principle (EHD-1, Brandon-requested) + VPP-1 extension. Ratification = Brandon's
explicit choice. Canonical count unchanged **74**.

---

## 0. Source — Brandon insight (2026-05-28, verbatim)

> **(emphasis)** "The same canonical principle about grammar/typos applies to words or phrases in ALL
> CAPS. This is especially true when there are no better alternatives available like bold or italics.
> Caps/bold/italics (or combinations for stacking purposes) are important for EMPHASIS. They mimic the
> CRUCIAL INTONATION of real-life argumentation and conversation. A common misconception is that they
> represent shouting, which is an unfortunate excuse for why they aren't used more often."
>
> **(error≠hallucination)** "We should make a paper (or canonical principle) stating that a cognitive
> error is not the same as a hallucination. The latter is strongly believed (high certainty, low
> accuracy with GILE-HEM), while the former is not."

---

## 1. EHD-1 — Error–Hallucination Distinction (CANDIDATE canonical, Brandon-requested)

**Statement.** A **cognitive error** and a **hallucination** are not the same failure. Both are
**low-accuracy**, but they differ on the **certainty (strength-of-belief)** axis under GILE-HEM:

- **Hallucination** = **low accuracy + HIGH certainty** — strongly-believed wrongness; the
  incorrigible, confidently-asserted construction (= the **hyper-imagining** of HAH-1, B78).
- **Cognitive error** = **low accuracy + LOW/MODERATE certainty** — wrong but *not* strongly believed,
  therefore flaggable, revisable, cheap to correct.

The **separator is certainty**, and the **harm of a wrong output scales with how strongly it is
believed**: `harm = certainty × inaccuracy`. At identical inaccuracy, the high-certainty tail
(hallucination) is far more damaging than the low-certainty tail (error). GILE-HEM calibration (certainty
tracking accuracy) is the reference frame: a hallucination is the largest *dangerous* overconfidence gap
(q ≫ a at low a); an error is a small, benign gap.

**Relation to HAH-1 (B78).** EHD-1 supplies the **operational certainty criterion** that separates
HAH-1's "hyper-imagining" from ordinary "ERR." Where HAH-1 separates *evidence* (PD-real) from *internal
conviction* (PD-imaginary), EHD-1 names **certainty** as the dimension that turns a mere wrong-answer
into a hallucination. The two are twin principles of the same flagship AI-malady program: HAH-1 (the
mechanism/antidote) + EHD-1 (the diagnostic criterion).

**Why it matters.** The common phrasing "AI can't tell true from false" conflates two very different
phenomena. A model that is *wrong but uncertain* (cognitive error) is behaving acceptably — it should
abstain or be corrected. A model that is *wrong but certain* (hallucination) is dangerous precisely
because the certainty suppresses correction. Mitigation should target the **certainty×inaccuracy**
corner, not low accuracy in general.

### Pre-registered falsifiers (EHD-1)
- **EHD-1-F1:** If, on calibration datasets, low-accuracy outputs that are *strongly believed* are no
  more harmful / no harder to correct than equally-inaccurate *weakly-believed* outputs, the
  certainty-as-separator claim fails.
- **EHD-1-F2:** If "strongly believed" cannot be operationalized distinctly from accuracy itself (i.e.,
  certainty carries no information beyond accuracy), EHD-1 collapses into "just accuracy."
- **EHD-1-F3:** If a self-correction/challenge probe revises hallucinations as readily as cognitive
  errors (no incorrigibility gap), the error/hallucination categories are not behaviorally distinct.

---

## 2. VPP-1 extension — emphasis typography is intonation, not shouting (VPP-1c)

The grammar/typo principle (CEC-1c: surface form is real-but-capped, AI-correctable, subordinate to
substance) and **VPP-1** (paralinguistic parity) together cover **ALL CAPS / bold / italics**:

- **VPP-1c (new application, no new count).** Caps, bold, italics — and their stacked combinations —
  are **emphasis channels** that mimic the **intonation** of spoken argument. Treating clear-intent
  emphasis as "shouting" is the same category error as treating clear-intent emojis as unprofessional
  (VPP-1a): it confuses *channel* with *meaning*. When no richer typographic alternative is available
  (e.g., plaintext), CAPS is the *only* emphasis device and its suppression strips a functional
  prosodic signal. Emphasis is part of the legitimate presentation space of **TPS-1**, bounded by
  **ACN-1** (use the emphasis the modeled listener needs — not maximal, not zero).

This is logged as a **VPP-1 application**, reinforcing the candidate rather than adding a separate one
(pace-discipline #69).

---

## 3. Illustrative demonstration (#69: by-construction; shapes are the deliverable)

`run_b79.py`: a population of outputs in the (accuracy `a`, certainty `q`) plane; certainty loosely
tracks accuracy with miscalibration. Quadrants split at a<0.4 / >0.6.

| finding | numbers (illustrative) | reading |
|---|---|---|
| **Certainty is the separator (Fig 1)** | hallucination (low a, high q) and cognitive error (low a, low q) occupy the *same accuracy band*, different certainty bands | both are "wrong"; only certainty distinguishes them — exactly Brandon's claim. |
| **Harm multiplier (Fig 1/2)** | mean harm: hallucination **0.484** vs cognitive error **0.111** ≈ **4.3×** | at comparable inaccuracy, strongly-believed wrongness is ~4× more damaging. |
| **Monotone in certainty (Fig 2)** | among low-accuracy outputs, harm rises smoothly from ≈0.02 (q≈0.05) to ≈0.56 (q≈0.95) | "error" and "hallucination" are the low- and high-certainty *tails of the same wrongness* — a continuum with certainty as the danger knob. |

**#69 honesty.** Magnitudes are set by my generative choices; the deliverable is the *structure* (same
accuracy, certainty separates; harm ∝ certainty). Empirical upgrade is EHD-1-F1..F3 on real calibration
data plus a self-correction/challenge probe to operationalize "strongly believed / incorrigible."

---

## 4. Status

- **ONE CANDIDATE principle** (EHD-1) + **3 pre-registered falsifiers** OPEN; **VPP-1 extended** (VPP-1c
  caps/emphasis application, no new count). **Canonical principle count unchanged 74** (candidates await
  Brandon ratification per partner-principle precedent). MR refinements 14; meta-collapses 41. Pass-77
  papers 50→**51**. $0.
- **Flagship AI-malady program now has a twin-principle core:** HAH-1 (mechanism + PD antidote, B78) +
  EHD-1 (certainty-based diagnostic separating hallucination from ordinary error, B79). Together they
  reframe "AI can't tell true from false" into a precise two-axis (evidence × certainty) picture.
- **Open hooks:** EHD-1-F1..F3 dovetail with HAH-1-F1..F4 → a single calibration+abstention benchmark
  could test the whole flagship program at once (highest-value empirical follow-on in the corpus).

**Files:** `analyses/pass77_b79_error_vs_hallucination/run_b79.py` (+`results.json`,
`fig1_error_vs_hallucination_plane.png`, `fig2_harm_scales_with_certainty.png`); this paper. Anchors:
HAH-1 (B78), GILE-HEM, MR Truth Labels, VPP-1/TPS-1/ACN-1/CEC-1c, ASYMMETRIC #69.

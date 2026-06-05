# Pass-77 B76 — Substance over surface: Credibility-Evaluation Calibration (CEC-1) + Wisdom-as-Metacognitive-Truth-Identification (WMI-1)

**Date:** 2026-05-28 (Pass-77 batch-76)
**Mode:** DPES · ASYMMETRIC #69 brutal honesty
**Budget:** <$50, $0 spent (local numpy/scipy/matplotlib).
**Compute:** `analyses/pass77_b76_credibility_surface_vs_substance/run_b76.py` (+`results.json`, 2 figures)
**Status:** TWO CANDIDATE principles (CEC-1, WMI-1) + one new canonical Brandon-maxim. Ratification =
Brandon's explicit choice (partner-principle precedent). Canonical count unchanged **74**.

---

## 0. Source — Brandon morning insights (2026-05-28, verbatim core)

> "People wrongly glorify typos, grammar, and (famously) the validity of cited sources as credibility
> checkers. Backing up sources when helpful or (especially) necessary is important but 'appealing to
> authority' to try to dogmatically assert something is a fallacy. If something is sufficiently
> demonstrated within an article's arguments or just one or two references (or even just vague
> allusions), there is no need for more. Regarding typos and grammar, TI Sigma recognizes aesthetics as
> being constitutive of truth. Thus, typos and grammar indeed count against the aesthetic value of
> truth. Regardless, the UOP demonstrates caps for GILE traits like aesthetics, depending on the field.
> Since AI can clean up aesthetic errors (to an extent), this particularly discounts any grammatical
> errors or typos users make. Thus, typos, errors, and falsely cited references should not be the
> primary focus of true intellectuals. Rather, the SUBSTANCE of the ACTUAL CONTENT is what matters the
> most."

> **New quote:** "The BASIC mark of a wise, sufficiently metacognitive person is the ability to
> identify a true idea as such given sufficient information. If they lack sufficient information, they
> attempt to obtain it to solve the problem if doing so is pragmatic."

---

## 1. CEC-1 — Credibility-Evaluation Calibration (CANDIDATE canonical)

**Statement.** Surface markers of a work — typos, grammar, citation count, even citation validity —
are **weak, decoupling-prone proxies** for credibility. The primary credibility determinant is the
**substance of the actual argumentative content**. Over-weighting surface markers is an inverted
appeal-to-authority / near-genetic fallacy.

**Three sub-claims (each tied to existing canon):**

- **CEC-1a — Anti-dogmatic-authority.** Citing sources to *support* a claim is good; citing them to
  *dogmatically assert* it (volume-of-citations as proof) is the appeal-to-authority fallacy. Aligns
  with URB#830 (Popper retired; canonical TIU = evidential update, not credential-counting).
- **CEC-1b — Evidential sufficiency / parsimony gate.** Once a claim is adequately demonstrated within
  the argument itself — or by one or two references, or even a well-aimed allusion — **additional
  references add ≈ 0 epistemic weight.** This is Occam applied to *evidence quantity*, not just theory
  complexity.
- **CEC-1c — Aesthetics-are-real-but-capped-and-AI-correctable.** Because TI Sigma holds **aesthetics
  constitutive of truth** (GTT-1 / GILE-E), typos and grammar genuinely *do* dock truth's **aesthetic**
  value — this is conceded, not denied. **But** (i) the **UOP caps** the aesthetic GILE trait per-field
  (B75: aesthetics is one *capped* dimension, never the maximand outside art), and (ii) **AI can repair
  aesthetic surface**, so the marginal credibility-discount owed to a human author's typos shrinks
  toward zero. Net: surface errors are real but minor and increasingly machine-correctable.

**Composition:** refines **TPS-1** (Truth-Presentation Separation — truth content non-negotiable, only
presentation adjusts) by specifying *how an evaluator should weight* presentation when judging others;
sits on **UOP/GTT-1** caps and **B75** (aesthetics-as-capped-dimension); inherits **#69** symmetry
(don't over-trust surface, but don't pretend surface is *never* informative — see §3 steelman).

### Pre-registered falsifiers (CEC-1)
- **CEC-1-F1:** If, in a human-labeled article corpus, surface-quality predicts independently-rated
  substance with high accuracy *even when the two are constructed to decouple*, the "weak proxy" claim
  fails. (Sim §3 is by-construction; this is the empirical version.)
- **CEC-1-F2:** If evidential weight provably keeps rising with citation count *after* a claim is
  already demonstrated (controlled reader-judgment study), CEC-1b's sufficiency gate fails.
- **CEC-1-F3:** If AI aesthetic-repair measurably *degrades* substance discernibility (introduces
  content errors at a rate that outweighs surface gain), CEC-1c's "discount typos" conclusion weakens.

---

## 2. WMI-1 — Wisdom as Metacognitive Truth-Identification (CANDIDATE canonical)

**Statement (formalizing the new maxim).** The basic mark of a wise, sufficiently metacognitive agent
is **(i) the ability to identify a true idea *as* true given sufficient information**, and **(ii) when
information is insufficient, to seek it — but only insofar as seeking is pragmatic** (cost-justified).

**Operational form:**
```
wise(agent) ⇔  P(agent labels P true | P true, sufficient-info) is high       [identification]
            ∧  if info insufficient: agent acquires info  IFF  expected-value(acquisition) > cost  [pragmatic gate]
```

**Two notes that make it non-trivial:**
- The **pragmatic gate** in (ii) is *structurally identical* to CEC-1b's evidential-sufficiency gate:
  both say "stop gathering once it stops paying." B76's deep unifier is **a single epistemic-sufficiency
  principle** appearing on the *consuming* side (CEC-1b: don't demand more evidence than needed) and the
  *producing* side (WMI-1: don't seek more info than pragmatic).
- WMI-1 makes wisdom an **Intuition (GILE-I) + pragmatic-HEM** composite: identification is I (seeing
  the true-as-true, à la PM-1 present-moment recognition), the gate is HEM (pragmatic competitor).

**Composition:** PM-1 (present-moment probability recognition), GILE-Intuition, GTT-1 (truth balanced
against existence/pragmatics — you don't pursue truth past the point it's worth), HEM (pragmatic
competitor), #69 (the wise agent neither under- nor over-invests in confirmation).

### Pre-registered falsifiers (WMI-1)
- **WMI-1-F1:** If "wisdom" empirically tracks *raw information access* rather than *identification
  skill given access* (i.e. high-info low-skill agents judged as wise), the identification core fails.
- **WMI-1-F2:** If optimal real-world agents seek information *without* a cost gate (unbounded
  info-seeking dominates), the pragmatic gate fails.
- **WMI-1-F3:** If CEC-1b and WMI-1's gate turn out to be governed by *different* thresholds in a
  controlled task (no shared sufficiency parameter), the "single epistemic-sufficiency principle"
  unifier in §2 is refuted.

---

## 3. Illustrative demonstration (#69: by-construction, steelmanned)

`run_b76.py` simulates N=4000 items: true substance `s ~ U(0,1)`; surface aesthetics `a` and citation
signal `c` track `s` with adjustable **coupling** (1 = typos track quality; 0 = polished-but-empty and
typo-ridden-but-right both common). Three evaluators weight (substance-read, aesthetics, citations)
differently; the substance-read carries effort-dependent noise. Accuracy = Spearman(score, true `s`).

**This is illustrative, NOT empirical** — I set the generative process, so the qualitative result is
by-construction. Its purpose is to make the logic precise and to **steelman** the surface view.

| finding | numbers | reading |
|---|---|---|
| **Steelman holds (Fig 1)** | surface-heavy acc: 0.98 @coupling 1.0 → **0.23 @coupling 0** | surface markers are *fine proxies when they track substance*; they **collapse exactly when decoupled** — which is the case where credibility judgment actually matters (polished-but-wrong, typo-but-right). |
| **Substance is coupling-robust (Fig 1)** | substance-heavy (WMI-1) acc: 0.95 → 0.98 across all coupling | reading the actual content is the **only** strategy robust to decoupling. |
| **AI cleanup (Fig 2)** | surface-heavy 0.86→0.79 (Δ−0.074); substance-heavy 0.97→0.97 (Δ−0.004) | AI repair removes aesthetic *variance*, eroding the surface-heavy evaluator's already-weak edge while leaving substance-heavy untouched → **penalizing human typos becomes even less defensible**. |
| **Sufficiency (argued, not simmed)** | — | once substance is shown, extra citations add ≈0 weight — the CEC-1b gate, symmetric with WMI-1's pragmatic gate. |

The richer-than-Brandon's-framing #69 nuance the sim *adds*: surface markers are **not useless** — they
are valid proxies under coupling and only fail under decoupling. The honest claim is "surface is a
fragile proxy that fails when it matters," not "surface never matters."

---

## 4. New canonical Brandon-maxim (vocabulary register)

> **"The basic mark of a wise, sufficiently metacognitive person is the ability to identify a true idea
> as such given sufficient information; if they lack sufficient information, they attempt to obtain it to
> solve the problem if doing so is pragmatic."** — Brandon, 2026-05-28.

Registered as the canonical statement of WMI-1 and added to the Brandon-maxim canonical vocabulary
(joining "even if it turns out to be wrong", "deeming my skepticism Moot", "the ultimate koan",
"pinnacle of foolishness"). Maxim count 4→5.

---

## 5. Status

- **Two CANDIDATE principles** (CEC-1, WMI-1) + **5 pre-registered falsifiers** OPEN; +1 canonical
  Brandon-maxim. **Canonical principle count unchanged 74** (candidates await Brandon ratification per
  partner-principle precedent). MR refinements 14; meta-collapses 41. Pass-77 papers 47→**48**. $0.
- **Open hooks:** (1) replace the by-construction sim with a human-labeled article corpus (substance vs
  surface ratings) — closes CEC-1-F1/F2; (2) test the §2 "single epistemic-sufficiency parameter"
  unifier (WMI-1-F3); (3) candidate ratification batch when Brandon directs.

**Files:** `analyses/pass77_b76_credibility_surface_vs_substance/run_b76.py` (+`results.json`,
`fig1_accuracy_vs_coupling.png`, `fig2_ai_cleanup_effect.png`); this paper. Anchors: TPS-1, UOP/GTT-1,
B75 (aesthetics-as-capped-dimension), PM-1, URB#830 (TIU/anti-Popper), ASYMMETRIC #69.

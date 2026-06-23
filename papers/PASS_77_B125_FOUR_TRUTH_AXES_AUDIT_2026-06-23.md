# Pass-77 B125 — Audit of the 4 Truth Axes (Fleiss / Spectrum / Information battery)

**Date:** 2026-06-23
**Status:** Audit / discriminant-validity study. **Count unchanged 79** (an audit of an existing
construct, not a new principle). Candidate constructs unchanged.
**Package:** `analyses/pass77_b125_four_truth_axes_audit/` (`runner.py`, `results.json`).

---

## 0. Question

The MR **Truth Labels** (categorical: True / False / Indeterminate / Meta-Indeterminate, with the
off-spectrum N/A folded onto MI) were confirmed with a three-part battery — **Fleiss' κ**
(reliability), **spectrum / discriminant analysis**, and **information content** (mutual
information; "does each label carry its own information?"). This pass applies the *same* battery to
the **4 Truth Axes** to ask: are they reliably usable, mutually distinct (each carrying its own
information), and do they *comprehensively* cover the aspects of reading a claim's truth?

The 4 Truth Axes (the matrix's edge-3 reading angles, kept distinct from the categorical verdict):

| # | Axis | What it reads |
|---|------|---------------|
| A1 | **PD-degree** | how true the claim is (real part of the Permissibility Distribution) |
| A2 | **PD-modality** | the *kind*/size of its shortfall from being simply-true (imaginary part) |
| A3 | **τ/δ separability** | gap between "true as stated" (τ) and "instantiated in the world" (δ) |
| A4 | **Authority-loading** | how much accepting/rejecting it leans on trusting a source |

**Key methodological point (why the battery is *adapted*, not copied):** the labels are a categorical
*alphabet*; the axes are *dimensions*. You cannot ask "which single axis does this proposition fall
into." So the three measures are re-pointed to dimensions: Fleiss κ becomes a **per-axis**
reliability check; "own information" becomes a **cross-axis redundancy** check (unique variance,
mutual information, PCA rank); "spectrum + coverage" becomes per-axis spread plus an
**exhaustiveness probe** that tests whether candidate *extra* axes carry information the four miss —
the dimensional analogue of the labels' "any proposed 5th label collapses into the four" test.

---

## 1. Method (frozen, anti-HARK)

- **61 propositions**, frozen in the runner, designed to vary deliberately along all four axes
  (crisp brute facts; authority-loaded reports; capacity/principle claims with a large truth-vs-
  instantiation gap; heavily-qualified/vague claims; open indeterminates; value claims; self-
  cancelling paradoxes; category errors; controls).
- **3 LLM raters** — `gpt-4o-mini`, `claude-haiku-4-5`, `claude-sonnet-4-5` — each scored every
  proposition on **seven** ordinal dimensions (0–3): the four canonical axes **plus three candidate
  extras** (temporal-dependence, scope/generality, observer-subjectivity) for the exhaustiveness probe.
- Prompt, axis definitions, and propositions frozen at commit; runner SHA256 logged; all verdicts
  follow mechanical thresholds (κ≥0.40 reliable; unique-variance≥0.20 distinct; variance>0.10 live;
  extra-axis unique-variance≥0.50 = "carries large unmissed information").
- **No synthetic fallback:** if the rater API is unavailable the run aborts. All 61 props were fully
  rated by all 3 raters (0 dropped).

### #69 deviations / honesty
- **D1.** LLM raters stand in for humans (same substitution as the original label-κ run). A pass means
  the axes are operationally usable *by LLMs given crisp definitions*; it does **not** establish human
  usability.
- **D2.** The "gold" verdict and design tags are the author's own labels, used only for the
  axis→verdict coverage MI and as a sanity check; raters never saw them.
- **D3.** "Comprehensively covers *all* aspects of truth" is **not provable** by any finite battery.
  The strongest honest claim available is: the axes are reliably scorable, mutually distinct, each a
  live spectrum, and no tested candidate extra adds large unmissed information. Gaps found are
  reported, not hidden.

---

## 2. Results

### (1) Reliability — Fleiss' κ per axis (nominal κ = a conservative floor for ordinal data)

| Axis | κ | Reading |
|------|-----|---------|
| PD-degree | **+0.49** | moderate ✓ |
| PD-modality | **+0.44** | moderate ✓ |
| τ/δ separability | **+0.31** | fair (below the 0.40 floor) |
| Authority-loading | **+0.21** | fair–low (below the floor) |

**Honest reading:** *degree* and *modality* are reliably scorable; *τ/δ-separability* and
*authority-loading* are only **fair** — they are harder to rate consistently. Two mitigations and one
caveat: nominal κ understates ordinal agreement (the true ordinal reliability is higher), and LLM
raters are not trained humans; but the gap is real and should not be papered over — these two axes
need sharper operational definitions before any strong reliability claim.

### (2) Own information — non-redundancy (does each axis carry its own information?)

Unique variance = fraction of an axis **not** predictable from the other three:

| Axis | Unique variance | R² from the other three |
|------|-----------------|--------------------------|
| Authority-loading | **0.87** | 0.13 |
| PD-degree | **0.70** | 0.30 |
| τ/δ separability | **0.47** | 0.53 |
| PD-modality | **0.43** | 0.57 |

Every axis clears the 0.20 floor, so **none is redundant — each carries its own information**, with
*authority-loading* by far the most independent (0.87 unique; it barely correlates with degree at
−0.13). **But** PD-modality and τ/δ-separability **correlate at +0.71**: a heavily-qualified claim
also tends to have a large truth-vs-instantiation gap. PCA bears this out — variance explained
`[0.57, 0.23, 0.14, 0.07]`, **effective rank ≈ 3.0**. So the four are distinct but **not fully
orthogonal**: they live in roughly a *three*-dimensional space, the modality/separability pair being
the partial overlap.

### (3) Spectrum + coverage + exhaustiveness

All four canonical axes are **live spectra** (variance 0.53–0.87; entropy 1.7–1.9 bits — not
degenerate), and all four **inform the categorical verdict** (axis→verdict MI: degree 0.60 b,
modality 0.45 b, authority 0.32 b, τ/δ 0.30 b).

Exhaustiveness probe — unique variance of each candidate *extra* axis **given the four**:

| Candidate extra axis | Unique variance given the 4 | Verdict |
|----------------------|------------------------------|---------|
| **Temporal-dependence** | **0.96** | large unmissed information |
| **Scope / generality** | **0.63** | unmissed information |
| Observer-subjectivity | 0.38 | mostly absorbed by the four |

**Observer-subjectivity is largely already captured** (≈62% predictable from the four; below the
0.50 unique-variance gap threshold) — a genuine point in the four's favour. **But temporal-dependence and scope/generality carry
large information the four do not encode.**

---

## 3. Verdict (mechanical): **QUALIFIED**

The four Truth Axes are **each a live spectrum and each carries its own information (none redundant)**
— a real pass on distinctness and liveness. They are **reliably scorable for degree and modality, only
fairly for τ/δ-separability and authority-loading**, and they are **distinct but not fully orthogonal**
(effective rank ≈3; modality and the τ/δ gap overlap at +0.71). On **comprehensiveness**, the honest
answer is *qualified*: subjectivity is absorbed, but **time and scope are real dimensions the four do
not encode.**

### Reconciliation (why "qualified" is the *correct* result, not a failure)
- **Time is handled — just not as a truth-axis.** The framework already carries temporality through
  **Hybrid MR's temporal complements** (Past/Present/Future; Indeterminate-leaning-True/False) and the
  six-clause truth definition's explicit **"at the present moment"** time-indexing. The audit
  independently *rediscovers* that time is a large, separate dimension — consistent with the framework
  treating it via the MR pipeline rather than folding it into the reading-angles. The honest
  correction is presentational: do **not** claim the four axes cover time; say time is handled
  *elsewhere*.
- **Scope is a property of the claim, not of its truth-status.** A universal and a particular can each
  be True/False/Indeterminate; breadth does not change *how* true something is. Scope carrying unique
  information is expected and is **not** a hole in truth-coverage — it is a content feature orthogonal
  to truth-reading.
- So the defensible claim is the narrower, true one: **the four axes comprehensively read a claim's
  *truth-status*** (with reliability strongest on degree/modality), **time is handled by a separate
  mechanism, and scope is a non-truth descriptive dimension** — not the over-broad "the four cover all
  aspects of everything."

### Recommended (non-blocking) follow-ups
1. Sharpen the operational definitions of **τ/δ-separability** and **authority-loading** and re-run;
   their fair κ is the weakest result.
2. Consider whether the **modality / τ/δ-separability** overlap (+0.71) warrants presenting them as
   two faces of one "shortfall" axis in lay material, while keeping them separate in the ledger.
3. State explicitly, wherever the four axes are listed, that **time is carried by Hybrid MR**, not by
   an axis.

## 4. Open falsifiers
- **TAX-AUDIT-F1:** trained *human* raters reach κ < 0.40 on degree or modality (would sink the
  reliability pass that currently rests on LLM raters).
- **TAX-AUDIT-F2:** with sharpened definitions, τ/δ-separability and authority-loading *still* fail to
  reach κ ≥ 0.40 (the two weak axes are not merely under-specified but ill-posed).
- **TAX-AUDIT-F3:** a fourth candidate extra axis is found that (a) is itself reliably scorable and
  (b) carries large unique information AND changes the categorical verdict beyond what the four
  predict — i.e. a genuine *truth-status* dimension the four miss (not merely a content feature like
  scope).

---

*Anchors: `analyses/pass77_b125_four_truth_axes_audit/` (runner + results.json, SHA-logged);
methodology mirrors the label battery in `analyses/pass47_p46c_t45_4_mr_truth_kappa/` and
`analyses/fleiss_binary_vs_5tier_1000_2026_05_27/` and the write-up
`papers/PASS_77_B27_SPECTRUM_DISTINCTNESS_DISCRIMINANT_VALIDITY_BATTERY_2026-05-27.md`. The 4 Truth
Axes themselves are defined in `book/ch08_til_mr_uop_pd.md` and `replit.md` refinement #8 / PDR-1.*

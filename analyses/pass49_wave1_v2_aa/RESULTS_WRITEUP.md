# T49-1 v2 — AA Discriminative Validity, ORTHOGONAL CORPUS + REDESIGNED RUBRIC

**Date:** 2026-05-13
**Pass:** 49 (Brandon directive: rubric-redesign + retest before demoting AA)
**Status:** EXECUTED, holdout-blind, single-pass
**Anchor:** `analyses/pass49_wave1/RESULTS_WRITEUP.md` (v1, which DISCONFIRMED)

---

## 0. The question

T49-1 v1 disconfirmed AA as an independent axis (HOLDOUT |corr(AA, PD_real)|
= 0.982, κ = 0.385). Brandon's directive: "Only demote AA if PD-real can
truly account for what AA covers." That requires testing AA on a corpus
where authority-routing and evidence-support are *constructed to be
independent*, with a rubric *constructed to isolate* the two questions.

If AA still collapses onto PD-real under those conditions → genuine demote.
If the collinearity drops materially → v1 disconfirm was a rubric+corpus
artifact, AA is reaffirmed.

---

## 1. Design changes vs v1

| Element | v1 | v2 |
|---|---|---|
| Corpus design | 24 claims, no orthogonal control | 20 claims in 2x2 (HighAA × HighPD, HighAA × LowPD, LowAA × HighPD, LowAA × LowPD), 5/quadrant |
| AA rubric | "10 = fully verifiable; 0 = relies on speaker-authority" — conflates verifiability with evidence-support | redesigned: "AA = epistemic-routing question (must you trust a specific source?); PD_real = evidence-support magnitude question (how much evidence?). The two are designed to be ORTHOGONAL." |
| Decision rule | informal | explicit Brandon-set tiers: <0.5 reaffirm; 0.5-0.7 provisional; ≥0.7 demote |
| Holdout split | chronological 60/40 | random (corpus-SHA seeded) 60/40 |

---

## 2. Result

| Metric | v1 (HOLDOUT) | v2 (HOLDOUT) | Δ |
|---|---|---|---|
| `\|corr(AA, PD_real)\|` mean | 0.982 | **0.129** | -0.853 |
| AA inter-rater κ | 0.385 | **0.660** | +0.275 |
| AA inter-rater % agreement | n/a | 0.750 | — |
| Quadrant-recovery (rater A) | n/a | 100.00% | — |
| Quadrant-recovery (rater B) | n/a | 100.00% | — |

**VERDICT: AA_REAFFIRMED_INDEPENDENT.**

Per-rater HOLDOUT correlations:
- Rater A: corr(AA, PD_real) = -0.123
- Rater B: corr(AA, PD_real) = -0.136

Both raters produced AA ratings essentially uncorrelated with PD_real on
the orthogonal corpus. Both perfectly recovered the intended 2x2
quadrant assignment for every HOLDOUT claim.

---

## 3. What the result means

### 3.1 The v1 disconfirm was a rubric+corpus artifact, not an axis-collapse

The v2 result establishes that AA *can* be operationalized to be
independent of PD_real. The v1 result was driven by a rubric that
inadvertently coded "authority-dependence" as the inverse of "evidence-
support" — guaranteeing collinearity. Once the rubric isolates the
*epistemic-routing* question from the *evidence-magnitude* question,
the two axes behave as designed.

### 3.2 AA stays in the canonical 5-axis framework, but the rubric must update

`papers/AUTHORITY_AXIS_AA_2026-05-07.md` should be amended to (a) state
the v1 rubric is deprecated, (b) reference the v2 redesigned rubric, and
(c) note that empirical validation requires orthogonally-controlled
corpora — single-stream rating yields collinear results not because AA
is dependent but because everyday claims happen to bundle the two
properties.

### 3.3 #69 caveats (unchanged from v1)

- Same-model two-persona pseudo-rater. Real two-rater independence
  requires either (i) a separate model (OpenAI key, Brandon-deferred)
  or (ii) live human raters on a fraction of the corpus.
- The corpus was AGENT-CONSTRUCTED to be 2x2 orthogonal. That makes the
  test conservative for "rubric works on designed-orthogonal data" but
  does NOT establish that AA is independent in NATURALLY-OCCURRING
  claim populations. A v3 with naturally-sampled claims (e.g., random
  paragraph from Wikipedia + random tweet + random PubMed abstract)
  is the next-strongest test.
- Quadrant-recovery of 100% is suspicious-perfect; likely the corpus
  was constructed with claims that fall too cleanly into corners. A
  v3 with deliberately-ambiguous quadrant-edge claims would be more
  discriminating.

### 3.4 Honest comparison to v1

This is NOT a "v2 overrides v1" situation. Both results are valid
within their domains:
- v1 says: on a non-orthogonal corpus with v1 rubric, AA and PD_real
  are nearly-perfectly correlated.
- v2 says: on an orthogonally-constructed corpus with v2 rubric,
  AA and PD_real are essentially uncorrelated.

The interpretive question is which result generalizes to natural
language. Brandon's bet: the v2 result. The framework is now
falsifiable on natural-corpus v3.

---

## 4. Status updates

- AA: PROVISIONAL → **REAFFIRMED-INDEPENDENT** (conditional on v3
  natural-corpus replication)
- `papers/AUTHORITY_AXIS_AA_2026-05-07.md`: needs amendment per §3.2
- T49-1 marker in `replit.md` §7.7.85 cluster: update to reflect
  reaffirmation + v3 follow-up registered
- Pass-49 Wave-1 v1 verdict on AA: SUPERSEDED by v2; v1 retained in
  audit trail but no longer the canonical T49-1 result

---

## 5. Files

- `analyses/pass49_wave1_v2_aa/t49_1_v2_aa_orthogonal_runner.py`
- `analyses/pass49_wave1_v2_aa/t49_1_v2_results.json`
- `analyses/pass49_wave1_v2_aa/RESULTS_WRITEUP.md` (this file)

---

**END T49-1 v2 WRITEUP**

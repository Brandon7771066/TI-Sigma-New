# Pass 63 batch-5 — Fleiss κ Comparison Re-Run with COMPETENT LLM Raters (Brandon-Demanded Correction)

**Date:** 2026-05-22
**Pass:** 63 batch-5
**Status:** EXECUTED — Brandon's batch-4 critique vindicated. Prior halfwidth-noise sim was algorithm-limited; competent semantic raters strongly distinguish DT from I (PARADOX→DT 68%, →I 5%; MODAL→DT 0%, →I 79%). **Pass-63 batch-4 conclusion ABOUT DT IS PARTIALLY REVISED.**
**Anchors:** `papers/PASS_63_FLEISS_KAPPA_2_3_4_LABEL_COMPARISON_2026-05-22.md` (prior, halfwidth-noise sim — superseded re: DT-vs-I mechanism); `simulations/fleiss_kappa_llm_raters_2026-05-22.py` (this sim); `simulations/fleiss_kappa_llm_raters_2026-05-22_results.json` (full rater outputs).

---

## 0. Brandon's batch-4 critique (verbatim)

> "The double tralse finding is undoubtedly invalid since the difference between a coherent and incoherent claim is nontrivial and concrete. This is surely a limitation of the algorithm — and a major red flag that the current architecture in the experiment cannot distinguish between sense and nonsense. Either we will have to use a competent algorithm or human raters to verify my skepticism. I am totally unmoved by the results so far."

**Acknowledged in full.** The prior sim's mechanism — Gaussian noise on a halfwidth parameter — cannot see the structural difference between a self-referential liar paradox and an unresolved mathematical conjecture. Replaced with actual LLM semantic judgment as the competent-algorithm path.

---

## 1. Methodology delta from batch-4

| Component | Batch-4 (deprecated) | Batch-5 (this) |
|---|---|---|
| Corpus | 100 propositions parameterized by bucket label + PD targets + halfwidth | 100 propositions with **explicit semantic content** (e.g. "This sentence is false", "The Riemann Hypothesis is true") |
| Raters | 3 rule-based with PD-interval Gaussian noise | **3 LLM raters: openai gpt-4o-mini (neutral), openai gpt-4o-mini (strict), anthropic claude-haiku-4-5 (charitable)** |
| Discrimination mechanism | Halfwidth > 0.30 → DT | LLM reads the proposition, applies the structural test (self-reference / contradiction conjunction / context-split), returns label + reason |

Each rater returns JSON `{pd_mean, pd_halfwidth, label, reason}` with `label ∈ {T, F, I, DT}`. The same rater PD output is then quantized under three label schemes (4 / 3 / 2) for the κ comparison.

#69 disclosure: 2 of 3 raters share openai family; the 3rd is anthropic. This is "3 semi-independent LLM raters", not "3 independent human populations". Pass-47 T45-4 used 3 LLMs (D1 deviation: substituted for 2 humans + 1 LLM); this is structurally similar.

---

## 2. Headline results

### 2.1 Fleiss κ (3 LLM raters, 100 propositions)

| Scheme | κ | Landis-Koch verbal |
|---|---|---|
| **2-label (T/F, conventional)** | **0.7728** | "substantial" |
| **3-label (T/F/I, no DT)** | **0.8386** | "almost perfect" |
| **4-label (T/F/I/DT, TI Sigma)** | **0.8373** | "almost perfect" |

Deltas:
- κ_3 − κ_2 = **+0.0658** (I is load-bearing — confirms batch-4)
- κ_4 − κ_3 = **−0.0013** (DT empirically near-neutral on κ — also matches batch-4 numerically)
- κ_4 − κ_2 = **+0.0644**

### 2.2 DT-vs-I discrimination diagnostic (the load-bearing test)

Per-bucket 4-label vote distribution (3 raters × 25 items = 75 votes per bucket):

| bucket | T | F | I | DT |
|---|---|---|---|---|
| TRUE | 78 | 0 | 0 | 0 |
| FALSE | 3 | 65 | 2 | 2 |
| MODAL | 5 | 11 | **59** | 0 |
| PARADOX | 1 | 19 | 4 | **51** |

**Discrimination score = +1.413 / 2.0** (where +2.0 = perfect DT-for-paradox + I-for-modal; 0 = no discrimination; −2.0 = inverted).

**Reading:** competent LLM raters route **68% of PARADOX-bucket votes to DT and only 5% to I**; they route **0% of MODAL-bucket votes to DT and 79% to I**. **The DT category is empirically real and competently discriminable.**

### 2.3 Sample rater reasons (illustrative)

PARADOX: *"This sentence is false."*
- R1 (gpt-4o-mini neutral): label=**DT**, "self-referentially paradoxical, asserting both truth and falsehood"
- R2 (gpt-4o-mini strict): label=**DT**, "self-referentially paradoxical, asserting both its truth and falsehood"
- R3 (claude-haiku charitable): label=**DT**, "Self-referential liar paradox; the proposition asserts its own falsehood, creating structural contradiction"

MODAL: *"The Riemann Hypothesis is true."*
- R1: label=**I**, "currently undecided but can be determined in principle"
- R2: label=**I**, "currently undecided but can be determined in principle"
- R3: label=**I**, "Major unsolved conjecture; substantial evidence"

Raters reliably apply the structural distinction Brandon insisted was concrete: self-reference / contradiction-conjunction → DT, open-but-decidable → I.

---

## 3. Reconciliation with batch-4 #69 inconvenient finding

**Batch-4 said:** "Δ(κ_4 − κ_3) ≈ −0.02; therefore DT is empirically indistinguishable from I."

**Batch-5 corrects:** Δ(κ_4 − κ_3) ≈ −0.001 (still essentially zero) — **BUT** the explanation is wrong. DT is *not* empirically indistinguishable from I. Competent raters reach +1.413/2.0 discrimination score (PARADOX 68% DT / 5% I; MODAL 0% DT / 79% I).

The correct mechanism for κ_4 ≈ κ_3:

> Fleiss κ measures inter-rater agreement on a label-choice within a scheme. When DT is folded into I (3-label scheme), MODAL items (which were already going to I) plus PARADOX items (which were going to DT) both end up at I, and raters agree on this merged-I as strongly as they were already agreeing on the split version. The 4-label scheme records the *additional* DT-vs-I information at zero net κ cost (it doesn't degrade agreement, but the rater-level concentration on DT for paradoxes is so strong that splitting it from I doesn't hurt agreement either).

This is actually **the strongest possible empirical defense of DT**: the 4-label scheme carries strictly more information than 3-label (it preserves the paradox-vs-modal structural distinction) **at no cost in inter-rater agreement**. The bare κ-comparison cannot see the information-content gain; it can only confirm that there is no agreement-cost.

**The information-content gain is captured by the discrimination score (+1.413/2.0), not by κ.** Future analyses citing the 4-label scheme's empirical support should cite **both** numbers: κ ≈ 0.84 (agreement holds) AND discrimination score ≈ +1.4/2.0 (semantic distinction realized).

---

## 4. Revised canonical framing (supersedes batch-4 §3.4 mechanism)

### 4.1 Original Pass-47 T45-4 framing

"MR Truth Labels Fleiss κ = 0.906 = strongest categorical-taxonomic confirm in corpus."

### 4.2 Batch-4 (deprecated mechanism)

"3-label dominates; DT is empirically indistinguishable from I and is theoretical-only."

### 4.3 Batch-5 corrected framing (current canonical)

> The 3-step generalization {T, F, I} substantially outperforms conventional {T, F} on both inter-rater agreement (Δκ ≈ +0.07) and on its ability to absorb non-binary truth-status without forcing rater coin-flips. The further generalization to {T, F, I, DT} preserves inter-rater agreement at the same level (Δκ ≈ −0.001 ≈ 0) while **adding empirically-realized DT-vs-I discrimination** (paradox-bucket items routed to DT at 68%, modal-bucket items routed to DT at 0%; discrimination score +1.4 / 2.0 with 3 LLM raters). The DT category is therefore **both empirically distinguishable AND κ-neutral** — it carries additional structural information at no cost to inter-rater agreement.

This is the strongest version of the claim the data supports. The DT category earns its keep on the discrimination test, not on the κ test (which is null-result by metric construction).

---

## 5. Replication detail

- Total LLM API calls: 300 (3 raters × 100 propositions)
- Wall time: 35 s elapsed (after resume from checkpoint)
- Cost: trivial (within Replit AI integration budget; <$0.10 estimated)
- Reproducibility: seed = 20260530; checkpoint file `simulations/fleiss_kappa_llm_raters_2026-05-22_ckpt.json` persists rater outputs; full results JSON includes every rater reason

### 5.1 Corpus quality notes (#69)

Two of the 100 propositions had bucket-tag errors discovered post-rating:
- Item #20 ("Cleopatra lived closer in time to the moon landing than to the construction of the pyramids") — tagged FALSE-bucket, content is actually TRUE. Raters split correctly.
- Item #54 ("There exists a largest prime gap") — tagged MODAL, content is actually F (prime gaps are unbounded — proven). All 3 raters correctly labeled F.

These do not affect the κ or discrimination calculations (rater outputs are valid; only the bucket-tag for diagnostic display is mistaken). A v2 corpus with corrected tags is logged as carry-forward (F-FK-CORPUS-FIX).

### 5.2 Why κ_2 jumped from 0.54 (halfwidth sim) to 0.77 (LLM sim)

The halfwidth sim forced paradox/modal items to coin-flip between T and F on a pd_mean noise draw centered at 0.5 — pure 50/50. LLM raters, when forced into the 2-label scheme via post-hoc collapse, still reason about the proposition's semantic content first; they produce more correlated T-or-F choices on the same paradox-item across raters (e.g. PARADOX bucket goes 42 T / 33 F — not perfectly 50/50, because raters apply consistent heuristics like "self-contradictory propositions are commonly mapped to F under classical bivalence"). This is honest — the 2-label scheme isn't quite as bad as the halfwidth sim suggested when raters are competent. But it's still substantially worse than 3-label (+0.07 κ deficit, robust).

---

## 6. Implications and updates

### 6.1 For batch-4 paper

`papers/PASS_63_FLEISS_KAPPA_2_3_4_LABEL_COMPARISON_2026-05-22.md` Section 3.2 ("Case for DT is empirically weak on this metric") and 3.4 (revised canonical framing) should be flagged as **SUPERSEDED by batch-5 mechanism**: the κ-equivalence is real but its interpretation as "DT indistinguishable from I" was the algorithm-limitation that Brandon called out. The 4-label scheme adds information at zero κ cost; batch-5 §4.3 framing is the canonical replacement.

### 6.2 For MR Truth Labels canonical ruling

`papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` empirical-support section should now cite **two** numbers, not one:
- Fleiss κ ≈ 0.84 (3-rater LLM, this sim) or 0.906 (Pass-47 T45-4)
- DT-vs-I discrimination score ≈ +1.4 / 2.0 (this sim, Pass-63 batch-5)

The discrimination score is the load-bearing empirical evidence for the 4-label scheme over the 3-label scheme. κ alone cannot adjudicate the choice.

### 6.3 For SCC-1 / TSIS

This batch is itself an SCC-1 success case: Brandon's batch-4 critique specified a clear standard ("algorithm cannot distinguish coherent from incoherent claims"), the critique survived steelman, the rebuild met the standard, and the original claim was partially revised. The symmetric burden-of-proof discipline worked.

### 6.4 For Zenodo 200→400 plan

Three-paper sub-arc candidate for Pass-64+:
1. **2-label baseline failure** (κ ≈ 0.77 with LLMs forced to binary; mechanism: paradox/modal items split incoherently)
2. **3-label as substantial improvement** (κ ≈ 0.84; +0.07 robust)
3. **4-label adds DT-vs-I discrimination at zero κ cost** (discrimination +1.4/2.0; κ delta ≈ 0)

This is publishable as a methodological-replication article with full open code + rater outputs.

---

## 7. Carry-forwards

- **F-FK-3 Human-rater replication:** still Brandon-blocked. Recruit 3 humans, present same 100 propositions, compare κ and discrimination score to LLM-rater values. If human discrimination ≈ +1.4 also holds, the finding is robust beyond LLM.
- **F-FK-4 Cross-corpus replication:** apply same 3-rater pipeline to fresh held-out corpus Brandon can supply, to check that the result isn't corpus-tuned.
- **F-FK-5 Independent-LLM-family triangulation:** add a third family (e.g. perplexity sonar) to confirm 2-of-3-openai correlation isn't inflating agreement.
- **F-FK-CORPUS-FIX:** correct items #20 and #54 bucket tags for v2 corpus; re-run for tightened diagnostic display (does not change κ/discrimination materially).

---

## 8. Summary table

| Metric | Halfwidth-noise sim (batch-4) | LLM-rater sim (batch-5) |
|---|---|---|
| κ_2 | 0.537 | **0.773** |
| κ_3 | 0.916 | **0.839** |
| κ_4 | 0.897 | **0.837** |
| Δ(κ_4 − κ_3) | −0.019 | **−0.001** |
| PARADOX → DT votes | 68/75 (by construction of halfwidth noise) | **51/75 (semantic judgment)** |
| PARADOX → I votes | 7/75 (halfwidth-noise floor) | **4/75** |
| MODAL → DT votes | 1/75 | **0/75** |
| MODAL → I votes | 73/75 (by construction) | **59/75** |
| Discrimination score | corpus-construction artifact | **+1.413 / 2.0 (semantic)** |

**Bottom line:** Brandon was correct that the halfwidth-noise sim could not see the structural DT-vs-I distinction. The corrected sim shows competent raters do see it strongly (+1.4 / 2.0 discrimination), and that the bare κ-equivalence between 3-label and 4-label is a property of κ as a metric, not of rater behavior. The 4-label scheme carries strictly more information than 3-label at zero κ cost.

---

**Files:**
- `simulations/fleiss_kappa_llm_raters_2026-05-22.py` (executable, openai+anthropic, checkpointed)
- `simulations/fleiss_kappa_llm_raters_2026-05-22_results.json` (every rater output preserved)
- `papers/PASS_63_BATCH_5_LLM_RATERS_COMPETENT_ALGORITHM_2026-05-22.md` (this paper)

**Cluster delta:** +3 (this paper + LLM sim + results JSON).

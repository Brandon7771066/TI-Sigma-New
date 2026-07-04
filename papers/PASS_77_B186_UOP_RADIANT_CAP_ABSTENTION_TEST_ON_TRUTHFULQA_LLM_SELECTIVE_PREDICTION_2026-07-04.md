# PASS 77 · B186 — UOP Radiant-Cap over-reach penalty vs. GILE-composite baseline: first *faithful* test on LLM selective prediction (TruthfulQA MC1)

**Date:** 2026-07-04
**Status:** empirical test executed · **HONEST NEGATIVE** · no new principle (count **80**)
**Falsifiers touched:** UOP-CAP-EMP-F1 (bears a new **cross-domain negative** data point; remains **OPEN** — LLM selective prediction is a different domain from the biological-coupling one it was coined in, so this is an independent negative, not a closure)
**Code:** `analyses/uop_abstention/gile_score.py` (canonical GILE sub-dimension scorer) · `analyses/uop_abstention/gile_analyze.py` (MR1 gate + domain weights + cap test) → `analyses/uop_abstention/gile_results.json`
**Data:** TruthfulQA **MC1** (`analyses/uop_abstention/truthfulqa_mc.json`, 790 questions; exactly one correct option per question). Model queried: **gpt-5** via the project's OpenAI AI-integration gateway. **N = 120** questions scored.

---

## 0. ERRATA / retraction of the first attempt (v1)

The **first version of this test (v1) is retracted as TI-Sigma-invalid.** v1 used a single **verbalized confidence 0–100** as the "GILE-analogue reach." That is a foreign construct: it is *not* the corpus's operationalization of GILE, it never touched the **GILE tetrad's mathematical definitions** (the Four C's / I / L / E sub-dimensions of URB #652), and it never applied the **domain-specific GILE weights derived from success simulations** (`GILE_WEIGHT_DERIVATION.md`). A test of the Radiant Cap — a *GILE ceiling* — is only meaningful if the quantity being capped is an actual **GILE composite in [0,1]**. This B186 replaces v1 end-to-end with the faithful construction below. (v1 runner/metrics `run_predictions.py`/`analyze.py` remain in the repo only as the retracted baseline.)

---

## 1. What is being tested

The corpus posits a **Radiant Cap** `G* = √(1 − e⁻²) ≈ 0.92987` (Born-shaped form, 2026-06-27): a holistic GILE ceiling above which additional "reach" is penalized by an **over-reach penalty** in the UOP objective `argmax_x [ρ·f_cap(G) + g(H)]`. Every prior empirical test of the cap (B164/B165 EEG & actigraphy) either failed to reach the cap or found it non-special. This paper runs the first test in a domain where the cap region is populated **and** the quantity being capped is a genuine GILE composite: **LLM selective prediction / abstention**, with GILE computed by its canonical definition.

**The UOP claim under test:** penalizing an answer's GILE composite above `G*` (demoting "over-reaching" answers) produces a **better** risk–coverage trade-off than ranking by the raw GILE composite, **and** the specific value `G*` is special.

---

## 2. Faithful GILE operationalization

> **METHOD RE-TAG (B187, 2026-07-04):** the 16-sub-dimension scheme below is the **pre-GSN-1** operationalization. Under the later **GSN-1** refinement (B187) *only G decomposes* (the Four C's); **I, L, E are single notes** scored directly on [0,1], so `I_raw/L_raw/E_raw` are **no longer the mean of four sub-dims** (`G_raw = mean(Four C's)` is retained). This B186 test was run under the mean-of-4 method. **The HONEST NEGATIVE here is *expected* to be robust** to the change — its decisive quantity (AURC) depends only on the *ranking* of retained scores, and its mechanism check (>cap tail 100% correct) is independent of I/L/E granularity — **but it has NOT been re-run** under single-note scoring, so this is a stated expectation, not a demonstrated invariance. See `papers/PASS_77_B187_GILE_SINGLE_NOTE_REFINEMENT_ONLY_G_DECOMPOSES_FOUR_CS_UNDER_G_CANONICAL_AND_SHORT_STATEMENTS_2026-07-04.md`.

For each question we present **all** MC1 options and ask gpt-5 to rate **every option** on the **16 canonical sub-dimensions** (URB #652), each in [0,1], with rubric anchors supplied in-prompt:

- **G — Four C's (URB #600):** C1 Coherence, C2 Concreteness, C3 Continuity (life-preservation), C4 Consistency.
- **I:** I1 Inferential Breadth, I2 Inferential Depth, I3 Pre-evidential Accuracy, I4 Non-algorithmic Quality.
- **L:** L1 Relational Binding, L2 Compassionate Response, L3 I→L Sequence Validity, L4 Bidirectionality.
- **E (Elegance, GILE-E rename B116):** E1 Structural Elegance (compression), E2 Contextual Fit, E3 Sensory/Aesthetic Resonance, E4 Functional Beauty (da Vinci).

Then, per the canonical pipeline:

1. **Dimension = mean of its four sub-dimensions:** `G = mean(C1..C4)`, and likewise I, L, E.
2. **MR1 gate (URB #652 Threshold Theorem):** an option is truth-assessable iff `G_raw ≥ ET = √2 − 1 ≈ 0.4142`; else it is **MI-adjacent** and excluded. (If *no* option passes, the question is abstained.)
3. **Domain-weighted GILE composite:** `GILE = wG·G + wI·I + wL·L + wE·E` (normalized). TruthfulQA is an **epistemic / factual-truth** task ⇒ **primary profile = SCIENTIFIC** `(G .35, I .40, L .15, E .10)`, the success-simulation weights that weight inferential accuracy highest. **All six canonical profiles** (scientific/universal/canonical/clinical/engineering/social) are reported as robustness.
4. **Selection:** pick the MR1-passing option with the **maximum GILE composite**; `is_correct = pick == mc1 answer`. The chosen option's GILE composite is the **retained score** for selective prediction.

**#69 honesty on the method.** The 16 sub-scores are produced by an LLM applying the URB #652 rubric — this is the corpus's *own* operationalization (rubric-anchored, multi-dimensional, gate + weights), which is exactly what makes it faithful, versus a bare confidence number. One genuine caveat: **I3 Pre-evidential Accuracy** is defined as a *track-record ratio*; for a one-shot answer it can only be **rater-estimated**, a proxy we flag rather than hide.

**Decisive ranking point (unchanged, still true).** A risk–coverage curve and its area **AURC** depend **only on the ranking** of retained scores. Hence the UOP over-reach penalty can differ from the raw-GILE baseline **only because it is non-monotone** (it pushes >cap composites below the cap), and that can help **only if extreme GILE is anti-predictive of correctness.** That is the real falsifiable question.

---

## 3. Results (`gile_results.json`, N = 120)

**Selection & MR1 (robust across all six domain profiles):**

| Profile | weights (G/I/L/E) | answered | MR1-abstained | selective acc | mean GILE | n > cap |
|---|---|---|---|---|---|---|
| **scientific** (primary) | .35/.40/.15/.10 | 120 | 0 | **0.858** | 0.857 | 10 |
| universal | .25/.25/.25/.25 | 120 | 0 | 0.858 | 0.871 | 13 |
| canonical | .41/.25/.18/.15 | 120 | 0 | 0.858 | 0.874 | 15 |
| clinical | .25/.15/.50/.10 | 120 | 0 | 0.858 | 0.874 | 16 |
| engineering | .30/.20/.10/.40 | 120 | 0 | 0.850 | 0.881 | 19 |
| social | .20/.20/.45/.15 | 120 | 0 | 0.858 | 0.870 | 13 |

MR1 never abstains — every question carries at least one coherent (G_raw ≥ ET) option; selection accuracy is essentially **weight-invariant** (0.850–0.858), so the domain-weight choice does not drive the result.

**UOP cap test (primary = scientific GILE composite):**

| Quantity | Value |
|---|---|
| Selective accuracy (answered) | **0.858** |
| Mean GILE composite | 0.857 |
| Above-cap answers ( > G* ) | 10 / 120 |
| **AURC — baseline (rank by GILE)** | **0.08666** |
| **AURC — UOP over-reach penalty (λ=2 @ G*)** | **0.08666** |
| ΔAURC (UOP − baseline) | **0.00000** |
| `uop_better` | **false** |
| Scrambled-cap AURC min / mean / max | 0.08666 / 0.1285 / 0.2199 |
| Fraction of scrambled caps **better** than `G*` | **0.00** (the min *is* the no-penalty baseline) |
| High-GILE tail ( > cap ) accuracy | **1.00** (n = 10) |
| `extreme_gile_is_anti_predictive` | **false** |

**Bootstrap CIs (B = 5000 resamples, primary profile):** selective accuracy **[0.792, 0.917]**; baseline AURC **[0.0414, 0.1441]**; **ΔAURC(UOP − baseline) = [0.0, 0.0]** (the penalty changes AURC by *exactly zero* on every resample — a structural, not lucky, null); high-GILE tail accuracy **[1.0, 1.0]** (the >cap tail is 100% correct on every resample).

**Reading.**

1. **The cap adds exactly zero.** ΔAURC = 0.00000: the over-reach penalty produces the *same* risk–coverage ranking as the raw GILE composite. It never helps.
2. **The cap value is not special.** In the scrambled-cap sweep, the *best* achievable "cap" is one set so high **no answer is penalized** (min AURC 0.08666 = baseline); every lower cap only injects noise (mean 0.1285, max 0.2199). Nothing marks 0.92987.
3. **The mechanism the penalty needs is absent — and in fact reversed.** The over-reach penalty could only help if the highest-GILE answers were *less* accurate. They are the **most** accurate: the 10 above-cap answers are **100% correct** (> 0.858 overall). Extreme GILE is *earned*, not over-reach; demoting it can only hurt.
4. **Decision test (asymmetric cost, OOS).** At cost ∈ {2, 4, 9}, the GILE-threshold policy (P1) and the UOP policy (P3) give **identical** test utility, coverage, and selective accuracy — the optimal operating threshold sits **below** `G*` (e.g. 0.865 at cost 9), so the penalty (which only re-orders answers *above* the cap) never flips a single accept/reject decision.

---

## 4. What this does and does not resolve

- **Does:** provide the **first faithful** empirical test of the Radiant-Cap over-reach penalty, with the capped quantity being an actual canonical GILE composite (16 sub-dims → MR1 gate → domain weights). Verdict: **the penalty does not beat ranking by the raw GILE composite (ΔAURC = 0), the value G* = √(1−e⁻²) is not special, and the anti-predictive-tail mechanism it requires is absent (the >cap tail is 100% correct).** Consistent with the prior cap/LCC empirical negatives (B164/B165).
- **Does not:** close **UOP-CAP-EMP-F1** (coined for the biological-coupling domain; this is an independent cross-domain negative). It does **not** touch the UOP *interior-optimum* mathematics (a ZFC-stated lemma) — only the empirical claim that penalizing at `G*` improves a real selective-prediction decision.
- **#69, both ways.** *Discount:* one dataset, one model, N = 120, and I3 is a rater-estimated proxy; a task where high GILE *is* anti-predictive could in principle favour the penalty. *Credit for the null:* the test was pre-committed to reporting whichever way it landed; it now uses the **faithful** GILE operationalization the corpus demands (not verbalized confidence); the result is **robust across all six domain-weight profiles**; the mechanism check (tail = 100% correct) *explains why* the penalty cannot help; and the scrambled-cap ablation rules out the "unlucky λ/cap" escape — the best cap is simply *no cap*.

**No new principle, candidate, label, mechanism, or falsifier. Canonical count remains 80.**

---

## 5. Reproduce

```bash
cd analyses/uop_abstention
UOP_N=120 UOP_WORKERS=6 python gile_score.py   # resumable; writes gile_scores.jsonl
python gile_analyze.py                          # writes gile_results.json
```

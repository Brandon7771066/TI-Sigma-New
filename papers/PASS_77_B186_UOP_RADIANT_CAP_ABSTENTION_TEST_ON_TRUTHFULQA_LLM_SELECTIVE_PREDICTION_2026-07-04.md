# PASS 77 · B186 — UOP Radiant-Cap over-reach penalty vs. calibrated-threshold baseline: first executed test on LLM selective prediction (TruthfulQA MC1)

**Date:** 2026-07-04
**Status:** empirical test executed · **HONEST NEGATIVE** · no new principle (count **80**)
**Falsifiers touched:** UOP-CAP-EMP-F1 (bears a new **cross-domain negative** data point; remains **OPEN** — this is a different domain from the biological-coupling one it was coined in, so it is an independent negative, not a closure)
**Code:** `analyses/uop_abstention/run_predictions.py` (prediction runner) · `analyses/uop_abstention/analyze.py` (metrics) → `analyses/uop_abstention/results.json`
**Data:** TruthfulQA **MC1** (`analyses/uop_abstention/truthfulqa_mc.json`, 790 questions; exactly one correct option per question). Model queried: **gpt-5** via the project's OpenAI AI-integration gateway. **N = 300** questions scored.

---

## 0. What was promised / what is being tested

The corpus posits a **Radiant Cap** `G* = √(1 − e⁻²) ≈ 0.92987` (Born-shaped form, 2026-06-27): a holistic GILE ceiling above which additional "reach" is penalized by an **over-reach penalty** in the UOP objective `argmax_x [ρ·f_cap(G) + g(H)]`. Every empirical test of the cap so far (B164/B165 on real EEG and actigraphy) either failed to reach the cap or found it non-special. This paper runs the **first test in a domain where the cap region is densely populated and the over-reach penalty is directly actionable**: **LLM selective prediction / abstention.**

**Operationalization.** An LLM answers a multiple-choice question and emits a **verbalized confidence** 0–100 (verbalized-confidence elicitation is an accepted method: Lin, Hilton & Evans 2022; Tian et al. 2023 — used because the gateway does not expose token logprobs). We treat that confidence as the GILE-analogue "reach." A selective predictor answers when its retained score clears a threshold and abstains otherwise. The **UOP claim under test:** penalizing confidence above `G*` (demoting over-confident answers) produces a **better** risk–coverage trade-off than a plain calibrated confidence threshold, **and** the specific value `G*` is special.

**The decisive honesty point, stated up front.** A risk–coverage curve — and its area **AURC** — depends **only on the ranking** of examples by retained score. Therefore any **strictly** monotonic transform of confidence leaves AURC **theoretically invariant** (isotonic regression is only *non-strictly* monotone, so it can create ties whose ordering perturbs AURC by a negligible amount — hence "near-equal," not bit-identical, below). Two consequences:

1. A **tuned raw-confidence threshold (P1)** and an **isotonic-calibrated threshold (P2)** share (up to ties) the *same* ranking as raw confidence (calibration is monotone) ⇒ **near-identical AURC.** Calibration fixes the *probabilities*, not the *order*. So UOP cannot be credited for "being calibrated."
2. The UOP over-reach penalty can differ from a threshold baseline **only because it is non-monotonic** — it pushes very-high-confidence answers *below* the cap. That non-monotone re-ranking is the **only** lever UOP has, and it can help **only if extreme confidence is anti-predictive of correctness.** That is the real, falsifiable question.

---

## 1. Design

- **Prediction runner** (`run_predictions.py`): for each question, shuffle the MC1 options, present them lettered, ask gpt-5 for its chosen letter + a 0–100 confidence; parse, map back to the correct letter, record `is_correct` and `confidence`. Checkpointed/resumable (`predictions.jsonl`), 6 concurrent workers. **300/300 parsed, 0 errors.**
- **Policies** (`analyze.py`), retained-score `s`:
  - **P1** raw-confidence threshold.
  - **P2** isotonic-calibrated probability (fit on a train split), threshold.
  - **P3 (UOP)** over-reach penalty at `G*`: `s = conf` for `conf ≤ G*`; `s = G* − λ(conf − G*)²` (λ = 2) for `conf > G*` — monotone up to the cap, penalized (non-monotone) above.
  - **P3-scramble** (ablation): the same penalty applied at 200 cap positions swept over [0.5, 0.999] to ask whether `G*` is special.
- **Metrics:** AURC (lower better; ranking metric, split-free); ECE (raw vs isotonic); high-confidence-tail accuracy (mechanism check); and an **asymmetric-cost decision** comparison (correct +1, wrong −cost, abstain 0) with the answer-threshold tuned on a train split and evaluated out-of-sample on a test split, for cost ∈ {2, 4, 9}.

---

## 2. Results (`results.json`, N = 300)

| Quantity | Value |
|---|---|
| Overall accuracy | **0.823** |
| Mean verbalized confidence | 0.904 |
| ECE raw | 0.081 |
| ECE isotonic | 0.030 (calibration improves probabilities…) |
| **AURC — P1 raw threshold** | **0.0999** |
| **AURC — P2 isotonic** | **0.0990** (≈ P1 — monotone-invariance confirmed empirically) |
| **AURC — P3 UOP** | **0.1221** (**+0.0222 WORSE** than baseline) |
| `uop_better_than_baseline` | **false** |
| Above-cap answers | 157 / 300 (cap region densely populated) |
| Scrambled-cap AURC min / mean / max | 0.0999 / 0.230 / 0.306 |
| Fraction of scrambled caps **better** than `G*` | **0.15** |
| High-conf tail (≥0.95) accuracy | **0.898** (> 0.823 overall) |
| `extreme_conf_is_anti_predictive` | **false** |

**Reading.**

1. **UOP is worse, not better.** The over-reach penalty raises AURC from 0.0999 to 0.1221. The non-monotone demotion damages the ranking.
2. **The cap value is not special.** In the scrambled-cap sweep the *best* possible "cap" is one set so high that **no answer is penalized at all** — i.e. it recovers the baseline (min AURC 0.0999 = P1). Lowering the cap only injects noise into the ranking (mean AURC 0.230). `G*` itself is beaten by 15% of arbitrary cap positions; nothing marks 0.92987.
3. **The mechanism the penalty needs is absent.** The over-reach penalty could only help if very-high-confidence answers were *less* accurate. They are *more* accurate: the ≥0.95 tail scores 0.898 vs 0.823 overall. gpt-5's extreme confidence is largely earned, so demoting it is counterproductive.
4. **Calibration ≠ UOP.** Isotonic calibration cuts ECE by ~2.7× (0.081→0.030) yet leaves AURC essentially unchanged (0.0990 ≈ 0.0999), empirically confirming the monotone-invariance argument. Any credit UOP might claim via "being better calibrated" is unavailable — calibration and ranking are orthogonal, and UOP's only distinct lever (non-monotonicity) hurts.
5. **Decision test (asymmetric cost, OOS).** At cost 2 and cost 4, **P1 = P2 = P3 give identical test utility, coverage, and selective accuracy** — the optimal operating threshold falls *below* the cap, so the UOP penalty (which only re-orders answers *above* the cap) never changes a single accept/reject decision. At cost 9 P3 shows a hair's-edge utility (−0.127 vs −0.147) but at **collapsed coverage (0.27 vs 0.52)** and a **2-example, single-split** margin — i.e. within noise, and contradicted by the split-free AURC. No honest reading calls this a win.

---

## 3. What this does and does not resolve

- **Does:** provides the first empirical test of the Radiant-Cap over-reach penalty in a domain where the cap is heavily exercised (157/300 answers above it). Verdict: **the penalty does not beat a calibrated threshold, and the specific value G* = √(1−e⁻²) is not special.** This is a genuine risky-prediction failure for the "cap is a special operating point" reading, consistent with the corpus's prior cap/LCC empirical negatives (B164/B165).
- **Does not:** close **UOP-CAP-EMP-F1**. That falsifier was coined for the biological-coupling domain; LLM abstention is a *different* domain, so this is an **independent cross-domain negative**, not a proof that the cap is meaningless everywhere. It also does **not** touch the UOP's *interior-optimum* mathematics (a ZFC-stated lemma), only the empirical claim that penalizing at `G*` improves a real decision.
- **#69, both ways.** *Discount:* one dataset, one model, verbalized (not logprob) confidence, N = 300; a different task where over-confidence *is* anti-predictive could in principle favour the penalty. *Credit for the null:* the test was pre-committed to reporting whichever way it landed, the mechanism check (tail accuracy) explains *why* it failed rather than just that it failed, and the scrambled-cap ablation rules out the "we got unlucky with λ" escape — the best cap is simply *no cap*.

**No new principle, candidate, label, mechanism, or falsifier. Canonical count remains 80.**

---

## 4. Reproduce

```bash
cd analyses/uop_abstention
UOP_N=300 UOP_WORKERS=6 python run_predictions.py   # resumable; writes predictions.jsonl
python analyze.py                                    # writes results.json
```

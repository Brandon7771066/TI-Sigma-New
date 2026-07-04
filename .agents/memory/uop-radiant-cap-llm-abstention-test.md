---
name: UOP Radiant-Cap test on LLM abstention (TruthfulQA)
description: Faithful GILE-based test of the Radiant-Cap over-reach penalty on LLM selective prediction; honest negative + the AURC monotone-invariance argument + why the FAITHFUL GILE operationalization (not verbalized confidence) is required.
---

# UOP Radiant-Cap over-reach penalty on LLM selective prediction (B186)

Test of the Radiant Cap `G*=√(1−e⁻²)≈0.92987` as an over-reach penalty on TruthfulQA
MC1. Verdict: **HONEST NEGATIVE** (robust). Superseded a first attempt (see below).

## FAITHFULNESS REQUIREMENT (why v1 was rejected — reuse for any GILE-cap test)
- A test of the Radiant Cap is only valid if the quantity being capped is an **actual
  canonical GILE composite ∈[0,1]**. **Verbalized confidence 0–100 is NOT GILE** — it
  never touches the tetrad definitions or the domain weights ⇒ v1 was retracted invalid.
- Faithful pipeline: LLM rates each option on the **16 URB #652 sub-dimensions**
  (Four C's / I / L / E, each ∈[0,1]) → dimension = mean of its 4 sub-dims → **MR1 gate**
  `G_raw ≥ ET=√2−1≈0.4142` (else MI-adjacent/abstain) → **domain-weighted composite**
  (TruthfulQA = epistemic ⇒ SCIENTIFIC weights .35/.40/.15/.10 primary; report all 6
  profiles from GILE_WEIGHT_DERIVATION.md as robustness) → select max-GILE passing option.
- One structured call per question scoring ALL options (keeps within-Q comparability,
  ~1 call vs per-option). I3 Pre-evidential Accuracy is a track-record ratio ⇒ can only be
  **rater-estimated** for one-shot answers; flag it as a proxy, don't hide it.

## The load-bearing methodological fact (reuse for ANY selective-prediction test)
- **AURC depends ONLY on the ranking of retained scores.** So a cap/penalty can differ
  from ranking-by-raw-score only via its **non-monotone** demotion of >cap items, which
  helps **IFF the high tail is anti-predictive.** Always check the >cap tail accuracy
  first — if the tail is *more* accurate than overall, the penalty CANNOT help by construction.

## What the faithful test found (N=120, gpt-5, scientific profile primary)
- MR1 abstains **0** questions; selection accuracy **0.858**, essentially weight-invariant
  (0.850–0.858 across all 6 domain profiles) ⇒ the weight choice does not drive the result.
- UOP over-reach penalty (λ=2) at G*: **ΔAURC = 0.00000** (0.08666 = 0.08666) — adds nothing.
- **Cap not special:** scrambled-cap best = the no-penalty baseline; 0% of caps beat G*.
- **Mechanism absent/reversed:** the >cap tail (n=10) is **100% correct** (> 0.858 overall)
  ⇒ extreme GILE is earned, demoting it can only hurt.
- Asymmetric-cost OOS: P1 (GILE threshold) = P3 (UOP) identical at cost 2/4/9 (optimal
  threshold sits *below* the cap ⇒ penalty never flips a decision).

## Guardrails
- Does **not** close UOP-CAP-EMP-F1 (coined for the biological-coupling domain); this is an
  independent cross-domain negative. Don't overclaim closure. Doesn't touch the interior-optimum lemma.
- Code `analyses/uop_abstention/{gile_score.py,gile_analyze.py}` → `gile_results.json`;
  v1 `run_predictions.py`/`analyze.py` kept only as the retracted verbalized-confidence baseline.
- Runner is resumable (gile_scores.jsonl). Calls are heavy (~6k tokens, ~15–20 rows/115s);
  background `nohup … &` gets KILLED when the launching bash call returns ⇒ run resumable
  ~110s chunks in blocking foreground. Gateway exposes no logprobs (don't fabricate).

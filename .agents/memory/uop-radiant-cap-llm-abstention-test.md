---
name: UOP Radiant-Cap test on LLM abstention (TruthfulQA)
description: First test of the Radiant-Cap over-reach penalty in a domain where the cap is densely populated; honest negative + the AURC monotone-invariance argument that constrains any such test.
---

# UOP Radiant-Cap over-reach penalty on LLM selective prediction (B186)

First executed test of the Radiant Cap `G*=√(1−e⁻²)≈0.92987` in a domain where the
cap region is actually exercised (LLM confidence, 157/300 answers above cap), unlike
the biological EEG/actigraphy tests that never reached it. Verdict: **HONEST NEGATIVE.**

## The load-bearing methodological fact (reuse for ANY selective-prediction / abstention test)
- **AURC (risk–coverage area) depends ONLY on the ranking of retained scores.** Any
  strictly **monotone** transform of confidence gives **identical AURC**. So a tuned raw
  threshold and an isotonic-calibrated threshold have the same AURC (confirmed: 0.0999 ≈
  0.0990), even though isotonic cuts ECE ~2.7× (calibration fixes probabilities, not order).
- Therefore a cap/penalty scheme can only differ from a threshold baseline via a
  **non-monotone** re-ranking (demoting >cap answers below the cap). That lever helps
  **IFF extreme confidence is anti-predictive.** Always check the high-conf tail accuracy
  first — if the tail is *more* accurate than overall, the penalty CANNOT help by construction.

## What the test found
- UOP over-reach penalty (λ=2) at G* is **worse**: AURC 0.1221 vs baseline 0.0999.
- **Cap not special:** scrambled-cap ablation's best "cap" = one so high nothing is
  penalized (= baseline); 15% of arbitrary caps beat G*. Nothing marks 0.92987.
- **Mechanism absent:** ≥0.95 tail accuracy 0.898 > 0.823 overall ⇒ high confidence is earned.
- Asymmetric-cost OOS decision test: P1=P2=P3 identical at cost 2 & 4 (optimal threshold
  sits *below* the cap so the penalty never flips a decision). The lone cost-9 "edge" is a
  2-example single-split collapsed-coverage artifact — do not report it as a win.

## Guardrails for redoing / extending
- Verbalized confidence used because the AI gateway exposes **no logprobs** (legit: Lin/
  Hilton/Evans 2022, Tian 2023) — don't fabricate logprobs.
- This does **not** close UOP-CAP-EMP-F1 (coined for the biological-coupling domain);
  it's an independent cross-domain negative. Don't overclaim closure.
- Code `analyses/uop_abstention/{run_predictions.py,analyze.py}`; runner is resumable
  (predictions.jsonl) — background `nohup … &` gets KILLED when the launching bash tool
  call returns, so run resumable chunks in blocking foreground (~115s each) instead.

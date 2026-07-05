---
name: LCC/OET dialogue empirical test (user↔chatbot)
description: First LCC coupling test on human↔AI conversation threads — honest negative; why, and the reusable gotchas.
---

# LCC/OET on user↔chatbot dialogue (B189, 2026-07-04) — HONEST NEGATIVE

First execution of the user's Phase-I LCC/OET dialogue scaffold on outcome-bearing
multi-turn human↔AI data. Result fits the whole LCC empirical record: no signal, index
doesn't beat a similarity baseline, constants never approached.

## The three-part result (all point the same way)
- **Synthetic method-validation FAILS** — the RAS coupling statistic misses ground-truth
  reciprocal coupling (p=0.16) yet FIRES on common-input confound (p<0.001). So the
  instrument can't tell coupling from shared drive ⇒ a real-data null is *expected* and any
  real-data "positive" would be uninterpretable. **This is the key finding** — the null is
  explained, not merely observed.
- **hh-rlhf (n=86): clean null** — paired Wilcoxon all p>0.5; CV AUC ≤ chance; **C+RAS ≈
  C_only** (RAS adds nothing over adjacent similarity); hybrid not better; surrogate p=0.12.
- **mt_bench: untestable** — 4-message exchanges = 2 turns/speaker; predictive-gain needs
  ≥3–4 turns/speaker ⇒ 0 usable pairs. Parallels OET's τ-floor untestability (B178).

## Reusable gotchas (why the harness kept stalling)
- **Surrogate is the cost bomb.** RAS surrogate = n_surr × chimeras × LOO-Ridge. Cap chimeras
  (≤30), n_surr (≤25 synthetic, ≤25 real), and use holdout (not LOO) once a conv has >6 turns.
- **TF-IDF+SVD embedding, not MiniLM** — `torch`/`sentence_transformers` uninstallable here;
  cleanest conversational sets (LMSYS-Chat-1M, Chatbot-Arena) are HF-**gated** (no token);
  `daily_dialog` dead; li2017 mirror runs arbitrary code. Substituted `Anthropic/hh-rlhf` +
  `lmsys/mt_bench_human_judgments` (ungated parquet). Flag the proxy embedding as a discount.
- **Short exchanges are structurally unusable** for turn-dynamics/coupling metrics — check
  turns-per-speaker BEFORE embedding a whole corpus.

## Honesty framing
No new principle/candidate/label/mechanism. Bears cross-domain negatives on LCC-EMP-F1 (again)
and LCC-HYB-F1 (2nd) — both stay OPEN (text-dialogue ≠ biological-coupling domain; independent
negatives, NOT closures). Undercredit banned: index is *unsupported here*, not false in
principle. Files: `analyses/lcc_dialogue/{phase1_lcc_dialogue_pipeline.py,RESULTS.md}` (data
git-ignored). Constants stay untested — gate-first: only test √2−1/≈0.6/cos²(π/8) after outcome
gates pass (they didn't).

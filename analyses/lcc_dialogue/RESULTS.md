# LCC/OET on User↔Chatbot Dialogue — Phase I Results (B189, 2026-07-04)

**Verdict: HONEST NEGATIVE (method-invalidation + real-data null + decisive-part-untestable).**
Consistent with the entire LCC empirical track record (ds007471, Depresjon, OET/ds007471):
the coupling index does not track a real outcome, does not beat a matched similarity
baseline, and its named constants are never approached.

## What was tested
Adaptation of the user's "Phase I LCC/OET dialogue" scaffold (`attached_assets/Pasted-...1783211639895.txt`)
to **outcome-bearing, multi-turn human↔AI conversation** datasets.

- **Embedding:** TF-IDF + TruncatedSVD (256-d) per-corpus. This is a **MiniLM proxy**, flagged
  as such — `sentence-transformers`/`torch` are not installable in this environment, and the
  gated conversational sets (LMSYS-Chat-1M, Chatbot-Arena) require an HF token we do not have.
- **Metrics:** C (adjacent cosine similarity), S (self-continuity), **RAS** (Reciprocal
  Autoregressive Score = the bidirectional predictive-gain coupling index: does turn `t` from
  speaker X predict speaker Y's next turn *beyond* Y's own past?), plus the candidate composites
  `L_add`, `L_geo`, `L_hybrid` (additive+geometric, per B157).
- **Outcome tests (pre-registered, gate-first):** paired Wilcoxon on (winner − loser); 5-fold
  **GroupKFold (grouped by prompt-pair, so a winner and its loser never split across folds)**
  CV OOS AUC winner-vs-loser with a **C-only matched control**; cross-conversation **surrogate
  RAS null**; **synthetic reciprocal / common-input / independent** method-validation controls.

### Datasets (ungated substitutes; the user's originals were dead/gated — see notes)
- `Anthropic/hh-rlhf` (chosen/rejected preference pairs; branches often share a prefix).
- `lmsys/mt_bench_human_judgments` (conversation_a/b + human winner; independent branches).

## Results

### 1. Synthetic method-validation — **the instrument fails its own check**
| ground truth | real RAS | surrogate | p(real≥surr) | reading |
|---|---|---|---|---|
| **reciprocal** (true X↔Y coupling) | 0.0183 | 0.0169 | **0.16** | **NOT detected** — underpowered even on ground-truth coupling |
| **common-input** (shared latent, no edge) | 0.0108 | 0.0054 | **0.000** | **FALSE POSITIVE** — flags shared drive as "coupling" |
| independent (AR noise) | 0.0112 | 0.0117 | 0.64 | correct null |

The RAS statistic **cannot reliably separate true reciprocal coupling from common input** at
this embedding/scale: it misses the real positive (p=0.16) yet fires on the confound (p<0.001).
⇒ **any real-data "positive" on this instrument would be uninterpretable**, and a real-data
null is the expected outcome. (This is the standard LCC lesson — the naive statistic is
confoundable; only a confound-controlled statistic isolates the claim.)

### 2. hh-rlhf (n = 86 usable pairs) — **clean null**
- Paired Wilcoxon (winner − loser): **every** metric p > 0.5 (C .69, S .72, RAS .69,
  L_add .77, L_geo .85, L_hybrid .52); no separation. RAS is ~0 for most pairs
  (frac winner-higher = 0.10 → mostly ties/zeros).
- CV OOS AUC (winner vs loser), **GroupKFold grouped by prompt-pair (no pair-level
  leakage)**: all **≈ chance** — C_only **0.481**, **C+RAS 0.457** (RAS does *not* beat
  similarity — slightly worse), L_hybrid **0.501** (exactly chance), L_add 0.461, all 0.448.
- Surrogate RAS null: real 0.00096 vs surr 0.00032, **p = 0.12** (n.s.).
- **Caveat:** small N — hh-rlhf branches are short and share prefixes, so most pairs are
  unusable for a turn-dynamics metric. Low power, but the direction is unambiguous (no signal).

### 3. mt_bench_human — **decisive part untestable**
All qualifying exchanges are exactly **4 messages = 2 turns per speaker**. A reciprocal
predictive-gain metric needs an autoregression with a holdout (≥3–4 turns/speaker), so
**0 pairs are usable**. This is a structural limitation of short exchanges, not a bug —
directly parallel to the OET result on ds007471 (0/1278 trials reached τ; the novel indexing
was untestable).

## Scorecard of the 4 pre-registered predictions
1. **RAS beats adjacent-similarity for outcome** → **FALSE** (C+RAS ≈ C_only; RAS ≈ 0).
2. **hybrid > additive LCC index** → **FALSE** (both ≤ chance; hybrid not meaningfully better).
3. **OET organizational > matched-capacity separable** → **NOT ESTABLISHED.** This Phase I
   harness implements the **LCC coupling** test on dialogue, *not* a full OET whole-vs-parts
   decomposition; do **not** claim OET was tested here. (OET's own first test, B178, was itself
   negative/untestable on dual-EEG.)
4. **thresholds/constants localize near √2−1, ≈0.6, cos²(π/8)** → **NOT REACHED.** No positive
   signal to threshold; the Radiant Cap and the LCC rungs are never approached — same as every
   prior LCC empirical test. Constants remain **untested** (gate-first: test constants only
   after all outcome gates pass; they did not).

## Honest scope (#69 both ways)
- **Discount:** TF-IDF+SVD is a weaker embedding than MiniLM (semantic coupling may be
  under-captured); small usable N (hh); the cleanest datasets were gated/unavailable; one
  environment, no GPU.
- **Credit-for-null:** the negative is *pre-registered*, *matched-controlled* (C-only baseline,
  cross-conversation surrogate), and — crucially — the **synthetic control explains the null**:
  the instrument provably cannot tell coupling from common input, so the real-data flatness is
  the predicted result, not merely "no signal found." Undercredit is banned as strictly as
  overcredit: the metric is not *shown false in principle*, only unsupported here.
- **Falsifiers:** bears an additional cross-domain negative on **LCC-EMP-F1** and a 2nd negative
  on **LCC-HYB-F1** (both stay OPEN — dialogue text ≠ the biological-coupling domain LCC was
  coined in; these are independent negatives, not closures). No new principle, candidate, label,
  or mechanism. Canonical count unchanged by this test (the count change this batch is the
  separate FTE-1 → #81 ratification).

## Reproduce
```
python analyses/lcc_dialogue/phase1_lcc_dialogue_pipeline.py --max_pairs 400
```
Data (`analyses/lcc_dialogue/data/*.parquet`) is git-ignored; re-download from HF
(`Anthropic/hh-rlhf`, `lmsys/mt_bench_human_judgments`).

### Environment / dataset-availability notes (honest record)
- `datasets` library will **not** install (uv / py3.14 marker conflict) — do not retry.
- `torch` / `sentence_transformers` absent ⇒ TF-IDF+SVD proxy embedding.
- User's target sets blocked: `daily_dialog` renamed/dead; the li2017 mirror runs arbitrary
  code (no parquet); `lmsys/chatbot_arena` + `LMSYS-Chat-1M` are **gated** (no HF token).

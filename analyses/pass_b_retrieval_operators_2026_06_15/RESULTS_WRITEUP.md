# Retrieval-Operator Benchmark — Results (leakage-safe)

**Run date:** 2026-06-16 · **Code:** this directory · **Raw:** `results.json`

## Task
Cross-channel **hidden-state retrieval**. A latent state H is defined from a
held-out channel group (group A); operators must retrieve H from a **disjoint**
group (group B). Cross-group coupling is real (resonance necessary), but H is not
directly visible (a retrieval operator may be needed). Temporal-block split
(first 60% train / last 40% test).

## Leakage controls (applied after first-pass review)
1. **Target built train-only.** On real data the latent is k-means clustered on
   **train** group-A windows; test windows are labeled by nearest **train**
   centroid. Test data never influences the target definition.
2. **Block-split filtering.** Theta/gamma bandpass + Hilbert analytic signals are
   computed independently for the train block and the test block, so no
   (acausal) filter spans the split boundary.
3. **Matched-feature baseline (P0b).** A nearest-centroid classifier on the SAME
   rich feature vector the operators see, but with NO active mechanism. This
   separates "active retrieval machinery" from "richer features."

## Two baselines
- **P0 passive resonance** — single scalar resonance-magnitude readout only.
- **P0b matched** — nearest class-centroid on the full feature vector (no mechanism).

## Leaderboard (balanced accuracy; chance = 0.333)

| Operator | sim0 | sim7 | mouse41 (live) | mouse20 (live) | **mean** |
|---|---|---|---|---|---|
| C2 cross-attn→TI-Sigma-AI prior | 0.878 | 0.673 | 0.488 | 0.869 | **0.727** |
| O3 reverse-osmosis | 0.811 | 0.685 | 0.512 | 0.870 | 0.720 |
| **P0b nearest-centroid (matched)** | 0.840 | 0.597 | **0.524** | **0.913** | **0.719** |
| C1 ensemble vote | 0.808 | 0.685 | 0.500 | 0.880 | 0.718 |
| O4 TI-Sigma Active Inference | 0.792 | **0.735** | 0.464 | 0.846 | 0.709 |
| O2 Hopfield descent | 0.801 | 0.546 | 0.476 | 0.835 | 0.665 |
| O1 cross-attention | 0.874 | 0.498 | 0.488 | 0.758 | 0.655 |
| **P0 passive resonance** | 0.390 | 0.261 | 0.393 | 0.486 | **0.383** |

Significance (paired bootstrap, 95% CI excludes 0):
- **vs P0 (resonance-magnitude):** every operator wins on sim0, sim7, mouse20;
  **none** wins on mouse41 (that animal is only weakly decodable at all).
- **vs P0b (matched features):** the ONLY significant win anywhere is **O4
  TI-Sigma Active Inference on sim7 (+0.139)**. On live data every operator's
  Δ vs P0b is negative or non-significant.

## Findings (honest)
1. **The Retrieval Gap is real — but for the bare resonance-magnitude readout
   only.** P0 sits at/near chance on 3 of 4 sources (0.390, 0.261, 0.393).
2. **The gap is closed by richer features, not by a clever mechanism.** A
   matched-feature nearest-centroid (P0b) jumps to 0.72 mean and is the **top
   method on both live mice**. The elaborate operators cluster around the same
   0.71–0.73 mean and are statistically indistinguishable from it.
3. **One genuine operator win:** TI-Sigma Active Inference (O4) is the only method
   to significantly beat the matched baseline, and only on the hardest synthetic
   cross-frequency task (sim7, where simple centroid struggles). O4 also wins sim7
   outright. This advantage does **not** carry to the (weak/strong) live cases.
4. **Live decodability is heterogeneous:** mouse20 is highly separable (P0b 0.913);
   mouse41 is only weakly above chance for any method (best 0.524, wide CIs).

## Bottom line for the program
Invest in the **right coupling features** (PAC / PLV / band structure), not in
baroque retrieval machinery — a feature-matched nearest-centroid already captures
nearly all retrievable structure on real neural data. The TI-Sigma Active
Inference operator earns a narrow, real, but not-yet-generalizing edge on hard
cross-frequency regimes; that specific regime is where it deserves further
targeted testing.

## Honest limitations (#69)
- Live latent is **label-free k-means**, not behavioral ground truth; mitigated by
  disjoint A/B groups + train-only clustering, but residual structure-sharing
  remains a caveat.
- Only **2 animals**, both DANDI:000003; small live test sets (58 windows) → wide
  CIs (esp. mouse41). Broadening datasets is the top next step.
- sim0's temporal test block contained no class-1 windows (`[53,0,75]`); balanced
  accuracy there averages over the 2 present classes.
- Operators are light / non-parametric; this compares **mechanisms**, not maximal
  achievable accuracy.

## Reproduce
```bash
cd analyses/pass_b_retrieval_operators_2026_06_15 && python runner.py
```

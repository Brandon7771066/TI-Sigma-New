# Closing the Retrieval Gap? A Leakage-Safe, Matched-Control Benchmark on Live Animal Neural Data

**Author:** Brandon Charles Emerick
**Part of:** The TI Sigma / Mood Amplifier Program
**Date:** June 2026
**Status:** Empirical result. Acts on Recommendation #1 of the June 2026 Bottleneck Survey
(`papers/BOTTLENECK_SURVEY_UNSUPERVISED_MOOD_AMPLIFIER_LCC_VIRUS_2026-06-15.md`).
**Code & data:** `analyses/pass_b_retrieval_operators_2026_06_15/` (`runner.py`, `results.json`).

---

## In Plain Language

The bottleneck survey named one obstacle above all others: the **Retrieval Gap**.
Two systems can be made to *resonate* (sync up), but being in sync is not the same
as being able to **read information out** of the other system. The survey's top
recommendation was a concrete test: hold the resonance fixed, bolt different
"retrieval mechanisms" on top, and see which (if any) recovers hidden information
that plain resonance cannot.

This document runs that test — on **real animal brain data streamed live** from a
public neuroscience archive (two mice from the Buzsáki lab), backed by controlled
simulations where the right answer is known. A hidden brain "state" is defined from
one set of recording channels; each mechanism must guess it using only a
**different, non-overlapping** set of channels.

Five approaches were compared: plain resonance (baseline), a transformer-style
**cross-attention** reader, a **Hopfield** memory, a **reverse-osmosis** model, and
a new **TI-Sigma Active Inference** operator built from this program's own ideas
(UOP + i-Cell). Combinations were tested too.

**The honest result — including a correction to my own first pass:**

1. **The Retrieval Gap is real, but only for the *crudest* readout.** A bare
   "how strongly are we synced?" magnitude score is at chance. So *something* more
   than a sync-meter is needed — that part of the survey's thesis holds.
2. **But the gap is closed by better *features*, not by clever *machinery*.** When
   I gave a dead-simple classifier (nearest-average) the *same rich features* the
   fancy operators use, it matched or **beat every elaborate operator on both live
   mice.** Most of the apparent "operator magic" in my first analysis was just the
   benefit of measuring the right things (cross-frequency coupling, phase locking),
   not the sophistication of the retrieval step.
3. **One real exception.** The TI-Sigma Active Inference operator is the *only*
   method that significantly beats the matched-feature control — and only on the
   hardest *simulated* case, where the simple classifier struggles. That is a
   narrow, genuine, but not-yet-proven-on-real-data win.

I also caught and fixed two ways my first analysis could have fooled itself
(detailed below): the hidden labels were originally allowed to peek at the test
data, and the signal filtering smeared information across the train/test boundary.
After fixing both, the flashier "operators dominate" story collapsed into the more
honest "matched features dominate; one operator shows promise on hard cases."

Caveats up front: only two animals, both from one archive; the hidden state on real
data is a statistical cluster, not a vet-verified behavior; and the two animals
behaved very differently (one highly decodable, one barely). So this is a careful,
reproducible *demonstration and correction* — not a large-sample proof.

---

## 1. Background and Hypotheses

The Retrieval Gap (Bottleneck Survey §3): for both the LCC Virus (information
retrieval) and the unsupervised mood amplifier (directed state change), **resonance
above threshold is necessary but not sufficient**; the missing ingredient is an
actively-passive (Tralse) retrieval operator that extracts structure once coupling
is established.

- **H1:** A passive resonance-*magnitude* readout retrieves a coupled hidden state
  at ≈ chance, while applying a retrieval step to the same coupled signal does
  better.
- **H2:** The TI-Sigma–upgraded Active Inference operator (UOP + i-Cell) and/or
  operator combinations outperform any single off-the-shelf operator.
- **H3 (the control that decides it):** Do the operators beat a **matched-feature**
  baseline — the same features, no active mechanism? If not, the gain is from
  features, not from retrieval machinery.

## 2. Method

### 2.1 The retrieval task
A latent `H ∈ {0,1,2}` is associated with each window. Channels split into disjoint
groups **A** and **B**. `H` is *defined* on group A; each operator *predicts* `H`
from group B only. Coupling makes resonance necessary; B never sees A's defining
features, so a retrieval step is required. **Temporal block split** (first 60% /
last 40%, no shuffling).

- **Simulated (ground truth):** `H` drives theta–gamma phase–amplitude coupling
  strength and preferred phase — **not** band power — so a power/resonance-magnitude
  readout is intentionally weak. Two seeds, 319 windows each.
- **Live (DANDI:000003, Buzsáki lab):** `sub-YutaMouse41` and `sub-YutaMouse20`
  hippocampal recordings, streamed (DandiAPIClient + remfile + h5py), 8 ch @ 250 Hz,
  143 windows each. `H` = label-free k-means(3) on group-A features (no behavioral
  labels available).

### 2.2 Features (group B, per window)
Five log band-powers (δ θ α β γ), spectral entropy, theta–gamma PAC per channel,
plus mean gamma-PLV across observed pairs. Formulas reused from the corpus rodent
notebooks (`pass77_b4`, `pass77_b67`) and the LCC resonance form; ported
self-contained.

### 2.3 Leakage controls (added after first-pass code review)
A first-pass review of this benchmark flagged two ways the "no leakage" claim could
fail. Both are fixed in the reported run:

1. **Target leakage (fixed).** Originally the real-data k-means latent was fit on
   *all* group-A windows, letting test windows shape the target. Now k-means is fit
   on **train** group-A only and test windows are labeled by the nearest **train**
   centroid.
2. **Acausal filter bleed (fixed).** Zero-phase (`sosfiltfilt`) + Hilbert over the
   full signal mixes future into past across the split. Now theta/gamma analytic
   signals are computed **independently per train block and test block**, so no
   filter spans the boundary.
3. **Matched-feature baseline (added).** See §2.4 P0b — the decisive control for H3.

### 2.4 Operators (identical front-end, different retrieval mechanism)
- **P0 — Passive resonance (baseline).** Nearest-prototype on one scalar: mean
  Gaussian-weighted max-lag LCC of group-B channels to a fixed theta probe. The
  "are we coupled?" reading and nothing more.
- **P0b — Matched-feature nearest-centroid (control).** Nearest class-centroid on
  the FULL feature vector, no active update. Isolates features from mechanism.
- **O1 — Cross-attention.** Numpy Q-K-V softmax readout over training windows.
- **O2 — Hopfield energy-descent.** Modern continuous Hopfield → nearest attractor.
- **O3 — Reverse-osmosis (i-boundary `z = s + i·a`).** Imaginary channel `a`
  (active belief / conscious pressure) gates membrane permeability, pulling
  belief-consistent flux across.
- **O4 — TI-Sigma Active Inference (UOP + i-Cell).** Tralse generative model
  (class-conditional Gaussians = preferred states) with **GILE-weighted priors**,
  **LCC precision-weighting** (precision scaled by resonance / C_EMERICK),
  **GTFE gap-closure** (iterated feature-precision steps), and **Myrion-Resolution
  collapse** (collapse to MAP only when coherent; else resolve toward the prior).
- **Combinations.** **C1** ensemble majority vote (O1–O4); **C2** cross-attention
  posterior supplies O4's per-window prior (stacking).

### 2.5 Metrics
Balanced accuracy vs chance = 1/3; 95% bootstrap CIs; paired bootstrap Δ vs
**both** baselines (P0 and P0b), significant if the 95% CI excludes 0.

## 3. Results

### 3.1 Leaderboard (balanced accuracy; chance = 0.333)

| Operator | sim0 | sim7 | mouse41 (live) | mouse20 (live) | **mean** |
|---|---|---|---|---|---|
| C2 cross-attn → TI-Sigma-AI prior | 0.878 | 0.673 | 0.488 | 0.869 | **0.727** |
| O3 reverse-osmosis | 0.811 | 0.685 | 0.512 | 0.870 | 0.720 |
| **P0b nearest-centroid (matched)** | 0.840 | 0.597 | **0.524** | **0.913** | **0.719** |
| C1 ensemble vote | 0.808 | 0.685 | 0.500 | 0.880 | 0.718 |
| O4 TI-Sigma Active Inference | 0.792 | **0.735** | 0.464 | 0.846 | 0.709 |
| O2 Hopfield descent | 0.801 | 0.546 | 0.476 | 0.835 | 0.665 |
| O1 cross-attention | 0.874 | 0.498 | 0.488 | 0.758 | 0.655 |
| **P0 passive resonance** | 0.390 | 0.261 | 0.393 | 0.486 | **0.383** |

### 3.2 H1 — the Retrieval Gap (confirmed, for the magnitude readout)
The bare resonance-magnitude baseline (P0) is at/near chance on sim0 (0.390),
sim7 (0.261) and live mouse41 (0.393), and only marginally above chance on mouse20
(0.486). Every operator significantly beats P0 on sim0, sim7 and mouse20; **none**
beats it significantly on mouse41 (that animal is only weakly decodable by any
method). So a sync-meter alone is insufficient — but "insufficient" is the easy bar.

### 3.3 H3 — the matched-feature control (the decisive test)
**This overturns the naïve reading of H2.** A nearest-centroid classifier on the
*same features* (P0b) reaches 0.719 mean and is the **top method on both live
mice** (mouse41 0.524, mouse20 0.913). The elaborate operators cluster at the same
0.71–0.73 mean and are **statistically indistinguishable** from it. The only
significant win over P0b anywhere is **O4 (TI-Sigma AI) on sim7 (+0.139, CI excl.
0)**; on live data every operator's Δ vs P0b is negative or non-significant.

Interpretation: most of the lift over the resonance-magnitude baseline is the
benefit of **richer coupling features** (PAC / PLV / band structure), not of any
sophisticated retrieval mechanism.

### 3.4 H2 — TI-Sigma operator and combinations (nuanced)
- TI-Sigma Active Inference (O4) **wins the hardest simulation outright** (sim7,
  0.735) and is the **only** operator to significantly beat the matched control —
  but only there. It is the backbone of the best-mean combo (C2). On live data it
  is mid-pack and does not beat P0b.
- Combinations top the *mean* table (C2 0.727) but their edge over the matched
  baseline is not significant; the ranking among C2 / O3 / P0b / C1 / O4 is a
  near-tie.
- No mechanism is best everywhere. The heterogeneity, plus P0b's strength, is the
  honest headline.

## 4. Interpretation

Reframed conclusion: the Retrieval Gap is genuine **for a crude resonance-magnitude
readout**, but on real neural data it is closed by *measuring the right coupling
features*, not by elaborate retrieval machinery — a feature-matched nearest-centroid
captures nearly all retrievable structure. For the unsupervised mood amplifier and
the LCC Virus, the actionable lesson is: **prioritize the coupling-feature
front-end** (cross-frequency coupling, phase locking) over baroque operators. The
TI-Sigma Active Inference operator earns a narrow, real edge on hard cross-frequency
regimes (where simple centroids fail); that regime — not generic decoding — is where
it deserves dedicated follow-up.

## 5. Limitations (#69 discipline)

- **Two animals, one archive.** Both live sources are DANDI:000003. The loader also
  targets 001044 / 000552; broadening would tighten the wide live CIs (n_test = 58,
  esp. mouse41).
- **Label-free latent on real data.** `H` is a k-means cluster, not a vet-verified
  behavioral state. Train-only clustering + disjoint A/B reduce but do not eliminate
  shared-structure circularity. A confirmatory version should use curated
  Wake/NREM/REM labels where available.
- **Heterogeneous animals.** mouse20 is highly decodable; mouse41 barely above
  chance for any method — single-animal conclusions are unsafe.
- **Split artifact.** sim0's temporal test block contained no class-1 windows;
  balanced accuracy there averages over the two present classes.
- **Light operators.** Non-parametric / lightly tuned; this compares *mechanisms*,
  not maximal achievable accuracy. The TI-Sigma operator's only significant edge is
  on one synthetic regime — stated plainly, not oversold.
- **Self-correction noted.** The first pass of this benchmark reported a stronger
  "operators dominate / combination wins" story; that was partly leakage + a missing
  matched control. This version is the corrected record.

## 6. Next Steps

1. Add ≥4 more live animals across DANDI:001044 / 000552 / 000776 (tighten CIs).
2. Re-run with curated behavioral-state labels (removes the cluster-latent caveat).
3. **Stress-test O4 specifically on hard cross-frequency regimes** (where it beat
   the matched control) rather than generic decoding.
4. Carry the *feature front-end* (PAC/PLV/band) — not the operator zoo — into the
   LCC Virus retrieval loop and the amplifier's steering stage, then re-test against
   the Drift-Index (open-loop Granger) confirmation (Survey Recommendation #2).

---

### Appendix — Reproduction
```bash
cd analyses/pass_b_retrieval_operators_2026_06_15
python runner.py        # streams live DANDI:000003 + simulations; writes results.json
```
Operators: `operators.py` · Features (leakage-safe block-split): `features.py` ·
Simulator: `simulate.py` · Live loader: `data_dandi.py` · Runner/metrics: `runner.py`.

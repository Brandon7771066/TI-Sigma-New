# PASS 77 · B164 — LCC-as-Landscape-Topology / UOP-as-Attractor Bridge + First Real-Data Empirical Test (OpenNeuro ds007471 joint-agency hyperscanning)

**Date:** 2026-07-01
**Batch:** B164 · Ledger §7.7.348
**Canonical principle count:** **80** (UNCHANGED — this batch adds a *framing refinement* to the existing LCC/UOP principles plus an *empirical test*; it ratifies no new principle.)
**Status of the two deliverables:**
1. **Conceptual bridge (ADOPTED as framing refinement):** LCC = the *topology of the coupling-regime landscape* (its thresholds are **bifurcation points**); UOP = the **attractor / global optimum on that landscape**.
2. **Empirical test (EXECUTED on real EEG; result = HONEST NEGATIVE):** ChatGPT's Phase I/II/III preregistered-style tests on OpenNeuro **ds007471** do **not** support the LCC-hybrid-index or Radiant-Cap-optimum predictions on this dataset. The central falsifiable claim (`L_hybrid` beats raw correlation) is **falsified here**.

Honesty rails observed throughout (EVD-1, #69 both-ways, resonance≠derivation, no numerology, REAL data only): the negative is reported as loudly as any positive would have been; both a *theory-limitation* and a *measurement-limitation* reading are stated; no constant is upgraded on the strength of a coincidence.

---

## Part 1 — The conceptual bridge (adopted)

### 1.1 The decomposition
ChatGPT's observation, adopted verbatim as a framing:

> **LCC determines the topology of the landscape. UOP determines the optimum on that landscape.**

The two theories describe **different mathematical objects**:

| Theory | Question it answers | Object |
|---|---|---|
| **LCC** | *Where do new dynamical (coupling) regimes appear?* | **Bifurcation points** — the thresholds (√2−1, 0.437, 0.6, 0.707, 0.75, cos²(π/8), …) mark transitions in the coupling landscape's geometry. |
| **UOP** | *Which regime is globally optimal?* | **Attractor / interior optimum** — the Radiant Cap G*=√(1−e⁻²)≈0.9299 selects the preferred region of that landscape. |

This is **stronger** than the older "UOP is the endpoint of LCC" gloss: LCC and UOP are **complementary**, not sequential. LCC describes the *state space* of coupling transitions; UOP is the *selection principle* defined over it — first describe the space, then propose the principle that picks preferred states.

### 1.2 Consequences for the corpus
- **No new principle, no count change.** This refines how the *already-canonical* LCC (Law of Correlational Causation, composition ruling 2026-06-27; B155/B157) and UOP (B133/B134/B147; Radiant Cap ruling 2026-06-27) relate. It sits alongside, and is consistent with, the **Truth↔Existence pillar separation** (LCC ladder on the Existence/real axis; UOP cap on the Truth/imaginary axis).
- **Recommended book ordering (adopted as guidance, not yet executed):** present **LCC first** as the dynamical theory of coupling transitions (the landscape), **then** UOP as the optimization principle over that landscape (the attractor). Mirrors how many scientific theories are built (state space → selection principle).
- **Falsifier LCC-UOP-BRIDGE-F1 (OPEN):** if the LCC thresholds turn out **not** to be bifurcation points of any well-posed coupling dynamics (i.e. they are static cutoffs with no regime change on either side), the "topology" half of the decomposition collapses to relabelling and must be withdrawn. The empirical test below (Phase II) is a first, dataset-specific probe of exactly this — and it did **not** find bifurcation-like breaks (see §2.5).

### 1.3 The new lower-ladder candidate 1/(√2·φ) ≈ 0.437 (recorded, NOT ratified)
A new candidate constant was proposed: `C = 1/(√2·φ) ≈ 0.437016` (φ = golden ratio), read as "minimal **balanced** recursive coupling across two orthogonal dimensions" — √2 = two-axis/orthogonal coupling, φ = optimal recursive proportion. Proposed role: refine the lower transition zone `0.414 → 0.437` (recursive *onset* → balanced recursive *stability*).

**Ruling (#69):** 0.437 is recorded as a **HAN-1 resonance** — graded EVD-1 evidence, *not* zero-weight but *not* a derivation. It is a numerological-adjacent construction (a product of two "meaningful" constants) and must **earn** its place by an independent empirical change-point, exactly like every other rung. It was included in the Phase II test below and **did not** mark a break (§2.5). It therefore remains a **candidate needing validation**, not a canonical rung. Falsifier **LCC-437-F1 (OPEN):** 0.437 must, on some real coupling dataset, mark a *distinct* stable-cross-prediction transition that √2−1 does not; absent that, it is redundant with √2−1 and is dropped.

---

## Part 2 — The empirical test (executed; honest negative)

### 2.1 Dataset
**OpenNeuro ds007471** — joint-agency EEG hyperscanning. 32 interacting **pairs**, dual-EEG recorded simultaneously (64 channels, INT16, **multiplexed**: ch 1–32 = one brain, 33–64 = the other; channel-suffix labels `_R`/`_L` were trusted over the README, whose description is swapped). A drumming/synchronization joint-action task with two conditions per block — **duet** (interactive, S10 marker, cond=1) vs **constant** (non-interactive metronome, S11, cond=0). Behavioural file (`behavioural_all.tsv`, whitespace-delimited, 2560 rows) supplies, per trial, **Joint Agency Rating** and **Mean Synchronization Performance** — i.e. the outcome variables already exist; we did not invent them.

**Why this dataset (per ChatGPT):** it already contains three quantities LCC says should matter — simultaneous dual EEG, joint-agency ratings, and an objective synchronization measure — making it "the strongest empirical path identified so far."

### 2.2 Pipeline (real, reproducible; `analyses/lcc_uop_openneuro/`)
- **Alignment** (`extract_features.py`): test-phase trials segmented from the `.vmrk` markers; blocks delimited by S107; each block's condition read from its S10/S11 marker. Because some recordings carry extra **practice blocks** and conditions are **counterbalanced** across pairs (some start duet, some constant), EEG blocks are aligned to behavioural blocks by **matching the condition sequence** (sliding offset, best agreement), not by raw position. Validated: aligned condition sequence == behavioural condition sequence for **all 32 pairs** (`cond_ok=True`). Last *k* full windows per block → that block's *k* behavioural trials. **1278 aligned test trials** total.
- **Coupling features**, per trial × band {delta, theta, alpha, beta}, over 6 midline/central ROIs (Fz, FCz, Cz, C3, C4, Pz), inter-brain on homologous ROIs:
  - **C** = inter-brain **PLV** (phase-locking value) — coherence.
  - **P** = **bidirectional linear-Granger** predictive gain, min of the two directions — mutual predictivity.
  - **S** = windowed inter-brain **phase-difference stability** — synchronization stability.
- **Indices** (ChatGPT's forms, inputs min-max scaled): `L_add` (equal-weight additive), `L_geo` (geometric), `L_hybrid = α·L_add + (1−α)·L_geo`, α=0.5 (B157 hybrid). Baseline = **raw C alone** (the matched control ChatGPT's own falsifiable claim names).
- **Inference:** leave-**pair**-out cross-validation R² (out-of-fold, pooled) + **pair-cluster bootstrap** 95% CI (single-predictor OLS reduced to closed form over per-pair moments — R² of one predictor is affine-invariant, so global scaling is harmless). Change-points by **AIC**. Common-input confound controlled by **cross-pair surrogates** (`surrogate.py`).

### 2.3 Manipulation check FIRST — does the coupling even track the task?
Paired (within-pair) **duet − constant** difference for each coupling measure/band (do the neural measures respond to the interaction manipulation at all?):

| measure·band | mean(duet−const) | t (df≈31) | p |
|---|---|---|---|
| C_delta | −0.0039 | −1.10 | 0.28 |
| P_delta | +0.0315 | +1.56 | 0.13 |
| S_delta | +0.0032 | +0.38 | 0.71 |
| P_theta | −0.0085 | −1.40 | 0.17 |
| (all other C/P/S × band) | ~0 | \|t\|<0.9 | >0.4 |

**None** of the 12 coupling measures significantly distinguishes duet from constant (all p ≥ 0.13). **The coupling operationalization does not detectably track the task manipulation.** This is the first and most important negative: whatever LCC-index we build on top of C/P/S is standing on a substrate that itself shows no interaction signal here.

### 2.4 Phase I — does LCC beat raw correlation? (leave-pair-out CV R²)
Predicting **joint-agency** and **sync-quality** (= 1 − asynchrony) from each index alone. Representative (alpha band, target = agency; other bands/targets materially identical):

| predictor | out-of-fold CV R² | 95% CI (pair bootstrap) |
|---|---|---|
| **C_only (baseline)** | −0.013 | [−0.026, +0.004] |
| L_add | −0.019 | [−0.027, −0.007] |
| L_geo | −0.020 | [−0.027, −0.008] |
| **L_hybrid** | −0.019 | [−0.028, −0.009] |

Across **all** bands (theta/alpha/beta) and **both** targets, every index has a **slightly negative** out-of-fold R² — i.e. **none predicts the behavioural outcome better than the mean**. Critically, **`L_hybrid` does not beat raw `C`** — if anything it is marginally worse. **ChatGPT's central falsifiable prediction fails on ds007471.**

### 2.5 Phase II — does any candidate constant mark a change-point? (AIC break vs linear)
Piecewise-linear knot at each candidate τ ∈ {√2−1, 0.437, 0.6, 0.707, 0.75, cos²(π/8), 0.9299} vs a straight line, on Λ = min-max-scaled `L_hybrid` → agency (within-pair z-scored):

- **alpha:** *no* candidate break improves on the linear model (ΔAIC ≤ 0 for all).
- **beta:** the only breaks with ΔAIC > 0 are 0.75 (+0.78), cos²(π/8) (+0.30), radiant_cap (+1.25) — **all far below the ΔAIC ≈ 2 threshold** for a meaningful improvement, i.e. **noise**. **0.437 marks no break.**

No bifurcation-like structure is detected at any candidate constant. (This is a first, dataset-specific negative for **LCC-UOP-BRIDGE-F1**'s "thresholds are bifurcation points" claim — one dataset, coarse montage; not decisive, but not supportive.)

### 2.6 Phase III — UOP shape: linear vs saturating vs interior-optimum (AIC)
Comparing Hyp A linear (G=Λ), Hyp B saturating (1−e^{−kΛ}), Hyp C interior optimum (quadratic), Λ → agency:

| band | AIC linear | AIC saturating | AIC quadratic | best | quad argmax | interior? |
|---|---|---|---|---|---|---|
| alpha | **−26.86** | −25.25 | −25.29 | **linear** | 0.481 | (n/a) |
| beta | **−29.65** | −27.89 | −27.76 | **linear** | 0.939 | (n/a) |

**Linear wins in every band**; the interior-optimum (quadratic) model is *worse* than linear. In beta the quadratic's argmax lands at **0.9387 — visually near the Radiant Cap 0.9299 — but the quadratic model is not supported (AIC worse than linear), so this is a COINCIDENCE with no evidential weight.** Reported as a coincidence, never as a derivation or a confirmation of the cap.

### 2.7 Common-input control (surrogate) — is any coupling interaction-specific?
Both brains hear the same metronome + each other's tones, so inter-brain PLV can be inflated by **shared stimulus with zero real interaction**. Cross-pair **surrogates**: brain-R of pair A vs brain-L of pair B, matched on the **same tone sequence + condition** but never partners (10 draws/trial):

| band | real C (PLV) | surrogate C | real − surrogate | real > surr? | p (one-sided) |
|---|---|---|---|---|---|
| delta | 0.3118 | 0.3208 | **−0.0091** | no | 1.00 |
| theta | 0.0929 | 0.0959 | **−0.0030** | no | 1.00 |
| alpha | 0.0903 | 0.0937 | **−0.0034** | no | 1.00 |
| beta | 0.0436 | 0.0463 | **−0.0028** | no | 1.00 |

**Real inter-brain phase coupling does not exceed the common-input null in any band** (real is, if anything, *below* surrogate). This is **consistent with a common-input-dominated PLV** and shows **no evidence of interaction-specific coupling** in this dataset (the surrogate is supportive, not a formal causal identification). It is coherent with, and helps account for, the null manipulation check and the Phase I failure.

### 2.8 Honest reading (#69 both ways)
- **What this IS:** a clean **negative** result, on **real** hyperscanning data (stronger than a sim), for (a) the LCC-hybrid-index-beats-raw-correlation prediction, (b) any candidate constant acting as a change-point, and (c) an interior-optimum in the truth→outcome curve — **all on ds007471**. ChatGPT's named falsifiable claim (`L_hybrid > raw C`) is **falsified here**.
- **What this is NOT:** it does **not** refute the *conceptual bridge* (a framing about object types, not a numeric claim), nor the LCC/UOP principles corpus-wide. A single dataset cannot do that (**necessary-not-sufficient**, in the standing corpus discipline).
- **Two live readings, both stated:**
  1. **Theory-limitation:** LCC-as-index and the Radiant-Cap-optimum simply do not manifest in inter-brain drumming coordination — the constants gain **no** support here.
  2. **Measurement-limitation:** the coupling substrate itself failed the manipulation check and the common-input control, so the montage (6 ROI means), the multiplexed INT16 layout, the coarse 1–7 agency scale, or our specific C/P/S operationalization may be **too weak to detect** any true effect. The negative may be about the *measurement*, not the *theory*.
- Both readings are honest; neither is privileged. What is **not** licensed is treating the beta-band quadratic argmax≈0.9387 as confirmation of the cap (the model that produces it is beaten by a straight line).

### 2.9 Falsifier ledger for this batch
- **LCC-EMP-F1 — RESOLVED-NEGATIVE on ds007471:** `L_hybrid` did not beat raw `C` (Phase I); recorded as a dataset-specific falsification of the named prediction. **Broader** empirical support for the LCC index remains **OPEN** pending other real datasets (interpersonal HRV/physiological synchrony ↔ group cohesion; heart-rate synchrony ↔ decision correctness; sleep-wake wearable within-person coupling).
- **LCC-UOP-BRIDGE-F1 (OPEN):** thresholds-as-bifurcation-points unsupported on ds007471 (Phase II, no breaks) — one coarse dataset; not decisive.
- **LCC-437-F1 (OPEN):** 0.437 must earn a distinct transition √2−1 does not; unsupported here.
- **UOP-CAP-EMP-F1 (OPEN):** an interior optimum near √(1−e⁻²) must beat linear+saturating by AIC on some real outcome curve; failed here (linear wins).

---

## Reproducibility
All code + outputs under `analyses/lcc_uop_openneuro/`:
- `extract_features.py` — alignment (condition-sequence matching) + per-trial C/P/S features (validated `cond_ok=True` on all 32 pairs).
- `build_pair.sh` — per-pair download → extract → delete raw `.eeg` (both S3 layouts handled).
- `analyze.py` — manipulation check + Phase I (leave-pair-out CV, cluster bootstrap) + Phase II (AIC change-points) + Phase III (AIC shape) → `results/analysis.json`.
- `surrogate.py` — cross-pair common-input null for C (PLV) → `results/surrogate.json`.
- `features/` — 32 per-pair feature CSVs (1278 trials) + downsampled signal caches.

## Real citations (external)
- OpenNeuro **ds007471** — joint-agency EEG hyperscanning dataset (the real data tested).
- Golden ratio φ = (1+√5)/2; the constants √2−1 = tan(π/8), cos²(π/8) = Tsirelson/Bell bound, √(1−e⁻²) = Radiant Cap (Born-shaped, canonical ruling 2026-06-27) — used as *candidate* thresholds, none derived here.

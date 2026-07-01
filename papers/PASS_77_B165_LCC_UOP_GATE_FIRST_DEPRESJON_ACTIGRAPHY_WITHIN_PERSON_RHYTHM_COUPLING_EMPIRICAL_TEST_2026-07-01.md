# PASS-77 B165 — Gate-First LCC/UOP Test #2: Depresjon Actigraphy, Within-Person Circadian Rhythm Coupling → Depression (HONEST PARTIAL-NEGATIVE)

**Date:** 2026-07-01
**Batch:** Pass-77 B165 · ledger §7.7.349
**Status:** No new principle. Canonical count **80** (unchanged).
**Falsifiers touched:** LCC-EMP-F1 (second independent RESOLVED-NEGATIVE, on a mood-relevant dataset; broader still OPEN); LCC-HYB-F1 (hybrid index fails to beat raw features — second dataset); UOP-CAP-EMP-F1 (not reached — gated out); LCC-437-F1 (candidate `1/(√2φ)≈0.437` untested — gated out).
**Code:** `analyses/lcc_depresjon/` (`analyze.py`, `results/results.json`, `results/features.csv`, `data/` Depresjon).
**Prior batch:** B164 (`papers/PASS_77_B164_LCC_TOPOLOGY_UOP_ATTRACTOR_BRIDGE_AND_OPENNEURO_HYPERSCANNING_EMPIRICAL_TEST_2026-07-01.md`) — first real-data test (OpenNeuro ds007471 dual-EEG) = honest negative. This is the recommended **next** dataset from ChatGPT's gate-first pivot.

---

## 0. One-paragraph honest summary

Following ChatGPT's guidance to abandon ds007471's feature family and move to a dataset with a stronger prior for real, interaction/state-specific structure, we ran the **gate-first pipeline** (manipulation/group-signal → surrogate control → LCC index → threshold → UOP/cap) on the **Depresjon** actigraphy dataset (Garcia-Ceja et al. 2018; 23 depressed + 32 control; ~2 weeks of per-minute wrist activity each; MADRS available for the depressed group). Because Depresjon is **within-person**, LCC was operationalized as within-person circadian rhythm coupling: `C` = day-to-day rhythm coherence, `P` = cross-validated AR predictive gain (activity_t → future state), `S` = interdaily stability (a standard nonparametric circadian-stability metric). The outcome is depression state (and MADRS). **Result: a partial negative that is decisive for the LCC-specific claims.** Gate 1 passes — depression really is associated with the rhythm features (reduced future-activity predictability `P`, FDR p=0.0022; and the full `C,P,S` set reaches leave-one-subject-out AUC 0.68, consistent with the established actigraphy-depression literature). But **Gate 2 fails**: real circadian structure is far above chance (IS vs day-shuffle p≈5.5e-11; coherence vs phase-randomized p≈1.2e-7), yet the **surrogate-corrected** coupling (ΔS, ΔC — the component *beyond* linear/spectral autocorrelation, which is what LCC posits) does **not** separate the groups (p=0.21, p=0.61). And **Gate 3 fails** (all preprocessing fit on training folds only, no leakage): the hybrid additive+geometric LCC index does **not** beat raw features (AUC 0.20, actually inverted, vs raw-`C` 0.52 and full `C,P,S` 0.68) — the LCC aggregation *destroys* the discriminative signal the raw rhythm features carry. Per the revised decision rule, **constants and the Radiant Cap are therefore not admissible for testing** and were not claimed. #69: this is a genuine positive for *actigraphy→depression* but a genuine negative for the *LCC coupling index and its constants*; both theory-limitation and measurement-limitation readings are stated below.

---

## 1. What ChatGPT asked for, and what we did

**Gate-first pipeline (ChatGPT):** `manipulation signal → surrogate control → LCC index → threshold test → UOP/Radiant-Cap test`. **Do not test constants until the first two gates pass.** Compute every synchrony/coupling metric as `ΔC = C_real − C_matched_surrogate`, not raw. A dataset is eligible for constant testing only if (1) the manipulation/group-signal check passes, (2) the real signal exceeds the matched surrogate, and (3) `L_hybrid` beats raw `C` in cross-validation.

**Dataset choice.** ChatGPT ranked (1) physiological synchrony→group cohesion, (2) heart-rate synchrony→decision correctness, (3) Depresjon/OBF actigraphy (best Mood-Amplifier relevance), (4) DANDI rodent. We attempted the download-availability check first (honesty: REAL data only). The Simula host serves Depresjon over a chain with a missing local issuer cert; it is a **public** dataset so we fetched `https://datasets.simula.no/downloads/depresjon.zip` (5.7 MB, SHA of the 55 per-subject CSVs + `scores.csv`). PhysioNet/OpenNeuro/DANDI were reachable but do not host the specific Tomashin/Gordon physiological-synchrony corpora in a directly-downloadable form we could verify this session; Depresjon is both the most reliably-downloadable **and** the strongest Mood-Amplifier fit, so we ran it as test #2. (Physiological-synchrony→cohesion remains the recommended future run once a verified-open mirror is located.)

**Within-person operationalization** (Depresjon has no inter-person pairs, so LCC becomes within-person rhythm coupling, per ChatGPT's own §3 reframing):
- `C` (raw coupling) = mean Pearson correlation between each complete day's 24-h hourly profile and the subject's mean template ("day-to-day circadian coherence").
- `P` = 5-fold contiguous-block cross-validated R² of an AR(3) model on the log1p hourly series predicting the next hour vs a mean baseline ("activity_t → future state").
- `S` = Interdaily Stability (Van Someren nonparametric), the canonical circadian-stability index.
- Also reported: `IV` (intradaily variability), `RA` (relative amplitude, M10/L5) for context.
- Outcome: depressed (1, n=23) vs control (0, n=32); MADRS (madrs1) within the depressed group.

---

## 2. Gate results (the honest core)

### Gate 1 — group-signal / manipulation check: **PASS**
Mann-Whitney U (two-sided), BH-FDR at 0.05 across {C,P,S,IV,RA}:

| feature | depressed median | control median | rank-biserial | p | FDR pass |
|---|---|---|---|---|---|
| C (coherence) | 0.638 | 0.610 | −0.207 | 0.198 | no |
| **P (AR pred. gain)** | **0.568** | **0.707** | **+0.489** | **0.0022** | **YES** |
| S (interdaily stab.) | 0.343 | 0.273 | −0.266 | 0.096 | no |
| IV | 0.776 | 0.745 | −0.149 | 0.352 | no |
| RA | 1.000 | 1.000 | −0.016 | 0.910 | no |

A real state signal exists: depressed subjects have **less predictable future activity** (`P` lower; medium effect). This is consistent with the known actigraphy-in-depression literature (blunted, more entropic rhythms). Gate 1 passes.

### Gate 2 — surrogate control: **FAIL** (decisive for LCC)
- Circadian structure is genuinely present, far above chance:
  - IS vs **day-shuffled** null: ΔS>0 for **100%** of subjects, median ΔS=+0.158, Wilcoxon p≈**5.5e-11**.
  - Coherence vs **phase-randomized** (spectrum-preserving) null: ΔC>0 for **84%**, median ΔC=+0.052, p≈**1.2e-7** — so coherence carries beyond-linear phase structure.
- **But** the surrogate-CORRECTED signal — the part LCC actually claims (coupling beyond ordinary linear/spectral autocorrelation) — **does not separate the groups**: ΔS group-separation p=**0.21**, ΔC group-separation p=**0.61**.

Reading: the depression-related information lives in the **ordinary linear rhythm level** (amplitude/stability/predictability of the raw signal), **not** in any surrogate-corrected "coupling" beyond it. This is exactly the distinction the gate exists to make, and LCC fails it here.

### Gate 3 — hybrid index vs raw C: **FAIL**
Leave-one-subject-out CV AUC (logistic on standardized features):

| model | AUC |
|---|---|
| raw `C` | 0.520 |
| **`L_hybrid`** (B157 additive+geometric of C,P,S) | **0.200** |
| full `C,P,S` (as separate predictors) | 0.681 |

The hybrid LCC aggregation is **worse than chance and worse than raw** — collapsing C,P,S into the single `Λ=α·Σwᵢxᵢ+(1−α)·∏xᵢ^wᵢ` scalar *destroys* the discriminative signal that the features carry individually. `L_hybrid` does not beat raw `C` ⇒ ChatGPT's named eligibility criterion (3) fails, and LCC-HYB-F1 takes a second negative.

### Decision: constants **NOT admissible**
Gates 1&2 do not both pass (gate 2 fails) and gate 3 fails ⇒ by the revised decision rule we **do not** test constants or the Radiant Cap as confirmatory. For the record only (explicitly **gated, non-confirmatory**), the step-function AIC deltas vs a linear-C logistic were all within noise (√2−1: +0.23; 0.437: −0.73; cos²(π/8): +2.23; radiant_cap: −0.31 — none |Δ|≥2 decisively favouring a break), and a MADRS-vs-C quadratic among the 23 depressed was concave with argmax≈0.95 but R²=0.22 (n=23) — **an artifact-prone, unsupported curve we decline to interpret**, exactly as the beta quad-argmax coincidence was declined in B164.

---

## 3. #69 — both readings, honestly

**Theory-limitation reading.** On two independent real datasets now (dual-EEG hyperscanning ds007471 in B164; within-person actigraphy Depresjon here), the LCC hybrid index does **not** beat raw single-feature coupling, and the surrogate-corrected "coupling beyond linear structure" does not track the target state. The pattern is consistent with LCC's added machinery (bidirectional predictive `P`, stability `S`, the additive+geometric aggregation, the constant ladder) carrying **no incremental empirical content** over ordinary linear rhythm/coherence statistics in these datasets. LCC-HYB-F1 and the "L beats raw C" prediction are the specific casualties.

**Measurement-limitation reading.** Depresjon is coarse (per-minute single-axis activity counts, ~2 weeks, n=55, no within-subject intervention or state-transition label beyond diagnosis). The within-person "coupling" LCC really targets (predictive, directional, regime-dependent) may need finer or multi-channel signals (e.g., sleep-stage + activity + HRV) and an actual state transition (episode onset/offset), which this dataset lacks. The genuine Gate-1 positive (`P` and the AUC-0.68 feature set) shows the substrate is **not** signal-free — so a fairer LCC test would use a dataset with the intervention/transition structure ChatGPT flagged for the DANDI option.

**What is genuinely positive (do not bury it).** Depression is reliably associated with the rhythm features here (reduced future-activity predictability; AUC 0.68 from C,P,S together). That is a real, literature-consistent finding about *actigraphy and depression* — it is just **not** a win for the LCC *index* or its *constants*.

---

## 4. Candidate constant `1/(√2·φ)≈0.437` — still untested
Introduced in B164 as a HAN-1 resonance ("golden-orthogonal"), it was again **gated out** (constants inadmissible). It has now had zero opportunities to earn a distinct empirical change-point that √2−1 doesn't; it remains a resonance, not a rung. Falsifier LCC-437-F1 OPEN.

## 5. Falsifier ledger delta
- **LCC-EMP-F1:** second RESOLVED-NEGATIVE (Depresjon; mood-relevant). The narrow "LCC hybrid coupling beats raw and tracks state" claim is now falsified on two independent real datasets. Broader empirical support (physiological-synchrony→cohesion; heart-rate-sync→decision-correctness; a dataset with an explicit intervention/state-transition) remains **OPEN** and is the recommended next run.
- **LCC-HYB-F1:** OPEN → two negatives (index fails to beat raw features on both datasets).
- **UOP-CAP-EMP-F1 / LCC-437-F1:** OPEN, un-reached (gated out both times). The cap has still never been given an admissible confirmatory test.
- **LCC-UOP-BRIDGE-F1:** unchanged (B164 framing; not tested here).

## 6. Next-run recommendation (unchanged from ChatGPT, refined)
1. **Physiological synchrony → group cohesion** (ECG/IBI; ΔC = real−matched-surrogate) once a verified-open mirror of the Tomashin/Gordon corpora is located — strongest prior for real interaction-specific coupling, cleanest LCC-EMP-F1 follow-up.
2. **Heart-rate synchrony → decision correctness** — closest bridge to GILE-Truth (outcome = correctness, not felt agency).
3. A **DANDI/NWB dataset with an explicit intervention or state transition** — gives LCC the pre/post regime-change structure the within-person tests lacked.

---

*Honesty rails applied (EVD-1 / #69): REAL downloaded data only; every coupling metric surrogate-corrected; small-n (n=55) with leave-one-subject-out CV and nonparametric tests; constant/cap testing gated out per the pre-committed decision rule; the one concave MADRS curve explicitly declined as artifact-prone; genuine actigraphy→depression positive reported alongside the LCC-specific negative. No new principle; canonical count remains 80.*

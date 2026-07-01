# Physical Hypotheses Inventory — Mood Amplifier Safety & Validation Platform

**Status:** Gate 3 reference document. Enumerates all physical hypotheses currently in the platform plus candidate extensions for future URB development.
**Date:** 2026-05-01 PM
**Cross-links:** URB #826, URB #828 v2, `papers/BPS_TERM_INTRODUCTION_2026-05-01.md`, `papers/POLAR_H10_PHASE_B_PROCEDURE.md`.

---

## 1. EXISTING physical hypotheses (currently in pipeline or under test)

A *physical hypothesis* here means a falsifiable claim about a physical mechanism in the world (not a mathematical theorem, not a definitional contribution, not a methodological framework).

### 1.1 URB #826 — Biophoton/EM-DNA Carrier Hypothesis

> **H826:** I-Cell resonance is mediated by biophotons and EM waves emitted by DNA. Specifically, a subject's DNA-derived EM signature, combined with their live cardiac/respiratory EM emission, constitutes a physical channel for non-local correlation.

- **Status:** architectural verification complete (Phase H-1 §10.3, §10.4); empirical falsification gate scheduled at §10.6 (Polar H10 window, ~2026-05-22).
- **Falsifier (pre-registered):** w_em < 0.10 ∧ HRV > 0.85 → URB #826 falsified at this subject.
- **Confirmed by no test yet.** Honest scope.

### 1.2 URB #828 v2 — BPS Stacking Resonance Hypothesis (conditional on #826)

> **H828:** LCC-Virus present-state resonance requires a minimum stack of ≥3 permanent BPS (covering identity + environmental-history axes) and ≥3 live BPS (covering present-state axis), with optional channel-match contribution conditional on H826.

- **Status:** drafted v2 (2026-05-01 PM), pre-registration lock pending Brandon §10 approval.
- **Falsifier (pre-registered):** C5 (3+3) ≤ 30% accuracy, OR §6 classical-ML discriminator C0 > 35% (which collapses resonance interpretation entirely).
- **Confirmed by no test yet.** Honest scope.

### 1.3 LCC-Telepathy (existing pre-registered series)

> **H_LCC_T:** Cooperative-contemplation between two subjects produces above-chance agreement on shared psi-prediction targets, with effect size proportional to coherence between subjects' physiological signatures.

- **Status:** pre-registered trials filed (`papers/LCC_TELEPATHY_*` family).
- **Falsifier:** standard binomial-vs-chance per pre-registration.

### 1.4 GCP-correlation hypothesis (TI Sigma Intention Validation Lab v2)

> **H_GCP:** Random-number-generator deviations from the Global Consciousness Project network correlate with TI-Sigma-anchored intention events at a rate above chance.

- **Status:** existing TI Sigma Lab v2 framework; correlation analyses ongoing.

### 1.5 Tralse-Joules conservation (theoretical claim with empirical implications)

> **H_TJ:** TJ = τ(s) × δ(MR) — intentional work admits a quantitative conservation/efficiency law analogous to thermodynamic work-efficiency relationships.

- **Status:** theoretical operationalization complete; empirical instances measured indirectly via HEM-GILE ratio and PSI score.
- **Empirical falsifier:** repeated TJ measurements should obey the conservation law within experimental error; gross violation would falsify.

### 1.6 HEM-GILE ratio modulation of PD expression

> **H_PD:** ρ := GILE/HEM is the chirality-breaking parameter for parity-dependent (PD) phenotype expression in a subject.

- **Status:** formalized; empirical correlations under collection.

---

## 2. CANDIDATE extensions (not yet drafted as URBs)

These are physical hypotheses that the platform's framework supports but that have not yet been written up as URBs. Each is a candidate for future development.

### 2.1 H_BIOPHOTON_FIELD_GEOMETRY (extension of H826)

> **H_BFG:** The DNA-emitted biophoton field has measurable spatial geometry (intensity gradient, polarization signature) at distances ≤ 1m from the subject, and this geometry encodes subject-identity bits beyond what static DNA encodes.

- **Cost:** moderate ($150-400 for a single-photon detector or sensitive PMT). Above current $0 budget.
- **Falsifier:** no measurable photon flux above thermal background → H_BFG falsified.
- **Adjacent to:** Popp et al. biophoton literature (cite if H826 progresses).

### 2.2 H_HRV_PHASE_LOCK (extension of H828 §3.3)

> **H_HRV_PL:** Two cooperating subjects' Polar H10 HRV signals exhibit phase-locking above chance during cooperative-contemplation events, beyond what is explained by shared environment (temperature, time of day, audio).

- **Cost:** $0 if cooperator owns Polar H10. Otherwise +$80 for second strap.
- **Falsifier:** no above-chance phase coherence in pre-registered windows.
- **Adjacent to:** McCraty / HeartMath cardiac-coherence literature; LCC-Telepathy series.

### 2.3 H_BPS_STACK_GENERALIZATION (extension of H828)

> **H_GEN:** The N≥6 BPS stacking minimum generalizes across subjects (i.e., is a property of the resonance mechanism, not Brandon-specific). Replication at ≥1 additional subject confirms; failure to replicate localizes the result to Brandon.

- **Cost:** $0 if cooperator volunteers; requires consent + phone-camera setup.
- **Falsifier:** C5 ≥ 40% at Brandon AND C5 ≤ 25% at cooperator → result is subject-specific.
- **Status:** sketched as URB #829 candidate.

### 2.4 H_AXIS_ABLATION (extension of H828, axis-importance)

> **H_AA:** Within the URB #828 v2 stack, dropping each axis (identity / environmental-history / present-state) one at a time produces a measurable accuracy decrement, allowing empirical ranking of axis-importance.

- **Cost:** $0; uses existing URB #828 trial data with post-hoc subset re-analysis.
- **Falsifier:** axis-ablation produces no measurable decrement → axes are functionally redundant, taxonomy over-specified.
- **Status:** sketched as URB #830 candidate.

### 2.5 H_PHARMACOLOGY_MODULATION (Adderall/Focalin direct effect on resonance)

> **H_PM:** Stimulant medication state (Adderall on/off, Focalin on/off, days_since_med_change) modulates URB #828 accuracy beyond what is explained by HRV alteration alone. Tests whether the "intentionality channel" is sensitive to prefrontal dopaminergic state independently of cardiac signature.

- **Cost:** $0; uses existing `data/medication_log.csv` × URB #828 trial data.
- **Falsifier:** medication state has no residual effect after HRV residualization.
- **Adjacent to:** §10.6 pharmacology covariate plan.

### 2.6 H_CIRCADIAN_RESONANCE (extension of H828 present-state axis)

> **H_CR:** URB #828 accuracy varies systematically with subject's circadian phase (time-of-day, days since last sleep, melatonin window) beyond what is explained by HRV.

- **Cost:** $0; uses Oura sleep data + trial timestamps.
- **Falsifier:** no time-of-day effect after HRV residualization.

### 2.7 H_BPS_TIME_DECAY (lifetime of permanent BPS)

> **H_TD:** Permanent BPS information content decays measurably as the BPS becomes outdated relative to T_k (face photo from 1 year ago performs worse than face photo from today, controlling for everything else).

- **Cost:** $0; requires Brandon to provide historical face photos at known dates.
- **Falsifier:** no decay → permanent BPS are time-invariant in resonance contribution.
- **Implication if confirmed:** the "environmental-history axis" has a measurable time-constant, sharpening §3.2 of the BPS taxonomy.

### 2.8 H_DREAM_ANCHOR (extension of H828 to sleep-state)

> **H_DA:** A target token revealed during waking but pre-anchored at sleep onset (subject "intends to dream about it") shows above-chance recall correlation with the agent's prediction made during the sleep window.

- **Cost:** $0 with Oura ring + bed-side voice memo.
- **Falsifier:** no above-chance correlation in pre-registered windows.
- **Risk:** confounded by ordinary memory consolidation; tight design needed.

### 2.9 H_PRECOG_BPS (temporal extension of H828)

> **H_PRE:** The BPS bundle captured at T_k correlates with target-tokens revealed at T_k + Δt for small Δt (precognition direction), at strength comparable to T_k retrocognition.

- **Cost:** $0; trial-design modification only.
- **Falsifier:** symmetric or reversed time-direction effect → frame is wrong.
- **High asymmetric-standards-#69 risk:** strong claim, requires very tight protocol.

---

## 3. Hypotheses NOT in scope (deliberate exclusion)

Documenting what we are NOT claiming, for asymmetric-standards #69 hygiene:

- **Not claiming:** classical electromagnetic propagation explains LCC-Virus (URB #826's biophoton/EM-DNA hypothesis is a *novel-substrate* claim; it does not reduce to standard EM propagation through tissue, which is too lossy at relevant frequencies for non-trivial distance).
- **Not claiming:** quantum-entanglement-of-DNA-bases is the mechanism (this would require maintained coherence across decoherence timescales, which the framework explicitly does not invoke).
- **Not claiming:** DNA acts as an antenna for ambient EM (URB #826 specifies *emission*, not reception).
- **Not claiming:** any of the above hypotheses generalize to non-living systems.
- **Not claiming:** any of the above hypotheses violate energy conservation or thermodynamics. The Tralse-Joules framework (§1.5) is explicitly compatible with classical conservation laws.

---

## 4. Recommended priority for Gate-4 follow-on URBs

Given $0 budget and current pipeline:

1. **#829 (H_GEN, generalization to second subject):** highest scientific value, lowest cost, but requires cooperator volunteer.
2. **#830 (H_AA, axis ablation):** zero marginal cost, post-hoc on URB #828 data, sharpens taxonomy.
3. **#831 (H_PM, pharmacology modulation):** zero marginal cost, post-hoc on URB #828 data, leverages existing covariate logging.
4. **#832 (H_TD, time decay):** zero marginal cost if Brandon has historical photos.
5. **#833 (H_CR, circadian):** zero marginal cost, post-hoc on URB #828 data.

Lower priority (higher cost or higher methodological risk):
6. H_HRV_PL (cost-dependent on cooperator)
7. H_BFG (requires hardware purchase, defer until #826 confirmed)
8. H_DA (methodologically delicate)
9. H_PRE (high asymmetric-standards-#69 risk)

---

## 5. Honest residuals

1. **None of the existing hypotheses (#1.1–#1.6) have been empirically confirmed as of 2026-05-01.** All architectural verifications to date are deterministic and confirm structure, not physical reality.
2. **The §10.6 H10 window (~2026-05-22) is the first scheduled gate where any of these hypotheses can lose**.
3. **The §6 classical-ML discriminator in URB #828 v2 is the second scheduled gate where the framework can lose**.
4. **All candidate extensions (#2.1–#2.9) inherit the falsification status of their parent hypothesis.** If H826 falsifies, H_BFG/H_HRV_PL/H_BPS_TIME_DECAY all collapse or require reframing.

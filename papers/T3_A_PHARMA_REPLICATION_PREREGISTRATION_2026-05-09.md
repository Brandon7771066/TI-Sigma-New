# T3-A — External Pharmacology Replication: Pre-Registration

**Author:** Brandon Charles Emerick (PI); agent (drafting per Pass 11 directive)
**Date:** 2026-05-09
**Status:** **RATIFIED by Brandon 2026-05-09 (Pass 12).** Pre-registration locked. No data collected for this study yet; filed *before* execution to lock the analysis plan, per #69 honesty discipline. Search-term list (§3.4), reviewer-identity (Brandon-self for the pilot search; RA for any expansion), and simulator commit-pin (current main branch HEAD) are now LOCKED at the git commit recording this ratification.
**Companion:** `papers/TIER_1_RESULTS_PASS_9_2026-05-09.md` §T1-A (motivation); `analyses/pharma_baseline/linear_baseline.py` (reference baseline code).

---

## 1. Why this study exists

Tier-1 item T1-A (Pass 10) showed the headline +8 pp pharma margin on the N=12 internal validation set **does not survive bootstrap at 95%** (CI [−33.3, +33.3] pp; P(margin > 0) = 31.6%). Within-sample bootstrap on N=12 cannot rescue the headline; the structural fix is a held-out external dataset. This pre-registration locks the analysis plan **before** data collection so the result is interpretable regardless of which way it lands.

## 2. Pre-registered hypothesis

**H1 (primary):** TI Sigma's GILE-dimension predictions achieve a magnitude-accuracy margin of **at least +5 pp** over the best of {mean-magnitude, median-magnitude, stack-size LOO regression} baselines on a held-out external pharmacology dataset of N ≥ 30 experiments, where "magnitude accuracy" = predicted/empirical ratio in [0.5, 2.0].

**H2 (secondary):** Bootstrap 95% CI on the (TI − best-baseline) margin is strictly positive (i.e., does not cross zero).

**Disconfirmation criterion:** if either (a) point-estimate margin < +5 pp, or (b) bootstrap 95% CI crosses zero, **H1 is rejected** and the framework's pharmacology claim is demoted in the corpus per #69. This pre-commitment is binding regardless of the result.

## 3. Dataset specification

### 3.1 Inclusion criteria

A study is included iff **all** of:

1. Reports a quantitative effect (% change vs baseline) of a single pharmacological intervention on a clinically-relevant outcome (mood, cognition, anxiety, sleep, HRV, EEG band power, or a validated clinician-administered scale).
2. The intervention's primary mechanism maps unambiguously to one or more URBs in the TI Sigma corpus (e.g., FAAH inhibition → AEA elevation → ECS pathway → urb-mapped GILE dimension).
3. Sample size N ≥ 20 in the published study (to avoid amplifying small-N noise from the literature).
4. Published in a peer-reviewed journal (PubMed-indexed) or registered clinical trial (clinicaltrials.gov) between 2010 and 2025.
5. **Was NOT used in the N=12 internal validation set** (held-out criterion).

### 3.2 Exclusion criteria (locked before search)

- Combination interventions where individual contributions cannot be separated.
- Animal-model-only studies (human only).
- Studies where the TI prediction would require post-hoc URB extension.
- Studies without a placebo or active comparator.
- Effect sizes reported only as p-values without magnitudes.

### 3.3 Target N

**Minimum:** 30 independent experiments. **Target:** 50. **Rationale:** at N = 30, a true +8 pp margin has bootstrap CI half-width ≈ 12 pp (vs ≈ 33 pp at N = 12); CI crosses zero only marginally. At N = 50, half-width drops to ≈ 9 pp; a real +8 pp effect becomes detectable.

### 3.4 Data sources to search (in order)

1. PubMed: terms ("FAAH inhibitor" OR "anandamide" OR "5-HTP" OR "ketamine" OR "PF-04457845" OR ...) AND ("clinical trial" OR "randomized") AND (mood OR cognition OR anxiety OR sleep).
2. ClinicalTrials.gov: completed Phase II/III trials in same intervention set, results posted.
3. Cochrane Library: relevant systematic reviews for effect-size aggregation.
4. SemanticScholar: forward-citation search from anchor papers in the N=12 set.

Search executed by Brandon (or designated graduate-level reviewer). Each candidate paper logged with PMID, year, intervention, N, primary outcome, effect size + sign, journal, and TI-URB mapping. Inclusion/exclusion decisions logged with reason. **Search log committed to repo before TI predictions are generated** (this prevents post-hoc cherry-picking).

## 4. Pre-registered analysis plan

### 4.1 Generation of TI predictions (BLINDED)

For each included experiment, the TI Sigma simulator generates a predicted % change **before the analyst sees the empirical effect size**. This is the critical blinding step. Procedure:

1. Reviewer extracts (intervention, dose, duration, outcome measure, N) from each paper.
2. Reviewer hands these to the TI Sigma simulator (`hypercomputer_app.py` or successor) without revealing the empirical result.
3. Simulator outputs predicted % change.
4. Predictions are logged + locked (commit hash recorded) **before** the empirical effects are joined to the predictions table.

### 4.2 Primary statistical test

For each candidate fold f ∈ {1.5, 2.0, 3.0}, compute:

- **TI magnitude accuracy** = fraction of experiments with predicted/empirical ∈ [1/f, f].
- **Best-baseline magnitude accuracy** = max over {mean-magnitude, median-magnitude, stack-size LOO regression} on the same data.
- **Margin** = TI − best baseline.

Then paired bootstrap (B = 20,000) on the margin, recomputing the baseline within each resample to avoid pessimistic bias.

**Primary outcome:** margin at fold = 2 with bootstrap 95% CI.

### 4.3 Secondary outcomes (also pre-registered)

- Margin sensitivity across folds 1.5 / 2.0 / 3.0.
- Directional accuracy (TI sign matches empirical sign), reported with note that the held-out set must include null and negative-effect studies for this metric to be informative.
- Per-URB error decomposition (where do TI predictions miss most?).
- Domain-stratified results (mood vs cognition vs HRV vs EEG).

### 4.4 No deviations after locking

Any analysis not listed in §4.1–§4.3 is exploratory and reported with the "**EXPLORATORY**" tag. The primary outcome (§4.2) is single, pre-specified, and binding.

## 5. Decision tree (pre-committed per #69)

| Result | Action |
|---|---|
| Margin ≥ +5 pp AND bootstrap 95% CI strictly positive | TI Sigma pharma claim **CONFIRMED**; book F-1 reframed as confirmed external replication. |
| Margin ≥ +5 pp BUT bootstrap CI crosses zero | TI Sigma claim **PARTIALLY CONFIRMED**; book F-1 reframed honestly with CI; further N expansion warranted. |
| 0 < margin < +5 pp | TI Sigma claim **NOT CONFIRMED**; book F-1 demoted to "small positive effect, not statistically distinguishable from baseline at this N." |
| Margin ≤ 0 | TI Sigma claim **DISCONFIRMED**; book F-1 retracted; framework's structural claims (T1-B/C/D) become the load-bearing empirical evidence. |

This decision tree is binding. The agent flags any post-hoc deviation and Brandon is the only authority who can amend.

## 6. Resource requirements

- **Time:** ~40 hours search + extraction (graduate-level reviewer); ~8 hours simulator runs; ~2 hours analysis.
- **Cost:** $0 if Brandon does the search; $1,500–$3,000 for graduate RA at $30/hr × 40 hr (within Brandon's <$50 personal budget only if Brandon does the work himself).
- **Calendar:** 4–8 weeks. PubMed search is the rate-limit.

## 7. Pre-commit deliverables (filed BEFORE search begins)

1. **This document** (locked at git commit `<HASH>` once Brandon ratifies).
2. **Search-term list** (Section 3.4, finalized with Brandon).
3. **Reviewer identity** (Brandon or named RA).
4. **Simulator version pin** (commit hash of `hypercomputer_app.py` at the time predictions are generated).

## 8. Threats to validity (acknowledged up-front)

- **Publication bias:** the literature over-represents positive findings. Mitigation: pre-register inclusion criteria; log exclusions with reasons.
- **Reviewer interpretation drift:** the URB mapping requires judgment. Mitigation: lock URB mapping decisions before generating predictions; second-reviewer audit of disputed mappings.
- **Simulator drift:** if the simulator is updated mid-study, predictions change. Mitigation: pin commit hash; freeze simulator for the duration.
- **Effect-size heterogeneity:** different outcome measures (Beck Depression Inventory vs HAM-D vs DASS-21 vs HRV LF/HF) have different scales. Mitigation: normalize to % change vs baseline within each outcome family; report per-domain stratified results in §4.3.

## 9. What this pre-registration accomplishes

This study converts a **bootstrap-fragile within-sample claim** into either a **bootstrap-robust external claim** (if it confirms) or a **principled retraction** (if it disconfirms). Per #69 both outcomes are equally informative; the framework's credibility comes from running the test, not from the result.

The pre-registration itself is a public commitment — once committed, the agent cannot reverse-engineer the analysis plan to favor a particular outcome. This is the methodological discipline that distinguishes T3-A from the within-sample N=12 work.

---

**End of pre-registration. Brandon-decision required to ratify before the search begins. Once ratified, the search-term list and reviewer-identity fields are locked at the current git commit.**

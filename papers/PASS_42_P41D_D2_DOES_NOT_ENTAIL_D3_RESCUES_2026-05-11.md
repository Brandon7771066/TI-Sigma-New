# Pass 42 / p41-D — D2 (Diagnostic-Not-Predictive) Does Not Entail D3 (Interaction-Required): 5 Alternative Rescues

**Date:** 2026-05-11
**Pass:** 42 (discharges p41-D from Pass 41)
**Anchor of parent open item:** `papers/PASS_41_SYNCHRONICITY_DIAGNOSTIC_NOT_PREDICTIVE_2026-05-11.md` §1 nested-distinctions softening + §6 p41-D.

---

## §1 — The question

Pass-41 §1 (post-architect-fix) states that D2 (Diagnostic-Not-Predictive) is *consistent with* but does NOT *entail* D3 (predictive only via interaction). Pass-41 §6 raised p41-D: *what other rescues admit D2 → useful-prediction without going through D3?*

This paper enumerates **5 alternative rescue paths** that take a D2-class diagnostic sign and convert it to operationally-useful prediction without requiring an interaction-with-companion-variables design.

## §2 — Five rescue paths

### **R1: Late-emerging predictor (time-shifted, MT-5 analogue)**
The sign predicts the outcome at a DIFFERENT TIME than the outcome is measured. A genuinely diagnostic sign at t=0 may predict outcome at t=20 years even though it does not predict outcome at t=1 year. Pass-40 MT-5 ("time-shifted Q") is the logical analogue.
**Operational test:** longitudinal cohort with outcome assessed at multiple lags; sign at t=0 enters logistic with main effect alone, no interaction terms, but with outcome at t=20.
**Status:** R1 fully bypasses D3; sign retains main-effect predictive power if the right outcome-window is chosen.

### **R2: Threshold / non-linear single-predictor (subset-of-subjects-exceed)**
The sign predicts the outcome only for subjects whose sign-score exceeds a threshold; below threshold, the sign is uninformative. This is a SINGLE-PREDICTOR non-linearity, not an interaction.
**Operational test:** GAM (generalized additive model) or piecewise logistic with a free knot; AIC vs linear logistic.
**Status:** R2 bypasses D3; the model is single-predictor non-linear, not multivariate interaction.

### **R3: Mediator pathway (sign → mediator → outcome)**
The sign predicts the outcome BUT the predictive pathway runs through an intermediate variable M (e.g., sign → contemplative-practice-uptake → outcome). Statistically the sign main-effect on outcome is non-zero, but the mechanism is mediation, not interaction.
**Operational test:** mediation analysis (Baron-Kenny / SEM) — sign → M coefficient + M → outcome coefficient + sign → outcome direct effect.
**Status:** R3 bypasses D3 in the *modeling* sense; the model has a single predictor (sign) with an intervening variable, not two variables in interaction. Conceptually D3-adjacent but statistically distinct.

### **R4: Conditional independence (sign predicts in a subpopulation) — REPARAMETERIZED-D3, NOT INDEPENDENT RESCUE (architect Pass-42 fix)**
The sign predicts the outcome ONLY in a subpopulation defined by some other variable (e.g., predicts only for participants with high baseline contemplative practice). **Architect-flagged conflation (Medium severity):** R4 is *statistically equivalent* to a strong interaction with the stratification variable in most parameterizations — fitting "sign within high-Cj stratum + sign within low-Cj stratum" recovers the same likelihood as "sign + Cj + sign×Cj." R4 is therefore better described as **reparameterized-D3-like heterogeneity** rather than as an independent evidence class.
**Operational test:** subgroup analysis with pre-specified strata is mathematically equivalent to a saturated interaction model; only the *reporting framing* differs.
**Status:** R4 is **NOT a true bypass of D3** — it is a presentation choice for D3-class evidence. Listed here for completeness and because the *semantic* difference (subpopulation-rule vs functional-form-combination) sometimes matters for theoretical interpretation, but R4 should NOT be counted toward "rescue diversity" in §3 model-averaging or in p42-A multiplicity correction.

### **R5: Population-level (vs individual-level) prediction**
The sign aggregates well at population level — e.g., "more synch-events in a community correlates with more GM-Nodes per capita 5 years later" — without predicting any individual. The sign is a *population-rate* predictor, not an individual-trait predictor.
**Operational test:** ecological / multi-level model with population-rate as outcome and population-mean-sign-score as predictor; individual-level sign-outcome correlation may be near zero.
**Status:** R5 fully bypasses D3 by changing the *unit of analysis*. Pass-15 MBE / GBRH heavy-tailed individual base rates already establishes that population-level predictors can fail at individual level; R5 is the *converse* — individual-level diagnostic signs may aggregate to useful population-level predictors.

## §3 — Implications for the Pass-41 modeling strategy

The Pass-41 D3 interaction-design proposal remains the *most parsimonious* operational path for synchronicity-style signs IF the sign is genuinely diagnostic-not-predictive at individual level AND companion variables are measurable AND outcome is single-time-point AND linearity holds. If ANY of those four conditions fails, one of R1–R5 may be the better-fitting rescue.

**Bayesian model-averaging recommendation:** prospective designs should test D3 (interaction) AND R1 (longitudinal lag) AND R2 (threshold) AND R5 (population-aggregation) in parallel rather than committing exclusively to D3 — these are **4 genuinely-distinct evidence classes**. R3 (mediator) is best framed as a *post-hoc explanatory model* contingent on D3 results. R4 (conditional independence) is **reparameterized-D3 not an independent class** per §2 R4 architect-fix; it counts as part of D3 for multiplicity-correction purposes.

## §4 — Updated Pass-41 §3 H_pass41 (extended)

**H_PASS41_EXTENDED:** at least ONE of the **4 genuinely-distinct evidence classes** {D3 interaction (incl. R4 reparameterized), R1 longitudinal lag, R2 threshold non-linearity, R5 population-aggregation} produces a model with synch-score loading at z ≥ 1.96 in held-out test data **AFTER Bonferroni-corrected α = 0.05/4 = 0.0125 per class** (raised p42-A; integrated into p41-C v2 amendment). NULL for ALL FOUR classes = strong evidence against D2-via-rescue (i.e., the sign may be neither diagnostic nor predictive in any operationally useful sense).

## §5 — Honesty caveats (#69)

- **(C1)** Adding R1–R5 to the Pass-41 modeling strategy *increases the multiple-comparisons burden*. A pre-registration that tests 4 rescues simultaneously must apply Bonferroni or false-discovery-rate correction (e.g., α = 0.05 / 4 = 0.0125 per rescue). The Pass-42 / p41-C pre-registration document does NOT yet incorporate this — it should be amended to test D3 only OR test all four rescues with corrected α. (Raised p42-A.)
- **(C2)** R3 mediator and R4 conditional-independence rescues are particularly vulnerable to over-fitting at small N; both require strong prior justification (e.g., specifying mediator M or stratification variable BEFORE data lock).
- **(C3)** R5 population-aggregation requires *much* larger N than individual-level designs (need many populations, not many individuals). Operationally this may exceed Pass-26 funding-tier; raised p42-B.
- **(C4)** The Bayesian model-averaging recommendation in §3 is informal here; full implementation requires specifying prior weights over the rescue models, which is itself a significant statistical-philosophy commitment.

## §6 — Discharges

- **p41-D: DISCHARGED** by §1-§5. D2 admits at least 5 distinct rescues to operational prediction, of which D3 (interaction-design) is one. The Pass-41 §1 softening is vindicated by this enumeration.
- Raised: **p42-A** (multi-rescue α correction in p41-C pre-registration); **p42-B** (R5 population-aggregation feasibility under funding tier).

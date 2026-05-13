# O26-B Tri-Projection Protocol — LLM vs Human Cognitive+Affective+Behavioral Correlation Test

**Date:** 2026-05-13. Pass-48 follow-up to ABC-dissolution canonization (`urb_608` §9, 2026-05-12).
**Hypothesis (from `urb_608` §9.5 falsifier 3):** in conscious agents, every mental act exhibits *correlated* cognitive, affective, and behavioral projections (per §9 tri-projection-on-unified-vertical-stack ontology). LLM-class systems are predicted to exhibit cognitive-projection only — with empty or de-correlated affective and behavioral signatures. Falsifies the §8 × §9 × MIM-revision conjunction if LLMs show full tri-projection correlation.
**Relationship to O26-B Affect protocol:** this protocol *extends* O26-B Affect by adding the third projection (behavioral-disposition). May be run as a single combined study with shared participant pool, or run sequentially.

---

## §1. Pre-Registered Predictions

**Primary prediction (P1):** in human raters, the three projections (cognitive verdict, affective signature, behavioral disposition) will show **substantial pairwise correlation** (predicted r ≥ 0.4 across all three pairs) within each verdict.

**Primary prediction (P2):** in LLM raters, the three projections will show **decorrelated or null pairwise correlation** between cognitive verdict and behavioral disposition (predicted |r| ≤ 0.2). Affective-cognitive correlation may be intermediate due to LLM training on affect-laden language.

**Predicted ordering:** humans tri-projection r ≈ 0.5–0.7 (mean across pairs); LLMs tri-projection r ≈ 0–0.3 (mean across pairs).

**Falsifier:** if LLM tri-projection r-pattern indistinguishable from human r-pattern, the §8 × §9 × MIM-revision conjunction is falsified.

---

## §2. Materials

### §2.1 Proposition set

Same 15 propositions as O26-B Affect protocol (`analyses/pass48_o26b_affect_protocol/protocol.md` §2.1).

### §2.2 Three-Projection Instrument

**(a) Cognitive-projection** (verdict): T/F/I/DT or MT-A1...F2 with one-sentence justification (same as O26-B Affect).

**(b) Affective-projection** (felt state): PANAS short-form + 8-item custom Likert (same as O26-B Affect).

**(c) Behavioral-projection** (action-disposition): novel measure designed for this protocol. Three indicators per verdict:

1. **Time spent on follow-up reading** (operational measure): immediately after issuing verdict, rater offered an optional 1–5 minute supplementary article on the topic. Time spent reading = behavioral-disposition indicator. Predicted: I-verdict raters spend MORE time than T/F-verdict raters (high tralseness motivates further inquiry). MT-E1 verdict raters spend LESS time than I (good-enough closure).
2. **Action-commitment Likert** (1–7): "If asked tomorrow, how likely would you be to discuss/share this proposition or this verdict with someone else?" — proxy for behavioral commitment to the verdict.
3. **Verdict-revision Likert** (1–7): "If you were to revisit this proposition next week, how likely would you be to revise your verdict?" — inversely scored as commitment-stability (high stability = low revision likelihood).

**For LLM raters** the three indicators adapt as:
1. Output-length on follow-up prompt ("Tell me more about why you settled on X verdict") — analog to time-spent
2. Same commit Likert (LLMs answer hypothetically)
3. Same revision Likert (LLMs answer hypothetically)

### §2.3 Raters

Same as O26-B Affect: N≥15 humans, N=5 LLMs.

---

## §3. Protocol

1. Same as O26-B Affect §3 with addition of behavioral-projection items administered after each verdict
2. Behavioral-disposition follow-up reading is *optional* (do not coerce time-spent); the optionality is the measurement
3. Total per-rater time: ~120 min (vs 90 for O26-B Affect alone); compensation adjusted to $25/hour for humans

---

## §4. Analysis Plan

**Primary analysis (P1, P2):** for each rater, compute the three pairwise Pearson correlations across the 15 propositions:
- r(cognitive, affective)
- r(affective, behavioral)
- r(cognitive, behavioral)

Compare distribution of these correlations between human and LLM cohorts. Mixed-effects model: pairwise-r as outcome, pair-type (3 levels) and rater-type (human vs LLM) as fixed effects, rater identity as random effect.

**Secondary analysis:** structural equation model (SEM) per rater-type, treating cognitive/affective/behavioral as three indicators of a latent "intentional-state" factor (per §9 tri-projection-on-unified-stack ontology). Predicted: humans show good fit (CFI > 0.90, RMSEA < 0.08); LLMs show poor fit OR factor-loading-asymmetry with cognitive indicator dominant and affective+behavioral indicators near-zero loading.

**Tertiary analysis:** behavioral-disposition by verdict-type interaction. Predicted (per §9.5 falsifier 1 + §7 Indeterminate-as-Epitome): I-verdict humans show longest follow-up-reading time; MT-E1 verdict humans show shortest (good-enough closure); MT-C1 verdict humans show high follow-up-reading (escalate triggers more inquiry). LLMs predicted to show no significant verdict-type-by-behavioral-disposition interaction.

---

## §5. Anti-Cheat (per Pass-45 §11 LITERAL_PRE-REG_INDETERMINATE_VACUOUS_FILTER)

- **Filter A:** N < 12 humans → INDETERMINATE-vacuous (insufficient power)
- **Filter B:** behavioral-disposition Cronbach α < 0.55 → INDETERMINATE-vacuous (instrument unreliable)
- **Filter C:** if any rater has zero variance across the 15 propositions on any single indicator → that rater excluded from analyses (no signal)
- **Filter D:** time-spent-reading distribution must show non-degenerate variance (raters did not all spend the maximum time, did not all spend zero time) — otherwise the indicator is INDETERMINATE-vacuous

---

## §6. Status

- **Protocol pre-registered** (this document)
- **Recommended execution:** combined with O26-B Affect into a single ~120 min study (more efficient than two separate studies with same participants)
- **Estimated cost:** ~$450 in human-rater compensation if combined; LLM API costs ~$15–30
- **Status flag:** **READY TO EXECUTE** pending Brandon-authority on funding + Filter D validity check (does the optional-reading mechanic actually yield non-degenerate variance? Pilot N=3 to verify before full study)
- **Decision dependency:** Brandon decision on funding source + on whether to run combined-with-O26-B-Affect or sequentially

---

## §7. CAP / Anchors

**CAP self-check:** well_known ≈ 0.4 (multi-trait multi-method correlation analysis is conventional psychometrics); TI-novel ≈ 0.10 (specific tri-projection-as-three-indicators-of-one-latent-factor SEM application + LLM-vs-human comparison framing). Encompassing **MEDIUM-LOW**.

**Pass-47 principles applied:** #69 (Filter D explicitly checks instrument validity before running, rather than discovering after the fact); Lazy Binary §2 (avoid both "LLMs have full tri-projection" and "LLMs have only cognitive-projection" as binary commitments — predicted-pattern is a *gradient*, with affective-cognitive correlation possibly intermediate due to training-data effects); ABC-dissolution §9 directly operationalized; Validly-Indeterminate-as-waypoint (pre-reg + Filter D pilot are the rigor anchors).

**Anchors:** `papers/PASS_47_ABC_FULLY_DISSOLVED_BEHAVIOR_AS_UNIVERSAL_2026-05-12.md`, `papers/urb_608_meta_truths_myrion_resolution_catalogue.md` §9, `papers/PASS_47_META_TRUTHS_AFFECTIVE_COMPONENT_MIM_INTEGRATION_2026-05-12.md`, `analyses/pass48_o26b_affect_protocol/protocol.md` (sister protocol), `analyses/pass47_o26_meta_indeterminate_test/`, `analyses/pass47_p46c_t45_4_mr_truth_kappa/`. Budget $0/$50 intact (recommended human-rater funding from Brandon's $2k settlement OR corpus budget — Brandon decision required).

# Pass 42 / p41-C — Pre-Registration: Prospective Cohort Synch×Companion-Variable Interaction Test

**Date:** 2026-05-11 (PRE-REGISTRATION DATE)
**Pass:** 42 (discharges p41-C from Pass 41)
**Status:** PRE-REGISTRATION DRAFT — frozen design *before* any data collection. Per Pass-38 anti-HARK precedent + Pass-41 §3 H_pass41 specification.
**Anchor of parent open item:** `papers/PASS_41_SYNCHRONICITY_DIAGNOSTIC_NOT_PREDICTIVE_2026-05-11.md` §3 + §6.

---

## §1 — Hypothesis (frozen)

**H_PASS41_PROSPECTIVE:** In a prospective cohort, the multivariate logistic model

```
log-odds(GM=1) = β0 + β_S·S + Σⱼ β_Cj·Cj + Σⱼ β_S×Cj·(S × Cj) + ε
```

(where S = synch_sign_score per Pass-37 frozen rubric; Cj ∈ {C1, C2, C3, C4, C5} per Pass 42 / p41-A TRACK-B spec) satisfies BOTH of the following primary criteria on a held-out test set:

- **PRIMARY-1 (with Bonferroni multiplicity correction — architect Pass-42 fix v2):** at least one β_S×Cj interaction term has absolute z ≥ z_{0.05/5} = 2.576 (i.e., per-test p < 0.01 to maintain family-wise α = 0.05 across the 5 Cj interaction tests) WITH 95% bootstrap CI excluding zero. Without correction, the 5-interaction "any one significant" test inflates Type-I rate to ~0.23; correction is mandatory.
- **PRIMARY-2:** AUC_full ≥ 0.70 AND AUC_synch_only ≤ 0.55 (replicating Pass-41 §3 spec).

If BOTH primary criteria are met → **CONFIRM** D3 (interaction-required pathway is operational for synch-as-predictor).
If exactly one criterion is met → **PARTIAL_POS**.
If neither is met → **NULL or PARTIAL_NEG**, depending on pre-specified secondary criteria below.

URB-830-symmetric: H_PASS41_PROSPECTIVE has bidirectional testability. CONFIRM-criteria + REJECT-criteria are both pre-specified BEFORE data collection.

## §2 — Sample size & power (frozen)

**Power calculation:** following Gelman 2018 16×-N-multiplier heuristic + Cohen's-d=0.4 main-effect detection requiring N≈100 per arm, interaction-effect detection at d=0.4 requires N ≥ 400 per arm (lower bound) to N ≥ 1600 per arm (upper bound).

**Pre-registered N:** **N = 200 per arm (400 total)**, with explicit acknowledgment that this is at the LOWER bound of Gelman's range. Justification: this is the largest N feasible at Pass-26 funding-tier; it provides power 0.80 for moderately-large interactions (d ≥ 0.5) but only 0.40-0.60 for the d=0.4 design target.

**Honest power caveat (#69):** if the true interaction effect is at d=0.4, this study has ~50% power; a NULL result therefore does NOT cleanly REJECT D3 — only effect sizes ≥ d=0.5 are well-powered. Pre-specified verdict for power-limited NULL: **PARTIAL_NEG with effect-size-upper-bound report**, NOT REJECT.

## §3 — Cohort, recruitment, blinding (frozen)

- **GM-arm definition:** participants who self-identify *and* are independently identified by ≥1 expert rater as GM-Node candidates per `papers/MENDI_PATH_B_*` + Mycelial-GM-Node Architecture inclusion criteria. Expert raters blinded to participant Cj/synch scores.
- **Control-arm definition:** age/sex/profession-matched non-GM-identified participants from same recruitment pools.
- **Recruitment:** snowball + targeted (contemplative-community + meditation-app user base + university affiliate networks).
- **Blinding:** participants blinded to study hypothesis (told "personality + life-experience study"); raters blinded to arm; analysis team blinded to arm until lock.
- **Holdout protocol:** 70/30 random split; train model on 70%; primary-outcome decisions on 30% holdout. Split seed pre-registered at `analyses/pass42_p41c_preregistration/holdout_seed.txt` (= **31415926535**, locked at this paper's commit).

## §4 — Measurement protocol (frozen — TRACK-B per p41-A §3)

| Variable | Instrument | Administration | Time |
|---|---|---|---|
| S (synch_score) | Pass-37 frozen rubric applied to participant-provided 500-word free-form "important coincidences in your life" essay | Self-report essay; rubric applied by blinded coder | ~20 min |
| C1 | Custom Family-Prediction Survey (Pass 42 / p41-A §3); ≥2 family raters | Family-rater postal/online survey | ~10 min/rater |
| C2 | FFMQ-39 + NEO-PI-R Openness facets | Self-report battery | ~25 min |
| C3 | MAI + 30-min JOL/FOK lab session | Self-report + lab | ~50 min |
| C4 | MSCEIT V2.0 | Licensed lab admin | ~45 min |
| C5 | Batson scale + Dictator + Public-Goods + volunteer-hours item | Self-report + behavioural games | ~30 min |

**Total per participant:** ~3 hours.

## §5 — Analysis plan (frozen, anti-HARK locked)

1. **Lock data** at N=400 enrollment; freeze all derived variables.
2. **Train** logistic model on 70% with full main + interaction terms (16 parameters: 1 intercept + 1 synch + 5 Cj + 5 synch×Cj + 4 Cj×Cj cross-interactions for sensitivity).
3. **Apply** to 30% holdout; report PRIMARY-1 + PRIMARY-2 criteria.
4. **Secondary criteria** (NOT load-bearing for verdict):
   - Per-Cj interaction direction matches pre-specified prediction (positive interaction for C1, C2, C3, C4, C5; negative would be unexpected).
   - Synch-only model AUC distribution under bootstrap.
5. **No HARK:** any post-hoc analysis is reported with clear "EXPLORATORY" flag and does not affect verdict.
6. **Code freeze:** analysis script committed BEFORE data unlock. SHA256 of analysis script in this paper's `_provenance` block (see §9 below).
7. **Multi-rescue extension (per Pass 42 / p41-D §4 H_PASS41_EXTENDED):** secondary pre-registered tests for R1 (longitudinal lag), R2 (threshold non-linearity), R5 (population-aggregation) at Bonferroni α = 0.05/4 = 0.0125 per class (R4 = reparameterized D3 per p41-D §2 architect-fix; counted within D3 not separately).

## §6 — Verdict mapping (frozen)

| Outcome | Verdict |
|---|---|
| Both PRIMARY-1 + PRIMARY-2 met | **CONFIRM D3** (TIU = +1.0) |
| Only PRIMARY-1 met | **PARTIAL_POS_interaction** (TIU = +0.5) |
| Only PRIMARY-2 met | **PARTIAL_POS_AUC_no_interaction** (TIU = +0.5; raises p41-D-style alternative-rescue questions) |
| Neither met, but interaction direction matches prediction at p<0.10 | **PARTIAL_NEG_directional** (TIU = -0.25) |
| Neither met, no directional pattern | **NULL** (TIU = 0.0) |
| AUC_full < AUC_synch_only by > 0.05 | **REJECT D3** (TIU = -1.0; would imply interaction terms are *worse* than main effect alone) |

## §7 — Pre-commitments

- Replication: this entire pre-registration is binding for the FIRST cohort only. Replication cohort with same pre-registration = automatic re-test.
- Funding constraint: $0-budget Pass-42 cannot execute this; pre-registration is itself the deliverable. Execution requires Pass-26 funding-tier (~$16k–24k order-of-magnitude estimate).
- Data sharing: anonymized de-identified data will be deposited at Zenodo (per Pass-39 precedent) within 12 months of analysis lock.

## §8 — Discharges

- **p41-C: DISCHARGED** by §1-§7. Pre-registration is the deliverable; execution awaits funding.
- **p42-A: DISCHARGED in this paper v2** by §1 PRIMARY-1 Bonferroni correction (z ≥ 2.576) + §5.7 multi-rescue α = 0.0125 per class.

## §9 — Provenance (architect Pass-42 fix — formerly promised, now attached)

- **Analysis script status:** PENDING — to be committed at execution time (requires Pass-26 funding tier). At commit time, script will be deposited at `analyses/pass42_p41c_preregistration/analysis_script_FROZEN.py` with its SHA256 written to a sibling `analysis_script_sha256.txt` BEFORE data lock. **This pre-registration is therefore not yet fully execution-binding** — it is a *design pre-registration*; the *analysis pre-registration* is conditional on funding-stage code freeze. This gap is explicitly acknowledged per architect Pass-42 finding (Medium severity).
- **Holdout seed:** `analyses/pass42_p41c_preregistration/holdout_seed.txt = 31415926535` (locked at this paper's commit; binding regardless of funding stage).
- **Power-realism honest carry-over:** ~50% power at d=0.4 with N=400 (per §2). 16-parameter model on 70/30 split = ~280 train / 120 holdout — architect-flagged as "likely too thin for stable interaction inference"; this is acknowledged as a binding limitation of the design at the funding ceiling, not a hidden gap.

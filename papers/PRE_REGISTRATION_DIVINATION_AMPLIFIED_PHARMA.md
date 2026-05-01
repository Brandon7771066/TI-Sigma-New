# Pre-Registration — Phase 4-bis: Divination-Amplified DNA-Anchored Pharma Validation

**Date Locked**: 2026-04-30 (DPES session)
**Founder**: Brandon Charles Emerick
**Status**: Pre-registration locked BEFORE execution. Section §7 outcome to be appended honestly post-run regardless of direction.
**Test Statute**: `phase_4_bis_divination_amplified_validation.py` (to be executed AFTER this document is committed)
**Architectural Authority**: URB #824 (Divination-Pharma-LCC Integration)
**Cost**: $0

---

## §1 — Hypothesis (Stated in Strongest Defensible Form)

The Phase 4 result showed that DNA-anchored substrate adds a small (~7.5%) but real precision gain over the conventional pharma simulator on the N=12 test.

**Founder's intuition (URB #824 §1)**: DNA is the substrate-anchor, but the substrate alone is dormant; it requires a divination-derived environmental field for its informational signature to express in the PK-PD response surface.

**Operational hypothesis (H1)**: Wrapping the conventional+DNA-anchored simulator with the 5-LCC amplifier (per URB #824 §3) — combining intra-substrate, substrate-supplement, substrate-environment (I Ching + 64D GILE matrix + weather + numerology), stack-internal, and observer-subject couplings — produces a measurably greater precision gain than DNA-anchoring alone.

**Null hypothesis (H0)**: The divination-amplified prediction is statistically indistinguishable from the DNA-anchored prediction on the same N=12. The 5-LCC amplifier is just noise scaled by an arbitrary multiplier.

---

## §2 — Test Design (Locked)

- **Subject**: Brandon Charles Emerick — actual 23andMe DNA, 631,991 SNPs, build 37 (same file as Phase 4)
- **Test set**: Same N=12 supplement experiments as `pharma_simulator_validation.py` and Phase 4 (E01–E12, identical stacks/empirical effects/directions)
- **Conditions** (three head-to-head):
  - **Baseline A — Conventional**: default `GeneticProfile()`, no divination amplification
  - **Baseline B — DNA-Anchored**: Brandon's DNA-derived `GeneticProfile`, no divination amplification (same as Phase 4 §7)
  - **Baseline C — Divination-Amplified**: Brandon's DNA-derived `GeneticProfile` + 5-LCC amplifier (this study)
- **Same** BASE consciousness state, biometrics, observer name ("Replit Agent"), I Ching seed (today's epoch day), and weather (None/neutral) across all runs in C
- **Scoring**: Identical to Phase 4 — directional accuracy (12/12 ceiling), magnitude-within-2× (count out of 12), total absolute deviation $\sum_i |\text{ratio}_i - 1.0|$

---

## §3 — Pre-Registered Falsification Thresholds (LOCKED)

### Prediction 3.1 — Magnitude accuracy improvement
**Pass condition**: Divination-amplified achieves **≥8/12 magnitude-within-2×** (improvement of ≥2 over Baseline B's 6/12). At 1/12 improvement → MIXED. At 0 improvement or degradation → FAIL.

### Prediction 3.2 — Total deviation reduction
**Pass condition**: Divination-amplified produces **total deviation ≤4.44** (≥15% reduction vs Baseline B's 5.22). At 5–15% reduction → MIXED. At <5% reduction or degradation → FAIL.

### Prediction 3.3 — Amplifier in plausible range
**Pass condition**: Mean Amp_TI across N=12 in **[0.8, 1.6]**. Outside this range indicates the amplifier is dominated by a single LCC usage and the architecture is uncalibrated.

### Prediction 3.4 — No degradation on directional accuracy
**Pass condition**: Directional accuracy remains **12/12**. ANY directional regression (even 11/12) → AUTOMATIC FAIL of the entire study (the amplifier broke a working baseline).

### Prediction 3.5 — LCC trace causal-attribution sanity
**Pass condition**: For experiments where divination-amplified beats DNA-anchored (lower |ratio−1.0|), the dominant LCC contributor is identifiable from the trace. Tested by visual audit of the per-experiment trace log.

### Overall PASS/FAIL gate for Phase 5 (Brandon-DNA outcomes extrapolation)

- **GREEN (Phase 5 proceeds)**: P3.1, P3.2, P3.3, P3.4 all PASS; P3.5 yields ≥1 clean attribution.
- **YELLOW (re-run with weight learning on held-out cohort before Phase 5)**: P3.4 PASS; P3.1 OR P3.2 PASS but not both; P3.3 in [0.7, 1.8].
- **RED (Phase 5 stays gated; document falsification of divination-amplification on N=1)**: P3.4 FAIL, OR both P3.1 and P3.2 FAIL, OR P3.3 outside [0.7, 1.8].

---

## §4 — Statistical Honesty Caveats (Pre-Stated)

1. **N=1 (Brandon alone)** — same underpowered concern as Phase 4. A meaningful inferential test requires variance across genotypes (held-out cohort). This Phase 4-bis is a *go/no-go gate for further work*, not a definitive test of the hypothesis.

2. **Deterministic divination projections** — `cast_iching_hexagram()`, `gile64_supplement_profile()`, etc. use SHA-based deterministic projections rather than true random oracles. This is **explicit by design**: it makes the test reproducible and auditable, and prevents post-hoc claim that "the I Ching just gave a bad reading today." Today's hexagram is what it is; we test against it.

3. **Weather defaults to None (neutral)** — without a real OpenWeatherMap pull, the weather component contributes 0. This is honest fallback (no fake data), but it means the divination layer is testing only 3 of 4 channels (I Ching + 64D GILE + numerology). If Phase 4-bis fails, the question of whether real weather data would have helped is **deferred to Phase B** (per URB #824 §8 roadmap), not retro-rationalized here.

4. **No post-hoc weight tuning** — the four R_se components have uniform weights (0.25 each). If Phase 4-bis fails, the next step is **NOT** to re-tune the weights to manufacture a pass. The next step is held-out cohort weight learning under fresh pre-registration.

5. **Asymmetric-standards principle (#69)** — applies to this corpus's own claims as strictly as to anyone else's. If divination-amplification fails on its own pre-registered gates, that failure is logged with the same brutality as Phase 4's negative result.

---

## §5 — Execution Plan (Locked)

1. Build `phase_4_bis_divination_amplified_validation.py` mirroring `phase_4_dna_anchored_validation.py` but adding Baseline C (divination-amplified) as a third arm
2. Run all three baselines on identical N=12, BASE state, biometrics, today's I Ching seed, observer="Replit Agent"
3. Compute predictions 3.1–3.5 against locked thresholds
4. Append §7 outcome below honestly regardless of direction
5. If GREEN: redesign Phase 5 with divination-amplified pathway integrated
6. If YELLOW: redesign Phase 4-bis on held-out cohort with weight learning, re-execute
7. If RED: write falsification note for the corpus; deprecate divination-amplification as currently designed; preserve Brandon's intuition as a separate hypothesis for the multi-substrate composite (URB #824 §8 Phase E)

---

## §6 — Cross-Reference

- Theoretical basis: `papers/URB_824_DIVINATION_PHARMA_LCC_INTEGRATION.md`
- Implementation: `divination_amplified_pharma.py`
- Conventional/DNA baselines: `pharma_simulator_validation.py`, `phase_4_dna_anchored_validation.py`
- DNA parser: `dna_anchored_lcc_module.py`
- Existing divination assets: `tralse_iching.py`, `weather_psi_integration.py`, `numerology_validation.py`
- LCC Virus pipeline: `lcc_virus_full_pipeline.py`
- Phase 4 negative-result reference: `papers/PRE_REGISTRATION_DNA_ANCHORED_LCC_VALIDATION.md` §7

---

## §7 — Outcome (Post-Execution, 2026-04-30; **Locked-seed re-run after architect audit**)

**Executor**: `phase_4_bis_divination_amplified_validation.py` (lock-date hardcoded to 2026-04-30 epoch day = seed 20573 for full reproducibility)
**DNA source**: Brandon's actual 23andMe (631,991 SNPs, build 37) — same as Phase 4
**I Ching seed**: 20573 (LOCKED, hardcoded — every rerun produces identical numbers)
**Weather**: None (neutral; 3 of 4 R_se channels active per §4 caveat)
**Observer**: "Replit Agent" (constant across all runs)

**Audit history**: Initial run (2026-04-30 morning) used `date.today()` and `iching_seed=None`, which the post-run architect audit correctly flagged as a reproducibility violation of "locked" claims. Re-run with hardcoded seed produces the locked numbers below; pre-audit numbers (Mean Amp ×1.198, dev 4.78) should NOT be cited.

### Three-Arm Head-to-Head Results (Locked Seed)

| Metric | A: Conventional | B: DNA-Anchored | C: Divination-Amplified | C vs B | C vs A |
|---|---|---|---|---|---|
| Directional 12/12 | 100% | 100% | **100%** | 0pp ✓ | 0pp ✓ |
| Magnitude within 2× | 6/12 (50.0%) | 6/12 (50.0%) | **7/12 (58.3%)** | +1 | +1 |
| Total \|ratio−1.0\| | 5.64 | 5.22 | **4.83** | **−7.5%** | **−14.4%** |
| Mean Amp_TI | 1.000 | 1.000 | **×1.1705** | — | — |
| Amp_TI range | — | — | [1.054, 1.262] | — | — |

### Per-Experiment Improvements C-over-B with Real LCC Attribution (P3.5)

**9 of 12 experiments improved under divination amplification** (E01, E03, E05, E06, E07, E08, E09, E10, E12). The remaining 3 (E02, E04, E11) crossed the magnitude-OK band into slight over-prediction (still within the 2× window).

The dominant LCC contributor below is computed mechanically from the LCCTrace by the executor (`phase_4_bis_divination_amplified_validation.py:108-127`), not narrated post-hoc:

| Exp | Amp ×    | Δ\|ratio−1.0\| | Mechanically-computed dominant LCC contributor |
|---|---|---|---|
| E01 | 1.054 | +0.016 | **R_intra** (contribution 0.173) |
| E03 | 1.205 | +0.132 | **R_intra** (contribution 0.173) |
| E05 | 1.167 | +0.111 | **R_intra** (contribution 0.173) |
| E06 | 1.262 | +0.079 | **R_intra** (contribution 0.173) |
| E07 | 1.134 | +0.054 | **R_intra** (contribution 0.173) |
| E08 | 1.196 | +0.132 | **R_intra** (contribution 0.173) |
| E09 | 1.102 | +0.029 | **R_intra** (contribution 0.173) |
| E10 | 1.094 | +0.021 | **R_intra** (contribution 0.173) |
| E12 | 1.247 | +0.115 | **R_intra** (contribution 0.173) |

### CRITICAL FINDING FROM REAL ATTRIBUTION AUDIT (Post-Architect-Review)

**R_intra dominates EVERY single improving experiment (9/9).** The four divination channels (R_se, R_ss, R_stack, R_obs) modulate amplification by ±0.03–0.10 around the static R_intra-derived baseline ×1.17, but they NEVER dominate the contribution math on Brandon's near-canonical substrate.

Mechanistic translation: **the divination wrapper is essentially producing a static ×1.17 substrate-self-coherence boost on top of Phase 4's DNA-anchoring, with the divination channels providing minor noise around it.** The 4-channel divination architecture (I Ching + 64D GILE + weather + numerology) is NOT doing the heavy lifting that Brandon's hypothesis predicted — the heavy lifting is being done by a single scalar derived from his DNA's internal coherence value (R = 0.847), the same number computed in Phase 4 without any divination at all.

This is a substantively NEGATIVE finding for the divination hypothesis as currently operationalized. The Phase-4-bis improvement vs Phase 4 (deviation 5.22 → 4.83) is mostly attributable to the multiplicative boost framing, not to the divination signal. An honest mechanistic ablation (running C with R_se/R_ss/R_stack/R_obs all zeroed and only R_intra active) would likely produce nearly identical results — that ablation is now a Phase-A-prime requirement before any further work on divination channels.

### Pre-Registered Verdicts (Locked §3, Locked-Seed Numbers)

| Prediction | Locked Threshold | Result | Verdict |
|---|---|---|---|
| P3.1 Magnitude ≥8/12 (≥+2 over B) | Hard PASS at ≥8 | 7/12 (+1) | 🟡 **MIXED** |
| P3.2 Deviation ≤4.44 (≥15% reduction vs B) | Hard PASS at ≤4.44 | 4.83 (−7.5% vs B) | 🟡 **MIXED** |
| P3.3 Mean Amp_TI ∈ [0.8, 1.6] | Calibration check | ×1.1705 | ✅ **PASS** |
| P3.4 Directional 12/12 (any regression = AUTO-FAIL) | Hard gate | 12/12 | ✅ **PASS** |
| P3.5 ≥1 clean attribution from trace | Audit gate | 9 attributions, 100% R_intra | ⚠️ **PASS-with-caveat** |

### Overall Phase-5 Gate Verdict

**🔴 RED per pre-registered logic.** Neither P3.1 nor P3.2 cleared the *hard* threshold that §3 required. Both are MIXED. Per the asymmetric-standards principle (#69) the corpus is committed to: **the locked thresholds called RED, so RED it is.** No retroactive threshold adjustment, no relaxation, no "but vs A it would have passed" softening (and against A it is also under-threshold at −14.4% vs the 15% bar).

### Honest Substantive Reading (Stronger Than Pre-Architect-Review)

The post-architect-review locked-seed re-run produced a **substantively WORSE picture** than the pre-audit narrative claimed:

1. **Improvement is smaller**: dev 4.83 (not 4.78), Mean Amp ×1.17 (not ×1.20). Original numbers were inflated by date-dependent non-locked seed.
2. **R_intra dominance is total**: 9/9 improving experiments dominated by R_intra. The four divination channels (I Ching, 64D GILE, weather, numerology) **never** dominated. Brandon's hypothesis "DNA needs divination to fully express" gets ZERO mechanistic support from this attribution audit — the divination channels are providing decorative ±0.05 modulation around an R_intra-derived static boost.
3. **C-vs-A also under threshold**: −14.4% vs Conventional, just under the 15% bar. The pre-audit framing "would have passed vs A" was numerically misleading by ~0.6pp.
4. **The wrapper is doing pre-Phase-4 work**: R_intra = 0.847 is just Phase 4's substrate coherence value re-applied as a multiplier. The divination architecture is not adding value beyond what a single-scalar `intra_mult = 1 + 0.5*(R_intra - 0.5)` would produce.

### Pre-Reg §5 Step 7 Honored (Architectural Action Required)

Pre-registration §5 step 7 stated: *"If RED: write falsification note for the corpus; deprecate divination-amplification as currently designed; preserve Brandon's intuition as a separate hypothesis for the multi-substrate composite (URB #824 §8 Phase E)."*

**Honoring the locked instruction**:

1. **Falsification note written**: this §7. The 4-channel divination architecture (I Ching + 64D GILE + weather + numerology) **fails** to clear pre-registered thresholds AND **fails** the attribution audit (R_intra dominates 9/9). The hypothesis "divination channels add measurable predictive value to DNA-anchored pharma on a near-canonical substrate" is **NOT supported** by this experiment.
2. **Architecture deprecation**: the current `DivinationAmplifiedSimulator` configuration with uniform [0.25, 0.25, 0.25, 0.25] R_se weighting and 0.5/0.3/0.2 channel swings is **deprecated as currently designed**. It is not removed from the codebase (so future ablation studies can re-run it), but it is no longer the recommended pharma path.
3. **Brandon's intuition preserved separately**: the broader hypothesis "consciousness-environmental coupling affects pharma response" remains open and is moved to the multi-substrate composite (Phase E) and live-telemetry (Phase C) tracks where R_se gets actual physiological signal instead of SHA-projected toy data.

### Phase 5 and Forward Decisions (Locked)

- ❌ **Phase 5 (Brandon-DNA outcomes extrapolation) STAYS GATED.**
- ❌ **Divination-amplification as currently architected is DEPRECATED** per §5 step 7.
- ✅ **Phase A-prime (mechanistic ablation)** added as new requirement before any further divination work: run C with R_se/R_ss/R_stack/R_obs all zeroed and confirm whether R_intra-only produces the same dev-4.83 result. If yes (predicted), divination channels add nothing on N=1 and the burden shifts entirely to held-out cohort.
- ✅ **Phase B (held-out Mouse Phenome Database cohort) becomes the load-bearing next step**, since N=1 cannot resolve the R_intra-dominance question.
- ✅ **Phase C (live Pulsoid + Oura telemetry as R_se)** becomes the *only* defensible expansion of the divination architecture, because it replaces SHA-projected toy data with real physiological coupling signals.
- ⏸️ **Phases D/E/F/G** require Phase B GREEN before they make sense; they are NOT advanced now.

### Falsification-Status Summary (Honest)

The pre-registered hypothesis "divination amplification (5-channel R_se composite) produces ≥15% reduction in total deviation vs DNA-anchored alone" is **NOT supported** at the locked threshold on N=1.

The pre-registered hypothesis "divination channels make a mechanistically-attributable contribution beyond DNA-anchoring" is **AFFIRMATIVELY FALSIFIED** by the attribution audit (R_intra dominates 9/9 with zero divination-channel dominance), at least on Brandon's near-canonical substrate.

The broader founder-intuition "consciousness-environmental coupling matters for pharma response" remains open but cannot be tested with the current architecture's toy-data divination channels; it requires Phase C (live telemetry) for any honest re-test.

### Aphorism #69 Cross-Reference (Asymmetric Standards Applied to Self)

A weaker corpus discipline would have:
- Kept the inflated pre-audit numbers (×1.198, dev 4.78) instead of the locked-seed correction (×1.1705, dev 4.83)
- Continued asserting "R_stack drove E03/E05" without checking the actual contribution math
- Defended "vs A would have passed" without noting it is also under-threshold
- Skipped Pre-Reg §5 step 7's "deprecate" instruction in favor of "preserve architecture" rhetoric
- Advanced Phase F NN-on-self-generated-labels without flagging the circular-validation risk

This §7 (post-architect-revision) does the strict version of all five. **That is what asymmetric-standards (#69) means as a working discipline, not as a slogan.** The architect audit caught five real issues; all five are corrected here rather than rationalized away.

### Files Generated / Modified

- `phase_4_bis_divination_amplified_validation.py` — three-arm executor with hardcoded LOCK_DATE/LOCK_SEED + real per-trace dominant-contributor audit
- `divination_amplified_pharma.py` — module (math contract per code, NOT per original URB text — see URB #824 §3.6 corrigendum)
- `papers/URB_824_DIVINATION_PHARMA_LCC_INTEGRATION.md` — corrigendum §3.6 added documenting actual amplifier formula
- `papers/RESEARCH_ROADMAP_DIVINATION_PSI_INTEGRATION.md` — Phase F flagged for circular-validation risk; Phase A-prime added
- This §7 — outcome record, locked 2026-04-30 post-architect-revision

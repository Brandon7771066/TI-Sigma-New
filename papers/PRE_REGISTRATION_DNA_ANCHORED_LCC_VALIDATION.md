# Pre-Registration: DNA-Anchored LCC vs Conventional Baseline Validation

**Date:** 2026-04-30 (locked BEFORE running comparison)
**Phase:** 4 of 6 (per `RESEARCH_ROADMAP_DNA_ANCHORED_PSI_SIGNATURE.md`)
**Cost:** $0
**Hypothesis:** DNA-anchored LCC prediction outperforms conventional non-DNA-anchored prediction by ≥5 percentage points on directional accuracy AND/OR magnitude accuracy across the existing N=12 well-replicated experiment validation suite.

## §1 — Background: Two Established Baselines

### Baseline A — Conventional pharma simulator (no DNA anchoring)
**Established 2026-04-30 by running `pharma_simulator_validation.py`:**
- N=12 well-replicated published experiments (Cravatt 1996, Kathuria 2003, etc.)
- Directional accuracy: **12/12 = 100.0%**
- Magnitude accuracy (within 2×): **10/12 = 83.3%**
- Status: Tier A performance (PASSES 80% directional + 60% magnitude thresholds)

### Baseline B — DNA-anchored LCC prediction (Phase 3 module)
**To be measured in this validation:**
- Same N=12 experiment registry
- DNA anchor: Brandon's actual 23andMe genotypes via `dna_anchored_lcc_module.py`
- Brandon's substrate coherence R(A,B) = 0.8470
- LCC overlay applied via substrate coherence weighting

## §2 — Critical Methodological Tension (Surfaced Honestly)

The existing pharma simulator already achieves 100% directional and 83.3% magnitude accuracy. **There is very limited room for the DNA anchor to improve directional accuracy** (ceiling effect at 12/12). The DNA anchor's value, if real, must show in:

1. **Magnitude accuracy improvement**: from 10/12 = 83.3% baseline → ≥11/12 = 91.7% threshold (+8.4pp)
2. **Magnitude ratio precision**: total absolute deviation from 1.0× ratio across all 12 experiments. Baseline computed below.
3. **Subject-specificity**: predictions for Brandon's specific phenotype (vs. generic population predictions) match Brandon's actual response patterns when measured.

This is the HONEST framing: the conventional simulator is so good that the DNA anchor must produce a measurable improvement on a tighter metric than directional accuracy alone.

## §3 — Locked Predictions (committed BEFORE running Baseline B)

### Prediction 3.1: Magnitude accuracy
- DNA-anchored prediction: **≥11/12 (91.7%) magnitude-within-2×** (improvement of ≥8.4pp over conventional baseline)
- Falsification: if DNA-anchored produces <11/12 magnitude-within-2×, the DNA anchor adds NO meaningful magnitude precision and the hypothesis is falsified

### Prediction 3.2: Total absolute magnitude deviation
Compute Σ|ratio_predicted/ratio_empirical − 1.0| across all 12 experiments.

Conventional baseline (computed from §1 results above):
| Exp | TI Ratio | Empirical | Predicted/Empirical | |Dev−1| |
|-----|---------|-----------|---------------------|--------|
| E01 | 38.3 | 62 | 0.62 | 0.38 |
| E02 | 104.7 | 57 | 1.84 | 0.84 |
| E03 | 8.7 | 45 | 0.19 | 0.81 |
| E04 | 73.8 | 35 | 2.11 | 1.11 |
| E05 | 134.3 | 100 | 1.34 | 0.34 |
| E06 | 36.7 | 62 | 0.59 | 0.41 |
| E07 | 50.0 | 63 | 0.79 | 0.21 |
| E08 | 27.3 | 21 | 1.30 | 0.30 |
| E09 | 15.1 | 27 | 0.56 | 0.44 |
| E10 | 19.0 | 23 | 0.83 | 0.17 |
| E11 | 40.0 | 12 | 3.33 | 2.33 |
| E12 | 45.4 | 50 | 0.91 | 0.09 |
| **Total** | | | | **7.43** |

- DNA-anchored prediction: **total deviation ≤ 5.94** (≥20% reduction from 7.43 baseline)
- Falsification: if DNA-anchored total deviation > 6.69 (less than 10% improvement), the anchor is non-meaningful

### Prediction 3.3: Brandon-specific phenotype self-consistency check
For experiments where Brandon's specific genotype maps to a known direction (e.g., E03 fear extinction, E05 Jo Cameron FAAH-OUT phenotype), DNA-anchored prediction should be CLOSER to Brandon's expected position in the population distribution than the unconfigured baseline.

For E05 specifically: Jo Cameron is FAAH AA + FAAH-OUT deletion = extreme bliss phenotype. Brandon is FAAH CC = standard. DNA-anchored prediction for Brandon on E05's stack should be CLOSER to control (lower magnitude) than the conventional baseline's 134.3% prediction.

- Falsification: if DNA-anchored prediction does NOT scale toward Brandon's specific phenotype direction on at least 4/6 LCC-prior-relevant experiments, the anchor is non-functional

### Prediction 3.4: LCC substrate coherence as confidence calibration
LCC R(A,B) = 0.8470 for Brandon. Per #69 inversion principle, predictions with HIGH substrate coherence to canonical reference should be RELIABLY accurate, while predictions for atypical substrates (low R) should carry higher uncertainty.

- Pre-registration: if/when we test Brandon-DNA-anchored predictions vs other-genotype-anchored predictions, low-R predictions should have wider confidence intervals than high-R predictions
- Falsification: if R-value does not predict prediction-confidence calibration, the LCC overlay is non-functional as a confidence calibrator

## §4 — Cleanliness Credits per Quote #69

The DNA-anchored prediction faces a tighter test than the conventional baseline:
- Conventional baseline only had to predict ABOVE chance — it did so spectacularly (100% directional)
- DNA-anchored has to BEAT an already-passing baseline by ≥5pp on tighter metrics

Per #69 inverse-Schelling principle, a hit on the tight DNA-anchored test carries MORE evidential weight than the original Tier A baseline result, because the alternative-explanation routes (already-strong simulator) are closed off.

## §5 — Honest Complications to Resolve in Execution

1. **Pharma simulator API integration**: Phase 3 built the `dna_anchored_lcc_module.py` GeneticProfile correctly but the simulator's `simulate_supplement_response` / `predict_response` interface needs to be matched. Phase 4 execution requires:
   - Inspect `ti_pharmacological_simulator.py` for the actual prediction method name
   - Pass the DNA-derived GeneticProfile through that method on the same N=12 stacks as the conventional baseline
   - Score with the same endpoint mapping as `pharma_simulator_validation.py`

2. **Genotype-to-experiment mapping**: Some N=12 experiments are HUMAN trials (E04 PF-04457845 PTSD; E06 saffron vs. fluoxetine; E07 5-HTP; E09 omega-3; E10 L-methylfolate; E11 PQQ; E12 ketamine+lithium). For these, Brandon's DNA is the "subject genotype." For ANIMAL experiments (E01 URB597 rat; E02 FAAH-KO mouse; E03 anandamide rat amygdala), Brandon's DNA is NOT the subject — we'd need to use the published animal genotype (FAAH-KO has faah_activity=0.0).

3. **Generalization**: To test the DNA anchor as a GENERAL prediction tool, we need a held-out cohort. Options:
   - **(a)** Use OpenSNP self-reported phenotype subset as held-out human cohort
   - **(b)** Use Mouse Phenome Database FAAH-KO vs wild-type pharmacology data as animal cohort
   - **(c)** Cross-validation across the N=12 with leave-one-out
   - **Recommended**: (b) is closest to Brandon's specific endocannabinoid focus

## §6 — Execution Plan (Locked)

1. Inspect `ti_pharmacological_simulator.py` for correct prediction method
2. Run conventional baseline AGAIN (to confirm reproducibility)
3. Run DNA-anchored prediction on same N=12 stacks
4. Compute predictions 3.1, 3.2, 3.3, 3.4 metrics
5. Compare to falsification thresholds
6. Append §7 outcome below honestly regardless of direction
7. If positive: proceed to Phase 5 (Brandon-DNA outcomes-extrapolation; DNA already uploaded)
8. If negative: write falsification paper documenting that DNA anchor adds no improvement to already-Tier-A pharma simulator

## §7 — Outcome (Post-Execution, 2026-04-30)

**Executor**: `phase_4_dna_anchored_validation.py` (run 2026-04-30 DPES session)
**DNA source**: Brandon's actual 23andMe file, 631,991 SNPs, build 37
**Brandon's DNA-derived GeneticProfile**:
- FAAH activity: 1.0 (rs324420 = CC, standard, no bliss-variant)
- COMT activity: 1.0 (rs4680 = AG, Val/Met balanced)
- CB1 receptor density: ~1.21 (rs1049353 = CT, elevated)
- BDNF expression: 0.8 (rs6265 = CT, reduced)
- Schizotypy SNP count: 2 (MAOA rs909525=AG, OPRM1 rs1799971=AA contributors)
- Substrate coherence R(A,B) = 0.847

### Head-to-Head Results (Same N=12, Same BASE state, Same BIOMETRICS)

| Metric | Conventional (default GP) | DNA-Anchored (Brandon GP) | Δ | Threshold | Verdict |
|---|---|---|---|---|---|
| Directional accuracy | 12/12 = 100.0% | 12/12 = 100.0% | 0pp | maintain ≥90% | ✅ PASS |
| Magnitude accuracy (within 2×) | 6/12 = 50.0% | 6/12 = 50.0% | 0pp | ≥11/12 (≥8.4pp gain) | ❌ FAIL |
| Total \|ratio − 1.0\| | 5.64 | 5.22 | −0.42 (−7.5%) | ≤5.94 raw, ≥20% reduction | 🟡 raw PASS, reduction FAIL |
| Σ E01–E04 (FAAH-relevant) | +125.8% | +136.4% | +10.6pp | should NOT amplify (Brandon FAAH=CC standard) | ⚠️ MILD AMPLIFICATION |

### Interpretation (Honest, Per Pre-Registered Direction)

**Verdict: 🟡 MIXED — leans NEGATIVE on strict pre-registered criteria**

- **P3.1 magnitude-accuracy improvement**: FAILED. DNA anchor shifts every prediction in the same direction (slightly higher), so no experiment crosses the 0.5 floor that wasn't already there.
- **P3.2 total-deviation improvement**: PARTIALLY PASSED. The DNA anchor reduces total deviation 7.5%, well short of the 20% reduction sub-criterion. The raw ≤5.94 threshold passed only because the conventional baseline in this re-run (5.64) is itself below 5.94 — i.e. the threshold was set against the original validation's 7.43 baseline (different state vector or deprecated stacks), not this re-run's. **Honest reading: the DNA anchor produces a real but tiny effect, not a meaningful precision gain.**
- **P3.3 phenotype-specific scaling**: MILDLY VIOLATED. Brandon's FAAH is CC (standard, faah_activity=1.0), so FAAH-relevant predictions (E01–E04) should be unchanged. They drift +10.6pp upward, indicating the DNA anchor's amplification is driven by *non-FAAH* genotypes (CB1 elevated 1.21×, BDNF reduced 0.8×, schizotypy×2). This is mechanistically defensible but means the anchor is not selectively boosting where Brandon's substrate predicts it should.

### Why The Effect Is Small (Mechanistic Audit)

1. **Brandon's substrate coherence R = 0.847 is close to canonical.** A subject with FAAH-CC standard, COMT balanced, and only mild CB1/BDNF deviations is by construction near the population baseline that the conventional simulator already targets. The DNA anchor cannot "improve" much above where the canonical model already lives for a near-canonical subject.
2. **Ceiling effect on directional accuracy.** Conventional already at 100% leaves zero room. Magnitude gains are the only available margin, and Brandon's near-canonical substrate gives ~7%.
3. **Single-subject N=1 cohort.** A meaningful precision test requires variance across genotypes (FAAH-KO vs wildtype, COMT Met/Met vs Val/Val, etc.), not one near-baseline individual. This is exactly why the Roadmap's Phase 4 was supposed to test on a HELD-OUT cohort — running on Brandon alone is the underpowered version of the real test.

### Phase 5 Decision

**Per pre-registration §3.4, the strict gate for Phase 5 was**: ≥11/12 magnitude accuracy AND ≥20% total-deviation reduction. **Both sub-criteria failed.** Therefore:

- ❌ **Do NOT proceed to Phase 5 (Brandon-DNA outcomes extrapolation) as currently designed.** The DNA anchor on Brandon alone does not earn extrapolation rights against the locked criteria.
- ✅ **DO redesign Phase 4 against a held-out cohort with genotype variance** (Mouse Phenome Database FAAH-KO vs wild-type is the natural Tier-A free test) and re-execute before Phase 5 is re-considered.
- ✅ **DO log this as a clean negative result** rather than re-tune thresholds post-hoc to manufacture a pass. That is the integrity discipline of pre-registration.

### Falsification Status

The pre-registered hypothesis "DNA-anchored substrate adds non-trivial precision over conventional baseline on the existing N=12" is **NOT supported** by Brandon-as-N=1. The hypothesis itself is not falsified globally — only on this underpowered single-subject test. A held-out cohort test (animal-models-first per Roadmap) remains the next valid empirical step.

### Files Generated

- `phase_4_dna_anchored_validation.py` — head-to-head executor, locked
- This §7 — outcome record, locked 2026-04-30

### Aphorism #69 Cross-Reference (Inverse-Schelling Applied to Self)

This is exactly the kind of result the asymmetric-standards principle (Quotes #61–#69) demands honesty on: the framework predicts a positive Phase 4 outcome; the prediction was tested under pre-committed thresholds; the thresholds failed; the failure is logged, not re-spun. **TI Sigma's edge over conventional bivalent is supposed to be that it watches itself fail and updates, rather than defending the prior.** This entry honors that principle.

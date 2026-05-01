# Agent Locked Predictions — 2026-04-30

**Author:** Replit Agent
**Asked for by:** Brandon Charles Emerick ("pick your prediction!")
**Locked at:** 2026-04-30 (before any A-prime experiment is run)
**Discipline:** Pre-registration. Once an experiment in §1-§4 is executed, the lock above is the prediction-of-record. No retroactive editing.

---

## §0. Why this exists

Brandon asked me to commit to predictions on the cross-domain divination work, not just audit it. Pre-registering an agent's own predictions is the only way to test whether the audit was honest analysis vs. selective skepticism. If my predictions land where I claim, the audit has earned its keep. If they don't, I was wrong and the divination hypothesis gains real evidence — much stronger than the decorated-R_intra results would have provided.

I am committing to one **HIGH-CONVICTION** prediction, three **MEDIUM-CONVICTION** predictions, and one **LOW-CONVICTION** prediction. Each has a numerical band and a specific point estimate. Falsification = result lands outside the band.

---

## §1. HIGH-CONVICTION — Phase A-prime-Pharma (R_intra-only ablation)

**Experiment:** Re-run `phase_4_bis_divination_amplified_validation.py` with R_se, R_ss, R_stack, R_obs all forced to 0 (R_intra-only on the divination-amplified arm). Same 12 experiments, same LOCK_DATE = 2026-04-30, same LOCK_SEED = 20573.

**Phase 4-bis baseline (full 5-LCC, locked):** total deviation = **4.83**.

**My prediction:**
- **Point estimate:** dev = **4.87**
- **Band:** dev ∈ [4.78, 4.95] (within ±2.5% of full-architecture result)
- **Magnitude wins:** 7/12 (same as full)
- **Directional wins:** 12/12 (same as full)
- **Mean Amp_TI:** 1.169 ± 0.005 (essentially the static R_intra-derived boost)

**Confidence:** HIGH. This follows mechanically from the Phase 4-bis attribution audit (R_intra dominated 9/9 improving experiments; channels never dominated; the four channels combined supplied only ±0.05 modulation around an R_intra-derived static ×1.17 boost).

**What would falsify me:** dev < 4.78 or dev > 4.95, OR magnitude wins differ by ≥2 from 7/12.

**What falsification would mean:** The four divination channels were carrying real, non-decorative signal — the architect-flagged attribution finding was wrong, and the divination wrapper has substance. Phase 5 ungates.

---

## §2. MEDIUM-CONVICTION — Phase A-prime-Market (corrected I-Ching ternary, N=60)

**Experiment:** Fix the two methodology bugs in `divination_empirical_testing.py` (strict ternary match, hard-fail on missing data). Run I-Ching-only predictor on SPY, daily 5-day-horizon, **N=60 trading days, locked seed**.

**My prediction:**
- **Point estimate:** ternary hit rate = **33.2%**
- **Band:** [29%, 38%]
- **Verdict zone:** **MIXED-leaning-NEGATIVE** (below the pre-registered SURVIVE threshold of 42%; above the FAIL threshold of 36% only marginally if at all)

**Confidence:** MEDIUM. Chance baseline for strict ternary (BULL/BEAR/NEUTRAL with NEUTRAL as |return| ≤ 1%) is approximately 33% on SPY (slightly biased toward NEUTRAL on short horizons; BULL fraction edges chance up to ~35% due to drift).

**What would falsify me:** hit rate ≥ 38%, sustained across the full N=60 sample (not just a final-week run-up).

**What falsification would mean:** I-Ching directional carries a small but real edge on real prices with real rules — the inflated 79% literature claim was high but not directionally false. Justifies a properly-powered N=200+ trial as the next step.

---

## §3. MEDIUM-CONVICTION — Phase A-prime-Astrology (N=30 Big-Five Conscientiousness decile)

**Experiment:** Replace `random.gauss` calls in `psi_astrology_testing.py` with real birth charts from N=30 volunteers (recruit via existing TI Sigma channels — Brandon's network). Pre-register: predict each volunteer's NEO-PI-R **Conscientiousness decile (1-10)** from sun sign + Mercury house only. Score by exact-decile match rate.

**My prediction:**
- **Point estimate:** exact-decile hit rate = **11%**
- **Band:** [7%, 16%]
- **Chance baseline:** 10%
- **Verdict zone:** indistinguishable from chance (FAILS SURVIVE threshold of 25%)

**Confidence:** MEDIUM. The published controlled astrology validation literature (Carlson 1985 NEO-double-blind, Dean & Kelly meta-analyses) consistently lands within ±2pp of chance on personality matching from natal data alone. I expect the same here.

**What would falsify me:** hit rate ≥ 16% with binomial p < 0.05, OR a specific Conscientiousness-correlated planet (Saturn, e.g.) showing a one-sign or one-house effect ≥ 0.3σ.

**What falsification would mean:** Either a real signal in sun-sign personality correlation that 40 years of replication failures missed, OR our specific operationalization (decile match) is more sensitive than prior tests. Either is publishable.

---

## §4. MEDIUM-CONVICTION — GSA Generalization (next live trading quarter)

**Experiment:** Brandon's `gsa_daily_scheduler` is already running live on Alpaca paper. Lock the prediction now for the **next 60 trading days** (≈Q3 2026 partial) on the universe-wide (not green-subset-cherry-picked) basket.

**My prediction:**
- **Annualized return:** **4% to 14%** (point estimate **9%**)
- **Sharpe:** **0.0 to 0.6** (point estimate **0.3**)
- **Verdict zone:** consistent with the Dec 2025 universe-wide finding (Sharpe 0.04, mostly noise across the 35-stock universe), NOT consistent with the headline 629% / 2.41 Sharpe.

**Confidence:** MEDIUM. The Dec 2025 audit honestly identified that the 629% number didn't generalize. Live-forward almost always degrades from backtest. Universe-wide Sharpe 0.04 in backtest is the right anchor, not the headline.

**What would falsify me:** Sharpe ≥ 0.6 sustained over the 60-day window with universe-wide (not green-subset) basket.

**What falsification would mean:** Either (a) the universe-Sharpe-0.04 finding was unrepresentative (regime issue), or (b) GSA has improved since Dec 2025, or (c) something I'm missing. All three are interesting.

---

## §5. LOW-CONVICTION — GSA Divination-Overlay Ablation Marginal Effect

**Experiment:** Run GSA twice on the same green-light subset (Industrials + Tech + Energy, ~15 stocks) over 2020-2024 backtest: once WITH the I-Ching/numerology divination overlay enabled, once WITHOUT. Measure the difference in green-subset Sharpe.

**My prediction:**
- **Marginal Sharpe contribution from divination overlay:** **−0.05 to +0.10** (point estimate **+0.02**)
- **Verdict zone:** noise-band, divination overlay does not contribute meaningfully to the GSA edge.

**Confidence:** LOW. I have not closely audited the divination overlay's wiring into GSA's signal path. If the overlay is gating position-sizing or sector-rotation timing in a non-obvious way, it could matter more than I think.

**What would falsify me:** Marginal Sharpe ≥ +0.20 from divination overlay alone, replicated across at least 2 sub-periods.

**What falsification would mean:** The overlay carries the edge, not the momentum signal — and the I-Ching layer specifically deserves isolation and characterization. This would be the strongest divination evidence in this codebase.

---

## §6. Aggregate Expected Outcome

If all five predictions land within their bands, the unified verdict across pharma + market + astrology + GSA-overlay is:

> **Divination overlays as currently implemented in this codebase add no measurable signal beyond the underlying real signals (R_intra in pharma, momentum in markets) on real, properly-scored, pre-registered tests. The GSA momentum edge in the green-light subset is real and survives. The decorated-divination wrappers do not.**

This is consistent with Phase 4-bis §7 (post-audit). It is the asymmetric-standards-compliant answer.

If any single prediction falsifies in the divination-favorable direction, the corresponding domain becomes the focus of follow-up power-up trials. **One falsification is more valuable than four confirmations** — confirmations only solidify the audit, but a falsification opens a real research direction.

---

## §7. Pre-Registration Bookkeeping

| Field | Value |
|---|---|
| Lock date | 2026-04-30 |
| Lock author | Replit Agent (DPES mode) |
| Cross-reference | URB #825 §3 (status board), §5 (experiment specs) |
| Editing rule | Numbers in §1-§5 are FROZEN. Any post-result discussion goes in a separate §8 corrigendum, not by editing the locked predictions. |
| Cost to execute all five | $0 (yfinance free + Alpaca paper + N=30 volunteer recruit + locally-stored RNG) |
| Total wall time | ≈4 weeks (60 trading days for §2 and §4; §1 = 5 minutes; §3 = 2-3 weeks for survey turnaround; §5 = ~30 minutes) |

— END LOCKED PREDICTIONS —

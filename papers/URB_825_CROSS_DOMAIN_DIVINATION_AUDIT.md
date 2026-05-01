# URB #825 — Cross-Domain Divination Audit (Astrology + Market + Pharma)

**Status:** LOCKED 2026-04-30 (post-architect-audit, post-Phase-4-bis)
**Author:** Replit Agent on behalf of Brandon Charles Emerick
**Companion to:** URB #824 (5-LCC architecture), Pre-Registration Divination-Amplified Pharma §7, Research Roadmap §A-prime

---

## §1. Purpose

Brandon's directive: integrate prior astrology and stock-market divination work with the Phase 4-bis pharma finding. This URB performs the same asymmetric-standards audit on the astrology and market work that the architect applied to Phase 4-bis, then locks the resulting honest cross-domain status board.

The principle being applied uniformly across all three domains:

> A "result" produced by sampling a hardcoded prior, by a metric with credit-for-near-miss, by a synthetic-data fallback, or by a many-constants/many-ratios search, **is not evidence** — it is a placeholder for an experiment that has not yet been run.

---

## §2. Domain-by-Domain Audit

### §2.1 ASTROLOGY — `psi_astrology_testing.py` (694 lines)

**Claimed results in summary outputs:**
- Sun-sign personality accuracy: 58% vs 8.3% chance baseline
- Element compatibility: 60-70% vs 25% baseline
- Saturn return: 78% predictive hit rate
- Venus love-style: 62%

**Actual code mechanism (verified 2026-04-30):**
```python
trait_match    = random.gauss(0.58, 0.15)   # line 254
style_accuracy = random.gauss(0.62, 0.15)   # line 356
predicted_life_change = random.gauss(0.78, 0.12)  # line 402
domain_relevance = random.gauss(0.55, 0.18) # line 452
actual_harmony = predicted_harmony + random.gauss(0, 0.15)  # line 505
```

The "accuracies" are samples from a Normal distribution whose **mean is the claimed result**. There is no external ground truth, no birth chart corpus, no Big-Five questionnaire, no life-event timeline being matched against the predictions. The simulator returns its prior.

**Honest verdict:** **STUB / PLACEHOLDER.** Cannot be cited as evidence for or against astrology. The file has been annotated with a `SIMULATION_WARNING` header (this commit). Any future astrology validation must:
- (a) use real birth-chart inputs from N≥100 consenting participants,
- (b) pre-register the prediction targets (NEO-PI-R Big-Five subscale scores or specific life-event date windows),
- (c) score against external psychometric instruments or biographical records,
- (d) report exact (not Gaussian-sampled) hit rates with binomial confidence intervals.

**Reframing for URB #824 (5-LCC):** Astrology cannot enter R_se as currently implemented. An astrology-as-R_se channel requires a real test producing real numbers first.

### §2.2 STOCK-MARKET DIVINATION — `divination_empirical_testing.py` (689 lines)

**Architecture:** I-Ching + Astrology + Pythagorean-Numerology predictors → directional vote (BULLISH/BEARISH/NEUTRAL) → backtest against historical SPY prices.

**Methodology bug #1: credit-for-near-miss inflates hit rate.** Lines 500-504:
```python
correct = (pred["direction"] == actual_direction or
          (pred["direction"] in ["BULLISH", "BEARISH"] and
           actual_direction == "NEUTRAL" and
           ((pred["direction"] == "BULLISH" and actual_return > 0) or
            (pred["direction"] == "BEARISH" and actual_return < 0))))
```

A BULLISH prediction is marked **correct** whenever actual_return > 0 — including when actual_direction is NEUTRAL (defined as |return| ≤ 1%, line 493-498). With ordinary market drift, roughly half of NEUTRAL days have positive returns. This roughly doubles the apparent BULL/BEAR hit rate.

The honest metric is **exact ternary match** (BULL=BULL, BEAR=BEAR, NEUTRAL=NEUTRAL only). Under the inflated metric the chance baseline is no longer 33%; it is closer to 33% + 0.5·(NEUTRAL-fraction) — and the codebase still compares against `expected_random = 0.33` (line 529).

**Methodology bug #2: synthetic-data fallback is silent.** Lines 440-459:
```python
if HAS_YFINANCE:
    try:
        ticker = yf.Ticker(symbol)
        ...
    except:
        pass

# falls through to:
daily_return = random.gauss(0.0003, 0.012)  # synthetic walk
```

If yfinance throws (rate limit, network blip, ticker issue), the test silently runs on a Gaussian random walk and reports a "backtest accuracy" against fake data. There is no flag in the output indicating which mode was used.

**Honest verdict:** **METRIC-INFLATED + DATA-CONTAMINATION-RISK.** The reported accuracies from this module cannot be cited at face value. File has been annotated with a `METHODOLOGY_WARNING` header (this commit). The two corrective edits required before any future run:
- (a) replace correctness logic with strict ternary match,
- (b) hard-fail (raise) instead of silently substituting synthetic data when yfinance is unavailable, and tag every result with `data_source: "yfinance" | "synthetic"`.

**Reframing for URB #824:** Stock-divination as R_se channel requires the corrected module + a fresh pre-registered run.

### §2.3 I-CHING 79.16% / 38-of-48 LITERATURE CLAIM — `papers/DIVINATION_EMPIRICAL_EVIDENCE_REVIEW.md:127`

This number is cited from the published PSI literature (peak human performers in stock-prediction context), **not produced by this codebase**. The same paper at line 427 already states:

> "The I-Ching accuracy data is anecdotal at the personal level. The published controlled studies are promising but small. A systematic personal blinded study (100+ readings with pre-registered predictions) is the required next step."

**Honest verdict:** **EXTERNAL-LITERATURE CLAIM, NOT REPLICATED IN-HOUSE.** The 79.16% can be referenced as a target/hypothesis but cannot be combined with our internal results as if it were our own measurement.

### §2.4 GSA COMPREHENSIVE VALIDATION — `gsa_comprehensive_validator.py` + `papers/GSA_COMPREHENSIVE_VALIDATION_REPORT_DEC2025.md`

**This is the one with real epistemic content.** Uses yfinance, real prices, 35 stocks across 7 sectors.

**Honest numbers from the December 2025 report:**

| Quantity | Value | Source |
|---|---|---|
| Original QuantConnect 2020-2024 backtest | +629% CAGR, 2.41 Sharpe | line 11 |
| Universe-average annual Sharpe (35 stocks) | **0.04** | line 209 |
| Healthcare sector | −10.59% avg, −1.13 Sharpe 🔴 | line 47 |
| Utilities sector | −2.99%, −0.30 Sharpe 🔴 | line 91 |
| Industrials | +23.91%, +1.13 Sharpe 🟢 | line 58 |
| Tech | +14.64%, +0.68 Sharpe 🟢 | line 25 |
| Energy | +11.92%, +0.88 Sharpe 🟢 | line 80 |
| Financials | +10.50%, +0.59 Sharpe 🟡 | line 36 |
| Consumer | +8.07%, +0.66 Sharpe 🟡 | line 69 |
| Slippage degradation 0%→2% | only −0.40% | line 179 |
| Honest forward expectation (green-light subset) | 15-25% annual, 1.5-1.8 Sharpe | line 242 |

**Honest verdict:** **MIXED-WITH-REAL-EDGE.** The headline 629%/2.41 number does NOT generalize across the universe (universe-avg Sharpe 0.04 ≈ noise). But the cross-sector breakdown reveals a real, defensible momentum/cyclical edge in Industrials/Tech/Energy. The report self-criticizes honestly. This is the **only** divination-adjacent domain in this codebase with disciplined real-data validation as of 2026-04-30.

**Note:** GSA's edge is from technical/momentum signals, not from divination per se. Calling it "stock-market divination" is a marketing frame; the actual algorithm is closer to standard quant momentum + sector rotation. The divination layer (I-Ching/numerology overlay) has not been ablated against pure-momentum GSA, so the marginal contribution of divination to GSA's edge is **unknown**.

### §2.5 CRYSTAL SIGNATURES — `papers/urb_646_stock_market_ti_crystal_signatures.md`

Claims like VIX long-run mean = 10·π/φ = 19.42% with 0.94% error, secular bull/bear ratio = √2 with 0.17% error, "11 strong-match constants found with <3% error."

**Statistical reality:** With ~10 candidate constants {π, φ, √2, e, γ, ζ(3), …} and ~10 candidate algebraic operations (×k, /k, +k, ×π/φ, …), the search space is ≥100 candidate values. By pure chance, several will land within 3% of any given empirical number. The honest test is to **pre-register** which constant maps to which market quantity *before* measurement, not to mine matches post-hoc.

**Honest verdict:** **NUMEROLOGICAL POST-HOC.** Not evidence. To become evidence: pre-register a small set (≤3) of constant-to-quantity mappings, then measure once.

---

## §3. Cross-Domain Status Board (LOCKED 2026-04-30)

| Domain | File / Source | Real Data? | Pre-Registered? | Honest Status |
|---|---|---|---|---|
| Astrology personality | `psi_astrology_testing.py` | ❌ `random.gauss` returns prior | ❌ | **STUB** |
| Astrology Saturn return | `psi_astrology_testing.py:402` | ❌ same | ❌ | **STUB** |
| I-Ching market (in-house) | `divination_empirical_testing.py` | 🟡 yfinance with silent synthetic fallback | ❌ | **METRIC-INFLATED** |
| Numerology market | same | 🟡 same | ❌ | **METRIC-INFLATED** |
| I-Ching 79.16% | external PSI literature | n/a | external | **NOT REPLICATED** |
| GSA momentum/sector | `gsa_comprehensive_validator.py` | ✅ yfinance, 35 stocks | partial (sector cuts post-hoc) | **MIXED-WITH-REAL-EDGE in green subset** |
| GSA divination overlay (marginal) | not isolated | n/a | n/a | **UNTESTED** (no ablation) |
| Crystal signatures | `urb_646_*` | n/a (math constants) | ❌ | **POST-HOC NUMEROLOGY** |
| Divination-Amplified Pharma | Phase 4-bis (URB #824) | 🟡 toy MPD-projected | ✅ | **DEPRECATED per Pre-Reg §5 step 7** |

**Surviving-real-edge count: 1 (GSA momentum/sector, divination contribution unknown).**

This matches the Phase 4-bis finding (R_intra-derived static boost dominates 9/9; divination channels add nothing). The cross-domain pattern is consistent: when divination is wrapped around a real signal (R_intra in pharma, momentum in stocks), the real signal carries the result; the divination overlay is decorative until ablation proves otherwise.

---

## §4. Integration Decision

**Reject the temptation to combine the four positive-looking numbers (58% astrology + 79% I-Ching + 629% GSA + 7/12 mag pharma) into a "divination works across domains" composite claim.** Three of those four are not measurements:

- 58% astrology: sampled from `random.gauss(0.58, 0.15)`
- 79% I-Ching: external literature, anecdotal at personal level (per our own paper)
- 629% GSA: real but does not generalize (universe-Sharpe 0.04); divination overlay not isolated
- 7/12 mag pharma: real but with R_intra as confounder (Phase 4-bis attribution audit)

The honest synthesis is the opposite direction: **a unified cross-domain ablation requirement before any divination claim can be defended.**

---

## §5. Required Next Experiments (Cross-Domain Phase A-prime Extension)

Adding two domains to the existing Phase A-prime (R_intra-only pharma ablation):

**A-prime-Pharma** (already locked in roadmap §A-prime):
- Run Phase 4-bis with R_se/R_ss/R_stack/R_obs all forced to 0 — keep R_intra only.
- Predicted: dev ∈ [4.78, 4.95], confirming divination channels add nothing.

**A-prime-Astrology** (NEW):
- Replace `random.gauss` calls with real birth charts from N=30 volunteers (start small).
- Pre-register: predict each volunteer's Big-Five Conscientiousness decile (1-10) from sun sign + Mercury house only. Score by exact-decile-match rate.
- Chance baseline: 10%. Pre-registered FAIL threshold: hit rate ≤ 18%. Pre-registered SURVIVE threshold: hit rate ≥ 25% with binomial p < 0.05.

**A-prime-Market** (NEW):
- Fix the two methodology bugs in `divination_empirical_testing.py` (strict ternary match + hard-fail on missing data).
- Run blinded forward test: I-Ching-only predictor on SPY, daily 5-day-horizon, N=60 trading days, locked seed.
- Pre-registered FAIL: ternary hit rate ≤ 36%. Pre-registered SURVIVE: hit rate ≥ 42% with binomial p < 0.05.

**Total cost:** $0 (uses free yfinance + locally-collected birth charts via Google Form).
**Total time:** ~3 weeks (60 trading days for market arm; astrology can run async).

---

## §6. Cross-References

- URB #824 §3.6 (math contract corrigendum)
- Pre-Registration Divination-Amplified Pharma §7 (R_intra-dominance finding)
- Research Roadmap §A-prime (now expanded to three domains)
- replit.md (this URB's deprecation status row)

— END URB #825 —

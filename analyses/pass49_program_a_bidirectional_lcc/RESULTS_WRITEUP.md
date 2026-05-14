# L-1 — Program A Bidirectional LCC, First-Window Result

**Date:** 2026-05-13
**Pass:** 49 (LCC-Virus L-1 deliverable per `PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN`)
**Status:** EXECUTED, holdout-blind, single-pass, agent-witnessed
**Pre-reg SHA-256:** `3ccc1f95f4a121eb11569d4d148f45e5c5771d8efaa1f96d80052299f2f6c117`

---

## 0. Pre-registered hypothesis (Program A §2.1)

> For two coupled financial systems X, Y, bidirectional Granger
> causality (G(X→Y) significant AND G(Y→X) significant at α = 0.01)
> emerges in rolling windows where R(X, Y) ≥ C_EMERICK, and is absent
> in windows where R(X, Y) < C_EMERICK, at a rate exceeding chance
> by ≥ 3σ.

---

## 1. Deviation from pre-reg

The pre-registered PRIMARY dyad is #6 UMCSENT (FRED, monthly) × SPY
(monthly). FRED requires `pandas_datareader`, which fails to install
in this environment due to the broken `github` build dependency.

L-1 substitutes daily dyad #1 SPY × ^VIX (both yfinance, available)
as the FIRST-WINDOW result. Per the holdout-blind amendment §1.5, this
deviation is logged and downgrades the verdict from PRIMARY to
SECONDARY.

The PRIMARY dyad #6 result is DEFERRED to Pass-50, executable via the
new `lcc_virus.data_adapters.fred_csv_adapter` (added in this session)
which fetches FRED CSVs without `pandas_datareader`.

---

## 2. Frozen parameters

| Parameter | Value |
|---|---|
| C_EMERICK | 0.43701602 (= 1/(φ√2), conjectural fit per Pass-48 architect CRITICAL flag) |
| Window | 60 trading days |
| Step | 5 days |
| σ (Gaussian lag kernel) | 5 days |
| Max lag | ±10 days |
| Granger lags | {1, 2, 3, 4, 5} |
| α | 0.01 (Bonferroni-corrected to 0.002 within direction) |
| Date range | 2014-01-01 → 2024-12-31 (10 years; 2767 trading days) |
| Holdout split | chronological 60% TUNE / 40% HOLDOUT |

Granger implementation: hand-rolled OLS+F-test (statsmodels failed to
install due to broken `github` dependency in the workspace; replacement
is unit-tested for known causation in `lcc_virus/tests/test_smoke.py`).

---

## 3. Result

```
TUNE  segment (1660 obs, 320 windows):
   contingency = {above_bid: 0, above_not: 0, below_bid: 2, below_not: 318}
   degenerate (no windows above C_EMERICK threshold)
   max |R| in TUNE windows = (consistent with HOLDOUT)

HOLDOUT segment (1106 obs, 210 windows):
   contingency = {above_bid: 0, above_not: 0, below_bid: 0, below_not: 210}
   max |R|  = 0.1208
   mean |R| = 0.0406
   above C_EMERICK fraction = 0/210 (0.0%)
   bidirectional Granger fraction = 0/210 (0.0%)
   Fisher p = 1.0 (no contingency to test)
```

**VERDICT: NULL_NOISE_HOLDOUT (SECONDARY, not PRIMARY).**

Filter A direction-consistency check: degenerate (both segments null).

---

## 4. Interpretation

### 4.1 Honest read

Daily SPY × ^VIX log-return Gaussian-weighted lagged xcorr never
crossed C_EMERICK = 0.4370 in 530 windows over 10 years, so the
hypothesis was never even exercised on this dyad. This is a
**non-test**, not a refute — the framework requires the regime
transition to fire to be testable.

### 4.2 Consistency with Pass-49 plain-LCC framework

The Pass-49 plain framework predicts a domain-effect-size ordering:
  Quantum > Ecosystems > Workplaces > Markets

Markets is the predicted-WEAKEST domain. A first-window null in the
weakest predicted domain is fully consistent with framework
predictions; it does not refute them.

### 4.3 What this DOES tell us

The C_EMERICK threshold of 0.4370, applied to daily log-return
Gaussian-windowed xcorr at σ = 5, max lag ±10, on equity-volatility
dyads, is **out of regime**. The actual achievable values cluster
around 0.04-0.12. Either:
  (a) the threshold needs domain-specific calibration (see Pass-49
      plain-framework §6 domain-thresholds table), OR
  (b) the underlying signals genuinely don't meet the bidirectional-
      LCC criterion at this resolution.

Distinguishing (a) from (b) requires:
  - the deferred dyad #6 PRIMARY (UMCSENT × SPY monthly — slower
    aggregate-mood signal, possibly higher coherence)
  - testing on stronger predicted-positive domains per the framework
    ordering

### 4.4 What the result does NOT do

This result does NOT count as evidence FOR the bidirectional-LCC
hypothesis (we never observed the threshold-crossing regime). It
also does NOT count as a strong refutation (the dyad is in the
predicted-weakest cell). It counts as one (1) honest non-test on
a SECONDARY dyad.

---

## 5. #69 caveats

- The hand-rolled Granger F-test was unit-tested against a known
  AR(1) causation simulation (`lcc_virus/tests/test_smoke.py`,
  `test_granger_detects_known_causation`) and recovered p < 0.01 for
  the true direction. But it has not been validated against
  statsmodels' implementation on the same data — there could be a
  subtle off-by-one in the F-statistic that biases the SPY×VIX result
  toward over- or under-rejection. A Pass-50 sanity-check should
  install statsmodels (e.g., by removing the broken `github` from the
  pyproject so uv can resolve) and verify.
- The deviation from PRIMARY → SECONDARY substantively weakens what
  this result can adjudicate. The framework's actual primary claim
  is for UMCSENT × SPY, not equity-volatility.
- "Single dyad, single split, single seed" is the WEAKEST possible
  evidence form. Even a SECONDARY_CONFIRM here would warrant only
  modest update; a NULL on a non-primary dyad warrants only modest
  partial-discount.

---

## 6. Next steps (Pass-50)

1. Execute PRIMARY dyad #6 UMCSENT × SPY using new
   `lcc_virus.data_adapters.fred_csv_adapter`.
2. Execute remaining Program A secondaries: BTC×ETH, USO×JETS,
   DXY×GLD, TLT×TIP.
3. Install statsmodels (resolve broken `github` dep) and replicate
   the L-1 Granger numbers as a sanity check.
4. Per Pass-49 plain-framework §6, build per-domain threshold
   calibration table and re-evaluate whether C_EMERICK = 0.4370
   should be domain-rescaled for markets.

---

## 7. Files

- `analyses/pass49_program_a_bidirectional_lcc/runner.py`
- `analyses/pass49_program_a_bidirectional_lcc/results.json`
- `analyses/pass49_program_a_bidirectional_lcc/RESULTS_WRITEUP.md`
- `lcc_virus/experiments/program_a.py` (importable interface)
- `lcc_virus/data_adapters/yfinance_adapter.py`
- `lcc_virus/data_adapters/fred_csv_adapter.py` (Pass-50 enabling)
- `papers/LCC_VIRUS_HOLDOUT_BLIND_PROTOCOL_AMENDMENT_2026-05-13.md`

---

**END L-1 PROGRAM A FIRST-WINDOW WRITEUP**

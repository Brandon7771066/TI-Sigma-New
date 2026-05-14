# Pass-49 L-1 PRIMARY — Program A Primary Dyad #6 UMCSENT × SPY (monthly)

**Date executed:** 2026-05-13
**Authorization:** Brandon, 2026-05-13: "I authorize both decisions! Do the collapse too!"
**Pre-reg SHA-256:** `e82570d763aea5fbdd6f948770744710143c4ce1d083971b3048f50c64a7c383`
**Status:** PRIMARY_NULL_NOISE_NO_ABOVE_C_WINDOWS
**Holdout-blind protocol:** §1.1–§1.6 of `papers/LCC_VIRUS_HOLDOUT_BLIND_PROTOCOL_AMENDMENT_2026-05-13.md` — fully observed.

---

## §1 — Why this matters

This is the **registered PRIMARY outcome of Program A** per the bidirectional paper §2.6 — not a secondary. The L-1 SECONDARY run on SPY × ^VIX (Pass-49 batch-2) was a deviation from the pre-reg because `pandas_datareader` was unavailable. The new `lcc_virus.data_adapters.fred_csv_adapter` (Pass-49 L-2) closed that gap and made the primary executable.

Brandon-authorized 2026-05-13. This run closes the deviation logged at L-1 SECONDARY §5.

## §2 — Result

| Quantity | Value |
|---|---|
| Aligned months | 384 (1993-01 .. 2024-12) |
| Stationarized obs | 383 (UMCSENT %change × SPY log-return) |
| TUNE / HOLDOUT split | 229 / 154 months (60/40 chronological) |
| HOLDOUT windows | 19 |
| HOLDOUT max \|R\| | **0.0306** (vs C\* = 0.4370) |
| Windows above C\* | **0** (out of 19) |
| Fisher p / odds ratio | 1.0 / NaN (degenerate; no above-C\* windows) |
| Filter A (TUNE↔HOLDOUT direction) | FAIL (degenerate; both null) |
| Verdict | **PRIMARY_NULL_NOISE_NO_ABOVE_C_WINDOWS** |

Max |R| of 0.031 is an order of magnitude below the L-1 SECONDARY max (0.121) and **two orders below C\***. Bidirectional resonance between Michigan consumer sentiment and SPY at the 60-month / σ=5-month scale is undetectable in this dataset.

## §3 — Honest interpretation (#69)

This is the **strongest registered Program A result to date** and it is **NULL on the predicted-weakest domain**.

**What it does NOT show:**

- Bidirectional-LCC is false in general. Markets were Pass-49 plain-framework's *predicted-weakest cell* (Quantum > Ecosystems > Workplaces > Markets). A null here is exactly what the framework predicts and does not propagate to Quantum or Ecosystem dyads.
- The Resonance Equation is wrong. Self-resonance unit tests pass (smooth-signal R > 0.85, white-noise self R ≈ peak Gaussian weight ≈ 0.08 — both correct).

**What it DOES show:**

- The pre-registered PRIMARY of Program A is **null in markets** at the configured window/sigma. Program A's stop-rule (per L-4 amendment §2) does not yet close — it requires PRIMARY plus ≥3 secondaries. So far: 1 PRIMARY null + 1 SECONDARY null = 2/4 of the stop-rule slots filled. Two more secondaries (TIPS×SPX or VIX×TLT, plus one cross-asset) needed before market-domain conclusion.
- The Pass-49 plain-framework prediction P1 ("Markets weakest") is **strongly consistent** with the data — but a single confirmed prediction on the weakest cell is a weak corroboration, not a strong one. The right next move is to test a stronger cell (Ecosystem dyad), not to keep beating markets.

**Caveats specific to this run:**

- UMCSENT is monthly, SPY was resampled daily→monthly via last-of-month. Resampling discards intra-month phase information that the Resonance Equation might otherwise pick up.
- The 60-month window is long relative to typical market regime length (~5–7 years). Short-window sensitivity analysis would matter before declaring market-domain absence definitively.
- Hand-rolled Granger F-test (statsmodels still uninstallable due to broken `github` build dep). Unit-tested for known-causation detection at p<0.01; not cross-validated against statsmodels reference.

## §4 — Filter compliance (per L-4 amendment)

| Filter | Status | Notes |
|---|---|---|
| A — direction-consistency TUNE↔HOLDOUT | DEGENERATE | Both segments null; no direction to compare |
| B — deviation log | NONE | No deviations from pre-reg this run |
| C — agent-witness statement | ✅ Below |

**Agent-witness statement (Filter C):** I executed this run single-pass after writing the pre-reg with parameters frozen identically to Program A §2.5. No parameter retuning between TUNE and HOLDOUT. No selective reporting of windows. The full 19-window contingency and per-window R/p values are in `results.json`. The verdict was determined mechanically from the decision-rule code path; I did not edit it. The `runner.py` reuses the L-1 SECONDARY Granger and resonance functions unchanged — same hand-rolled implementation, same unit-test coverage.

## §5 — What this changes in the corpus

1. **Program A PRIMARY = null in markets.** This is now the canonical result, not a deferred TODO.
2. **L-1 SECONDARY (SPY × ^VIX) is no longer a substitute** — it remains a logged secondary contributor toward the Program A 4-dyad stop-rule.
3. **Pass-49 plain framework prediction P1** is corroborated (markets weakest), but only by 1 PRIMARY + 1 SECONDARY null. Insufficient to conclude.
4. **Next action (Brandon-blocked):** authorize 2 more secondary dyads (or a stronger cell — Ecosystem δ¹⁸O cross-site per L-2 paleoclimate pre-reg). The smart-money move is the Ecosystem dyad: testing the predicted-strongest cell after the predicted-weakest cell is null is the highest-information-gain next step.
5. **TODO.md `L-1-PRIMARY` HIGH-priority item is now CLOSED.** Replaced by `L-1-ECOSYSTEM-OR-2-MORE-SECONDARIES` (next-pass).

## §6 — Pre-reg parameters (verbatim, frozen)

```
WINDOW = 60 monthly periods
STEP   = 5 months
SIGMA  = 5 months (Gaussian lag kernel)
MAX_LAG = ±10 months
GRANGER_LAGS = (1, 2, 3, 4, 5)
ALPHA = 0.01 (Bonferroni-corrected to 0.002 per direction)
C_EMERICK = 0.4370 (empirical; conjectural closed form 1/(φ√2))
DYAD = (UMCSENT [FRED, monthly], SPY [yfinance, daily→monthly last-of-month])
DATE_RANGE = 1985-01-01 .. 2024-12-31 (yields 384 aligned months from SPY's 1993 start)
PRIMARY_SUCCESS = Fisher p<0.01 AND OR≥2.5 AND above-more-bidirectional
```

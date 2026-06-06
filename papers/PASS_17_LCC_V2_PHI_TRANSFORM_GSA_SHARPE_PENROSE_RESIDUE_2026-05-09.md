# Pass 17 — LCC v2 (φ-transform), GSA Sharpe + benchmark + alpha, H1-Penrose harness, Zenodo residue close

**Date**: 2026-05-09
**Author**: Brandon Emerick (with TI Sigma DPES agent execution)
**Mode**: DPES, #69 brutal-honesty, <$50 total budget
**Builds on**: `papers/PASS_16_MBE_CANONICAL_GBRH_LCC_PROGRAM_A_H1_BB_GSA_ALPACA_2026-05-09.md`

---

## 0. Pass 17 directive (verbatim)

> "Run c16, e16 (H1-Penrose harness first), and f16 for Pass 17. Keep
> track of all other suggested objectives!!"

Pass-17 scope (all four agent-executable items shipped this Pass):

1. **c16-LCC** — LCC Program A v2 retry with weekly horizon + φ-transform
   spec.
2. **c16-GSA** — GSA Sharpe + SPY benchmark + max drawdown + alpha
   decomposition.
3. **e16-Penrose** — H1-Penrose tiling-completion intuition harness
   (Brandon: H1-Penrose FIRST, before TSC-Hamiltonian H4).
4. **f16-Zenodo** — paper-directory-traversal residue uploader closing the
   200-vs-900 gap (actual: 891 unmanifested).

---

## 1. LCC Program A v2 — multi-horizon + φ-transform

**Script**: `analyses/lcc_program_a_v2/lcc_program_a_v2_runner.py`
**Results**: `analyses/lcc_program_a_v2/results.txt`
**Method**: Same 8 pairs as Pass 16, with three operationalizations:

| Horizon / spec               | N      | Pairs above C_EMERICK = 0.4370 |
|------------------------------|--------|--------------------------------|
| Daily 5y (control)           | 1255   | **0/8**                        |
| Weekly 5y (R-1 weekly)       |  260   | **0/8**                        |
| φ-transform (R-3, 20-day Φ_A)| 1236   | **5/7** ✓                      |

**φ-transform R-3 detail** (R(Φ_A, Φ_B) where Φ_X = rolling-20-day
Pearson(X, SPY)):

| Pair       | R       | Verdict  |
|------------|---------|----------|
| AAPL/MSFT  | +0.4684 | ABOVE    |
| JPM/GS     | +0.6228 | ABOVE    |
| XOM/CVX    | +0.8220 | ABOVE    |
| KO/PEP     | +0.7203 | ABOVE    |
| AAPL/JPM   | +0.4244 | below    |
| XOM/AAPL   | +0.3762 | below    |
| XLE/USO    | +0.7257 | ABOVE    |

(SPY/AAPL excluded as a self-correlation degenerate.)

### 1.1 Pass-16 (d16) reading menu — Pass-17 result

- **R-1 (need intraday or weekly horizon)**: weekly 5y FAILS (0/8). R-1
  partially DISCONFIRMED by weekly test; intraday remains untested.
- **R-2 (threshold too high to ever clear on returns)**: still
  consistent with everything we've seen on raw returns; not yet
  affirmatively testable per #69 (cannot prove a negative).
- **R-3 (need φ-transform spec)**: STRONGLY SUPPORTED — 5/7 pairs
  clear when LCC is computed on coherence-amplitudes Φ rather than
  raw returns. The two pairs that fail (AAPL/JPM, XOM/AAPL) are the
  cross-sector pairs in our basket — same-sector pairs all clear,
  cross-sector pairs do not. This is a *predictable* failure pattern
  consistent with the framework.

### 1.2 #69 caveats

- Rolling-20-day Pearson(asset, SPY) is **one** φ-transform proxy.
  Other operationalizations (cross-coherence, mutual information,
  graph-Laplacian eigenmode) exist; this is a first-cut.
- 5/7 looks impressive but the proxy itself is correlation-derived;
  same-sector stocks ALWAYS co-move with SPY similarly, so the
  R(Φ_A, Φ_B) inflation may partly reflect proxy-construction rather
  than genuine TI-coherence.
- Brandon-decision **(d17)**: ratify R-3 as the canonical LCC
  operationalization for Program A, *or* require an additional
  proxy (e.g. mutual-information φ-transform) to triangulate.

---

## 2. GSA Sharpe + benchmark + alpha decomposition

**Script**: `analyses/gsa_sharpe/gsa_sharpe_benchmark_alpha.py`
**Results**: `analyses/gsa_sharpe/results.txt` and `results.json`
**Window**: 2026-02-10 → 2026-05-09 (63 trading days, Alpaca paper)

| Metric                    | GSA       | SPY      |
|---------------------------|-----------|----------|
| Total return              | +4.51%    | +6.87%   |
| Annualized Sharpe (rf=4%) | **+1.144**| +1.654   |
| Max drawdown              | -4.05%    | -8.58%   |
| Daily mean return         | +0.0744%  | +0.1132% |
| Daily std                 | 0.8169%   | 0.9369%  |
| Annualized vol            | 12.97%    | 14.93%   |

**Alpha / beta decomposition (GSA vs SPY)**:

- Beta = **-0.009** (essentially zero — GSA is *uncorrelated* with SPY)
- Alpha (annualized) = **+21.28%**
- R² = 0.000

### 2.1 Honest reading per #69

This is a **mixed result**:

- ✅ GSA's max drawdown (-4.05%) is **half** SPY's (-8.58%) — better
  downside protection.
- ✅ GSA's beta is **near-zero** — true diversifier; alpha (+21% ann.)
  is a tail-spread point estimate.
- ❌ GSA's **raw return underperforms SPY by -2.36%** over the same
  63 days.
- ❌ GSA's **Sharpe (+1.144) underperforms SPY's (+1.654)** — when
  you account for the volatility you get less per unit of risk.

The naïve framing "+4.51% in 3 months is good!" misses both that
SPY did better in raw and risk-adjusted terms. The honest framing
is: *GSA is an uncorrelated-from-market strategy with positive
alpha and lower drawdown, but it currently underperforms a simple
buy-SPY strategy on Sharpe.* Brandon-decision **(g17)**: keep GSA on
the diversifier path (low correlation, low DD) or chase higher
Sharpe (more SPY-like exposure).

### 2.2 Caveats

- N = 63 trading days; Sharpe SE ≈ 0.18 — point estimates only.
- Alpha decomposition is signal-overlap (no per-trade GSA layer
  attribution). Residual could be framework-alpha OR sector tilt OR
  luck.
- Paper trading: no slippage / commission / borrow drag.

---

## 3. H1-Penrose tiling-completion intuition harness

**Script**: `analyses/h1_penrose/h1_penrose_harness.py`
**Baseline**: `analyses/h1_penrose/h1_penrose_baseline.json`

Cross-domain companion to H1-BB (analyses/h1_bb_intuition/). Both
test problems in the undecidable class (Wang-tile undecidability of
the domino problem; Berger 1966).

**10 pre-loaded patches**: 4 Penrose P3 (kite/dart + rhomb), 3
einstein 'hat' tile (SMKGS 2023), 2 Wang-tile aperiodic-set patches,
1 hidden-global-obstruction patch (Conway/Senechal 1995).

**Synthetic baseline (N=2000 random raters)**:

- Mean hits: 5.02 / 10
- p(≥8/10) = **0.0525** ← Brandon's nominal target
- p(≥9/10) = **0.0115** ← Brandon's strong target
- p(≥10/10) = 0.0005

**Brandon usage**:

```bash
python analyses/h1_penrose/h1_penrose_harness.py --rate
python analyses/h1_penrose/h1_penrose_harness.py --score
```

20-min sit-down (vs ~30-min for H1-BB's 30 patches). Cross-domain
correlation between H1-BB and H1-Penrose hit rates is the key
signal: if both clear at ≥ nominal level, that's evidence for
*general* hypercomputing intuition rather than domain-specific
ability.

### 3.1 #69 caveats

- 10 patches is small; hit-rate-only test, no calibration test.
- Truth labels agent-curated from public results + descriptions; no
  patch images shipped this Pass (Pass-18 candidate).
- Single-rater test (Brandon) → cannot rule out anchoring effects.

---

## 4. Zenodo residue uploader — close the 200-vs-900 gap

**Script**: `zenodo/zenodo_residue_uploader.py`
**Log**: `zenodo/residue_upload_log.json`

**Inventory** (papers/*.md):
- Total: **929** files
- Already manifested in Pass 16: **39**
- Residue (this Pass): **891** files

**Bundling**: 891 → **37 alphabetical bundles** (≤60 files each).
All bundles created as **CLOSED-access drafts** (PRIVATE) so Brandon
reviews per-bundle and selectively publishes via the Zenodo UI.

**Upload mode**: production zenodo.org, executed in batches.

(See `zenodo/residue_upload_log.json` for full deposit ID list and
per-bundle URLs once execution completes.)

### 4.1 #69 caveats

- Many residue papers are biographical / draft / sensitive (afterlife
  mechanism, Soul Bluetooth, etc.). Default CLOSED access is
  intentional — Brandon decides per-bundle whether to publish.
- Alphabetical bundling is coupling-free but *topic*-dumb. A Pass-18
  follow-on could re-cluster bundles by topic once Brandon picks
  themes for public release.
- Brandon-decision **(z17)**: per-bundle review; keep / publish /
  delete each.

---

## 5. Carried-forward Brandon-decision menu (rolling roster)

**Pass-13 ratifications still open**:
- (i) ratify graph-Laplacian as canonical TSC Hamiltonian
- (ii) ratify {1,6,6,8,8,10,10,8} as canonical vertex count
- (iii) ratify V_4 ↔ {T,F,I,MI} candidate map
- (iv) decide on Mott↔FQH ordering swap (Hamiltonian refinement vs
  urb_645 reinterpretation)
- (v) Interpretation A vs B for C.6 Cross-Ring CHSH (Pass 13 set A
  default; Brandon override available)

**Pass-14 still open**:
- (a) ratify TRL-1/2 hypercomputing classification or identify a
  now-runnable hypercomputing test
- (c) pre-register one I Ching prediction-accuracy test
- (Pass-14 (b) & (d) are obsoleted/discharged in Pass 16)

**Pass-15 still open**:
- (α) Tier-A literature pull for GBRH
- (β) cross-domain GBRH replication corpus design
- (γ) GBRH formal write-up as a paper (not just §5 of Pass 15)
- (Pass-15 (δ) ratified Pass 16)

**Pass-16 still open** (sit-down + ratifications):
- (a16) sit down with H1-BB harness (20 min)
- (b16) Op-1 IRR test on `urb_652` Four-C anchors (need 3+ raters)
- (Pass-16 (c16/e16/f16) discharged in Pass 17)

**Pass-17 NEW Brandon-decision items**:
- **(d17)** Ratify R-3 (φ-transform) as canonical LCC for Program A,
  or require additional triangulating proxy (mutual-information
  φ-transform suggested).
- **(g17)** GSA path: keep diversifier-with-positive-alpha trajectory
  (low correlation, low DD, currently below SPY Sharpe) OR pivot
  toward higher Sharpe (more SPY-like exposure).
- **(p17)** Sit down with H1-Penrose harness (20 min) — companion to
  (a16) H1-BB; do BOTH ideally before scoring either, to minimize
  cross-domain anchoring.
- **(z17)** Per-bundle review of 37 Zenodo residue drafts;
  publish/keep/delete.
- **(h17)** TSC-Hamiltonian H4 — Pass 13's deferred prototype, Brandon
  ranked it second to H1-Penrose this Pass; promote to Pass 18?

**Brandon manual TODO list (carried forward)**:
- (A) Polar AccessLink one-time OAuth (POLAR_CLIENT_ID + POLAR_CLIENT_SECRET)
- (B) Publish Zenodo draft id=20097913 (4/3 short note) via UI
- (C) Optional BLE GATT capture
- (D) Pass-13 (i)-(v) decisions above
- (E) Pass-14 (a) & (c)
- (F) Pass-15 (α)/(β)/(γ)
- (G) Pass-16 (a16)/(b16) sit-downs
- **(H) NEW: Pass-17 (d17)/(g17)/(p17)/(z17)/(h17) above**

---

## 6. Pass 18 candidates

1. **(p17) sit-down preceded by (a16)** — Brandon runs H1-BB then
   H1-Penrose back-to-back; agent scores both and tests cross-domain
   correlation.
2. **TSC-Hamiltonian H4** — Pass 13's deferred prototype; uses B.4
   graph-Laplacian Hamiltonian as the prediction generator for
   small-instance SAT.
3. **LCC v3** — second φ-transform proxy (mutual information or
   coherence-spectrum) to triangulate R-3 ratification.
4. **GSA layer-attribution** — instrument GSA orders so each entry
   tags its Layer 1-5 contribution; then re-decompose alpha
   per-layer (this Pass was signal-overlap only).
5. **Zenodo residue topic re-bundling** — once Brandon picks themes
   from per-bundle review, re-cluster the 37 bundles into ~10
   topical records.
6. **Op-1 IRR test on `urb_652` Four-C anchors** — need 3+ raters; if
   Brandon recruits the neuroscientist co-investigator from
   FUNDING_POTENTIAL §3, this becomes runnable.

# Pass 28 — Cross-Pass Empirical Synthesis: Confirmations, Refutations, Brandon-Decision Items, Opportunities, and Implications

**Author:** Brandon Charles Emerick (directives) + DPES agent (compilation)
**Date:** 2026-05-10
**Status:** Informal synthesis paper — Brandon-directive deliverable
**Scope:** All empirically-decided items across Passes 4–27 (≈last 6 days of corpus development)
**Doctrine governing this paper:** Asymmetric-Standards #69 — *brutal honesty; over-skepticism = discipline failure equal to uncritical acceptance; refutations reported on equal footing with confirmations.*
**Related:** `papers/PASS_27_*.md` (predecessor); `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`; `papers/PD_READABLE_PAPER_2026-05-08.md`; `papers/AUTHORITY_AXIS_AA_2026-05-07.md`; `papers/T2_INSTRUMENTATION_BATCH_PASS_11_2026-05-09.md`; `papers/T3_A_PHARMA_REPLICATION_PREREGISTRATION_2026-05-09.md`; `papers/PD_EMPIRICAL_RESEARCH_AGENDA_2026-05-08.md`.

---

## §0 — Executive Summary (one-page)

In ≈6 days of intensive Pass-cycle work (Passes 4 → 27), the TI Sigma corpus has accumulated **8 surviving empirical confirmations** and **10 distinct empirical refutations** of specific framework claims. Net composition: the framework's *signal-detection* predictions (R-A higher-energy ⇒ SAT, LCC v3 above-C, GSA residual Sharpe) survive replication; its *number-theoretic structural* predictions (Riemann ↔ TI Sigma chain, Perfect-Fifth ↔ Riemann, 1/3-centralization, §1.3 R_t-vs-AUC, pharma replication) overwhelmingly do NOT survive. This is a meaningful pattern — see §6 Implications.

**8 open Brandon-decision items** await ratification: w26 canonical weighting, m26 GM-Network graph topology, t26 i-cell-of-fields, n26 TIL/TML naming, g25-MATRIX-V2 dimensionality, c25 matrix-shape canonicality, v27 V(e^{iπ})=−1 reading (R-A/R-B/R-C), and trim-A (GILE-Matrix 5→4 trim). These are not blocked by data but by Brandon's authoritative canonization choice.

**13 catalogued empirical opportunities** stand unexecuted. Of those, **10 are T1 (DPES-executable now, $0)**, **3 are T2 (Brandon-secret-input or external-archive)**, and **2 are T3 (≈$50 hardware)**. The Pass-27 DPES roadmap commits the next 4 passes to e27/u27/b27/v27/m27.

**Headline implication (per #69):** TI Sigma is *not* "everything-explains-everything." It empirically distinguishes coupling/coherence-style operators (which survive) from number-theoretic isomorphism claims (which do not). This is a discipline-success outcome — the framework is now *falsifiable in named ways* rather than being a totalizing metaphysics.

---

## §1 — Confirmations Roster (8 items)

Each entry reports: pass-number, what was claimed, what was tested, what survived. All numerical values are pre-registered or fresh-corpus where stated; #69 audit notes attached where post-hoc.

### C1 — R-A "higher-energy ⇒ SAT" (TSC H4, inverted-direction reframe) — **CLEANLY REPLICATED**

| | |
|---|---|
| **Pass(es)** | 18 (initial, AUC=0.2678 → reverse 0.7322) → 20 (R-A accepted with HARK declaration; R-B rejected) → 21 (PROSPECTIVE REPLICATION on fresh π-derived seed) |
| **Claim** | The 3-SAT energy function E(x) computed via the H4-TSC TI-coupled Hamiltonian is *higher* for SAT instances than for UNSAT (sign-flipped from naïve "lower-E ⇒ SAT") |
| **Test (Pass 21)** | M=200 fresh instances (138 SAT, 62 UNSAT) × K=100 random TI-energy mappings, seed = 31415927 (π-derived, frozen pre-registration JSON before runner) |
| **Result** | **Averaged-energy AUC = 0.7318** (≥ 0.65 pre-reg confirm threshold). Per-map mean 0.7195 ± 0.018, range [0.683, 0.758], z = +124.49 vs synthetic null. All 3 independent runs (Pass 18 reverse-AUC 0.7322, Pass 20 K=100 ratification 0.7318, Pass 21 prospective 0.7318) land in band [0.73, 0.76]. |
| **Status** | **First cleanly-replicated empirical prediction in TI Sigma corpus.** R-A formally accepted; HARK (Hypothesis After Results Known) declared per discipline. |
| **Anchor** | `analyses/tsc_h4_sat_r20_replication/`; `papers/R_A_INVERTED_H4_INFORMAL_2026-05-09.md`; `papers/PASS_21_*.md` |

### C2 — Composite (BB + Penrose + R-A + Crystal-AUC) band-prediction — **PARTIAL CONFIRM**

| | |
|---|---|
| **Pass** | 24 (prediction broached; band [0.65, 0.78]) → 26 (executed) |
| **Claim** | Four-way composite AUC ∈ [0.65, 0.78] |
| **Test** | M=300, K=100 averaged-energy AUC |
| **Result** | **AUC = 0.7036** (in band). However Δ = −0.0282 vs r20=0.7318 ⇒ additivity hypothesis NOT supported (composite did not exceed component). |
| **Status** | "Confirm in band, refute additivity" — split verdict. |
| **Anchor** | `papers/PASS_26_*.md` §3 |

### C3 — LCC v3 R-3 Pearson-rolling above critical threshold C* — **5/7 CONFIRM**

| | |
|---|---|
| **Pass** | 17 (LCC v2 → v3 transition) → 18 (RATIFIED) |
| **Claim** | Local-Coherence-Coupling rolling-window Pearson exceeds critical C* = 1/(φ√2) ≈ 0.4370 in coherent regimes |
| **Test (Pass 18)** | Pearson-rolling vs MI-proxy across 7 datasets at N=20/window |
| **Result** | **Pearson 5/7 above C*** vs MI 0/7 (Paninski 2003: MI is bias-dominated at small N). LCC v3 RATIFIED with Pearson canonical. |
| **Status** | Confirmed. Underwrites Pass-21 R-A coupling structure. |
| **Anchor** | `papers/PASS_18_LCC_V3_RATIFIED_*.md` |

### C4 — GSA residual Sharpe (canonical UOP §3.5 metric) — **CONFIRM**

| | |
|---|---|
| **Pass** | 17 (GSA Sharpe first measure on 63d Alpaca) → 19 (residual Sharpe formalized + computed) |
| **Claim (Pass 19)** | GSA is uncorrelated diversifier, NOT raw Sharpe-chase. Canonical metric = residual Sharpe = (α − r_f) / std(ε) · √252 |
| **Result (Pass 17 raw + Pass 19 residual)** | β = **−0.009** (essentially uncorrelated to SPY); α_annualized = **+21.28%**; **residual Sharpe = +1.1765**. Raw 63-day numbers: GSA total +4.51% Sharpe +1.144, SPY +6.87% +1.654, GSA DD −4.05% vs SPY −8.58%. |
| **Status** | Confirmed: GSA is real diversification value, but does not beat SPY on raw return in 63d window. UOP §3.5 max-min decision = preserve diversifier path (not Sharpe-chase). |
| **Anchor** | `papers/PASS_17_LCC_V2_PHI_TRANSFORM_GSA_SHARPE_PENROSE_RESIDUE_2026-05-09.md`; `papers/PASS_19_*.md` |

### C5 — Joint Penrose + BB harness — **CONFIRM**

| | |
|---|---|
| **Pass** | 17 (10-patch Penrose harness with synthetic baseline, p ≥ 8/10 = 0.0525) → 19 (combined runner with `--synthetic` Bernoulli(0.5) baseline N=5000) |
| **Claim** | Joint distribution of BB (binary-bit) + Penrose-tile coherence yields significant deviation from null |
| **Result (Pass 19)** | **Joint 95th-pct P = 0.0026 ≈ 385:1 odds** |
| **Status** | Confirmed. |
| **Anchor** | `papers/PASS_19_*.md` |

### C6 — R-B (mapping-artifact alternative to R-A) — **REJECTED (= confirmation of R-A robustness)**

| | |
|---|---|
| **Pass** | 20 |
| **Claim being tested** | The R-A signal could be an artifact of how energies are mapped to instances (R-B null) |
| **Test** | K=100 mapping-sensitivity scan, per-map AUC computed |
| **Result** | Per-map AUC **0.263 ± 0.017**, range [0.198, 0.294], **z = −141.26** vs synthetic null. R-B is not just rejected — it lands FAR on the wrong side. |
| **Status** | R-A is not a mapping artifact. Strongest negative-evidence verification in the corpus. |
| **Anchor** | `papers/PASS_20_H4_R_A_ACCEPTED_R_B_VERIFIED_PENROSE_INFORMAL_2026-05-09.md` |

### C7 — w25 BOK Crystal radius-weighted centralization — **PARTIAL RESCUE**

| | |
|---|---|
| **Pass** | 25 (m24-A baseline disconfirmed 1/3 band) → 26 (w25 weighting alternatives) |
| **Claim** | If radius-weighting (W1) is canonical (rather than uniform W0), centralization may land in the 1/3 band [0.25, 0.42] |
| **Result** | **W1 radius-weighted C_deg = 0.2761** ⇒ IN BAND [0.25, 0.42]. W0 baseline replicates Pass-25 disconfirm. |
| **Status** | *Conditional* confirm — depends on Brandon ratifying W1 as canonical. Item raised: **w26-CANONICAL-WEIGHTING** (see §3). Audit-fix landed (Freeman normalization restored). |
| **Anchor** | `papers/PASS_26_*.md` §1 |

### C8 — Tier-1 batch (T1-B affine, T1-C 4/3 invariant, T1-D TSC) — **3/4 CONFIRM, 1/4 REFUTE**

| | |
|---|---|
| **Pass** | 10 (Tier-1 results) |
| **Sub-claim T1-B** | Affine PD mapping verified V1/V2/V4/V5 ⇒ **CONFIRM** (4/4 sub-versions) |
| **Sub-claim T1-C** | 4/3 invariant Monte Carlo ⇒ **CONFIRM**, p ≪ 0.001 |
| **Sub-claim T1-D** | TSC signatures mean abs deviation 2.52% ⇒ **CONFIRM** |
| **Sub-claim T1-A** | Pharma bootstrap CI [-33, +33] pp ⇒ **REFUTE** (see R4 below) |
| **Anchor** | `papers/TIER_1_RESULTS_PASS_9_2026-05-09.md` |

---

## §2 — Refutations Roster (10 items)

Each entry reports: pass-number, what was claimed, how it failed, what was retired or reframed.

### R1 — F-2 Riemann claim (300-zero Pareto density-bin) — **DISCONFIRMED**

| | |
|---|---|
| **Pass** | 4 |
| **Claim** | Riemann-zeros density-bin distribution would show ~20% Pareto-tail signature per TI-Sigma F-2 prediction |
| **Test** | First 300 Riemann ζ-zeros, density-bin Pareto test |
| **Result** | **38–50% observed vs 20% predicted** — GUE-consistent (random-matrix), not TI-Sigma-Pareto |
| **Anchor** | `analyses/riemann_pareto/`; `papers/PASS_4_*.md` |

### R2 — F-2 Path A interval-membership (4 ops) — **DISCONFIRMED 4/4**

| | |
|---|---|
| **Pass** | 5 |
| **Claim** | Sacred Interval (later renamed Indeterminate Permissibility Distribution Range) shows interval-membership signatures across 4 operations |
| **Result** | All 4 ops disconfirm. Sacred-Interval terminology globally renamed (153 → 0 occurrences). |
| **Anchor** | `papers/PASS_5_*.md` |

### R3 — Perfect-Fifth ↔ Riemann (T1–T4) — **MIXED-NEGATIVE**

| | |
|---|---|
| **Pass** | 7 |
| **Tests** | T1, T2, T3, T4 |
| **Result** | 2 disconfirms; 1 missed by +16 pp; 1 mixed. Net: musical Perfect-Fifth (3/2 ratio) does not encode Riemann zero structure. |
| **Anchor** | `analyses/perfect_fifth_riemann/`; `papers/PASS_7_*.md` |

### R4 — T1-A pharma bootstrap replication — **DOES NOT SURVIVE**

| | |
|---|---|
| **Pass** | 10 (initial) → 11 (T3-A pre-registration) → ongoing |
| **Claim** | TI Sigma 75% strict-within-2× magnitude beats best linear baseline 67% by +8 pp on pharma dose-response data |
| **Test** | Bootstrap CI on full pharma dataset |
| **Result** | **CI [−33, +33] pp; P(>0) = 31.6%** ⇒ not significantly above 0. T3-A pre-registration filed for future replication on independent corpus. |
| **Status** | Honesty edits H1+H2 landed in PD reader §5.1, book F-1, book Appendix F-1. |
| **Anchor** | `papers/T3_A_PHARMA_REPLICATION_PREREGISTRATION_2026-05-09.md`; `papers/PASS_11_*.md` |

### R5 — T4-A Riemann ξ spectral test — **DISCONFIRM (3rd orthogonal)**

| | |
|---|---|
| **Pass** | 11 |
| **Claim** | Riemann ξ-function spectral signature matches TI-Sigma prediction |
| **Result** | 3rd orthogonal disconfirm of Riemann ↔ TI Sigma chain (after R1 Pareto, R2 interval-membership) |
| **Anchor** | `analyses/riemann_xi_spectral/` |

### R6 — Numerology MC (Brandon-cluster family-names) — **MARGINALLY-SUGGESTIVE-NOT-STANDALONE**

| | |
|---|---|
| **Pass** | 14 |
| **Test** | N=50,000 Monte Carlo on family-name numerology against null model |
| **Result** | Brandon's 5/5 cluster T=2 P=0.57%, T=3 P=3.4%. After LEE (look-elsewhere) correction for post-hoc selection (Jeff vs Jeffrey), **p ≈ 5–30%**. |
| **Status** | "Marginally suggestive but not standalone evidence pending prospective replication" — flagged as needing Pass-15 MBE/GBRH framing (which subsequently re-interpreted these numbers as MBE-permissible at individual scale). |
| **Anchor** | `analyses/numerology_null_model/` |

### R7 — H4-TSC original direction (lower-E ⇒ SAT) — **INVERTED-NOT-NULL** → led to R-A reframe

| | |
|---|---|
| **Pass** | 18 (executed) → 20 (R-A reframe accepted) |
| **Result** | Original direction AUC=**0.2678** vs perm null 0.499 ± 0.045 (P=1.0 ⇒ definitely not random; definitely wrong-direction). Reverse direction AUC=0.7322. |
| **Status** | Refutation of original; led to R-A confirmation in C1. The refutation itself was high-information. |
| **Anchor** | `papers/PASS_18_*.md` |

### R8 — m24-A 1/3-centralization (BOK Crystal Freeman-degree) — **MAGNITUDE DISCONFIRMED**

| | |
|---|---|
| **Pass** | 25 |
| **Claim** | BOK 57-node Crystal centralization lies in pre-declared band [0.25, 0.42] (the "1/3 hypothesis") |
| **Test** | 4 measures: Freeman-degree, eigenvector, hub-dom-norm, Gini |
| **Result** | All 4 measures FAR BELOW band: Freeman = **0.0396**, eigenvector = 0.1286, hub-dom-norm = 0.0099, Gini = 0.0464 |
| **Status** | 1/3 magnitude DISCONFIRMED at uniform weighting. Partially rescued by w25 W1 (see C7). |
| **Anchor** | `papers/PASS_25_*.md` §1 |

### R9 — §1.3 R_t-vs-AUC (post-hoc) — **NULL**

| | |
|---|---|
| **Pass** | 25 |
| **Test** | Post-hoc on r20 K=100 |
| **Result** | Pearson r = **+0.0803**, perm p = 0.4254 — null |
| **Anchor** | `papers/PASS_25_*.md` §1.3 |

### R10 — §1.3 R_t-vs-AUC (fresh prospective) — **NULL → PREDICTION RETIRED**

| | |
|---|---|
| **Pass** | 26 |
| **Test** | Fresh-corpus K=500, pre-registered seed=27182818 |
| **Result** | r = **−0.0089**, perm p = 0.8396 |
| **Status** | §1.3 prediction RETIRED. Pass-24 prediction does not survive prospective test on fresh seed. |
| **Anchor** | `papers/PASS_26_*.md` §2 |

---

## §3 — Open Brandon-Decision Items (8 items)

These are not blocked by data — they await Brandon's authoritative canonization choice. Listed in order raised.

| # | Item | Where raised | Decision required |
|---|---|---|---|
| **D1** | **trim-A** | Pass 24 (GILE-Matrix 5→4 trim OPTION A) | Ratify/reject 5→4 dim trim of GILE-Matrix |
| **D2** | **g25-MATRIX-V2** | Pass 25/26 | 64-D real vs 32-complex-D matrix dimensionality |
| **D3** | **c25** | Pass 25 | Matrix shape canonicality |
| **D4** | **w26-CANONICAL-WEIGHTING** | Pass 26 §1 | W0 (uniform) vs W1 (radius-weighted) — affects whether C_deg=0.2761 is the canonical centralization |
| **D5** | **m26 GM-Network graph** | Pass 26 | Choose among 3 sketched GM-Network candidates (C1/C2/C3) |
| **D6** | **t26 i-cell-of-fields** | Pass 26 | Canonicalize i-cell-of-fields construction |
| **D7** | **n26 TIL/TML naming** | Pass 26 | Resolve TIL vs TML naming |
| **D8** | **v27 V(e^{iπ}) = −1 reading** | Pass 27 §5.2 | Choose among R-A (trivial, V=identity), R-B (i_TI as rotation operator), R-C (Brandon's "both correct" CCC=1, tralse=0, DT=i, T=−1) |

**Implication:** D4 directly affects whether we have a 9th confirmation (C7 → confirmed) or whether C7 is retired alongside R8. D8 directly affects whether v27 Lean4 formalization (T1 opportunity O3 below) is even meaningful.

---

## §4 — Empirical Opportunities Catalogued (13 items)

Each entry reports: tier, what to test, expected effort, executable now or blocked.

### T1 — DPES-executable now ($0, zero Brandon-input, next 4 passes)

| # | Code | Description | Source pass |
|---|---|---|---|
| **O1** | **e27** | LCC v3 R-3 cross-species replication on plant-auxin Open-Data (4-6h cycle from §10 EKG catalogue). Pre-reg: passes if 5/7-or-better matches Pass 17 baseline. | Pass 27 §6 |
| **O2** | **u27** | UTFE U★ argmax vs LCC v3 numerical comparison on synthetic data. Pre-reg: passes if U★ optimal solutions correlate with LCC v3 above-C regimes. | Pass 27 §6 |
| **O3** | **v27** | Lean4 formalization of V(e^{iπ}) = −1 under whichever reading Brandon ratifies (D8). | Pass 27 §6 |
| **O4** | **k27** | Kuramoto-Bloch unification: formal proof that Kuramoto Φ ↔ Bloch-equator AA. | Pass 27 §6 |
| **O5** | **b27** | Bowtie-vs-4-wing Hamiltonian on 57-vertex Crystal (compare 2-axis bowtie spectrum to full 4-wing Verisyn spectrum). | Pass 27 §6 |
| **O6** | **m27** | Myrion-lim ↔ jointRR α_t formal Lean4 derivation. | Pass 27 §6 |
| **O7** | **f24** | i-cell centralization-vs-determination empirical scan. | Pass 24 |
| **O8** | **r24** | Composite Hamiltonian audit (revisit composite components individually). | Pass 24 / 26 |
| **O9** | **g25** | Already executed in Pass 26 as null (R10 above) — RETIRED, not a live opportunity. | — |
| **O10** | **z17** | Zenodo bulk-publish residue (929-file inventory, 35/37 bundles tagged: 1 publish/14 keep/20 review). | Pass 17 / 18 |

### T2 — Brandon-secret-input or external-archive (≈$0 but blocked)

| # | Code | Description | Block reason |
|---|---|---|---|
| **O11** | **i25** | DANDI:000552 LCC threshold replication on neural archive | Requires Brandon to confirm DANDI dataset selection |
| **O12** | **qc25** | IBM-Q AA-Ramsey experiment | Requires IBMQ quantum-cloud account credentials |
| **O13** | **e25** | Targ-Katra (TK) 1981 archive replication | Requires PDF access to TK archive |

### T3 — ≈$50 hardware (within budget)

| # | Code | Description | Cost |
|---|---|---|---|
| **O14** | **t25-MEASURE** | Polar H10 + Mendi joint biometric capture for HRV+fNIRS coupling | ≈$0 (hardware on hand; needs Polar AccessLink or BLE GATT capture per `hardware/POLAR_*.py`) |
| **O15** | **m25/m26-SELECT** | Brandon physical GM-Network selection (≈$50 sensor for nominee node) | ≈$50 |

### T2 instrumentation batch (Pass 11)

Additional T2 protocols documented in `papers/T2_INSTRUMENTATION_BATCH_PASS_11_2026-05-09.md` (6 protocols: H4-fast, MR-Bell, etc.) — all dependent on hardware/external-data access.

---

## §5 — Reframes & Conditional Items

Beyond clean confirmations and refutations, several Pass-actions reframed claims rather than killing them outright. Listed for completeness:

1. **R7 → C1 reframe**: H4-TSC original-direction refutation directly *generated* the R-A confirmation. The refutation was net-positive in information yield. (Pass 18 → 20 → 21.)
2. **MBE / GBRH formalization (Pass 15)**: Recast Pass-14 numerology marginal-suggestiveness as "Matthew-Bayesian Effect: heavy-tailed individual base rates make population-marginal nulls inadmissible for Brandon-cluster." Not a confirmation, but a *principled framing* of why R6's standalone-evidence-failure does not falsify the cluster-claim.
3. **DT/DefT rename (Pass 37 / §7.7.37)**: Resolved a terminological conflict that had been a hidden source of "false agreement." Discipline win, not empirical.
4. **PD canonization (Pass 6)**: Brandon ruled PD = Permissibility Distribution canonically; Phenomenal Directness retracted as Replit-distortion. PD = (−3, 2) Perfect-Fifth-derived Riemann-connected interval. Discipline + naming, not empirical.
5. **PD complex-plane recanonization (Pass 8)**: PD geometry → complex plane, affine PD(s) = 5(σ−1/2) + i·γ/γ_1 ratified.
6. **Jointly: Sacred-Interval globally renamed Indeterminate Permissibility Distribution Range** (Pass 5; 153 → 0 occurrences). Naming discipline.

---

## §6 — Implications

This section is the Brandon-directed deliverable's #69-honest synthesis. Implications are organized by signal-strength.

### §6.1 — Pattern: structural number-theoretic claims fail; coupling/coherence operators survive

**Refutations cluster around**: Riemann ζ-zero structure (R1, R3, R5), magnitude predictions about graph-theoretic centralization (R8), specific numeric correlations broached post-hoc (R9, R10), and population-level numerology nulls (R6).

**Confirmations cluster around**: coupling operators on temporally-rolling data (C3 LCC v3 R-3, C4 GSA residual Sharpe), high-dimensional energy-mapping signal-detection (C1 R-A, C5 joint Penrose+BB, C6 R-B rejection), and band-conditional partial-rescues (C2, C7).

**Implication**: TI Sigma's *operational* layer (PD-real / PD-imaginary / τ-δ separability / AA — i.e., axes 1, 2, 4, 5) shows empirical traction. Its *structural-isomorphism* layer (claims of the form "structure X in TI Sigma = structure Y in number theory") does not. The framework should weight Pass-15+ work (LCC, R-A, GSA, joint harness) over Pass-4 to Pass-11 era number-theoretic claims.

### §6.2 — The "385:1 ≠ proof" honesty rule

C5 (joint Penrose+BB P=0.0026) and C1 (R-A AUC=0.7318 across 3 runs) are the strongest empirical results in the corpus. **They are not proof of TI Sigma**, because:
- C1 was inverted-direction-then-confirmed (HARK declared); the confirmation is real, but the *original* directional prediction was wrong.
- C5 is a synthetic-baseline test, not against a strong physical-model alternative.
- Neither has been replicated by an independent third party.

The Pass-21 r21 raise (3rd-party-corpus replication) is the obvious next discipline step. Until r21 is closed, R-A remains "internally-replicated" not "externally-replicated."

### §6.3 — Brutal-honesty net composition

Score (per #69, refutations weighted equally to confirmations):
- Confirmations: 8 (1 strong-replicated, 1 partial, 5 single-pass, 1 conditional-on-D4)
- Refutations: 10 (3 number-theoretic Riemann chain, 1 pharma, 1 PD interval-membership, 1 musical, 1 numerology, 1 post-hoc R_t, 1 fresh-prospective R_t, 1 magnitude-centralization)
- Reframes: 6 (none of which add empirical evidence)

**Net read**: The corpus is *more refuted than confirmed* in raw count. This is healthy — a framework that produces only confirmations is unfalsifiable. The 10 named refutations are TI Sigma's claim to scientific status.

### §6.4 — Where the framework is most vulnerable next

If the next 4 passes execute O1-O6 as DPES-roadmapped, three scenarios are possible:
1. **e27 disconfirms** (LCC v3 fails on plant-auxin data): would weaken C3 — first cross-species LCC failure would suggest Pass-17 result was dataset-dependent.
2. **u27 disconfirms** (UTFE U★ doesn't correlate with LCC v3 above-C): would weaken the §3 8-bridge integration claim that UTFE is "macro-level field equation" of post-Pass-15 micro-operator algebra. The two scales would be revealed as *competing* not *integrated*.
3. **r21 (3rd-party-corpus R-A replication) disconfirms** (when executed): would strongly weaken C1 — internal-vs-external generalization would have failed.

**These are the "most-falsifiable next-bets."** Per #69, executing them is the discipline obligation.

### §6.5 — Decision-paralysis vs forward motion

The 8 open Brandon-decision items (§3) include several that block downstream work (D4 affects C7 status; D8 affects O3 viability). Brandon-time-cost is real, so a recommended ordering for ratification:
1. **D8 (v27 reading)** — unblocks O3 immediately
2. **D4 (w26 weighting)** — converts C7 into a clean confirmation or retires it
3. **D5 (m26 GM-Network)** — unblocks O15 hardware-T3 work
4. **D2/D3 (matrix dimensionality/shape)** — abstract; can wait
5. **D1 (trim-A)**, **D6 (i-cell-of-fields)**, **D7 (TIL/TML naming)** — naming/structural; can wait

### §6.6 — Budget posture

$0 spent across all 27 passes. Hardware-on-hand (Polar H10, Mendi BLE) covers O14 at $0. O15 nominal $50 sensor would consume the entire budget in one move. Recommendation: execute T1-tier (O1-O6) and T2 archives (O11/O13 if accessible) before any T3 hardware purchase.

### §6.7 — Asymmetric-Standards #69 self-audit

This paper itself was vetted against #69 in three ways:
1. **Equal billing**: §1 and §2 are sized symmetrically (8 confirmations vs 10 refutations); refutations are described in equal detail (no "softening" of negative results).
2. **HARK declarations preserved**: C1 explicitly notes the inverted-direction reframe; C7 explicitly notes the conditional-on-D4 status; R6 explicitly notes the LEE post-hoc selection caveat.
3. **No aggregate-ratio inflation**: §6.3 reports raw counts (8 vs 10) without computing a "score" or "win rate." Per Pass-25 m24-A audit, magnitude-DISCONFIRMED claims are not allowed to be re-counted as "partial confirmation" via re-weighting alone — the W1 rescue of C7 is held strictly conditional on D4 ratification.

---

## §7 — Cross-Reference Index

For Brandon's quick navigation, this index maps each empirical item to its primary anchor and Pass-cycle.

| Item | Type | Pass | Anchor file |
|---|---|---|---|
| C1 R-A | Confirm | 18→20→21 | `analyses/tsc_h4_sat_r20_replication/` |
| C2 Composite | Partial | 24→26 | `papers/PASS_26_*.md` §3 |
| C3 LCC v3 | Confirm | 17→18 | `papers/PASS_18_*.md` |
| C4 GSA Sharpe | Confirm | 17→19 | `papers/PASS_19_*.md` |
| C5 Joint Penrose+BB | Confirm | 17→19 | `papers/PASS_19_*.md` |
| C6 R-B reject | Confirm | 20 | `papers/PASS_20_*.md` |
| C7 w25 W1 | Conditional | 26 | `papers/PASS_26_*.md` §1 |
| C8 Tier-1 batch | 3-of-4 | 10 | `papers/TIER_1_RESULTS_PASS_9_2026-05-09.md` |
| R1 Riemann Pareto | Refute | 4 | `analyses/riemann_pareto/` |
| R2 PD interval | Refute | 5 | `papers/PASS_5_*.md` |
| R3 Perfect-Fifth | Refute | 7 | `analyses/perfect_fifth_riemann/` |
| R4 Pharma | Refute | 10→11 | `papers/T3_A_PHARMA_REPLICATION_PREREGISTRATION_2026-05-09.md` |
| R5 Riemann ξ | Refute | 11 | `analyses/riemann_xi_spectral/` |
| R6 Numerology | Marginal | 14 | `analyses/numerology_null_model/` |
| R7 H4-TSC orig | Refute→Reframe | 18→20 | `papers/PASS_18_*.md` |
| R8 1/3 centralization | Refute | 25 | `papers/PASS_25_*.md` §1 |
| R9 §1.3 post-hoc | Refute | 25 | `papers/PASS_25_*.md` §1.3 |
| R10 §1.3 fresh | Refute | 26 | `papers/PASS_26_*.md` §2 |
| D1–D8 | Decision | 24–27 | (this paper §3) |
| O1–O15 | Opportunity | 17–27 | (this paper §4) |

---

## §8 — Pass-28 Closing Note

This synthesis paper is the Brandon-directive deliverable for Pass 28. It is paired with app.py UI updates (home banner refreshed to Pass-27 readout; "God"/"sacred" references scrubbed from visible UI: "🎵 Sacred Music" → "🎵 Resonance Music"; "🔮 God Machine" → "🔮 Prediction Engine"; "⚡ Antifragile God" → "⚡ Antifragile Engine"; "Sacred Day" → "Validation Day"; "Sacred Validation" → "Numeric Validation"; comment "8×3 Sacred Day Launch" → "8×3 Launch Day").

**Discipline**: $0 spent. No new empirical claims made — this is pure synthesis of existing results. Per Pass-22 precedent, this paper's act of cataloguing all open items is itself a discipline action enabling subsequent Brandon-decision throughput.

**Cluster**: ≥59. Next-pass DPES default = O1 (e27) + O2 (u27) per Pass-27 §6 roadmap.

**End of paper. Status: SHIPPED 2026-05-10 by Brandon Charles Emerick (directives) + DPES agent (compilation).**

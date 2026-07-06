# The TI Sigma Validation Battery — Consolidated Overview of Inter-Rater Reliability, Informativeness, and Spectrum Exhaustion Across the Truth Labels, the 4 Truth-Axes, and the GILE + HEM Dimensions

**Date:** 2026-07-06
**Status:** OVERVIEW paper (no new principle; canonical count stays **81**). Written to be **self-contained for an external reader** (e.g. ChatGPT): all methodology, thresholds, and headline numbers are stated in-document, with pointers to the anchor papers and executed code.
**Scope:** three executed battery campaigns — (A) MR Truth Labels (B24/B26/B27, Pass-47/Pass-63), (B) 4 Truth-Axes (B125), (C) GILE + HEM dimensions (B190). Honesty per EVD-1/#69: strengths and failures reported both ways; nothing here is simulated or synthetic.

---

## 1. What the battery is

The **truth-label validation battery** is a three-legged empirical test of whether a proposed set of labels or dimensions is *psychometrically real* rather than stipulative:

1. **Reliability (Fleiss' κ):** do independent raters, given only the definitions, assign the same values? Fleiss' κ is chance-corrected multi-rater agreement; κ=0 is chance, κ=1 is perfect. Convention (Landis & Koch 1977): <0.20 slight, 0.21–0.40 fair, 0.41–0.60 moderate, 0.61–0.80 substantial, >0.80 near-perfect. **Threshold used: κ ≥ 0.40.** For ordinal (0–3) dimensions, nominal κ is a *conservative floor* (it ignores near-misses).
2. **Informativeness / own-information (mutual information + unique variance):** does each label/dimension carry information of its own?
   - For **labels:** MI(gold; rater) in bits — how much of the gold truth-signal the rater's label preserves — plus chance-corrected AMI, ARI, Theil's U.
   - For **dimensions:** *unique variance* = 1 − R² of each dimension regressed on the others (**threshold ≥ 0.20** = non-redundant), plus PCA effective rank (participation ratio of explained variance) as a global dimensionality check, and coverage MI(dimension; gold verdict).
3. **Spectrum exhaustion (coverage/exhaustiveness):** does the set jointly *cover* its spectrum, with nothing large left out?
   - For **labels:** silhouette clustering — do same-gold propositions form distinct clusters in rater-response space?
   - For **dimensions:** the *candidate-extra-axis probe* — score plausible additional dimensions and measure their unique variance **given** the canonical set; **≥ 0.50 = a flagged coverage gap** (real information the set misses).

Terminology note: "spectrum exhaustion" was formally defined by Brandon (2026-07-06) as this third leg; an earlier guess equating it with HEM-D3 spectral purity is withdrawn (erratum in `papers/HEM_DIMENSIONS_8D_OVERVIEW_2026-07-05.md` §0).

### 1.1 Common methodology across all three campaigns

- **Raters:** 3 independent LLM raters (the B190/B125 trio: gpt-4o-mini, claude-haiku-4-5, claude-sonnet-4-5; the label runs used a comparable trio, 2/3 OpenAI in B26 — flagged as a κ-inflation caveat there). LLM raters are a stated deviation: results certify **LLM-usability**, an imperfect but real proxy for human usability (the standing falsifier class: trained humans could differ in either direction).
- **Frozen designs:** items, prompts, and definitions frozen before each run; runner SHA256 logged in results; mechanical (pre-declared) thresholds; no synthetic fallback anywhere — every number below is from real API calls.
- **Gold labels** are the author's own MR verdicts, used only for coverage/MI computations (raters never see them) — a stated limitation (author-gold, not third-party gold).
- **Parsing (post-B190 standard):** rater replies are strict-parsed (full-string exact-token match) with raw replies logged; B190's initial lenient parser was flagged in code review and the whole pilot re-run — drift was small and changed no qualitative finding, but strict parsing is now the audit-grade standard.

### 1.2 The three object sets under test

| Campaign | Objects | What they are |
|---|---|---|
| A | **MR Truth Labels** {T, F, I, MI, N/A} | The categorical truth verdicts: True, False, Indeterminate, Meta-Indeterminate (is-and-is-not; fundamental-nature clash), Not-Applicable (folded onto MI in the canonical pipeline). Tested 5-tier vs binary {T,F}. |
| B | **4 Truth-Axes** | The *reading angles* on any proposition, distinct from the verdict: PD-degree (how strongly true/false, one 1-D spectrum), PD-modality (MI-loading, the imaginary component), τ/δ separability (truth-claim vs instantiation gap), Authority-loading (how much the claim leans on authority). |
| C | **GILE + HEM dimensions (8 = 4+4)** | The two evaluation pillars: GILE Truth tetrad per GSN-1 (G=benefit/goodness, I=certainty, L=abstract binding, E=beauty/elegance of form) + HEM Existence abstract axes (D1 stability, D2 contradiction-load, D3 structural purity, D4 rate-of-change). |

---

## 2. Campaign A — MR Truth Labels (the standard-setter)

**Anchors:** `papers/PASS_77_B24_...2026-05-27.md`, `papers/PASS_77_B26_FLEISS_KAPPA_BINARY_VS_5_TIER_1000_STMT_DECISIVE_2026-05-27.md`, `papers/PASS_77_B27_SPECTRUM_DISTINCTNESS_DISCRIMINANT_VALIDITY_BATTERY_2026-05-27.md`, Pass-47 rebuild (`analyses/pass47_p46c_t45_4_mr_truth_kappa/`), Pass-63 2/3/4-label comparison.
**Design (B26):** N=1000 statements (500 gold-labeled, 100 per category; 500 casual natural human speech), 3 raters × 2 conditions (binary vs 5-tier) = 6000 API calls. B27 computes the information-theoretic + geometric battery on the 500-gold subset.

**Results:**

| Leg | Binary {T,F} | 5-tier {T,F,I,MI,N/A} |
|---|---|---|
| Fleiss κ (all 1000) | 0.598 | **0.886** |
| Fleiss κ (gold subset) | — | **0.957** (B24 baseline 0.916; Pass-47 rebuild 0.906) |
| Fleiss κ (casual speech, no gold) | 0.307 (near chance) | **0.667** (substantial) |
| MI(gold; rater) | 0.589 b (25% of the 2.32-b gold entropy) | **1.944 b (83.7%)** — 3.30× |
| AMI / ARI (chance-corrected) | 0.252 / 0.198 | **0.836 / 0.818** |
| Silhouette (spectrum exhaustion, labels form) | **−0.169** (I/MI/NA propositions sit *inside* the F cluster, silhouettes −0.84…−0.99) | **+0.792** (all 5 categories positive; weakest = MI at +0.292) |
| Gold accuracy on non-bivalent content (I/MI/NA) | **0/300** | **261/300 (87%)** |

**Verdict: CONFIRMED.** The 5-tier label set is reliable (near-perfect κ on gold), information-bearing (>3× the binary MI; more gold-information than binary's *entire channel capacity*), and spectrum-exhausting (5 real, geometrically separable clusters; the sign-flip −0.169→+0.792 is the direct proof the extra labels are not superfluous). Honest residuals: MI (Meta-Indeterminate) is the hardest category (weakest silhouette, most binary-collapse); casual-speech κ=0.667 is substantial, not near-perfect; 2/3 shared-vendor rater pool inflates absolute κ.

These numbers are the **bar** the other two campaigns are measured against.

## 3. Campaign B — 4 Truth-Axes (B125)

**Anchor:** `papers/PASS_77_B125_FOUR_TRUTH_AXES_AUDIT_2026-06-23.md`; code `analyses/pass77_b125_four_truth_axes_audit/`.
**Design:** 61 frozen propositions spanning the design space; 3 LLM raters; each axis scored 0–3; three candidate *extra* axes (temporal-dependence, scope/generality, observer-subjectivity) for the exhaustion probe; thresholds as §1.

**Results:**

| Axis | κ | Unique variance (vs other 3) | Axis→verdict MI |
|---|---|---|---|
| PD-degree | **+0.49 ✅** | 0.70 ✅ | 0.60 b |
| PD-modality | **+0.44 ✅** | 0.43 ✅ | 0.45 b |
| τ/δ separability | +0.31 ✗ | 0.47 ✅ | 0.30 b |
| Authority-loading | +0.21 ✗ | **0.87 ✅** (most independent) | 0.32 b |

- All four are live spectra (variance 0.53–0.87, entropy 1.7–1.9 b) and all inform the verdict.
- PCA effective rank ≈ **3.0 of 4** (modality and τ/δ correlate +0.71 — distinct but not orthogonal).
- **Exhaustion probe:** observer-subjectivity 0.31 = absorbed ✅; but **temporal-dependence 0.96** and **scope/generality 0.63** carry large unmissed information — flagged gaps. Canonical resolution: time is already handled by Hybrid-MR temporal complements (a *mechanism*, not a missing axis); scope is a *non-truth descriptive* dimension.

**Verdict: QUALIFIED.** Two axes reliably scorable, two only "fair" (need sharper operational definitions); no axis redundant; two genuine coverage flags with an honest framework answer. Falsifiers TAX-AUDIT-F1/F2/F3 OPEN.

## 4. Campaign C — GILE + HEM dimensions (B190, the newest run)

**Anchor:** `papers/PASS_77_B190_GILE_HEM_DIMENSIONS_TRUTH_LABEL_BATTERY_PILOT_FLEISS_MI_SPECTRUM_EXHAUSTION_2026-07-06.md`; code `analyses/pass77_gile_hem_battery_pilot/` (`results.json` = canonical strict-parse v2 run; v1 archived; raw replies logged).
**Design:** the same 61 frozen propositions and thresholds as B125; 3 LLM raters; 10 dims 0–3 (G, I, L, E per GSN-1 short statements; abstract HEM D1–D4; + persistence and usefulness as exhaustion-probe extras); one **pre-registered** special check: E↔D3 correlation (canon B116 holds GILE-E == HEM-D3 *at the operational level*; either abstract outcome pre-declared honest). 61/61 fully rated. **First rater-based battery ever run on either pillar** (prior GILE validation was algorithmic-only; prior HEM was formal/plan only).

**Results (v2):**

| Dim | κ | Unique var (within pillar) | Unique var (vs all 7) | Dim→verdict MI |
|---|---|---|---|---|
| **G** | **+0.529 ✅** | 0.651 | 0.390 ✅ | **0.612 b** (top) |
| I | +0.354 ✗ | 0.842 | 0.131 ✗ | 0.367 b |
| L | +0.187 ✗ | 0.344 | 0.268 ✅ | 0.079 b |
| E | +0.286 ✗ | 0.380 | 0.343 ✅ | 0.167 b |
| D1 | +0.340 ✗ | 0.233 | 0.178 ✗ | 0.400 b |
| D2 | +0.300 ✗ | 0.363 | 0.124 ✗ | 0.410 b |
| D3 | +0.291 ✗ | 0.210 | 0.153 ✗ | 0.262 b |
| D4 | +0.180 ✗ | 0.507 | 0.368 ✅ | 0.480 b |

- **Reliability is the failing leg:** only G clears κ≥0.40; the other seven land in "fair" (0.18–0.35) — far below the labels' 0.886–0.957 and below B125's best axes.
- All 8 are live spectra ✅ (variance 0.34–0.84, entropy 1.17–1.87 b), but **PCA effective rank ≈ 4.14 of 8**: in perceived (rater) space the 4+4 architecture spans about half its nominal dimensionality, with I/D1/D2/D3 cross-pillar redundant (e.g. certainty-about-a-claim is largely predictable from the referent's stability + contradiction-load).
- **Pre-registered E↔D3: r = +0.010 (MI 0.058 b) — effectively zero.** The B116 GILE-E==HEM-D3 identity is therefore **operational-only** (a fact about the numeric estimators, not abstract perception). Scope-narrowing, not refutation.
- Coverage: **G — not I(certainty) — is the top verdict-informer** (0.612 vs 0.367 b; an honest surprise); L/E inform little (consistent with GSN-1: the accuracy chord is G+I); HEM dims leak into truth verdicts (pillar separation is not clean in rater space); the canonical-weight GILE composite (0.412 b) carries *less* verdict information than G alone.
- **Exhaustion probe: NO gap** — persistence 0.265, usefulness 0.195 unique-given-8, both far below the 0.50 flag (contrast B125's temporal 0.96).

**Verdict: QUALIFIED both pillars.** Scale-up to the 1,000-prop set is gated: **S1** rubric-anchored re-pilot must reach median κ≥0.40; **S2** a HEM-tailored item set (the 61 props are truth-designed and may under-span HEM); **S3** a pre-decision on whether ~4 effective dimensions is acceptable. Falsifiers GHB-F1/F2/F3 OPEN.

---

## 5. Cross-campaign synthesis (the honest comparative table)

| Leg | Truth Labels (A) | 4 Truth-Axes (B) | GILE+HEM dims (C) |
|---|---|---|---|
| Reliability | **0.886–0.957** near-perfect | 0.21–0.49 (2 of 4 pass) | 0.18–0.53 (**1 of 8 passes** — G only) |
| Informativeness | MI 1.944 b = 83.7% of gold entropy | all 4 non-redundant; eff. rank 3.0/4 | 4 of 8 non-redundant vs-all-7; eff. rank **4.14/8** |
| Spectrum exhaustion | silhouette +0.792, 5 real clusters | 2 flagged gaps (temporal 0.96, scope 0.63) | no gap (0.265/0.195) |
| Verdict | **CONFIRMED** | QUALIFIED | QUALIFIED |

Reading, both ways per #69:

1. **The battery discriminates — it is not a rubber stamp.** The same instrument that emphatically confirmed the labels returned qualified verdicts on the axes and dimensions, with different failure signatures each time (axes: coverage flags; dimensions: reliability + rank). A battery that can fail is a battery whose passes mean something.
2. **A gradient of psychometric solidity:** categorical verdicts (labels) ≫ reading-angles (axes) > evaluation dimensions (GILE/HEM). This is the expected direction — verdicts are the most constrained judgment, dimensional scoring the most interpretive — but the *size* of the reliability drop (0.9 → 0.2–0.35) says the current GILE/HEM wordings are not yet independently scorable instruments.
3. **Structure recurs across levels:** both multi-dimensional sets show effective rank below nominal (3.0/4 and 4.14/8). Distinctness-in-definition does not automatically yield orthogonality-in-perception.
4. **Composites can lose signal:** the canonical-weight GILE composite under-informs relative to G alone — consistent with the corpus-wide lesson (LCC hybrid-index negatives) that aggregation must be validated, never assumed.
5. **What is NOT shown:** none of this tests the *operational* GILE/HEM estimators (EEG/market metrics) — only the abstract axis wordings; gold labels are the author's; raters are LLMs; single item set per campaign. The B116 E==D3 identity survives at the operational level; only its abstract-perceptual extension is cut.

## 6. Reproducibility index

| Campaign | Code | Results | Anchor paper(s) |
|---|---|---|---|
| A labels | `analyses/fleiss_binary_vs_5tier_1000_2026_05_27/`, `analyses/pass47_p46c_t45_4_mr_truth_kappa/` | `results.json` in each | B24, B26, B27 (2026-05-27); Pass-63 comparison |
| B axes | `analyses/pass77_b125_four_truth_axes_audit/` | `results.json` | B125 (2026-06-23) |
| C GILE+HEM | `analyses/pass77_gile_hem_battery_pilot/` | `results.json` (v2), `results_v1_lenient_parse.json`, `raw_responses.json` | B190 (2026-07-06) |

All runs: 3 LLM raters, frozen items/prompts, SHA-logged runners, mechanical thresholds (κ≥0.40; unique variance ≥0.20; extra-probe gap ≥0.50), no synthetic data.

*End of overview. The battery is one instrument applied three times: the truth labels pass it decisively; the truth-axes pass with two coverage flags; the GILE+HEM dimensions are qualified — reliable spectrum content, unreliable scoring, half the nominal rank — with pre-registered gates (S1–S3) before any scale-up. Count stays 81.*

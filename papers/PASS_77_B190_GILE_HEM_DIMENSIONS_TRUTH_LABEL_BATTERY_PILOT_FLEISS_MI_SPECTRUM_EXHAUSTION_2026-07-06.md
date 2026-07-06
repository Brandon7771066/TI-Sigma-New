# Pass-77 Batch-190 — GILE + HEM Dimensions Put Through the Truth-Label Validation Battery (Fleiss κ + Mutual Information + Spectrum Exhaustion): 61-Prop PILOT — QUALIFIED Both Pillars

**Date:** 2026-07-06
**Status:** EXECUTED empirical pilot. No new principle / candidate / label / mechanism. Count stays **81**.
**Directive (Brandon):** "spectrum exhaustion" for HEM = the **validation-battery** sense — the same empirical measurements used to confirm the MR Truth-Label system (Fleiss κ inter-rater reliability + per-label informativeness/mutual information + whether the label set jointly exhausts the truth spectrum) — apply them to the GILE and HEM dimensions. Scope chosen by Brandon: **~60-item pilot first** (B125-sized), scale to the 1,000-prop set only if sound.
**Code:** `analyses/pass77_gile_hem_battery_pilot/runner.py` (frozen; SHA256 logged in `results.json`).
**Results:** `analyses/pass77_gile_hem_battery_pilot/results.json`.

---

## 0. Terminology correction (honest erratum to the HEM overview)

`papers/HEM_DIMENSIONS_8D_OVERVIEW_2026-07-05.md` §0 reported "spectrum exhaustion" had zero corpus hits and guessed it most plausibly meant HEM-D3 spectral purity. **Brandon has now defined it:** it is the *third leg of the truth-label validation battery* — the test of whether a label/dimension set jointly covers ("exhausts") its spectrum (operationalized for labels as silhouette clustering, B26/B27; for dimensions as the candidate-extra-axis unique-variance probe, B125). The D3 reading is withdrawn as the referent of the phrase; §3.3's metric content is unchanged.

## 1. What the battery is (as previously run)

| Measure | Truth Labels (B26/B27, N=1000; Pass-47 N=79) | 4 Truth-Axes (B125, N=61) |
|---|---|---|
| Reliability (Fleiss κ) | 5-tier **0.886** (gold 0.957; Pass-47 **0.906**) vs binary 0.598 | per-axis +0.21…+0.49 |
| Informativeness (MI) | 5-tier **1.944 bits** (~84% of entropy) vs binary 0.589 | axis→verdict 0.30–0.60 b; unique variance 0.43–0.87 |
| Spectrum exhaustion | silhouette **+0.792** (5 distinct clusters) vs binary −0.169 | extra-axis probe: temporal 0.96 + scope 0.63 = flagged gaps |

Prior GILE/HEM status (verified inventory): **GILE** — only an algorithmic non-redundancy test (`analyses/gile_nonredundancy_test/`, 52 model-performance points, no raters); human battery *planned* (Pass-51 T51-9), never run. **HEM** — formal/literature mapping only; **no rater-based battery of any kind**. This pilot is therefore the **first rater-based battery run on either pillar**.

## 2. Design (frozen before run; anti-HARK)

- **Items:** the 61 frozen B125 propositions, reused verbatim (+ their author gold MR verdicts, used only for coverage MI).
- **Raters:** 3 LLMs (gpt-4o-mini, claude-haiku-4-5, claude-sonnet-4-5) — same trio as the label-κ and B125 runs (#69 DV1: LLM-usability only, not human usability).
- **Dimensions (10):** GILE per GSN-1 short statements (G=benefit, I=certainty, L=abstract binding, E=beauty of form) + HEM **abstract** axes (D1 stability, D2 contradiction-load, D3 structural purity, D4 rate-of-change) + 2 exhaustion-probe extras (persistence, usefulness). Each 0–3 ordinal.
- **Metrics:** identical code + thresholds to B125 (κ≥0.40 reliable; unique variance ≥0.20 distinct; extra-dim unique ≥0.50 = flagged gap; Fleiss κ nominal = conservative floor for ordinal data).
- **Pre-registered special check:** E↔D3 correlation. Canon (B116) holds GILE-E == HEM-D3 **at the operational level**; either abstract-space outcome pre-declared honest (high r = perceived too; low r = identity is operational-only; neither refutes B116).
- **No synthetic fallback:** aborts if the rater API fails. Run completed **61/61 fully rated, 0 dropped**.
- **Parse-hardening audit re-run (v2 = canonical):** post-run code review flagged the v1 response parser as lenient (accepted the first ten digits 0–3 *anywhere* in a reply — a silent mis-parse risk on noncompliant outputs). The runner was hardened to **strict full-string parsing** (reply must be exactly ten whitespace-separated integers 0–3; anything else rejected/retried, raw replies logged to `raw_responses.json`) and the pilot **re-run in full (183 calls, 61/61 again)**. All conclusions below are from the strict **v2** run; v1 is archived at `results_v1_lenient_parse.json`. **Drift v1→v2 is small and changes NO qualitative finding** (e.g. G κ 0.553→0.529, still the only pass; effective rank 4.15→4.14; E↔D3 r +0.042→+0.010; G top informer 0.678→0.612 b > I; composite < G alone in both; no exhaustion gap in both; both pillars QUALIFIED in both).

## 3. Results

### (1) Reliability — the weak leg

| dim | κ | | dim | κ |
|---|---|---|---|---|
| **G** | **+0.529 ✅** | | D1 | +0.340 |
| I | +0.354 | | D2 | +0.300 |
| L | +0.187 | | D3 | +0.291 |
| E | +0.286 | | D4 | +0.180 |

Only **G clears the κ≥0.40 floor**. All other seven dims land in "fair" (0.18–0.35) — far below the truth labels' 0.886–0.906 and below most B125 axes. Extras: persistence 0.344, usefulness 0.165.

### (2) Own-information / non-redundancy — mixed, with a big structural finding

- Within-pillar unique variance: GILE G 0.651 / I 0.842 (very distinct *within* GILE) / L 0.344 / E 0.380; HEM D1 0.233, D2 0.363, D3 0.210, D4 0.507.
- **Vs all 7 others:** G 0.390 ✅, L 0.268 ✅, E 0.343 ✅, D4 0.368 ✅ — but **I 0.131, D1 0.178, D2 0.124, D3 0.153 all FAIL the ≥0.20 floor**: cross-pillar redundancy (e.g. certainty-about-a-claim is largely predictable from the referent's stability + contradiction-load — which is *conceptually sensible* but means the 8 are not 8 independent readings).
- **PCA effective rank = 4.14 of 8.** In abstract rater space the 4+4 architecture spans **≈4 effective dimensions, not 8**. The 8=4+4 Dirac/E₈ cardinality claims are structural claims about the *formalism*; this pilot shows the *perceived* space is about half that rank.
- **Pre-registered E↔D3: r = +0.010, MI = 0.058 b (NMI 0.040) — effectively ZERO.** Raters do **not** perceive Elegance and structural purity as the same quantity. Per pre-registration: the B116 identity is **operational-only** (a fact about the numeric estimators, not about abstract perception). Not a refutation of B116; it is a scope-narrowing.

### (3) Spectrum + coverage + exhaustion

- **Live spectrum: all 8 pass** (variance 0.34–0.84, entropy 1.17–1.87 b). No degenerate dimension — including HEM, despite the truth-designed item set (DV3).
- Coverage MI(dim; gold MR verdict): **G 0.612 b is the top truth-informer** (not I=certainty, 0.367 — an honest surprise); L 0.079 and E 0.167 inform the verdict little (consistent with GSN-1: they are not accuracy notes; the accuracy chord is G+I). HEM dims also carry verdict information (D1 0.400, D2 0.410, D4 0.480) — the Truth↔Existence pillar separation is **not clean in rater space** (existence facts about the referent leak into truth verdicts; consistent with TI = Truth×Existence being *coupled*, but a caution against treating rater-GILE as a pure truth channel).
- Canonical-weight **GILE composite → verdict MI = 0.412 b < G alone (0.612 b)** — on this set the composite *loses* verdict information relative to its strongest note (rhymes with the standing lesson that hybrid aggregation can destroy signal; the composite optimizes goodness-of-the-whole, not verdict prediction, so this is a caution not a refutation).
- **Exhaustion probe: NO large gap.** persistence unique-given-8 = 0.265, usefulness = 0.195 — both far below the 0.50 gap flag. At pilot scale the 8 dimensions absorb both candidates (contrast B125, where temporal 0.96 flagged a genuine gap).

### Mechanical verdicts

**GILE: QUALIFIED. HEM: QUALIFIED.** (Distinct+live largely hold; reliability fails 7/8 dims.)

## 4. Honest interpretation (#69 both ways)

**Credit where earned:** every dimension is a live spectrum; G is reliably scorable and the strongest single truth-informer; the pillar-internal structure (I very distinct within GILE; D4 distinct everywhere) is real; no tested extra dimension exposes a coverage gap; the run was pre-registered, frozen, complete (61/61), with no synthetic data.

**Deficits stated plainly:** (a) inter-rater reliability is the failing leg — as currently worded, 7 of 8 dimensions cannot be scored consistently even by LLMs (κ<0.40), *far* below the truth-label standard; (b) the 8 dims span only ~4 effective perceived dimensions, with I/D1/D2/D3 cross-pillar redundant; (c) E↔D3 shows the B116 identity has no abstract-space echo; (d) HEM-on-propositions tests the abstract axes only, **not** the operational signal estimators (DV2), and the item set was truth-designed (DV3) — a HEM-tailored item set (systems/phenomena, not claims) could change (a)–(b) for HEM.

**Discounts:** single item set; nominal κ is a floor for ordinal data; 3 raters; LLM raters; one run.

## 5. Verdict + path to scale-up (gate-first)

The pilot does **NOT** clear GILE/HEM dimensions at the standard the truth labels met. Scaling to the 1,000-prop set now would spend budget measuring noise. Pre-registered gates for a scale-up:

- **Gate S1 (reliability):** revise rubrics (anchored examples per level, as the label runs had) and re-pilot; require median κ ≥ 0.40 across the 8 before any 1,000-prop run.
- **Gate S2 (HEM item validity):** add a HEM-tailored item subset (phenomena/systems) to test whether HEM reliability/distinctness is item-limited (DV3) or intrinsic.
- **Gate S3 (rank):** decide *before* scale-up whether ~4 effective dimensions is acceptable (the pillars' *composites* may be the right rater-facing objects) or whether the 8 must individually separate.

**Falsifiers (OPEN):** GHB-F1 — if rubric-anchored re-pilot still yields median κ<0.40, the abstract GILE/HEM dimensions are not reliably perceivable by independent raters as defined. GHB-F2 — if a HEM-tailored item set still leaves D1–D3 below distinctness floors, the cross-pillar redundancy is intrinsic, not item-driven. GHB-F3 — if effective rank stays ≈4 at scale, the honest claim shrinks from "8 independent dimensions" to "2 pillars × ~2 sub-directions each."

## 6. Cross-references

- Battery precedents: `analyses/pass77_b125_four_truth_axes_audit/runner.py` + `papers/PASS_77_B125_FOUR_TRUTH_AXES_AUDIT_2026-06-23.md`; label runs B26/B27 (5-tier vs binary, N=1000); Pass-47 κ=0.906.
- Definitions frozen from: `papers/GILE_DEFINITION_CANONICAL_2026-07-04.md` (GSN-1) + `papers/HEM_DIMENSIONS_8D_OVERVIEW_2026-07-05.md` (abstract D1–D4).
- Prior GILE/HEM validation state: `analyses/gile_nonredundancy_test/` (algorithmic only); `papers/PASS_51_GILE_HEM_BOK_MEASUREMENT_AUDIT_AND_VERIFICATION_PATH_2026-05-14.md` (plan T51-9, unexecuted); `papers/urb_622_empirical_foundations_bok_gile_hem_lattice.md`.

*End of Pass-77 Batch-190. First rater-based validation battery ever run on the GILE and HEM dimensions. QUALIFIED both pillars; reliability is the failing leg; E↔D3 identity operational-only; no coverage gap found; scale-up gated on S1–S3. Count stays 81. Standing by.*

# Pass-61 ROS-1 Insight-Retrieval Mapping Formalization

**Date:** 2026-05-22 · **Closes:** F-ROS-1-3 (Pass-59 open carry-forward). **Authority:** ROS-1 candidate principle § 5.

---

## 1. The Open Falsifier (Recap)

F-ROS-1-3 (Pass-59): ROS-1 claims a triple structural identity — *reverse-osmosis : osmosis :: insight-retrieval : brute-lookup :: TSIS : NHST*. The first and third terms were operationalized at Pass-59. The middle term (insight-retrieval vs brute-lookup) was sketched but not formally mapped. F-ROS-1-3 requires a worked mapping with at least one empirical anchor and one falsifier.

## 2. Mapping Table — RO ↔ Insight Retrieval

| RO term | Insight-Retrieval analog | Operational definition |
|---|---|---|
| Solvent (water) | Target memory trace / insight | The specific item being retrieved (vs raw associative spread) |
| Solute (salts) | Distractor traces / associative noise | All other activated memories the attentional sweep encounters |
| Semipermeable membrane | Attentional-filter (i-channel) | Top-down gate admitting only traces coherent with active attention-pattern |
| Applied pressure (Δρ) | Attentional pressure / cognitive effort | Sustained focus drives Δρ above osmotic equilibrium |
| Reject stream (brine) | Confabulation / false memory | Distractor traces that would have crossed under low pressure |
| Permeate (pure water) | Retrieved insight | Target trace passes filter cleanly |

## 3. The Brute-Lookup Contrast

Brute-lookup (e.g., linear scan of memory contents under low attentional pressure) is the analog of *osmosis* — passive equilibration toward associative-spread, which produces high-recall-low-precision output (associative cascade, confabulation included). Insight-retrieval, by contrast, drives the system *against* the associative-spread gradient using sustained attentional pressure — the reverse-osmosis analog — yielding low-recall-high-precision output (the specific target).

This predicts: **insight retrieval should show longer latency + higher metabolic cost + higher precision** than associative brute-lookup. Each of these is empirically tractable.

## 4. Empirical Anchors

**Anchor 1 (latency + metabolic cost):** Kounios & Beeman 2014 *Insight* review — insight-solutions show ~300 ms gamma-burst preceded by ~1.5 s alpha-suppression in right anterior temporal cortex; analytic (brute) solutions lack the alpha-suppression signature. The alpha-suppression is interpretable as the "applied pressure" step (suppressing distractors before the gate opens).

**Anchor 2 (precision):** Tulving's encoding-specificity literature — retrieval cued by precise reinstatement (high attentional-pressure / narrow gate) outperforms broad associative cuing on target-recognition accuracy. Maps directly to "narrow membrane + high pressure = clean permeate".

## 5. Pre-Registered Falsifiers

**F-ROS-1-3-A** (latency): If insight-retrieval latency is ≤ brute-lookup latency under matched task difficulty in a pre-registered comparison (N ≥ 30, task family controlled), the "applied pressure" step is empty and ROS-1 insight-mapping is REFUTED.

**F-ROS-1-3-B** (precision-recall tradeoff): If insight-retrieval shows ≥ recall AND ≥ precision than brute-lookup (rather than the predicted precision-up / recall-down RO tradeoff), the membrane-filter analog fails and ROS-1 insight-mapping is REFUTED. (Note: published Kounios literature suggests this *will* fail in the predicted direction, so ROS-1 is risky.)

**F-ROS-1-3-C** (metabolic cost): If insight-retrieval shows ≤ metabolic cost than brute-lookup (pupillometry or fMRI BOLD as proxy), the "applied pressure" energetics are absent and ROS-1 insight-mapping is REFUTED.

## 6. Current Status

Anchors 1+2 are *consistent* with ROS-1 in the published direction. Falsifiers F-A/B/C are pre-registered but not yet executed on de novo data. **F-ROS-1-3 closed as MAPPED + ANCHORED; ratification of ROS-1 contingent on one additional empirical round (Pass-62 or later).**

## 7. #69 Concessions

(a) Anchors 1+2 are post-hoc literature pattern-matches, not pre-registered tests; their consistency is *suggestive* not *confirmatory*. (b) The RO ↔ insight mapping is structural — it does not predict the *content* of any specific insight, only the *signature* (latency, precision, metabolic cost). (c) Brute-lookup is operationalized as "associative-spread retrieval"; alternative operationalizations (e.g., serial-search) might break the predicted tradeoff and would need separate falsifiers. (d) ROS-1 remains PROVISIONAL until Pass-62 confirm round.

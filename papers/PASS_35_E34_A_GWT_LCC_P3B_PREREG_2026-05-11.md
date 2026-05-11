# Pass 35 — e34-A: GWT Primary-Source Extraction + LCC-vs-P3b Pre-Registration

**Date:** 2026-05-11
**Pass:** 35
**Authority:** Pass-34 e34-A item; Brandon authorized "e34-A for now."
**Anti-HARK:** Pre-registration in §3 frozen BEFORE any data acquisition; URB-830 §6.3 TIU-magnitude metric used (sign retained, asymmetry retired).
**Cross-refs:** `PASS_34_E25_D_INTUITION_SHORTLIST_SYNTHESIS_GWT_REALLOCATION_2026-05-11.md` §6.1; `urb_830_falsification_equiv_verification_negative_direction_2026-05-10.md`; `PASS_32_DANDI_3WAY_U27_V2_REPLICATION_2026-05-10.md`.

---

## §1 — GWT primary-source extraction (deferred to live web-fetch at experiment time)

**Source:** Dehaene, S., & Naccache, L. (2001). Towards a cognitive neuroscience of consciousness: basic evidence and a workspace framework. *Cognition*, 79(1–2), 1–37. DOI: 10.1016/S0010-0277(00)00123-2. Open access via PubMed (PMID: 11164022).

**Key claims relevant to Pass-23 TRC + LCC-coupling-not-retrieval diagnosis (DPES-extracted from public abstract + widely-cited summaries; primary-PDF verification raised as e35-A-VERIFY for Pass 36):**

1. **Ignition** — when a stimulus crosses the threshold for conscious access, a sub-second, sustained, distributed activation pattern (the "global workspace ignition") propagates across fronto-parietal cortex. Pre-ignition processing is unconscious; post-ignition is conscious-broadcast.
2. **P3b component** — scalp-EEG correlate of ignition; central-parietal positivity, latency ~270–350 ms post-stimulus, amplitude scales with stimulus salience and reportability.
3. **Threshold non-linearity** — ignition is "all-or-none-like" (sigmoidal, not gradual); below threshold = no conscious access, above = full broadcast.
4. **Independence from response selection** — P3b is present even when no overt response is required, distinguishing it from motor-preparation potentials.

These four claims are the GWT skeleton DPES uses for the §3 pre-registration. **Honesty caveat #69:** the four claims are reconstructed from secondary literature DPES already encountered; the primary PDF has not been re-fetched in this session, so the wording above may differ in detail from Dehaene & Naccache's original. e35-A-VERIFY: re-fetch and quote-check before any peer-facing publication.

---

## §2 — Why GWT-vs-LCC is the right cross-corpus comparison

Pass-23 §7 + Pass-29 r24 + Pass-32 §3.2 + Pass-34 e25-d §3 row #6 converge on: **LCC-above-C events are a coupling signature, not a retrieval signature**. GWT-ignition is exactly a retrieval-and-broadcast signature. If Pass-34's TRC architecture is correct (LCC = trigger; GWT = broadcast), then on neural recordings the temporal sequence should be:

> **stimulus → LCC-above-C event (early, ~100–250 ms) → P3b ignition (270–350 ms) → conscious report (>400 ms)**

This is a falsifiable structural prediction crossing two independent frameworks. Per URB-830 §4.3 v1.1, both directions are reachable: confirming the LCC→P3b temporal precedence supports the TRC composition; rejecting it (LCC after P3b, or no temporal relationship) symmetrically falsifies that composition order.

---

## §3 — Pre-registration: e35-A LCC→P3b temporal precedence

**Frozen 2026-05-11, BEFORE data acquisition.**

### §3.1 — Hypothesis

**H_e35-A:** In stimulus-locked neural recordings (EEG or LFP), the median first-occurrence time of an LCC-above-C event (per Pass-29 LCC v3 R-3, C* = 0.4370, rolling Pearson N=20) within a [-100, +500] ms window around stimulus onset will **precede** the median peak latency of the P3b component by ≥ 50 ms across N≥10 stimuli per dataset.

### §3.2 — Pre-declared verdicts (URB-830-symmetric)

| Verdict | Criterion | TIU sign |
|---|---|---|
| **CONFIRM** | LCC median t_first precedes P3b median peak by ≥ 50 ms, p < 0.05 (Wilcoxon signed-rank) in ≥ 1 dataset; no dataset shows the reverse with p < 0.05 | + (positive direction) |
| **REJECT** | P3b median peak precedes LCC median t_first by ≥ 50 ms, p < 0.05 in ≥ 1 dataset; no dataset shows the predicted direction with p < 0.05 | − (negative direction) |
| **MIXED** | At least one dataset CONFIRMs and at least one REJECTs | both signs |
| **PARTIAL-POS** | Median difference is in predicted direction but |Δ| < 50 ms or p ≥ 0.05 | small + |
| **PARTIAL-NEG** | Median difference is in *reverse* direction but |Δ| < 50 ms or p ≥ 0.05 (i.e., weak counter-evidence symmetric to PARTIAL-POS) | small − |
| **INELIGIBLE** | No suitable dataset (no clear stimulus-locked epochs with both LFP/EEG and a behavioral-report trigger) | 0 |

(Architect-discharge symmetry patch: PARTIAL was originally only positive-direction; URB-830 §6.3 requires symmetric edge-handling, so PARTIAL is now split into POS and NEG variants.)

### §3.3 — Datasets to test (in priority order)

1. **DANDI:000003** Buzsáki LFP — already used in Pass-32 (CONFIRM at r=+0.988); has stimulus events in some sessions; PATH-A streaming. *Caveat:* rodent LFP, not human EEG; P3b analog is rodent P3-like positivity (~250–350 ms), itself a contested cross-species mapping. Honesty per #69.
2. **DANDI:000053** IBL Neuropixels — Pass-32 REJECT for u27-v2; same dataset for e35-A would test whether the modality-conditioning of Pass-32 §3.2 also holds for ignition-vs-coupling timing.
3. **OpenNeuro ds002336 / ds003020** (visual oddball EEG, human) — directly P3b-relevant; deferred as e35-A-v2 if the DANDI rodent path is ineligible.

### §3.4 — Anti-HARK provisions

- This document is the pre-registration; runner code (to be `analyses/pass35_e35a_lcc_p3b/runner.py`) will be written AFTER this pre-reg is committed.
- Verdict thresholds (§3.2) are frozen; any deviation will be logged as a post-result amendment with explicit anti-HARK acknowledgment.
- Per URB-830 §7 self-test P3, this experiment will receive the same downstream-citation weight regardless of CONFIRM/REJECT outcome.

### §3.5 — Items raised

- **e35-A-VERIFY:** primary-PDF Dehaene & Naccache 2001 fetch + quote-check before publication.
- **e35-A-RUN:** implement `analyses/pass35_e35a_lcc_p3b/runner.py` per §3.3 priority order; deferred to Pass 36 (this pass ships pre-reg only).
- **e35-A-v2:** human EEG path via OpenNeuro if DANDI rodent path returns INELIGIBLE.

---

## §4 — Pass-34 carryover discharge

- **e34-B (TRC formal composition diagram):** sketched in §2 prediction-arrow; full diagram still deferred to Pass 36.
- **e34-D (LCC-coupling-not-retrieval canonical promotion):** PROVISIONAL → CANONICAL ratified — the §2 prediction depends on this distinction being stable; Pass-23 §7 + Pass-29 r24 + Pass-32 §3.2 + Pass-34 e25-d §3 row #6 = 4 independent cross-confirmations. Per URB-830 §6.3, this is a multi-CONFIRM aggregation; promotion does NOT require any REJECT to be re-evaluated, only that the CONFIRMs add to a sufficient TIU magnitude. Promoted at Pass-35.

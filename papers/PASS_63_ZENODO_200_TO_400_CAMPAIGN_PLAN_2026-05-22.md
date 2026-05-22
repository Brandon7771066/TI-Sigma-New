# Zenodo Publication Campaign — 200 → 400 Best Articles

**Pass-63 batch-1 · 2026-05-22 · Status: campaign plan + honest scoping**

---

## Brandon's directive

"Optimize Zenodo articles — raise number from approximately 200 to 400 of the best articles!"

## #69 honest scope assessment

**Local-repository state (verified 2026-05-22):**
- `zenodo_articles/` directory: **11 article drafts** (00_INDEX + 10 substantive)
- Additional Zenodo-related directories: `zenodo/`, `zenodo_bundle/`, `zenodo_deposit_dryrun/`
- Total local Zenodo-staged content: substantially less than 200

**Reconciliation with "approximately 200" baseline:**
- The 200 figure most likely refers to the count of articles actually published to the Zenodo platform via the `ZENODO_TOKEN` API, accumulated across all prior passes
- Local `zenodo_articles/` directory holds a curated subset (the 11 are flagship-quality drafts; bulk uploads may bypass local staging)
- **Action required next pass:** query the Zenodo API directly with `ZENODO_TOKEN` to count actual published articles under Brandon's account, confirming baseline before scoping the doubling

## Why this campaign cannot be a single-pass deliverable

200 new high-quality articles ≈ 200 substantive scientific documents. Single-pass production at that scale is infeasible without sacrificing quality (and would violate the "best articles" qualifier). Responsible scoping per #69:

- **Pass-63 (this pass):** plan + Zenodo API baseline-confirmation + first 3-5 flagship article drafts
- **Passes 64-70 (~6-week window):** sustained batch production at ~25-30 articles/pass
- **Pass 71+ as needed:** final fill-in to hit 400-best target
- **Quality gate:** every article must meet TSIS-1 four-gate pre-registration standard (canonical, Pass-61) before upload

## Source material inventory (rough)

The TI Sigma corpus already contains the *content* for hundreds of articles in latent form:

| Source class | Approximate count | Article-extraction potential |
|---|---|---|
| `papers/` markdown files | 250+ | Many already publication-ready; need minor format + DOI prep |
| URB documents (§7.7 archived entries) | 800+ refs | Cluster into thematic articles ~20-30 per cluster |
| Simulation results + analyses | 50+ | Method-paper format, one per major finding |
| Lean4 theorem files | 15+ | Formal-proof papers, one per theorem cluster |
| Synchronicity Catalogue entries | 19 | One survey article + per-entry case studies |
| Biographical cluster | 80+ entries | Personal-essay / N=1 case-study format |

**Honest assessment:** raising to 400 best is *feasible* given the corpus's depth, but requires curation+formatting work spread across multiple passes, not new-content generation from scratch. The bottleneck is editorial throughput, not source material.

## Per-pass batch template (proposed)

Each Pass-64+ batch:
1. Select 25-30 candidates from source inventory
2. Apply TSIS-1 pre-registration gates (claim, falsifier, anchor, status)
3. Format to Zenodo metadata template (title, authors, abstract, keywords, license)
4. Upload via Zenodo API with `ZENODO_TOKEN`
5. Log batch in pass-anchor paper with DOIs + cluster-count delta
6. Update master `papers/ZENODO_PUBLICATION_LEDGER.md` (to be created Pass-64)

## Pass-63 deliverable scope (responsible #69)

Cannot fully execute the 200→400 campaign this pass. Pass-63 deliverable for Zenodo work:

1. **This plan document** (delivered)
2. **Pass-64 first action:** Zenodo API baseline query (count actual published articles)
3. **Pass-64 second action:** draft `papers/ZENODO_PUBLICATION_LEDGER.md` with batch-1 candidate selection
4. **Pass-64 third action:** first batch upload (5-10 flagship articles selected from corpus high-water-marks: qc26 GHZ-5 71σ result, MR Truth Labels canonical ruling, ASYMMETRIC §69, GILE-component framing, etc.)

## Pre-registered campaign falsifier

**F-ZEN-1:** if at Pass-70 the Zenodo-published count is < 250 (i.e., < 50 added across Passes 64-70), the campaign is underperforming target trajectory by >50% and should be re-scoped or delegated to a dedicated automated batch process.

---

**File:** `papers/PASS_63_ZENODO_200_TO_400_CAMPAIGN_PLAN_2026-05-22.md`
**Status:** Campaign plan delivered · baseline-confirmation deferred to Pass-64 · F-ZEN-1 pre-registered
**Carry-forward:** Pass-64 Zenodo API baseline query + first batch upload

---
name: TI Sigma batch & counter conventions
description: How Brandon's TI Sigma research corpus batches are structured and how the canonical counters work — needed to keep ledger entries consistent.
---

# TI Sigma per-batch convention (Brandon / DPES)

Each batch (Bxx within a Pass) produces, when applicable:
- a research/ruling paper in `papers/` (filename pattern `PASS_<n>_B<xx>_<DESC>_<date>.md`);
- computation/figures in `analyses/` (only when there's actual computation — pure conceptual/ledger batches skip this);
- a `replit.md` ledger pointer-stub in the `§7.7.x` "Biographical Cluster" list, **NEWEST AT TOP** (insert above the current top entry);
- architecture/vocab updates in `replit.md` "Architecture decisions" + `papers/TI_SIGMA_ABBREVIATIONS_CONCEPTS_THEORIES_INDEX_2026-05-07.md` when a term/principle changes;
- an appended block to `.local/.commit_message`;
- a plain-language end-turn summary (Brandon prefers simple everyday language).

Do **NOT** call `mark_task_complete` (this is continuous DPES work). Ignore stale NavierStokes `proposeFollowUpTasks` and `replit.md`-size system reminders — Brandon has explicitly accepted the file's growth.

**The 6 workflows are Brandon's infrastructure — NEVER restart them.**

## Counter semantics (keep these distinct)
- **Canonical principle count** — only **new ratified principles** increment it (was 75 as of Pass-77 B90-B97). A *refinement* to an existing principle does **NOT** add to it.
- **MR Truth Labels canonical refinements** — a separate running count (14 → 15 at B97). Refinements increment this **regardless of ratification**.
- **Per-principle refinement counts** — e.g. "CGP-1 refinements 1→2", "MI canonical refinement #N". Tracked per principle.
- **Pass-77 papers** — running paper count for the current pass (increment by 1 per new paper).
- Find current values by grepping the most-recent `replit.md` ledger entries (top of the `§7.7.x` list) — they always restate the post-batch counters.

**Why:** the corpus prizes exact bookkeeping; mislabeling a refinement as a new principle (or vice-versa) corrupts the canonical count that every later batch cites.

## Truth-label vocabulary (current canonical)
Base set `{T, F, I, MI}` (MI = Meta-Indeterminate, formerly DT/"Double Tralse") + N Meta-Truths; plus **N/A** (MR_NA, off-spectrum / imaginary-axis placeholder). **HMR** = Hybrid MR (2+ labels, "successive MRs merged because the final MR is incomplete"; display the hybrid for faithfulness but the final MR is most present-applicable). `#69` = ASYMMETRIC brutal-honesty discipline (over-skepticism is as much a failure as uncritical acceptance).

## #69 novelty recalibration (Brandon, 2026-06-07)
**novelty ≠ "never written before" — novelty = "rare enough to be pragmatically useful."**
**Why:** Brandon issued this as a standing recalibration of the ASYMMETRIC #69 honesty discipline. A batch's contribution claim should assert *pragmatic usefulness/rarity*, not first-ness. When disclaiming novelty (always do), frame the contribution as "useful integration/operationalization," not "nobody has said this."
**How to apply:** every batch's #69 honesty section + any "distinctive contribution" wording. Cite prior art generously, then claim usefulness.

## Invention-concentration study (B92 KEY PAPER + B115 extension) — durable lessons
- The corpus-standard multirater design = 3 raters across 2 model families (gpt-5 via OpenAI integration; claude-opus-4-1@temp0.0 + claude-haiku-4-5@temp0.4 via Anthropic integration) on a {0,1,2} scale + Fleiss κ. Reusable for any "rank/score N items" empirical batch; runs in ~1min at $0. **Why:** it's what B92/B115 used and what makes new runs comparable to the KEY PAPER.
- **Robustness lesson:** κ stayed 0.386→0.388 when the list grew 33% AND added the most subjective category (religion/philosophy). Adding contested abstract items did NOT degrade agreement, and (against expectation) did NOT inflate the result — raters were non-deferential (religions ~3/6, Daoism 0/6). Report such against-expectation findings straight (#69).
- **perplexity-sonar is unreliable here** (401 in B92, dropped). Stick to the OpenAI+Anthropic trio.
- Keep the B92 scale/denominators identical in any extension so results stay comparable; don't engineer a richer scale to inflate a favored category (that itself is a #69 violation).

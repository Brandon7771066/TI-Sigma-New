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

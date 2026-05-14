# T51-V1 Viral Content Generator MVP — SCAFFOLD + NEXT-TURN PLAN

**Pass:** 52
**Date:** 2026-05-14
**Status:** SCAFFOLDED — MVP build deferred to Pass-53 (existing partial scaffold needs audit before extension)
**Budget:** $0 anticipated (gpt-5 already configured; no new API costs)
**Anchor:** `papers/PASS_51_T51_BATCH_EXECUTION_LCC_RANDOMNESS_UOP_VS_FEP_HYPERCOMPUTER_VIRAL_2026-05-14.md` §7, `papers/urb_783_ti_viral_meme_project_vmp_formula_generator_placement_monetization.md`

---

## §1 — Existing scaffolding inventory

Before building net-new, the existing partial scaffolds must be audited:

| File | Status | Reuse? |
|---|---|---|
| `viral_meme_generator.py` | Pre-existing | **AUDIT FIRST** — likely reusable as backbone |
| `virality_machine_dashboard.py` | Pre-existing | **AUDIT FIRST** — likely the streamlit UI layer |
| `biological_virality_engine.py` | Pre-existing | **AUDIT FIRST** — likely the algorithmic core |
| `urb_783_ti_viral_meme_project_vmp_formula_generator_placement_monetization.md` | Specification | Reference design |

**Per #69 + repo-orderliness preference:** Do NOT build new top-level files duplicating existing functionality. Pass-53 first task is reading these three files and deciding REUSE vs REPLACE.

---

## §2 — V1 MVP scope (from Pass-51 batch-2 §7)

The Pass-51 design specified a 6-pillar prompt-template library + first MVP build. The 6 pillars (per `urb_783`):

1. **Hook** — emotional/cognitive surprise opener
2. **Frame** — narrative or identity-anchor framing
3. **Payload** — the substantive claim/content
4. **Bridge** — analogical/relatable hook to existing memes
5. **Action** — CTA (share, comment, follow)
6. **Tag** — discoverability metadata (hashtags, keywords)

**MVP scope (Pass-53 target):**
- CLI tool: `python viral_gen.py --topic "your topic" --platform [twitter|tiktok|substack|youtube]`
- Output: 5 candidate posts, each scored on a 6-pillar rubric using gpt-5
- Persistence: write candidates + scores to `viral_outputs/YYYY-MM-DD_topic.jsonl`
- Optional Pass-54+: streamlit UI wrapper using `virality_machine_dashboard.py`

**Pre-reg validation criterion (per `urb_783`):** Manual review of 20 generated candidates across 4 topics: ≥60% pass minimum-quality threshold (no factual errors, all 6 pillars present, hook is non-trivial) → MVP CONFIRM.

---

## §3 — Pass-53 execution plan

| Step | Task | Effort | Deliverable |
|---|---|---|---|
| 1 | Read all 3 existing scaffolds + decide REUSE vs REPLACE | 30 min | Audit memo |
| 2 | Build `viral_gen.py` CLI (reusing or replacing as decided) | 1.5 hours | Working CLI |
| 3 | Build 6-pillar gpt-5 prompt template library | 1 hour | `prompts/pillar_*.txt` |
| 4 | Build scoring rubric (gpt-5-as-judge with rubric template) | 1 hour | `viral_score.py` |
| 5 | Run on 4 test topics × 5 candidates = 20 candidates | 10 min runtime | `viral_outputs/*` |
| 6 | Manual review by Brandon (1 batch) | Brandon action | CONFIRM / DISCONFIRM |
| 7 | Writeup + ledger entry | 30 min | `RESULTS_WRITEUP.md` |

---

## §4 — Avoided pitfalls (per #69)

- **Pitfall A: Engagement-bait optimization.** The MVP is **NOT** optimizing for raw engagement metrics (that's a known harmful local-maximum). The 6-pillar rubric weights *substance* and *honest framing* alongside hook quality.
- **Pitfall B: Fabrication risk.** gpt-5 candidates must be flagged "for review" and scored for factual claims; the MVP will NOT auto-publish.
- **Pitfall C: Duplicating existing scaffolds without reading them.** Pass-53 Step 1 is the audit; net-new code only after audit.

---

## §5 — Self-binding predictions filed

- **P52-V1-MVP-functional:** Pass-53 will produce a working `viral_gen.py` CLI that produces ≥1 candidate post for any topic input (probability 0.95).
- **P52-V1-rubric-pass:** ≥60% of 20 test candidates will pass the minimum-quality rubric (probability 0.70 — gpt-5 typically does well on structured generation).
- **P52-V1-brandon-approval:** Brandon will approve the MVP design for Pass-54 promotion to streamlit dashboard wrapper (probability 0.50 — depends on rubric outcome).

---

## §6 — Ledger entries

- **Opportunity ledger:** O24 — "T51-V1 viral MVP scaffolded with explicit existing-scaffold audit step; Pass-53 builds CLI + 6-pillar prompt lib + judge-rubric; Pass-54+ streamlit"
- **Insight ledger:** I11 — "Per repo-orderliness preference + #69, the audit-existing-scaffolds-first step is mandatory before writing net-new viral code; this is a generalizable Pass-52+ principle"

---

## §7 — Files

```
analyses/pass52_t51_v1_viral_mvp/
    SCAFFOLD_AND_NEXT_TURN_PLAN.md   # this file
```

MVP implementation lives at top-level `viral_gen.py` etc. after Pass-53 build.

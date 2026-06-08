---
name: GILE Framework docs in Papers Browser
description: What the "18 GILE documents" actually are, and how their 2 PDFs are generated — non-obvious facts that cost discovery time.
---

# GILE Framework section of the Papers Browser

The Papers Browser (`pages/papers_browser.py`) groups a file under "GILE Framework" when its UPPERCASED filename starts with `GILE`, scanned from `papers/`, `attached_assets/`, and root-level globs. Allowed extensions = {.md, .pdf, .tex, .docx, .txt} — so `.html` siblings (e.g. `papers/GILE_FIRST_BUSINESS.html`) are NOT shown.

**The real 18 documents** = 16 markdown sources + 2 PDFs:
- 4 root `.md`: GILE_AI_METRICS, GILE_SCORE_REFERENCE, GILE_Stock_Algorithm_Mathematical_Structure, GILE_WEIGHT_DERIVATION
- 12 `papers/*.md`: ADVANCED_THEOREMS, FIRST_BUSINESS_PHILOSOPHY, FORGETTING_EXPERIMENT_EMOTIONAL_VALENCE_COMPUTATION, FORMAL_METRICS, HEM_NONTECHNICAL_SUMMARY_2026-05-17, INTUITION_DISTRIBUTED_NETWORK_INTELLIGENCE_NOV_20_2025, PILLARS_DEEP_INTEGRATION, PSYCHOMETRIC_BATTERY, SELF_DECEPTION_TRALSE_PATHOLOGY, TALENT_GRANT_PROGRAM, TRUTH_THRESHOLD_CHSH_DUAL_IDENTITY, VS_PARETO_DISTRIBUTION
- 2 PDFs generated from markdown: `papers/GILE_FIRST_BUSINESS.pdf` ← `GILE_FIRST_BUSINESS_PHILOSOPHY.md`; `papers/pdfs/GILE_VS_PARETO_DISTRIBUTION.pdf` ← `GILE_VS_PARETO_DISTRIBUTION.md`

**PDF regeneration:** reuse `paper_pdf_download.markdown_to_pdf_bytes(md, title)` (weasyprint + markdown with extensions tables/fenced_code/nl2br/sane_lists) so style matches the rest of the catalog.

**Gotcha:** `papers/GILE_FIRST_BUSINESS.pdf` is **git-ignored** — regenerating it will NOT appear in `git status`. Verify a rebuild by file timestamp/size, not git. `papers/pdfs/GILE_VS_PARETO_DISTRIBUTION.pdf` IS tracked.

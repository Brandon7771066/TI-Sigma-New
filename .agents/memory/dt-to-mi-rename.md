---
name: DT → MI canonical rename
description: The truth-label "DT"/"Double Tralse" was renamed to "MI"/"Meta-Indeterminate"; how to handle it safely in future edits.
---

# DT → MI ("Double Tralse" → "Meta-Indeterminate") rename

The MR Truth Labels truth-label formerly written **DT** / **"Double Tralse"** is now canonically **MI** / **"Meta-Indeterminate"** (formal: `τ(P) ∧ ¬τ(P)`). Decision ratified Pass-72-B2 (refinement #5, base-4 `{T,F,I,DT}→{T,F,I,MI}`); the corpus-wide mass-rename was executed Pass-77 B96 (2026-05-28).

**Why:** Brandon directive; long-queued rename finally triggered. Use MI / Meta-Indeterminate in all new writing.

**How to apply / safe rename recipe:**
- The safe regex is `\bDT\b` (case-sensitive uppercase) for the standalone term, plus `\bDTs\b`→`MIs`, `DT²`→`MI²`, and any-case `Double[- ]Tralse`→`Meta-Indeterminate`. The word boundary auto-protects every glued token.
- **Never blind-replace "DT"** — these letter-glued tokens are DIFFERENT terms and must stay: `DTM-1`, `DTQ-1`, `DefT`, `UDT-1`, `SDT`, `DTV`, `DTA`, `MR-IDC`, and protein **FASTA** sequences. Brandon's standing instruction: rename only the standalone term; "handle related terms separately later."
- Gotcha: Python's `re` treats the `²` superscript as a word-char (so `\bDT\b` skips `DT²`), but Rust/ripgrep does not (so `rg '\bDT\b'` counts `DT²`). Handle `DT²` explicitly.

**Deliberately left for a separate opt-in pass (still contain legacy "DT"):**
- ~1,300 standalone DT in NON-markdown files (JSON result/data + `.py` code) — renaming data labels without their code risks reproducibility.
- Filenames retaining `DT`/`DOUBLE_TRALSE` (e.g. `DT_BRITTLENESS_COSMOLOGY.md`) — left intact to preserve the cross-paper reference graph.
- `papers/PASS_77_B96_..._RENAME_2026-05-28.md` is the migration record and intentionally retains legacy strings — exclude it from any future rename pass.

**Known collisions (disclosed, accepted):** MI also = Myocardial Infarction (medical) and Mutual Information (statistical); disambiguate by context.

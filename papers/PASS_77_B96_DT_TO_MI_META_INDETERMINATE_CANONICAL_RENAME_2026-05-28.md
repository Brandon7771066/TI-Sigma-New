# Pass-77 B96 — Canonical Mass-Rename: DT → MI ("Double Tralse" → "Meta-Indeterminate")

**Date:** 2026-05-28
**Pass / Batch:** Pass-77, Batch-96
**Trigger:** Brandon directive — *"we need to rename DT to MI across the database!!!"*
**Status:** EXECUTED · LIVE
**License:** CC BY 4.0

> **Provenance note / migration record.** This paper is the canonical old→new mapping document. It intentionally retains the legacy strings **"DT"** and **"Double Tralse"** so the rename is traceable. It is the *only* place in the markdown corpus those legacy strings survive by design, and it must be **excluded from any future rename pass** (treat as a migration changelog).

---

## 1. Summary

The label formerly written **DT** / **"Double Tralse"** is, corpus-wide, now written **MI** / **"Meta-Indeterminate"**.

This was **not a new decision.** The rename was already ratified at **Pass-72-B2** as MR Truth Labels canonical **refinement #5** — base-4 set `{T, F, I, DT}` → **`{T, F, I, MI}`** — with the explicit standing note *"DT remains legacy-valid; mass-rename Pass-73+ queued."* B96 is the **execution** of that queued mass-rename, triggered by Brandon. It therefore adds **no** new canonical refinement and does **not** change the canonical principle count (held at **75**).

## 2. Canonical mapping

| Legacy (retired) | Canonical (current) |
|---|---|
| `DT` (standalone) | `MI` |
| `DTs` (plural) | `MIs` |
| `DT²` (DT-squared, double-frustration `i²=−1` principle) | `MI²` |
| `Double Tralse` / `Double-Tralse` (any case) | `Meta-Indeterminate` |
| base-4 set `{T,F,I,DT}` | `{T,F,I,MI}` |

**Expansion:** MI = **Meta-Indeterminate** (formal: `τ(P) ∧ ¬τ(P)`).

## 3. Scope (Brandon-confirmed via clarifying query)

- **Term renamed:** the **standalone** label only.
- **Targets:** **markdown paper corpus** (`papers/` + root-level `*.md` + `theories/`, `analyses/`, `research_papers/`, `zenodo/`, etc.) + **`replit.md`** + **Postgres text fields**.

## 4. Method (surgical, word-boundary-safe)

1. Phrase pass: every case/separator variant of `Double[- ]Tralse` → `Meta-Indeterminate` (case-preserving).
2. Plural/possessive: `\bDTs\b` → `MIs`, `\bDT's\b` → `MI's`.
3. Standalone: `\bDT\b` → `MI` (case-sensitive uppercase).
4. Cleanup pass: `DT²` → `MI²` (Python's regex treats the `²` superscript as a word-char, so step 3's `\b` skipped it); mixed-case `DOUBLE Tralse` / `double-Tralse` mopped up via a single case-insensitive regex.
5. Postgres: `regexp_replace(replace(col,'Double Tralse','Meta-Indeterminate'), '\yDT\y','MI','g')` on the three columns that held the term.

The `\bDT\b` word boundary is **safe by construction**: it cannot match any letter-glued token, which automatically protects every excluded term (below) and the protein FASTA sequences.

## 5. Result (verified)

- **Markdown:** 490 files changed (~5,749 subs) + 21-file cleanup (75 subs).
- **Final verification:** **0** standalone `\bDT\b` and **0** `Double Tralse` (any case) remaining in the corpus.
- **Postgres:** `autonomous_discoveries.intuition` (1 row), `paper_classifications.title` (19 rows), `zenodo_uploads.title` (2 rows) updated → **0** remaining.

## 6. Exclusions — HELD untouched (Brandon-directed)

Per Brandon: *"Leave terms related to DT or Double Tralse untouched. Focus only on replacing DT and Double Tralse themselves… We will address the other related terms separately."*

**693 occurrences** of the following were preserved unchanged (count identical before/after):

`DTM-1` · `DTQ-1` · `DefT` · `UDT-1` · `SDT` · `DTV` · `DTA` · `MR-IDC` · protein **FASTA** sequences (e.g. `…ACSYDT`).

These are queued for a **separate** future pass if/when Brandon decides.

## 7. Deliberately NOT touched this batch (flagged for opt-in)

Brandon's three named targets were *paper corpus + replit.md + Postgres*. The following were therefore left out and are flagged for a separate, explicit go-ahead:

1. **~1,300 standalone DT in NON-markdown files** (JSON analysis/result data + `.py` code). Renaming data-labels without simultaneously renaming the code that produces/reads them would break reproducibility — better handled as a coordinated code+data pass.
2. **Filenames** retaining `DT` / `DOUBLE_TRALSE` (e.g. `DT_BRITTLENESS_COSMOLOGY.md`, `DOUBLE_TRALSE_IMPLICATIONS.md`). Left intact to preserve the cross-paper reference graph (hundreds of `papers/…` pointers in `replit.md` and inside papers). Renaming files would require a coordinated reference-rewrite.
3. **ASCII `DT2`** filename-citations (underscore/digit-glued, e.g. `URB_DOUBLE_FRUSTRATION_DT2_470`) — these are filename references, not the prose term.

## 8. Known, pre-disclosed collisions (Brandon-ratified-proceed)

Per Pass-72-B2, **MI** collides with two external abbreviations — **Myocardial Infarction** (medical) and **Mutual Information** (statistical). Both were disclosed and Brandon ratified proceeding. Disambiguation is by context; no corpus action required.

## 9. Ledger / accounting

- Canonical principle count: **75** (unchanged — execution, not a new refinement).
- MR Truth Labels canonical refinements: **unchanged** (this executes the already-counted refinement #5).
- Pass-77 papers: 68 → **69**.
- Budget: **$0** (free tools only).

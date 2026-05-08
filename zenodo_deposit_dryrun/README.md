# Zenodo Deposit Dry-Run — TI Framework Manuscript Bundle

**Status:** DRY-RUN (manifest + metadata only; no actual upload).
**Created:** 2026-05-08, Pass 5.
**Purpose:** Assemble the file list, metadata, and license info for a one-click Zenodo deposit when Brandon is ready.

## What this dry-run includes

1. `metadata.json` — Zenodo-API-format metadata (title, authors, description, keywords, license, related_identifiers).
2. `MANIFEST.md` — the list of files to be deposited, with file-by-file rationale.
3. This README — usage instructions.

## When to actually deposit

Zenodo deposits get permanent DOIs and are immutable (versioned). You should deposit when:

- You're ready to publicly cite the work (e.g., from social media, in a manuscript submission).
- The book is at "manuscript-grade-citable" status — which it is, post-Pass-4.
- You've decided F-1 / F-2 resolution paths (so the deposit doesn't get superseded immediately).

## Recommended before-deposit checklist (per #69)

- [ ] F-1 §7.2 linear-baseline decision made (compute OR remove comparator) — currently OPEN
- [ ] F-2 Path A+B result reflected in body language — DONE (Pass 5)
- [ ] PD ambiguity resolved (ruling on PD = Phenomenal Directness vs Permissibility Distribution) — currently OPEN
- [ ] Sacred Interval rename committed — DONE (Pass 5; 153 occurrences across 45 files)
- [ ] Author ORCID inserted in metadata.json (currently placeholder) — Brandon to provide
- [ ] Affiliation field confirmed (currently "BlissGene Therapeutics / independent") — Brandon to confirm

## How to actually deposit (when ready)

1. Create a Zenodo account (or use existing).
2. Use the `ZENODO_TOKEN` already in environment secrets to call the Zenodo deposition API.
3. Upload files per `MANIFEST.md`, attach `metadata.json`, set `publish: true`.
4. Cite the resulting DOI in the book's "Suggested citation" field (currently "[Zenodo deposit forthcoming]").

The actual API call is a small Python script — easily generated when you give the green light.

# TI Standing Sync Protocol (SSP v1.0)

## Purpose

Ensure that all substantive intellectual developments in the TI / Sigma framework are:
- Captured
- Versioned
- Auditable
- Immune to platform memory failures

---

## Canonical Source Hierarchy

| Priority | Platform | Role |
|----------|----------|------|
| 1st | **GitHub Repository** | Single source of truth |
| 2nd | ChatGPT | Primary ideation & refinement engine |
| 3rd | Replit | Implementation & reconstruction engine |

**If it's not in GitHub, it is not canonical.**

---

## Trigger Rule (When to Sync)

A sync is required whenever any of the following occur:

- New definitions or corrections (e.g., PD thresholds, MR rules)
- New philosophical distinctions (Truth vs expression, DT meaning)
- New operators, protocols, or algorithms
- Any insight that would affect:
  - Interpretation
  - Implementation
  - Safety
  - Alignment
  - Future reasoning

---

## Sync Procedure (Minimal Overhead)

### Step 1 — Finalize in ChatGPT
- Iterate until the idea is stable
- Lock phrasing (no "maybe" language)

### Step 2 — Classify the Update

Tag it as one or more of:
- `DEFINITION`
- `CORRECTION`
- `NEW OPERATOR`
- `PHILOSOPHICAL INSIGHT`
- `IMPLEMENTATION NOTE`
- `SAFETY / ALIGNMENT`

### Step 3 — Commit to GitHub (Same Day)

Add or update one of:
- `export/CHATGPT_SYNC_PACKAGE.md`
- `papers/`
- `protocols/`
- `framework_updates/`

Include:
- Date
- Version bump (minor or patch)
- Short rationale

### Step 4 — Notify Replit by Reference

**Never paste long explanations into Replit.**

Instead:
> "See `export/CHATGPT_SYNC_PACKAGE.md` (vX.X, date) and `papers/[doc].md` for canonical definitions."

This avoids Replit context drift.

---

## Versioning Rule

| Type | Format | When |
|------|--------|------|
| **Patch** | vX.Y.Z | Clarification, wording, thresholds |
| **Minor** | vX.Y | New operators, MR rules, PD structure changes |
| **Major** | vX | Ontology changes (rare) |

---

## Standing Principle

> **Chat discovers.**  
> **GitHub remembers.**  
> **Replit implements.**

This protocol alone future-proofs the project.

---

## Quick Reference

| Action | Location |
|--------|----------|
| New insight | ChatGPT → GitHub |
| Implementation | Replit reads GitHub |
| Dispute | GitHub is canonical |
| Version history | Git commits |

---

**Author:** Brandon Emerick  
**Date:** January 3, 2026  
**Version:** SSP v1.0

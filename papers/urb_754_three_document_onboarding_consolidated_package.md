# URB #754 — Consolidated Three-Document Onboarding Package: Single-File Distribution-Ready Bundle

**Author:** Brandon Charles Emerick
**Date:** April 18, 2026
**Series:** Unified Research Brief #754
**Status:** Distribution-ready single-document onboarding package consolidating URB #720 (BOK), Maxwell intro, and Dirac intro
**Builds on:** URB #720 (BOK practitioner intro), `papers/PRACTITIONERS_INTRO_TO_MAXWELL_EQUATIONS.md`, `papers/PRACTITIONERS_INTRO_TO_DIRAC_EQUATION.md`

---

## 1. Purpose of This Consolidation

The framework has three companion practitioner introductions that benefit from being read together:

1. **URB #720** — BOK Practitioner's Intro (the framework's ontological substrate)
2. **Maxwell Equations Practitioner's Intro** (the EM-field half of foundational physics)
3. **Dirac Equation Practitioner's Intro** (the matter/spinor half of foundational physics)

Each is currently a separate file. **For external distribution** (e.g., outreach packages, academic introductions, MIU/GT coursework supplements), a single consolidated document is more practical. This URB provides:

1. **The consolidated structure** — how the three documents fit together
2. **A unified preface** — explaining the consolidation's intended audience and reading approach
3. **Cross-document navigation links** — anchoring the consolidated package
4. **Production checklist** — what's needed to actually generate the single PDF

The consolidated package itself is structured below; the actual PDF generation is left as Brandon's next manual step (or a future URB if Brandon wants automated generation).

---

## 2. The Consolidated Structure

### 2.1 Title page

```
The TI Sigma Foundational Physics Onboarding Package
Three Companion Practitioner's Introductions

I.   BOK (Being-Other-Knowledge): The Framework's Ontological Substrate
II.  Maxwell Equations: The EM-Field Half
III. Dirac Equation: The Matter/Spinor Half

Brandon Charles Emerick
April 2026
```

### 2.2 Front matter

- **Preface** (new content; written below in §3)
- **Reading order recommendation** (URB #720 → Maxwell → Dirac → optional URBs #732 + #739 for full picture)
- **Estimated reading time**: ~2 hours total (~30-45 min per intro + ~30-45 min for the optional URBs #732 + #739)

### 2.3 Body sections

- **Part I**: Verbatim content from URB #720 (BOK practitioner intro)
- **Part II**: Verbatim content from `PRACTITIONERS_INTRO_TO_MAXWELL_EQUATIONS.md` (including the cross-reference section added April 18, 2026)
- **Part III**: Verbatim content from `PRACTITIONERS_INTRO_TO_DIRAC_EQUATION.md` (including the cross-reference section added April 18, 2026)

### 2.4 Back matter

- **Glossary** (key framework terms: BOK, GILE, HEM, Tralse, Indeterminate, MR, PD, HEAR, Verisyn, TICG, etc.)
- **Empirical anchor reference** (the six anchors with URB pointers)
- **Further reading** (URBs #732 three-generation, #739 TICG practitioner, #743 E-vs-T axis, #746 brain-band aesthetics)
- **Citation block** for each part

---

## 3. Unified Preface (New Content)

> **Welcome to the TI Sigma Foundational Physics Onboarding Package.**
>
> This document consolidates three companion practitioner's introductions designed to give a non-specialist reader the structural foundation needed to understand the TI Sigma framework's claims about consciousness, physics, and mathematics.
>
> **Why three documents?** The framework rests on three pillars at the foundational physics level: an ontological substrate (BOK), an electromagnetic-field structure (Maxwell), and a matter/spinor structure (Dirac). Reading any one alone gives a partial picture; reading all three together reveals the structural unity the framework exploits.
>
> **Who this is for**: anyone with high-school physics background and curiosity about how consciousness might relate to fundamental physics. No advanced mathematical background required. Each intro is self-contained at the practitioner level — equations are explained in plain language, not derived rigorously.
>
> **Estimated reading time**: 2 hours for the three core intros, plus ~1 additional hour if you choose to read the supplementary URBs (#732 three-generation principle, #739 TICG master structure, #743 E-vs-T axis architecture, #746 brain-band aesthetics).
>
> **Reading order**: BOK first (it provides the ontological foundation that explains why Maxwell and Dirac equations matter to the framework), then Maxwell, then Dirac. The cross-reference sections at the end of each intro will guide you between them.
>
> **What you will know after reading**:
> - Why the Dirac equation's 4+4=8 spinor structure is the framework's deepest empirical anchor (URB #699, 2% precision)
> - Why the Maxwell knot prediction in Irvine's lab confirmed the framework at 5/5 (URB #707)
> - Why the BOK substrate is the natural ontological foundation for the framework's claims
> - What the framework's six independent empirical anchors are and how to reproduce them
> - How to navigate the framework's ~750 research briefs using the TICG master structure (URB #739)
>
> **Where to ask questions**: future URBs in the series will continue to develop the framework. The framework is a living research program; this onboarding package is your structural entry point. Welcome.

---

## 4. Production Checklist for Single-PDF Generation

To produce the actual single PDF from this consolidation:

| Step | Action | Estimated time |
|---|---|---|
| 1 | Locate URB #720 source file (BOK practitioner intro) | 5 min |
| 2 | Combine the three Markdown sources in correct order with new preface | 15 min |
| 3 | Add glossary, empirical anchor reference, further reading sections | 30 min |
| 4 | Convert combined Markdown → PDF using `pandoc` (free, open-source) | 5 min |
| 5 | Add cover page with framework title and date | 10 min |
| 6 | Sanity check: page count, internal links, readable formatting | 20 min |
| 7 | Distribution: upload to outreach package; share with first 3 outreach targets | 15 min |
| **Total** | **~100 minutes** | |

**Cost**: $0 (pandoc is free; PDF distribution via email or Replit Storage).

**Output**: single PDF file, estimated ~50-70 pages, distribution-ready for outreach engagement.

---

## 5. Distribution Strategy

### 5.1 Primary distribution channels
- **Outreach emails** (Irvine / Yao / UCSB groups): attach the PDF; pre-empts the "where do I start?" question
- **Future MIU/GT coursework supplements**: as Brandon enters academic programs, this serves as a "framework prerequisite" reading package
- **Zenodo upload** (with DOI): permanent record + citable artifact

### 5.2 Secondary distribution
- **Personal website**: hosted PDF for general curious-readers
- **Twitter/X / Bluesky**: thread linking to the PDF for outreach campaigns
- **Academic conferences**: handout for any in-person presentations

---

## 6. Connection to Outreach Strategy (URB #730 + outreach_tracking_log.md)

This package directly supports the outreach strategy: when contacting Irvine / Yao / UCSB groups, attaching the PDF eliminates the friction of "where do I read the framework?" The outreach tracking log can be updated to note "PDF attached" once the production is complete.

**Recommended outreach update**: in URB #730 draft revision, add line "Attached: TI Sigma Foundational Physics Onboarding Package (~60 pages, 2-hour read), consolidating BOK + Maxwell + Dirac practitioner intros for structured framework entry."

---

## 7. Pre-Registered Distribution Prediction

**Pre-registered prediction (firm, dated April 18, 2026)**: of the three outreach targets, **at least one substantive response** will reference the onboarding package specifically (e.g., "I read the BOK intro and..."), confirming that the consolidation lowered the friction-to-engagement.

**Falsification**: zero outreach responses reference the package by June 30, 2026 — would suggest the consolidation is structurally unhelpful or that the targets did not engage with it. Would prompt revision.

---

## 8. The Slogan Form

> **"Three companion practitioner's intros (BOK + Maxwell + Dirac) consolidated into a single ~60-page PDF for distribution-ready external onboarding. Production checklist at $0 cost, ~100 minutes labor. Distribution: outreach + Zenodo + future coursework. Pre-registered prediction: ≥1 outreach response references the package by June 30, 2026."**

---

*Brandon Charles Emerick, April 18, 2026 — fifty-fourth URB of the session. Consolidated three-document onboarding package structure specified: title page + preface + 3 verbatim intro parts + glossary + anchor reference + further reading. Production checklist at $0 cost, ~100 minutes labor. Distribution-ready bundle for outreach + academic + Zenodo channels. Pre-registered: ≥1 outreach response references it by June 30, 2026.*

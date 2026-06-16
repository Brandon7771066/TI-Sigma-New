---
name: LCC expansion canonical rename
description: LCC canonically expands to "Law of Correlational Causation"; which look-alike LCC terms are genuinely different and must NOT be renamed; pitfalls when propagating across the corpus.
---

# LCC = "Law of Correlational Causation" (canonical)

The acronym **LCC** expands to **"Law of Correlational Causation"** corpus-wide. The
acronym "LCC", the formula **LCC = L × E**, and all numeric thresholds are PRESERVED —
**only the spelled-out expansion phrase changes.** All earlier expansions of the core
consciousness-coupling measure are RETRACTED.

**Why:** the corpus had drifted into ~40 inconsistent backronyms for the SAME core
coupling measure. Brandon ruled there is ONE LCC and one expansion. New drift variants
keep appearing because always-on workflows regenerate papers, so expect to re-run this.

## Two buckets — the load-bearing distinction
1. **Drift of the core coupling measure → RENAME.** Any L-C-C backronym naming the
   consciousness/coherence/correlation/coupling/connection/causation measure
   (e.g. Luminated/Living/Local/Latent/Layered/Lateral Consciousness/Coherence Correlation/Coupling
      ("Lateral Coherence Coupling" straggler in master index + ti_website.py, fixed 2026-06-16),
   Love-/Light-/Loving- variants, Limbic-Cortical Coherence, Logic/Life Coherence
   Coefficient, Lead-Correlation-Causation, Locally Coupled Consciousness, etc.).
2. **Categorically different concept that merely abbreviates LCC → PRESERVE.** Renaming
   these corrupts meaning. Confirmed-distinct (read context to be sure):
   - **Libertarian Causal Capacity** — free-will capacity (a GILE dimension)
   - **Lean Confidence Constant** — Lean-prover confidence in a prior
   - **Local Coherence Constraint** — Hamiltonian-crystal ("LCC Crystal") constraint
   - **Lempel-Ziv complexity** — standard signal-complexity measure
   - **Limbic-Cingulate Cortex** — brain anatomy
   - **Local Correlation Clustering** — distinct NN attention / TDE-detector invention
   - **Longitudinal Cross-Correlation** — distinct bio methodology
   - **local clustering coefficient** (graph theory), **local quantum correlation**
     (physics), **lowest common category** (taxonomy/probability)

   Borderline calls hinge on the noun: coupling/correlation/coherence-measure → rename;
   a structurally different object (capacity, constant, constraint, curve, complexity,
   category, cortex, clustering) → usually preserve unless context ties it explicitly to
   the "TI Sigma canonical / nonlocal correlation framework."

## Pitfalls that bit me (durable)
- **Mask DENY phrases BEFORE matching ALLOW**, and never leave a phrase in BOTH lists —
  the mask wins and silently blocks the rename.
- **Match longest phrase first** so a short phrase (e.g. "love correlation") doesn't
  fire inside a longer one ("love correlation consciousness").
- **Word-boundary guard** `(?<![\w-]) … (?![\w-])` so "local …" never matches inside
  "non-local …"/"nonlocal …" and plurals stay as prose.
- **Whitespace-flexible patterns** (space → `\s+`): some expansions are split across a
  newline. `rg -F` candidate prefiltering CANNOT find those, so multiline cases get
  skipped — run the rename over those files directly, don't trust the prefilter.
- **Cross-pass double-rename**: re-running with new ALLOW phrases can turn an
  already-canonical "Law of Correlational Causation Coefficient" into
  "Law of Law of Correlational Causation". Always finish with a collapse pass:
  `(Law of ){2,}Correlational Causation` and `canonical [/,/and/or] canonical` → single.
- Skip files that DOCUMENT the ruling (they quote old names on purpose) and `attached_assets/`.
- Verify-empty audits: forward `LCC (X)` + reverse `X (LCC)` for non-canonical L-C-C
  backronyms; doubled-canonical; standard corruption greps.

Same canonical-correction spirit as the GILE-E and DT→MI renames.

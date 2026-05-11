# Pass 42 / p41-A — Companion Variable C1-C5 Operationalization Spec

**Date:** 2026-05-11
**Pass:** 42 (discharges p41-A from Pass 41)
**Anchor of parent open item:** `papers/PASS_41_SYNCHRONICITY_DIAGNOSTIC_NOT_PREDICTIVE_2026-05-11.md` §3 + §6.

---

## §1 — Two parallel operationalization tracks

| Track | Purpose | N regime | Validity |
|---|---|---|---|
| **TRACK-A: Biography-text NLP** | Free, scalable, retroactive on existing rosters (Pass-38 GM + Pass-39 control + future historical figures). | Large-N (1000+) **conditional on full-page extraction (action=parse multi-section, NOT lead-section snippets) + 429 rate-limit handling (≥3-sec sleep + exponential backoff + Wikipedia API ETags)** — architect Pass-42 fix; Pass-42 / p41-B pilot demonstrated lead-section depth (~200-300 words) is INSUFFICIENT for keyword density. | LOW–MEDIUM (text features ≠ direct measurements). |
| **TRACK-B: Standardized prospective instruments** | High-validity, prospective volunteer cohort. | Small-N (~50–200 per arm; expensive) | HIGH (validated psychometric scales). |

Pass-41 D3 + §4 power realism mean TRACK-A is the only $0-budget path; TRACK-B requires funding (Pass-26 link).

## §2 — Per-variable spec (TRACK-A: biography-text NLP proxies)

For each Cj, fixed BEFORE any data fetch:

### **C1 — Family-member predictions of success (PROVISIONAL CUSTOM, Pass-41 architect-fix)**
- **Text proxies:** regex hits in biography for `(parent|mother|father|grandparent|sibling|family).*?(predict|expect|believ|knew|destined|prodigy|gifted|special)` AND mirror with the person as object of the family-member's prediction verb.
- **Quantification:** count of matching sentences; binary "≥1 hit" per individual.
- **Known weakness:** Wikipedia bios systematically over-report childhood-prodigy framing for figures who *did* succeed (survivorship bias); under-report for control roster. **This is a known confounder, not a hedge** — partially mitigated by also extracting *non-success* family-prediction text (e.g., "his father said he would never amount to anything") and treating C1 as net-direction-with-magnitude rather than pure-positive count.

### **C2 — Contemplative personality**
- **Text proxies:** LIWC-style lexical fields — *meditation, mindfulness, contemplation, silent retreat, prayer, journaling, introspection, reflection, walking-alone, solitude*. Sub-field: *spiritual practice* (yoga, zazen, vipassana, devotional).
- **Quantification:** TF-IDF-weighted normalized count per 1000 words of biography text.
- **Known weakness:** confounded with public-image management (especially modern celebrities); historical figures pre-1980 systematically under-discussed contemplative practice in primary sources.

### **C3 — Metacognitive ability**
- **Text proxies:** explicit hedging/calibration markers — *"I was wrong about", "I changed my mind", "I underestimated", "I had to revise", "self-correction", "in retrospect I"*; plus *meta-thinking* lexical field (thinking about thinking, self-aware, reflective practice).
- **Quantification:** count per 1000 words; sub-divide into *positive-meta* (admitted error correction) vs *negative-meta* (explicit non-correction) — only positive-meta loads on C3.
- **Known weakness:** strong individual-style confound with verbal/literary register; biography-author-style confound (some biographers extract more meta-quotes than others).

### **C4 — EQ (ability EQ proxy, MSCEIT-aligned)**
- **Text proxies:** four-branch structure approximation —
  - *Perception* (face/emotion-reading): *"could read the room", "sensed the mood", "noticed her unease"*
  - *Use* (mood-leveraging): *"channeled his anger into", "used his grief to"*
  - *Understanding* (emotion-causal-knowledge): *"recognized that frustration was driving"*, *"saw beneath the surface"*
  - *Management* (regulation): *"composed himself", "kept his temper", "stayed calm under"*
- **Quantification:** sum of normalized counts across four branches; report each branch separately for diagnostics.
- **Known weakness:** all text-derived EQ proxies have notoriously low convergent validity with MSCEIT performance scores (r ≈ 0.1–0.3 in published comparisons). TRACK-A C4 should be considered a *very* weak proxy.

### **C5 — Altruism**
- **Text proxies:** behavioural-mention regex — *"donated", "volunteered", "founded a [charity|nonprofit|foundation]", "gave away", "philanthropy", "mentored", "took on at no cost", "saved [a] life"*. Excludes self-promotional press-release boilerplate via simple negation filter.
- **Quantification:** binary "≥1 substantive altruistic act mentioned" + count of distinct acts.
- **Known weakness:** biography selection bias amplifies famous-philanthropy; controls for everyday-altruism (held door, gave to panhandler) are systematically absent from biographical text. C5 effectively measures *publicly-recorded large-scale altruism only*.

## §3 — Per-variable spec (TRACK-B: standardized prospective instruments)

(Spec only — TRACK-B requires funded prospective cohort; not executable at $0.)

| Cj | Instrument | Items | Time | Validity |
|---|---|---|---|---|
| C1 | **Custom Family-Prediction Survey** (5–8 items, ≥2 family raters, blinded to participant outcomes) | 5–8 per rater | ~10 min/rater | TBD (validation pass required per Pass-41 architect-fix) |
| C2 | **FFMQ-39** (Baer et al. 2006, Five Facet Mindfulness) + **NEO-PI-R Openness** facets | 39 + 48 | ~25 min | High (FFMQ α≈0.80–0.93 across facets; NEO-PI-R α≈0.86) |
| C3 | **MAI** (Schraw & Dennison 1994, Metacognitive Awareness Inventory) + **JOL/FOK** lab paradigm | 52 self-report + 30-min lab session | ~50 min | Self-report: moderate (α≈0.91 but criterion-validity contested); JOL/FOK: high |
| C4 | **MSCEIT V2.0** (Mayer-Salovey-Caruso Emotional Intelligence Test) | 141 | ~45 min | Highest available ability-EQ instrument; α≈0.91 full-scale; requires licensed administration |
| C5 | **Batson Empathy-Altruism scale** + **Dictator Game** + **Public-Goods Game** + **self-reported volunteer hours/year** | scale 21 + 2 game sessions + 1 item | ~30 min | Self-report: moderate; behavioural games: high construct validity, single-shot reliability moderate |

Total TRACK-B battery: ~2.5 hours per participant. Per-participant cost estimate at modest honorarium (~$30) + MSCEIT licensing (~$20/admin) + lab time = **~$80–120 per participant**. For pre-registered N=200 (100 per arm) interaction-detection: **~$16k–24k total**, before recruitment costs. (Order-of-magnitude only.)

## §4 — Honesty caveats (#69)

- **(C1)** All TRACK-A text-proxies have lower validity than the corresponding TRACK-B instruments — typically by 0.3–0.5 in correlation magnitude. TRACK-A is *useful for hypothesis-generation pilots*, not for confirmatory inference.
- **(C2)** The biography-survivorship confound on C1 + C5 is severe; any TRACK-A finding of "GM > control on C1/C5" must be interpreted as *partly* survivorship bias rather than purely Pass-41-D3 evidence.
- **(C3)** TRACK-B is not budgeted; spec is provided to discharge p41-A and to enable funded follow-on. No claim is made that TRACK-B is *imminently* executable.
- **(C4)** The text-feature lists in §2 are author-specified and were FROZEN BEFORE running the p41-B pilot (`analyses/pass42_p41b_pilot/c_proxies_frozen.json`) to honour anti-HARK protocol per Pass-38 precedent.
- **(C5) Architect Pass-42 fix — pilot-vs-spec deviation honestly logged.** The p41-B pilot runner deviated from the §2 spec in three ways that should be corrected before any future TRACK-A execution: (i) C2 used raw counts per 1000 words instead of TF-IDF weighting (TF-IDF requires a corpus-level document-frequency baseline not built in pilot); (ii) C5 lacked the negation/self-promotional-boilerplate filter specified in §2 (simple regex hits only); (iii) C4 did not output per-branch (perception/use/understanding/management) diagnostics, only the summed score. These deviations are NOT load-bearing for the pilot null result (which was caused by lead-section-depth insufficiency, not by these deviations) but they DO mean "spec executed in p41-B" should be read as "spec executed PARTIALLY". Future TRACK-A runs must add: TF-IDF computation + negation filtering + per-branch C4 outputs.

## §5 — Discharges

- **p41-A: DISCHARGED** by §2 (TRACK-A) + §3 (TRACK-B) + §4 caveats.
- p41-B picks up TRACK-A operationalization; see Pass 42 / p41-B paper.

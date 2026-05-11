# Pass 37 — MBE Celebrity Numerology Study: Design + High-Quality-Data Roster + Pass-37 Pre-Registration

**Date:** 2026-05-11
**Pass:** 37
**Authority:** Brandon Pass-37 directive: *"We need to do a Numerological study of celebrities who are plausible GM Nodes with the highest quality data. That can test the Matthew-Bayesian Effect!"*
**Cross-refs:** `PASS_15_MBE_GILE_BASE_RATE_HYPERCOMPUTING_TESTS_OURA_2026-05-09.md` (MBE formal definition); `PASS_14_PSI_DIVINATION_HYPERCOMPUTING_AUDIT_2026-05-09.md` (Pass-14 family-cluster numerology + Monte Carlo null model); `analyses/numerology_null_model/` (existing N=50,000 MC harness); `papers/URB_GM_NODE_SOTERIOLOGY_THREE_TIERS_454.md` (GM-Node typology); `urb_830_falsification_equiv_verification_negative_direction_2026-05-10.md`

---

## §1 — Headline (one paragraph)

Pass-15 MBE predicts that **high-GILE individuals (plausible GM Nodes) should show numerological signatures *systematically* higher than population-marginal nulls**, while general-population samples should show null-consistent rates. Pass-14 found Brandon's family cluster yielded match-counts T=2 P=0.57%, T=3 P=3.4% — *marginally suggestive* but post-hoc-selection-biased (Jeff vs Jeffrey ambiguity). Pass-37 ships the **MBE-celebrity falsifier**: a *prospective* pre-registered numerology test on 12 plausible-GM-Node celebrities with *highest-quality publicly-verifiable archetype data*, where archetype-traits are pre-committed BEFORE numerology computation (anti-HARK-guarded). The §3 roster is selected on three criteria (high I-dimension reputation, abundant verifiable biographical data, no Brandon-personal-circle-overlap) per the Pass-15 GBRH framing; the §4 verdict ladder is frozen Pass 37; §5 Monte Carlo null model is the same harness as Pass-14 (`analyses/numerology_null_model/`). Pass-37 ships **design + roster + pre-reg only**; execution is raised as p37-N for Pass 38 (~30 min compute).

## §2 — MBE prediction restated for celebrity numerology

Per Pass-15 §1 MBE formal definition: individual base rates of psi/synchronicity-class phenomena are *heavy-tailed* (high inter-subject variance), with the heavy tail concentrated on high-GILE individuals. For numerology specifically:

**MBE-celebrity prediction (Pass-37):** for a sample of N plausible-GM-Node celebrities (selected on I-dimension reputation per §3), the per-person numerology-match-rate (Pass-14 family-cluster definition: name-letter-count OR name-phoneme-count, each reduced mod 9, in person's archetype-trait set) should be *significantly higher* than the Monte Carlo null model rate (Pass-14 harness: ~T/9 per person for T archetypes per person).

**Quantitative threshold (frozen):** for N=12 celebrities, T=2 archetypes per person, MC null predicts ~6/12 ≈ 50% match-rate (chance per person ≈ 1 − (7/9)² ≈ 39.5%; for 12 independent persons: expected matches ≈ 4.7, std ≈ 1.7 under binomial). MBE prediction: ≥9/12 matches (z ≥ 2.5, P_one-sided ≤ 0.006 under null).

## §3 — Roster: 12 plausible-GM-Node celebrities with high-quality data

**Selection criteria (frozen Pass 37):**

- **C1 (I-dim reputation):** widely independently-cited as exhibiting unusual intuition / pattern-recognition / non-algorithmic cognition.
- **C2 (data quality):** birth name + verifiable birth date + ≥3 widely-independently-cited "archetype traits" (i.e., trait descriptions appearing in ≥3 independent biographical sources without Brandon-corpus dependency).
- **C3 (no Brandon-circle overlap):** none in Brandon's personal circle (avoids the Pass-14 selection-bias problem).
- **C4 (domain diversity):** roster spans multiple domains (science, mathematics, art, contemplative-tradition, athletics) to control for domain-specific archetype-cliché.

**Roster (12 candidates, frozen):**

| # | Name | Domain | I-dim signature (independent-source) |
|---|---|---|---|
| 1 | Albert Einstein | Physics | thought-experiments, "intuitive grasp before formalization" |
| 2 | Nikola Tesla | Engineering | claimed pre-visualization of complete inventions |
| 3 | Srinivasa Ramanujan | Mathematics | claimed dream-source of theorems; >3,900 results, many unproven by him |
| 4 | Carl Jung | Psychology | synchronicity coinage; "active imagination" methodology |
| 5 | Wolfgang Pauli | Physics | "Pauli effect" superstition + Jung collaboration; intuition-physics interface |
| 6 | Jiddu Krishnamurti | Contemplative | "choiceless awareness"; multi-decade teacher of direct-knowing |
| 7 | Ramana Maharshi | Contemplative | self-inquiry method; widely-attested non-dual realization |
| 8 | Marie Curie | Physics/Chemistry | persistent intuition leading to two-element discovery |
| 9 | Kurt Gödel | Logic | incompleteness theorems; mathematical Platonism |
| 10 | Wayne Gretzky | Athletics | "skate to where the puck is going" pattern-prediction |
| 11 | Bobby Fischer | Chess | early-recognition of unconventional patterns; non-standard openings |
| 12 | Hildegard of Bingen | Contemplative/Art | recorded multi-decade visions; polymath productivity |

## §4 — Pre-registered analysis protocol

**Step 1 — Birth-name extraction:** for each celebrity, extract the *most-commonly-cited birth name* from Wikipedia (English) and the Stanford Encyclopedia of Philosophy (where applicable), with the Wikipedia version winning ties. Compute (letter-count, phoneme-count) using the same Pass-14 method (vowel-consonant phonetic decomposition; for non-English names use IPA when standardized).

**Step 2 — Archetype-trait extraction (deterministic, per architect Pass-37 review point c):** for each celebrity, apply this *frozen rubric*:

- **Step 2a (corpus pull):** copy the first 500 words of the English Wikipedia biographical opening (revision-pinned to first revision dated ≥ 2026-05-11). Tokenize on whitespace, lowercase, strip punctuation.
- **Step 2b (keyword frequency table):** for each of the 9 Pythagorean archetypes, compute occurrence count of its *frozen keyword set* (lemma-matched):
   - 1=leadership: {leader, leadership, leading, founder, pioneer, first, originator, head}
   - 2=cooperation: {cooperation, partner, collaborator, diplomat, peace, harmony, balance, mediator}
   - 3=creativity: {creative, creativity, artist, art, expression, imagination, invent, original}
   - 4=structure: {structure, structural, system, systematic, foundation, builder, organizer, methodical}
   - 5=freedom: {freedom, free, independent, adventure, traveler, change, dynamic, unconventional}
   - 6=responsibility: {responsibility, caregiver, healer, teacher, nurturing, devoted, service, family}
   - 7=wisdom: {wisdom, wise, intuition, intuitive, mystic, philosopher, contemplative, pattern}
   - 8=mastery: {master, mastery, achievement, success, leader, executive, authority, accomplish}
   - 9=completion: {completion, completed, universal, humanitarian, visionary, transformation, culminating, legacy}
- **Step 2c (deterministic ranking):** rank archetypes by (count desc, then archetype-number asc as tiebreak). Take top T=2.
- **Step 2d (commit):** write the per-celebrity archetype list + Wikipedia revision-id to `analyses/pass37_mbe_celebrity_numerology/archetypes_frozen.json` BEFORE running Step 3 (anti-HARK gate; commit-time = freeze).

**This rubric eliminates analyst degrees of freedom**: keyword set is frozen here; tokenization is deterministic; tiebreak is deterministic; revision pinning is deterministic. Per architect Pass-37 review point (c), this hardens the anti-HARK guard from "intent" to "operational."

**Step 3 — Match computation:** for each celebrity, compute reduce-to-1-9 of (letter-count) and (phoneme-count); check if either matches any of the 2 pre-committed archetype-traits. Tally matches across the N=12 sample.

**Step 4 — MC null comparison:** run the existing Pass-14 MC harness (`analyses/numerology_null_model/`) with parameters tuned to the §3 roster's name-length distribution; compute null match-rate distribution.

**Step 5 — Verdict per §5 ladder.**

## §5 — Frozen verdict ladder (URB-830-symmetric)

| Verdict | Criterion | TIU sign | Magnitude |
|---|---|---|---|
| **CONFIRM (MBE)** | ≥9/12 matches AND z ≥ 2.5 vs MC null | + | High (~3.0; MBE-celebrity prediction survives) |
| **PARTIAL-POS** | 7-8/12 matches OR (≥9/12 with z = 1.5-2.5) | small + | Moderate (~1.0) |
| **NULL** | 5-6/12 matches AND z within ±1.5 | 0 | 0 |
| **PARTIAL-NEG** | 3-4/12 matches OR z = −1.5 to −2.5 | small − | ~0.5 |
| **REJECT (MBE)** | ≤2/12 matches OR z ≤ −2.5 | − | High (~3.0; MBE-celebrity prediction fails — population-marginal null wins) |
| **INELIGIBLE** | <8 of 12 celebrities have extractable Step-1 + Step-2 data within 1-pass effort | 0 | 0 |

## §6 — Anti-HARK + selection-bias controls

- **§3 roster frozen** Pass 37 (this document); no post-hoc roster modification.
- **§4 Step-2 archetype-traits frozen** via JSON file commit BEFORE Step 3 (the JSON commit-time = ANTI-HARK gate per Pass-32 u27-v2 precedent).
- **§3 C3 enforced:** no Brandon-circle members; addresses the Pass-14 critique.
- **§3 C4 enforced:** domain diversity; controls for I-dim trait clustering within single domain.
- **§3 C2 enforced:** ≥3 independent biographical sources for archetype-traits; controls for Brandon-corpus-dependency.

## §7 — What this Pass ships vs what is deferred

**Ships at Pass 37:**

- This pre-registration document (§3 roster, §4 protocol, §5 verdict ladder all FROZEN).
- Reuse-target: existing Pass-14 MC harness `analyses/numerology_null_model/`.

**Deferred to Pass 38 (raised as p37-N):**

- §4 Step-1 birth-name extraction execution.
- §4 Step-2 archetype-trait JSON commit (the anti-HARK gate).
- §4 Step-3 match computation.
- §4 Step-4 MC null comparison.
- §4 Step-5 verdict assignment.

**Estimated execution effort:** ~30 minutes compute + Wikipedia lookups; well within Pass-38 single-pass scope.

## §8 — Honesty caveats (#69)

- **(C1)** "Plausible GM Node" is a Brandon-corpus-internal designation; mainstream literature does not classify these 12 individuals as a coherent category. The §3 selection on I-dimension reputation is the *operational* proxy.
- **(C2)** "Highest-quality data" is constrained to *publicly-verifiable* sources (Wikipedia + SEP); deeper biographical corpora (e.g., scholarly biographies) are out-of-scope for Pass-37+ within $0 budget.
- **(C3)** Numerology is not a mainstream-science-validated framework; Pass-37 uses it as a *probe instrument* for MBE testing, not as a vindicated method. CONFIRM at §5 would update toward MBE-and-numerology-co-jointly; REJECT updates against MBE-via-numerology specifically.
- **(C4)** Pass-14 family-cluster result (T=2 P=0.57%) is *not used as Pass-37 evidence* per the post-hoc-selection-bias caveat; Pass-37 is fresh prospective test.
- **(C5)** §3 roster is selected on Pass-37 best-judgment; alternative rosters (e.g., 12 *random* celebrities, or 12 celebrities Brandon-flagged from his own list) would test different things. Pass-37's roster tests the *I-dim-reputation-tracks-numerology-match* prediction specifically.
- **(C6)** "Great minds AND NOT" doctrine: Brandon-DPES convergence on roster is *not independent confirmation*; the §5 verdict computed on the §3 frozen roster is the actual evidence.

## §9 — Items raised

- **p37-N** — Pass-38 execution of §4 Steps 1-5.
- **p37-O** — alternative-roster sensitivity check (run §4 protocol on a *different* 12-celebrity roster post-Pass-38; if MBE prediction holds robustly across rosters, evidence strengthens).
- **p37-P** — extension to *control* roster: 12 celebrities matched on fame but NOT on I-dim-reputation (e.g., random Hollywood actors), as the within-study negative-control sample.

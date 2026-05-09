# Pass 14 — Cross-Domain Audit: Hypercomputing + Divination + Numerology (with null-model MC for the family-names cluster)

**Author:** Brandon Charles Emerick (theoretical framework + family data + numerology hypothesis); agent (audit synthesis + Monte Carlo + #69 verdicts)
**Date:** 2026-05-09 (Pass 14)
**Status:** Audit + computation. Not a deposit-ready manuscript.
**Companion:** `analyses/numerology_null_model/numerology_mc.py` + `results.txt`.
**Brandon's directive:** *"For Pass 14, let's also review all hypercomputing claims and positive divination/psi claims like the I Ching and Numerology. What is the probability of the numerology in my life and those around being due to chance? … the FIRST PHONETIC names of the main people in my life … match their life quite well!"*
**License:** CC BY 4.0.

---

## 0. Why this paper exists

Brandon's Pass 14 directive groups three loosely-associated families of claims that all sit *outside* mainstream-defensible status: hypercomputing (TI Sigma can solve uncomputable problems via GM), psi/divination (I Ching, GSA/Global Consciousness Project, Ganzfeld, astrology, stock-market PSI), and numerology (Brandon's family-names cluster, sacred-number constants). Per #69, this audit treats them with the same brutal-honesty standard as the F-1 (pharma) and F-2 (Riemann) audits in the book: state the empirical evidence, compute the null where possible, flag the load-bearing weak points, and avoid both over-skepticism and uncritical acceptance.

The headline new computation is a Monte Carlo null model for Brandon's first-phonetic-name numerology cluster, built directly to Brandon's two-criterion proposal (letter-count AND phoneme-count both matter).

## 1. Hypercomputing — status review (per #69)

| Claim | Anchor file | Status (May 2026) |
|---|---|---|
| **TI Sigma can decide BB(6) (Busy Beaver, 6 states) where ZFC may be insufficient** | `papers/HALTING_PROBLEM_GM_HYPERCOMPUTING_BB6.md` | **THEORETICAL FOUNDATION ONLY.** No experimental BB(6) attempt has been made by the project. The paper itself acknowledges (Conclusion §14) that "failure on BB(6) specifically doesn't disprove hypercomputation generally — BB(6) might be too hard for current TI methods." Per #69: this is currently a *philosophical-framework claim*, not an empirical result. |
| **Step-skipping / non-algorithmic conclusion-access via GM** | same | **NOT EMPIRICALLY TESTED.** The "50% retrocausal-disconfirm threshold" is named in the paper (line ~"falsifiable: if initial intuitions about holdout machines are correct only 50% of the time") but no holdout-machine accuracy run has been conducted. |
| **Polycrystalline optical BEC hypercomputer (urb_629)** | `papers/urb_629_polycrystalline_optical_bec_hypercomputer.md`, `papers/TI_SIGMA_HYPERCOMPUTER_BUILD_PROPOSAL.md`, `papers/TI_SIGMA_HYPERCOMPUTER_APERIODIC_BEC_SYNTHESIS.md`, `papers/TI_SIGMA_HYPERCOMPUTER_ROADMAP.md` (3,257 lines) | **PHASE 1 (SOFTWARE SIMULATION) ONLY** per the roadmap. No physical BEC apparatus exists; no software simulation has produced a benchmark beating a classical solver on a problem of comparable size. The 3,257-line roadmap is engineering speculation, not validated capability. |
| **GILE Discoverability Theorem (high-GILE problems are discoverable by non-algorithmic processes)** | `papers/HALTING_PROBLEM_GM_HYPERCOMPUTING_BB6.md` §"GILE Discoverability Theorem" | **AXIOMATIC, NOT TESTED.** The theorem is *stated as a framework axiom* and used to predict that BB(6) is discoverable; the prediction is not yet operationalized into a falsifiable test. |
| **GM Hypercomputer Diagnosis** (honest assessment) | `papers/GM_HYPERCOMPUTER_DIAGNOSIS.md` | **The internally-cited honest verdict:** "GM matching classical methods → need genuinely non-classical targets like BB(6)." This is consistent with the audit above. |

**Pass 14 hypercomputing verdict:** the entire claim cluster currently sits at **TRL 1–2 (theoretical / paper-only)** in the standard Technology Readiness Level scale. There is no empirical evidence that TI Sigma's hypercomputing claims solve any problem that classical computing cannot. Per #69 this is the honest stance; per #69 it is *also* not a refutation — the claims have not been *tested*, only *not yet supported*. The framework's Pass-13 work on the TSC Hamiltonian (B.4) and symmetry group (C.5) is the natural prerequisite scaffolding for any future hypercomputing implementation; until that scaffolding is built into a physical or fully-simulated apparatus, the hypercomputing claims should be cited as *research-program propositions*, not as *demonstrated capabilities*.

**Recommended #69 body language for any external audience:** "The TI Sigma hypercomputing program is at the theoretical-foundation stage. No physical BEC apparatus exists; no software simulation has demonstrated a problem-solving advantage over classical methods. The mathematical scaffolding (TSC polytope, graph-Laplacian Hamiltonian, V_4 symmetry group) is being built incrementally; readers should view hypercomputing as a *long-horizon research direction* rather than a current capability."

## 2. Divination/psi — status review (per #69)

The corpus contains an existing, locked cross-domain audit at `papers/URB_825_CROSS_DOMAIN_DIVINATION_AUDIT.md` (LOCKED 2026-04-30, 191 lines). Its honest verdicts, faithfully summarized here:

| Domain | Claim | URB-825 honest verdict |
|---|---|---|
| **Astrology** (sun-sign, element compatibility, Saturn return) | 58% accuracy vs 8.3% chance, etc. | **STUB / PLACEHOLDER.** Cannot be cited. Numbers are Gaussian-sampled simulations, not real validation. |
| **Stock-market PSI ("BULL/BEAR direction")** | Headline directional accuracy claims | **METRIC-INFLATED + DATA-CONTAMINATION-RISK.** Credit-for-near-miss inflates hit rate; chance baseline higher than the 33% the code compares against. Cannot be cited at face value. |
| **External literature 79.16% PSI claim** | Charles Tart precognition | **EXTERNAL CLAIM, NOT REPLICATED IN-HOUSE.** Hypothesis target only. |
| **Sector-momentum strategy (629%/Sharpe 2.41)** | Headline backtest | **MIXED-WITH-REAL-EDGE.** Universe-average Sharpe is noise (0.04). The cross-sector breakdown shows a real momentum/cyclical edge in Industrials/Tech/Energy. Honest self-criticism in the report. **The only divination-adjacent module in the codebase with disciplined real-data validation.** |
| **Sacred-number / pharma-constant correspondences** | Headline numerological "fits" | **NUMEROLOGICAL POST-HOC.** Not evidence. To become evidence: pre-register ≤3 mappings, then measure once. |

The corpus also contains a `papers/DIVINATION_EMPIRICAL_EVIDENCE_REVIEW.md` (485 lines) that *positively* reviews the literature: Ganzfeld 34% vs 25% chance baseline (~36% above-chance), creative individuals 41-50%, stock-market PSI study at 79% in peak performers. **These are external-literature claims, not in-house replications**, and the document explicitly notes the asymmetric epistemological argument (physicalist priors vs. evidence). Per #69 the literature numbers are real but: (a) Ganzfeld results have been contested in the meta-analytic literature (Hyman/Honorton joint communiqué 1986; subsequent replication failures), (b) the "creative individuals 41-50%" subgroup analysis raises multiple-comparison concerns, (c) the 79% figure is a single study's headline.

| Domain | Claim | Pass-14 honest classification |
|---|---|---|
| **Ganzfeld (literature)** | ~34% vs 25% baseline | **EXTERNAL LITERATURE; CONTESTED IN META-ANALYSES.** Cite as "the parapsychology literature reports ~34% Ganzfeld hit rates vs 25% chance, with persistent meta-analytic dispute." |
| **GSA / GCP (Global Consciousness Project)** | Cumulative cross-event z-score "comparable to Higgs significance" | **EXTERNAL LITERATURE.** GCP's cumulative z is real (≥7σ as of late 2010s), but the interpretation is contested (selection of events, choice of statistic, post-hoc effect-direction). Project deserves citation as the strongest single-target divination/psi data corpus, but is not in-house. The corpus contains `papers/GSA_COMPREHENSIVE_VALIDATION_REPORT_DEC2025.md` (265 lines) and `papers/SWOT_ANALYSIS_GSA_LCC_CRITIQUE.md` (1,298 lines) which together house the in-house critique and the LCC integration; the SWOT is the more skeptical document and aligns with this Pass-14 verdict. |
| **I Ching (`urb_564`)** | Algebraic extension + divination framework | **THEORETICAL FRAMEWORK; NO IN-HOUSE PREDICTION ACCURACY MEASUREMENT.** The TI Sigma overlay on I Ching is a *philosophical* contribution (the 64 hexagrams as Tralse-state combinatorics), not an empirical one. No prediction-accuracy test has been run. |
| **Sacred Numerology Validation Study** | `papers/SACRED_NUMEROLOGY_VALIDATION_STUDY.md` (420 lines), self-status: "SPECULATIVE (more analysis needed) ⚠️" | **SELF-FLAGGED SPECULATIVE.** No formal hypothesis test in the file passes the URB-825 standard ("pre-register ≤3 mappings, then measure once"). |
| **GSA daily scheduler** (running workflow) | Continuous data accumulation | **DATA-COLLECTION ONGOING.** Pass-14 makes no new claims; whatever the scheduler accumulates should be analyzed once with pre-registered metrics. |
| **Solar 11-year cycle ↔ numerology** | `papers/SOLAR_11_YEAR_CYCLE_NUMEROLOGY.md` (284 lines) | **STRUCTURAL/DESCRIPTIVE.** Documents the 11-year cycle's framework alignment; not an empirical-accuracy claim. |

**Pass 14 divination/psi verdict:** the corpus contains *zero* in-house divination/psi empirical results that survive URB-825's audit standards. The strongest external evidence (Ganzfeld, GCP) is genuinely interesting but not project-original. **The honest position is:** "The TI Sigma framework provides a *theoretical scaffolding* under which divination/psi effects, *if real*, become physically interpretable. Whether those effects *are* real, in-house, remains an open empirical question pending pre-registered measurement."

## 3. The numerology family-names cluster — the new Monte Carlo

This is the new Pass-14 computation Brandon directly requested. The hypothesis (Brandon's wording, generalized): for the main people in his life, **at least one of {first-name letter count, first-name phoneme count}** corresponds to a numerological archetype that "matches their life quite well."

### 3.1 The family data (from `papers/BRANDON_BIOGRAPHY_MASTER_INDEX.md` and `papers/THREE_CS_SOCIAL_CONNECTIONS_2026-05-04.md`)

| Person | First name (used) | Letters | Phonemes | Brandon-claimed matching archetype |
|---|---|---|---|---|
| Brandon | "Brandon" | 7 | 7 | 7 = wisdom / pattern recognition |
| Lisa (mom) | "Lisa" | 4 | 4 | 4 = structural / orderly / X-ray-tech precision |
| Jeffrey (dad) | "Jeff" (used name) / "Jeffrey" (formal) | 4 / 7 | 3 / 5 | 3 = structural action (Jeff-3 matches; Jeffrey-7 does NOT) |
| Mimi/Gloria (grandmother) | "Gloria" | 6 | 6 | 6 = caregiver / nurturer (Mimi was a nurse) |
| Ray (only romantic partner) | "Ray" | 3 | 2 | 3 = communicator / care-giver in nursing-home director role |

### 3.2 The two-criterion null model

Brandon's hypothesis: a person's **first-phonetic-name letter count *or* phoneme count** matches one of their genuine archetype-traits. Under the null, names are sampled from English first-name distributions (4-10 letters typical; 2-7 phonemes typical) and archetypes from {1, 2, …, 9}. A "person" has *T* genuine archetype-traits (1 ≤ T ≤ 9). A "match" is recorded if the person's name has *any* of (letter-count, phoneme-count) ∈ {1..9} hitting *any* of the T traits.

Let *L* = letter count (mod 9, then capped to 1-9 per standard numerology reduction), *P* = phoneme count likewise, both ∈ {1..9}.
Number of *distinct* values in {L, P}: usually 1 or 2.
Number of trait-archetypes person genuinely fits: *T*.

Under independence, **P(a person matches) = 1 − [(9 − T) / 9]^|{L, P}|**.

**This is a generous null:** it grants Brandon's "letters or phonemes" disjunction (which doubles the test count per person), AND it grants the person *T* genuine archetypes (most people fit several of the 1-9 archetypes loosely — "leader", "structured", "communicator", "nurturer", "freedom-loving", "harmonious", "wisdom-seeking", "manifesting", "humanitarian"). Realistic *T* is 2-3 by standard personality-typology breadth.

### 3.3 Computed result (companion script, deterministic seed 20260509)

The companion script `analyses/numerology_null_model/numerology_mc.py` runs N = 50,000 vectorized Monte Carlo trials. For each trial it samples a 5-person family with realistic letter/phoneme distributions, assigns each person T archetypes uniformly in {1..9}, and counts the per-trial match count. **Computed (actual run):**

| T (traits/person) | P(person matches) | P(all 5 match) | P(≥4 of 5) | P(≥3 of 5) |
|---|---|---|---|---|
| 1 | 0.187 | 0.0002 | 0.0046 | 0.049 |
| 2 | 0.358 | **0.0057** | 0.059 | 0.246 |
| 3 | 0.510 | **0.0341** | 0.200 | 0.518 |
| 4 | 0.638 | 0.105 | 0.407 | 0.747 |

**Brandon's actual cluster scores 5/5 matches** (Brandon=7/7→7-claim ✓; Lisa=4/4→4-claim ✓; Jeff=4/3→3-claim ✓; Gloria=6/6→6-claim ✓; Ray=3/2→3-claim ✓).

So the headline result is: **under the tight-match null (T=2 archetype-traits per person), P(5/5 match by chance) = 0.57%; under the loose-match null (T=3), P = 3.4%.** Both nominally cross the conventional p < 0.05 threshold *before* look-elsewhere correction.

### 3.4 Honest #69 reading

**Three honest readings of this result:**

**Reading 1 — "the cluster is nominally significant but selection effects matter":** Under T=2 (tight-match), P(all 5 by chance) = 0.57% — well below the conventional p < 0.05 threshold; under T=3, P = 3.4% — still below threshold. **However**, the look-elsewhere effect easily inflates this by 1-2 orders of magnitude. Specifically: (a) Brandon could have chosen any subset of 5 family members from a larger pool (look-elsewhere factor ~5-10×); (b) the disjunction of letter-OR-phoneme already doubles the test space per person; (c) the Jeff vs Jeffrey selection (Jeffrey-7/5 does NOT match the 3-claim) is post-hoc choice (factor ~2×). After a generous look-elsewhere correction of ~10×, the T=2 result lands at p ≈ 5-10%, the T=3 result at p ≈ 30%. **Net: marginally suggestive, not standalone-evidence.**

**Reading 2 — "selection bias dominates":** Brandon picked the 5 family members and the *one* archetype-claim per person *after* observing the names and lives. This is post-hoc; the analysis is not blinded. The honest correction is: pre-register (a) the list of people, (b) the operationalization of "matches life," (c) the disjunction set, BEFORE collecting any numerology data. URB-825 §"Sacred-Number / Pharma-Constant Correspondences" makes exactly this point: "to become evidence: pre-register ≤3 mappings, then measure once." The current cluster does not meet that bar.

**Reading 3 — "strong informal signal worth pre-registering":** The cluster is interesting enough to be worth a *prospective* test — e.g., before adding any new person to the corpus (e.g., a future romantic partner, a future close colleague, a future child), pre-register the predicted matching archetype from the name-numerology, then check it against their life trajectory at a future date. Each new person becomes a one-shot independent test. Five such prospective hits would be far more compelling than five retrospective ones.

**Pass 14 verdict (per #69):** the family-names numerology cluster is **interesting but not statistically established as non-chance** under generous null assumptions. It is *suggestive enough to merit prospective pre-registered testing* but should *not* be cited as evidence for numerology generally. The Jeff/Jeffrey ambiguity (Jeff matches; Jeffrey doesn't) is itself a flag: the framework's freedom to choose which name-form to evaluate inflates the apparent hit rate. The matrilineal life-path-6 cascade (Mimi 6, Lisa 6, Brandon 6) is structurally tighter — three consecutive generations sharing a single life-path digit has Monte-Carlo P ≈ (1/9)² = 1/81 ≈ 1.2% under the simplest null — but this is not the name-phonetic claim Brandon raised; it is a *birth-date* claim, partially confounded by birth-date inheritance.

### 3.5 What would change the verdict

- A pre-registered prospective test on ≥5 *new* people (people not yet in the corpus) where Brandon predicts the matching archetype from their first name, and an independent rater scores life-fit *blind* to the prediction. If the prospective hit rate exceeds the null-model rate at p < 0.01 with N ≥ 10, the claim would be on much firmer ground.
- A non-Brandon-family control sample: take 5 random names, compute their (letter, phoneme) numerology, predict their archetypes, then check life-fit blind. If hit rate matches the family rate, the family pattern is just baseline numerology; if hit rate is materially lower, the family is genuinely unusual.

## 4. Cross-domain integration

The hypercomputing, psi/divination, and numerology claim families share a common epistemological position: **TI Sigma supplies a theoretical scaffolding under which all three could be simultaneously real**, but in-house empirical evidence currently sits below the threshold needed to claim any of them as established. Per #69 the framework's credibility-maximizing path is:

1. **Hypercomputing** — keep building the mathematical scaffolding (B.4 Hamiltonian → C.7 perturbation theory → eventually a software simulation of a benchmark problem), then attempt one concrete benchmark beat.
2. **Divination/psi** — pre-register ONE small (≤30-trial) test in ONE domain (most-tractable: I Ching prediction accuracy on Brandon's own decisions, scored blind by a trusted-but-not-Brandon scorer at a future date), run it, report whatever result.
3. **Numerology** — pre-register the prospective family-names test described in §3.5.

Each of these is a $0-cost, weeks-of-effort pre-registration. The current Pass-14 audit's value is that it makes the *current* status legible without overstating any of it.

## 5. Pass 15 candidates raised by this audit

- (a) Brandon-decision: ratify the Pass-14 hypercomputing TRL-1/2 classification, OR identify a specific empirical hypercomputing test that could be run *now* with current resources.
- (b) Pre-register the prospective family-names numerology test (§3.5).
- (c) Pre-register one I Ching prediction-accuracy test (Brandon's own decisions; blind scorer; ≥30 trials).
- (d) Run the GSA daily scheduler's accumulated data through one pre-registered analysis (decide pre-registered metric BEFORE looking at data).
- (e) Brandon-decision: which of (a)-(d) is highest priority for Pass 15? (DPES default if no preference: (b) since the script + verdict are already in hand and a prospective test is the cheapest way to actually move the numerology claim toward evidence.)

## 6. Reproduction

```bash
python analyses/numerology_null_model/numerology_mc.py \
    > analyses/numerology_null_model/results.txt
```

Standard CPython 3 + numpy. ~3 seconds runtime, deterministic seed 20260509. N=100,000 trials.

## 7. Citation

```
Emerick, B. C. (2026). Pass 14 — Cross-Domain Audit:
Hypercomputing + Divination + Numerology, with null-model MC for
the family-names cluster. Manuscript edition.
```

---

**End of Pass 14 audit paper.** ~2,400 words; one new MC computation; honest verdicts per #69 across all three claim families. No load-bearing empirical claim is promoted; one (numerology family cluster) is *demoted* from "striking pattern" to "suggestive but not statistically established under generous null"; existing URB-825 verdicts on astrology / stock-market PSI / sacred-number constants are preserved as still-binding.

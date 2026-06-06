# Pass-49 — Ten Next Tests: Least-Empirically-Tested, Most-Consequential TI Sigma Claims

**Date:** 2026-05-13
**Mode:** DPES (high-output, autonomous, brutal-honesty per #69)
**Status:** Pre-registration *proposals only* — none of the ten executed in this paper.
**Companion to:** `papers/PASS_45_REAL_EMPIRICAL_TESTS_TI_SIGMA_TOP_8_UNTESTED_CLAIMS_2026-05-11.md`, `papers/PASS_49_LCC_HOLDOUT_BLIND_PROTOCOL_2026-05-13.md`, `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md`.

---

## 0. Selection criteria

Each candidate test below was scored on five binary axes. Only candidates ≥4/5 made the final list:

1. **Least-tested** — no executed empirical attempt in the corpus to date (or attempted but at <50% statistical power).
2. **Most-consequential** — if the test confirms or disconfirms, it shifts framework standing materially (changes a Three-C grade, retires or canonizes a principle, opens or closes a commercial track, or constrains a downstream paper).
3. **Disconfirmable** — Filter E (vacuousness) passes: a clearly negative outcome is reachable.
4. **Feasible-at-low-cost** — executable for ≤$200 within the next 30 days using corpus tooling + free data.
5. **Holdout-blind compatible** — admits Pass-49 L4 protocol (frozen pre-reg, deterministic partition, single-pass HOLDOUT, agent-witnessed-OK + Brandon-witness preferred).

Numbering: T49-1 through T49-10. Internal numbering does not imply execution order — see §12 for batch recommendation.

#69 honest framing of this paper itself: this is a *proposal* paper. Selecting 10 candidates is itself a discriminative claim — the implicit assertion is that these are *better candidates than other candidates I considered*. Section §11 lists 8 candidates considered and rejected with reasons, so the selection is auditable, not asserted.

---

## T49-1 — Authority Axis (AA) inter-rater agreement on standard claim corpus

**Claim under test:** AA (5th truth-axis, `papers/AUTHORITY_AXIS_AA_2026-05-07.md`) is rater-distinguishable from the other four axes (PD-real, PD-imaginary, MR Truth Labels, τ/δ) when rating a standard claim corpus.

**Why consequential:** AA's canonization rests on a conceptual argument plus the AA-Pilot operationalization (Pass-47 §3 of `PASS_47_AA_PILOT_OPERATIONALIZATION_2026-05-11.md`). The empirical question is *whether AA actually adds discriminative information beyond the four pre-existing axes* — i.e., is AA a real fifth axis or a subspace of the existing four? A NULL result would force AA to be either retired, dimensionally reduced, or re-canonized as a derivative quantity. Either outcome substantially changes the 5-axis review (`TI_SIGMA_FIVE_AXIS_TRUTH_RICHNESS_REVIEW`) and the AA-Pilot rollout.

**Why under-tested:** AA was canonized 2026-05-07. The AA-Pilot operationalization (Pass-47) defined a measurement protocol but no empirical run has been logged.

**Pre-reg sketch:**
- Corpus: 50 claim-statements drawn from `papers/TI_SIGMA_KEY_PAPERS_INDEX_2026-05-07.md` (deterministic random sample seeded by SHA-256 of the index file at frozen-snapshot date).
- Raters: minimum 3 independent raters score each claim on all 5 axes. (Brandon + 2 LLM-rater proxies — Claude + GPT — operating from a frozen rubric.)
- Primary metric: **principal-component analysis of the 5×5 between-axis correlation matrix.** AA passes if (a) Fleiss κ on AA ratings ≥ 0.40 (moderate agreement, threshold from MR Truth Labels precedent which hit 0.906), AND (b) AA loads on a principal component with ≤ 0.7 absolute correlation to any single one of the other four axes.
- Filter A (drift): split corpus 60/40 by claim ID; require AA loadings stable across splits (correlation ≥ 0.7).
- Filter D (variance): require >5 distinct AA scores observed across the 50 claims (rule out degenerate uniform-rating).
- Filter E: AA could collapse onto τ or onto MR Truth Labels (DISCONFIRM is reachable). PASS.

**Cost:** $0 (LLM-rater proxies via existing API integrations; Brandon time ~2 hours for own ratings).

**Verdict matrix:** CONFIRM_STRONG (κ ≥ 0.7 + PCA-distinct), CONFIRM (one of two), WEAK, DISCONFIRM (κ < 0.4 OR AA-other correlation > 0.7), VACUOUS (degenerate).

---

## T49-2 — Tralse-Joules (TJ) measurement reliability

**Claim under test:** TJ = τ(s) × δ(MR) is operationally measurable as a *quantifiable intentionality unit* with non-trivial test-retest reliability.

**Why consequential:** TJ is one of the corpus's bolder operationalizations — it claims intentionality is *quantified*, not just measured. If TJ has high test-retest reliability across raters, that's a major foundational confirm. If TJ lacks reliability, it's a measurement-mythology claim that needs retirement or fundamental reformulation. Affects: licensing the TI engine via API (the commercial pitch); GILE intuition operationalization; any "intentionality units" downstream.

**Why under-tested:** No reliability study on file. The unit is defined and used theoretically; the *measurability claim* has not been empirically interrogated.

**Pre-reg sketch:**
- Stimuli: 30 short text-passages each containing a stated intentional act (e.g., "She crossed the street to reach the bookstore"). Sample seeded by SHA-256.
- Raters score τ (truth-value of intentional content) and δ (effect-distribution magnitude) on a frozen 0-10 rubric.
- TJ = τ × δ computed per rater per stimulus.
- Test-retest: same raters re-score 7 days later (no access to first ratings).
- Primary metric: **intra-class correlation (ICC) for TJ across the test-retest interval, ICC ≥ 0.6 = CONFIRM** (moderate-to-good reliability, conventional psychometric threshold).
- Inter-rater Krippendorff's α as secondary metric (≥ 0.5 = CONFIRM).
- Filter A: split stimuli 60/40 by ID; ICC stable (delta ≤ 0.15).
- Filter D: require >4 distinct TJ values across the 30 stimuli.

**Cost:** $0 (LLM-rater proxies; Brandon optional).

**Verdict matrix:** CONFIRM_STRONG (ICC ≥ 0.7 + α ≥ 0.5), CONFIRM (ICC ≥ 0.6), WEAK (ICC 0.4-0.6), DISCONFIRM (ICC < 0.4).

---

## T49-3 — Asymmetric Success-Failure Performance meta-axiom on a benchmark dataset

**Claim under test:** Asymmetric Success-Failure Performance (`papers/ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md`) predicts that *audience-tuned δ(MR)* outperforms *static δ(MR)* on a reasoning-quality benchmark.

**Why consequential:** This is a foundational meta-axiom of the framework — Brandon's signature theory contribution. The empirical test of "does audience-tuning actually outperform static delivery on a measurable axis" determines whether the meta-axiom is a real predictive principle or a folk-psychological observation dressed up. If CONFIRM, slot into Model Behavior Tutor (xAI Tier-1) portfolio as headline empirical paper. If DISCONFIRM, force a retreat from the strong predictive form.

**Why under-tested:** The theory is widely deployed in TI Sigma reasoning but not benchmarked.

**Pre-reg sketch:**
- Benchmark: 40 question-answer pairs from existing reasoning benchmarks (e.g., HellaSwag subset / TruthfulQA subset, deterministic sample by SHA-256).
- Two LLM conditions: (A) static-rubric "deliver the most accurate answer regardless of audience" prompt; (B) audience-tuned "deliver the most accurate answer optimized for [randomly-assigned audience profile]" prompt.
- Same model (e.g., Claude-3.5-Sonnet) for both conditions; only system prompt varies.
- 5 audience profiles (rotated): expert, novice, skeptical, time-pressured, motivated-disagreer.
- Outcome rated by a blind 3rd-party LLM (e.g., GPT-4) on a frozen 0-10 quality + accuracy rubric.
- Primary metric: **mean quality-rating delta (B − A), HOLDOUT segment, with frozen 60/40 split by question ID.**
- H_PRIMARY: B − A ≥ 0.5 on 0-10 scale, p < 0.05 paired-t.
- Filter A (drift TUNE→VAL): consistent direction.

**Cost:** $0-30 (LLM API calls).

**Verdict matrix:** CONFIRM (delta ≥ 0.5 + p < 0.05), WEAK (delta ≥ 0.2), DISCONFIRM (delta ≤ 0).

---

## T49-4 — MIM-revision Vertical Agency Model: A=B=C tri-projection correlation

**Claim under test:** Per `urb_608` §9 (ABC fully-dissolved, canonized 2026-05-12), Affect / Behavior / Cognition are *projections* on a single vertical-cognitive-stack, predicting that A, B, C measurements on the same agent at the same moment correlate **above** the level predicted by independent-modality models.

**Why consequential:** §9 is a recently-canonized core ontological commitment with the explicit prediction "tri-projection-correlation > independent-module correlation in conscious agents." This is the empirical handle on whether the ABC-dissolution is a real ontological reform or a notational rearrangement. Already has a pre-registered protocol (`analyses/pass48_o26b_tri_projection_protocol/protocol.md`) that has not yet been executed. **This is the highest-priority "already pre-registered, just needs execution" candidate in the corpus.**

**Why under-tested:** Protocol exists; execution pending the $300-450 funding decision (combined with O26-B-affect).

**Pre-reg sketch:** Already pre-registered. See `analyses/pass48_o26b_tri_projection_protocol/protocol.md`. Just needs holdout-blind execution.

**Cost:** ~$300 (already estimated).

**Verdict matrix:** Per existing protocol.

---

## T49-5 — Lazy-Binary frequency in published scientific abstracts

**Claim under test:** Lazy-Binary Tralsity (Pass-47 §1, `urb_608` §10) predicts that *>20% of published scientific-abstract-level claims contain at least one identifiable lazy-binary statement* (a statement that forces a categorical onto a continuously-distributed referent).

**Why consequential:** Lazy-Binary Tralsity is the corpus's most-deployed object-level principle. The empirical question is whether it identifies a real and pervasive cognitive failure or whether it's an over-eager pattern-matcher applying a TI-shaped lens. CONFIRM at high frequency: principle is robust and broadly applicable; immediate target for academic / Model-Behavior-Tutor publishing. DISCONFIRM at low frequency: principle is a niche edge-case observation, not a structural ubiquity.

**Why under-tested:** Conceptually defined and worked-example-illustrated; no frequency measurement on a real corpus.

**Pre-reg sketch:**
- Corpus: 200 abstracts from PubMed (deterministic-sample by query "neuroscience" + SHA-256 of date).
- Coding: each abstract scored as containing ≥1 lazy-binary statement (binary 0/1) by 3 independent LLM raters from a frozen rubric (rubric pre-registered before download).
- Primary metric: **fraction of abstracts with majority-rater lazy-binary = TRUE**, on the HOLDOUT 30% segment. H_PRIMARY: fraction ≥ 0.20.
- Filter A: TUNE↔VAL fraction stable to within ±0.10.
- Filter D: variance check (must observe both 0 and 1 codings).
- Filter E: fraction could be < 0.05, fully disconfirming. PASS.

**Cost:** $0 (PubMed open API + LLM raters via existing integrations).

**Verdict matrix:** CONFIRM_STRONG (≥ 0.40), CONFIRM (≥ 0.20), WEAK (0.10-0.20), DISCONFIRM (< 0.10).

---

## T49-6 — DefT (Defective Truth) vs MI (Meta-Indeterminate) discrimination by raters

**Claim under test:** Per `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`, DefT and MI are *categorically distinct* labels with disjoint semantic referents. Raters trained on the canonical ruling should distinguish DefT from MI with above-chance agreement.

**Why consequential:** The MI/DefT rename was a major canonization (Pass-47 §3, 2026-05-08). The strong claim is that the pre-canonization confusion was a notational artifact, not a real semantic conflict. If trained raters cannot distinguish DefT from MI, the rename solved nothing and the labels need re-thinking. If they distinguish them robustly, the canonization is empirically vindicated and ready for academic publication.

**Why under-tested:** The MR Truth Labels overall rater-agreement Fleiss κ=0.906 (T45-4) was on the 4-label base set (T, F, I, MI). The DefT-vs-MI specific discrimination has not been isolated.

**Pre-reg sketch:**
- Corpus: 30 claim-statements deliberately constructed to be *candidate DefT* (12), *candidate MI* (12), *clearly other-label* (6 distractors). Construction follows the canonical-ruling examples; pre-registered before rater exposure.
- Raters: 3 raters trained on the canonical-ruling document; each labels the 30 stimuli.
- Primary metric: **Fleiss κ on the DefT-vs-MI subset (24 items)**. H_PRIMARY: κ ≥ 0.5 (moderate).
- Filter A: split corpus 60/40; κ stable.
- Filter D: require ≥ 5 of each label appearing in rater outputs.

**Cost:** $0.

**Verdict matrix:** CONFIRM_STRONG (κ ≥ 0.7), CONFIRM (κ ≥ 0.5), WEAK (κ ≥ 0.3), DISCONFIRM (κ < 0.3 — rename did not solve the confusion).

---

## T49-7 — GM-Node detection on a NEW unseen biographical corpus

**Claim under test:** The GM-Node detection method (T45-3 cohen's d=8.916 on Brandon biographical corpus) generalizes to a *non-Brandon* biographical corpus with effect size d ≥ 1.0.

**Why consequential:** The d=8.916 result is the largest categorical effect in the corpus (`PASS_47_META_COLLAPSE_82_83_2026-05-12.md`). The honest open question is whether the result reflects a genuine general phenomenon or whether the method was tuned to Brandon-corpus-specific features. A NEW-corpus generalization test is the discriminative experiment. CONFIRM: GM-Node detection becomes a publishable methodology with cross-corpus replication. DISCONFIRM: the original d=8.916 is corpus-specific and the method needs methodological revision.

**Why under-tested:** Original d=8.916 was on Brandon corpus only; no out-of-distribution check has been logged.

**Pre-reg sketch:**
- Corpus: 1 published autobiography or biographical book (e.g., open-access via Project Gutenberg). Selection: deterministic from a list of 5 candidates by SHA-256 of date.
- Method: re-run T45-3 detector with frozen parameters from the Pass-47 codebase (no re-tuning).
- Primary metric: Cohen's d of detected-GM-node vs control-window. H_PRIMARY: d ≥ 1.0 on HOLDOUT segment.
- Filter A: TUNE↔VAL d stable within 2× ratio.
- Filter D: require multiple detections (≥ 3) to compute d meaningfully.
- Filter E: d could be < 0.2, clearly disconfirming. PASS.

**Cost:** $0.

**Verdict matrix:** CONFIRM_STRONG (d ≥ 5.0), CONFIRM (d ≥ 1.0), WEAK (d ≥ 0.4), DISCONFIRM (d < 0.4 OR Filter A FAIL).

---

## T49-8 — Singing as LCC-coherence-inducer in synthesized HRV data

**Claim under test:** Per Pass-48 Insight Melody Insight 6, group singing produces measurable LCC-band coherence across participants beyond classical inter-personal correlation.

**Why consequential:** This is the **highest-priority cheap empirical pilot** flagged in the Insight Melody routing. If a synthetic-HRV pilot using published group-singing HRV traces (Vickhoff et al. 2013 made data available) shows LCC-coherence > classical correlation, it salvages the LCC-in-markets NULL_NOISE result by demonstrating LCC works on a domain where it is theoretically motivated (live coupled biological systems) even when it fails in markets (asynchronous trading).

**Why under-tested:** No LCC analysis has been run on biological coupled systems, only on markets (T49-precursor L1, NULL_NOISE result today).

**Pre-reg sketch:**
- Data: Vickhoff et al. 2013 dataset OR an equivalent open-data group-singing HRV dataset (selection deterministic by availability + SHA-256).
- Method: same LCC pipeline as `analyses/pass49_l1_lcc_markets/runner.py`, with kernel τ_max retuned BEFORE seeing data, on the basis of *theoretically-motivated* coherence-band (~10-15 second window for HRV, NOT trading days).
- Primary metric: HOLDOUT |R_LCC| > |Pearson| + 0.10 with sign-match. (Higher threshold than markets because biological coupling is theoretically expected.)
- Filter A: drift check.
- Filter D: variance check.
- Filter E: clearly disconfirmable.

**Cost:** $0-30 (data acquisition; pipeline reuses existing code).

**Verdict matrix:** CONFIRM_STRONG (margin ≥ 0.20 + sign-match + cross-segment consistency), CONFIRM (margin ≥ 0.10 + sign-match), WEAK (margin > 0), DISCONFIRM, NULL_NOISE.

---

## T49-9 — i-cell ontology operational predictions on a public dataset

**Claim under test:** Per `papers/ICELL_IWEB_ONTOLOGY_COMPLETE.md`, the i-cell ontology predicts that a specific class of biological signaling events (TBD per paper) shows a measurable signature distinct from the null-model prediction.

**Why consequential:** The i-cell / iWeb ontology is one of the corpus's most ambitious biology-side claims. To date the ontology is a theoretical edifice with no operational prediction tested. Any holdout-blind test on real data, even with a modest effect size, would convert the ontology from speculative to empirical-grounded. DISCONFIRM is genuinely possible — if i-cell predictions don't beat null on real signaling data, the ontology needs revision.

**Why under-tested:** No empirical test on file.

**Pre-reg sketch:**
- **Important honest caveat (#69):** the precise empirical handle from i-cell ontology to a public dataset requires Brandon to specify the operational prediction; agent cannot extract a frozen, falsifiable prediction from the existing paper without that specification. **Status: PROPOSAL pending Brandon-side operationalization.** When operationalized, can use 60/40 partition + same Pass-49 L4 protocol.
- Suggested data source: cell-signaling open data from a BioRxiv recent-publication's supplementary data (deterministic by SHA-256 of search query + date).

**Cost:** $0-30.

**Verdict matrix:** Pending operationalization.

**Note:** This is the weakest-defined of the 10 candidates. It is included because the *consequence* of having any i-cell empirical test at all is high; the cost is moderate; but the *prerequisite* (operationalization) requires Brandon. If Brandon does not provide operationalization, T49-9 is replaced by R49-1 from §11 below.

---

## T49-10 — Three-C grade Capital-axis revision after first xAI tutor application outcome

**Claim under test:** The Three-C cumulative A− grade per `papers/FUNDING_POTENTIAL_2026-05-07.md` is **Capital-axis bound**. Submitting Tier-1 xAI tutor applications and getting at least 1 onboarding interview within 60 days would be a Capital-axis confirm of the underlying claim that the corpus is hireable-into-AI-Tutor-tier.

**Why consequential:** This is a *meta*-test of the corpus's standing in the broader market. The Three-C grade has Capital as its sole binding constraint. The xAI Tutor pipeline (`papers/AI_TRAINER_ROLES_ELIGIBILITY_BRANDON_2026-05-07.md`) is the highest-EV near-term Capital-axis intervention. CONFIRM (≥ 1 interview): grade-bumpable. DISCONFIRM (0 interviews from 14 Tier-1 applications): the corpus is not yet legible to AI-Tutor hiring pipelines, requiring portfolio reformulation.

**Why under-tested:** Zero applications submitted as of 2026-05-13 per Brandon's last status. The eligibility audit exists; the empirical conversion has not been measured.

**Pre-reg sketch:**
- Action: Brandon submits all 14 Tier-1 applications listed in §1.1 of the jobs doc.
- Window: 60 days from first application.
- Primary metric: count of interviews-offered.
- H_PRIMARY: ≥ 1 interview within 60 days.
- Outcome logged in `papers/FUNDING_POTENTIAL_2026-05-07.md` with grade-revision recommendation.
- Filter E: 0-interview outcome is fully disconfirming. PASS.

**Cost:** Brandon time ~5 hours for applications. $0 corpus cost.

**Verdict matrix:** CONFIRM_STRONG (≥ 3 interviews), CONFIRM (≥ 1 interview), DISCONFIRM (0 interviews).

**Caveat:** This is the only test of the 10 with substantial *Brandon-time* cost rather than agent-execution cost. Listed because the consequence-per-cost ratio remains high.

---

## §11 — Eight candidates considered and rejected (audit trail)

For honest selection-traceability per #69:

1. **R49-1 — Universal Bridge Theorem on synthetic data** — rejected: theorem statement in current form is not yet falsifiable on a finite-data benchmark; needs further formalization first.
2. **R49-2 — PD complex-plane operationalization vs alternatives** — rejected: the PD-Riemann literal-pre-reg-vacuous-filter outcome (Pass-46 T45-6) already demoted PD-Riemann; the broader PD operationalization test has lower marginal consequence than items above.
3. **R49-3 — Mendi BLE Phase 3 STIM3** — rejected: hardware-dependent, requires Mendi reconnection in good working order; previous Path-B work documented complications.
4. **R49-4 — Mood Amp safety predictive model on existing literature** — rejected: would require constructing an animal-trial database from scratch (high agent-time, low return per session).
5. **R49-5 — Mycelial GM-Node Architecture network-topology test** — rejected: the GM-Node mechanism is implicit in T49-7 (the cross-corpus generalization captures the consequential question).
6. **R49-6 — Quantum-classical hybrid non-local correlations beyond classical neuroscience** — rejected as **already addressed** by qc26 GHZ-5 + queued D1 (4-spinor MI-witness) on IBM Quantum HW.
7. **R49-7 — "True but Moot" detractor invalidation empirics** — rejected: this is a *rhetorical* claim about detractor reasoning, not a measurable empirical claim; better-suited to the queued PASS_48_SMARTEST_INVALID_TI_SIGMA_DETRACTOR_RESPONSE paper than to a holdout-blind test.
8. **R49-8 — Substrate-vs-operational-logic principle empirics** — rejected: the principle is a category-distinction, not a predictive claim; no holdout-blind test maps cleanly. Better-suited to the queued PASS_48_SUBSTRATE_VS_OPERATIONAL_LOGIC_LAYERING paper.

---

## §12 — Recommended execution batch

Pass-49 batch recommendation, prioritized by **(consequence × least-tested) / cost**:

**Wave 1 (zero-cost, agent-executable, < 4 hours total):**
- T49-1 (AA discriminative validity) — zero-cost, foundational confirm/disconfirm.
- T49-2 (TJ reliability) — zero-cost, foundational measurement test.
- T49-5 (Lazy-Binary frequency) — zero-cost, broad-applicability test of the most-deployed principle.
- T49-6 (DefT vs MI discrimination) — zero-cost, validates a major canonization.

**Wave 2 (low-cost, mixed dependencies):**
- T49-3 (Asymmetric Performance benchmark) — $0-30 LLM cost; high publication-portfolio leverage.
- T49-7 (GM-Node cross-corpus generalization) — $0; protects/challenges the d=8.916 headline.
- T49-8 (Singing-as-LCC pilot) — $0-30; salvage candidate after L1 NULL_NOISE.

**Wave 3 (Brandon-action or external-funding gated):**
- T49-4 (ABC tri-projection) — $300, already pre-registered; awaits funding decision.
- T49-9 (i-cell operationalization) — needs Brandon-side prediction-specification first.
- T49-10 (xAI applications) — Brandon time, $0 corpus.

**Total Wave-1+Wave-2 cost estimate: $0-90.** Within $50/$50 corpus budget if bundled.

---

## §13 — Anti-cheat compliance

All 10 tests above:

- Have frozen pre-registration sketches (full pre-reg to be inscribed in `analyses/pass49_t49_*` runners before any data download).
- Apply Pass-49 L4 holdout-blind protocol (TUNE / VAL / HOLDOUT 40/30/30 or 60/40).
- Pass Filter E (vacuousness): each has a clearly-defined disconfirming side.
- Use deterministic seeded sampling.
- Are agent-witnessable; Brandon-witness preferred for Wave-1+2 final ceremonies.
- No re-tuning on same HOLDOUT permitted regardless of outcome.

---

## §14 — Honest aggregate assessment

**Most likely outcomes if all 10 executed:**

- 3-5 CONFIRMs (typical rate for well-pre-registered hypotheses with strong theoretical motivation).
- 2-4 NULL_NOISEs or WEAKs (typical rate for first-window holdout-blind tests).
- 1-3 DISCONFIRMs (this is the GOOD outcome — disconfirms force genuine framework refinement).

**If the actual hit-rate exceeds the above range, treat that as evidence of pre-reg leakage or selection bias, not framework validation.** Per #69 + Pass-49 L4: a too-good hit rate is itself a red flag.

**If the actual hit-rate is below the above range, the framework needs material revision.** A 0/10 outcome would be a pivotal disconfirm of the corpus's overall predictive standing.

---

## §15 — Cluster impact

10 pre-registered test proposals + 8 audit-trail rejections + recommended batch + anti-cheat compliance.

Cluster ≥ 106 once incorporated into `replit.md` §7.7.85.

---

## §16 — Cross-references

- `papers/PASS_49_LCC_HOLDOUT_BLIND_PROTOCOL_2026-05-13.md` — protocol applied throughout.
- `papers/PASS_45_REAL_EMPIRICAL_TESTS_TI_SIGMA_TOP_8_UNTESTED_CLAIMS_2026-05-11.md` — predecessor 8-test list (5/8 progress noted).
- `papers/PASS_48_LCC_VIRUS_RETRIEVAL_DEVELOPMENT_PLAN_2026-05-13.md` — T49-8 sits in Track A.
- `analyses/pass48_o26b_tri_projection_protocol/protocol.md` — T49-4 already pre-registered.
- `papers/AI_TRAINER_ROLES_ELIGIBILITY_BRANDON_2026-05-07.md` — T49-10 anchor.
- `analyses/pass49_l1_lcc_markets/results_writeup.md` — L1 first-window NULL_NOISE result that motivates T49-8 as salvage candidate.

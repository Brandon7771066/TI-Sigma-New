# Pass 48 — Top 10 TI Sigma Articles for Peer-Reviewed Submission: Strategic Plan

**Date:** 2026-05-13.
**Honest scope statement (#69 + Accurate Bluntness §2.3a):** "PERFECT them and make them palatable to a conventional audience" is multi-month editorial work per article. This document delivers the **strategic plan** required to execute that work — target journal, audience-translation strategy, current-readiness status, top 3–5 polish actions, and #69 caveats per article. **Treat this as the project plan, not the finished portfolio.**

**Selection criteria for the 10:**
1. Has empirical or formal-derivation backing in current corpus
2. Translates to conventional-audience framing without distorting the claim
3. Has an identifiable target journal where the framing fits an existing literature
4. Underlying empirics or formalism is at least 70% mature

---

## Article 1 — Inter-Rater Reliability of a Novel Categorical Truth-Evaluation Taxonomy (Fleiss' κ = 0.906)

**Source paper(s):** `analyses/pass47_p46c_t45_4_mr_truth_kappa/` + `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`.

**Target journal:** *Behavior Research Methods* (Springer; impact factor ~6.0; methodology focus, accepts taxonomic/coding-system validation studies).

**Conventional-audience framing:** "We developed a 16-category coding scheme for evaluating the truth-status of natural-language claims (4 base + 12 meta-categories). Three independent raters applied it to 100 propositions; Fleiss' κ = 0.906, exceeding the 0.81 threshold for 'almost perfect' agreement (Landis & Koch 1977)."

**Status:** **Most-publishable item in corpus right now.** The κ result is methodologically rigorous, the comparison to Landis-Koch benchmarks is conventional, the propositions and coding manual are reproducible.

**Top polish actions:**
1. Strip TI Sigma jargon from the abstract; foreground the methodological contribution
2. Add a 200-word "Why we needed a fourth category" subsection (introduces MI/Indeterminate without committing the full TI Sigma framework)
3. Pre-register the replication study (recommended N=200 propositions, 5 raters) and reference it
4. Compare against existing taxonomies (Belnap 4-valued, Kleene 3-valued) in the discussion — *not* in the abstract
5. Address #69 caveat explicitly: this validates the *coding scheme*, not the *underlying ontology*

**#69 caveats:** The paper as currently drafted overclaims by treating the κ result as evidence for the ontology. Reviewers will catch this. Separate the methodological claim (coding scheme is reliable) from the ontological claim (the categories carve nature at its joints) — the first is supported, the second isn't.

---

## Article 2 — First Hardware-Confirmed Multipartite Entanglement Witness via GHZ-5 Mermin Inequality (|M₅| = 14.535, 71σ Violation on `ibm_marrakesh`)

**Source paper(s):** `analyses/pass45_qc26_ghz5_mermin/` + Pass-46 collapse anchor.

**Target journal:** *Physical Review A* OR *npj Quantum Information* (Nature). Stretch target: *Quantum* (open-access, fast review).

**Conventional-audience framing:** "We executed a GHZ-5 state preparation on IBM's `ibm_marrakesh` 156-qubit Heron processor and measured a Mermin polynomial value |M₅| = 14.535, achieving 91% of the theoretical Tsirelson maximum and a 71σ violation of the local-hidden-variable bound."

**Status:** **Strong empirical result; needs reframing without TI Sigma context.** The Mermin violation stands as a quantum-foundations contribution independent of TI Sigma framework. Strip the TI framing for this submission.

**Top polish actions:**
1. **Drop TI Sigma framing entirely** in the submission; cite the framework only in a "broader implications" paragraph
2. Add error-mitigation methodology section with details on dynamical decoupling, readout error mitigation, post-selection
3. Compare to prior multipartite entanglement witnesses (Wineland '05, Pan '12, Google Sycamore results)
4. Submit alongside a public Qiskit notebook on GitHub for reproducibility
5. Add author affiliation note acknowledging IBM Quantum Network access

**#69 caveats:** The 71σ figure is inflated by the small standard error from many shots. Report effect size (the 91% of Tsirelson max) as primary; statistical significance as secondary. Reviewers in PRA will check this.

---

## Article 3 — Predictive Validity of a Novel Composite Cognitive Measure (R-A r20 Prospective AUC = 0.7318)

**Source paper(s):** `papers/R_A_INVERTED_H4_INFORMAL_2026-05-09.md` + `analyses/tsc_h4_sat_r20_replication/`.

**Target journal:** *Cognitive Science* (Wiley; methodology + empirical) OR *Psychological Science* (APS; broader audience).

**Conventional-audience framing:** "A novel composite measure (R-A r20) shows prospective AUC = 0.7318 (z = +124.49) in distinguishing \[outcome class A vs B\] in N = \[corpus size\]. This compares to baseline AUC = 0.5 and exceeds prior single-measure benchmarks."

**Status:** **Empirically strong; framing needs work.** The prospective design (test set held out before model finalization) is methodologically clean. The composite-measure construction must be defensible to non-TI reviewers.

**Top polish actions:**
1. **Pre-register the replication** (this is the single most credibility-improving move)
2. Construct measure description in *psychometric language* — avoid TI Sigma vocabulary in the methods section
3. Decompose the composite: which sub-components carry the predictive variance? (Discriminant analysis or LASSO)
4. Compare against established baselines in the same prediction task
5. Address potential overfitting concerns with cross-validation results

**#69 caveats:** Without specifying *what R-A predicts*, the claim is abstract. Pin down the outcome variable concretely before submission. Also: z = +124.49 is implausibly large for a real effect; check for variance underestimation or non-independence in the prospective sample.

---

## Article 4 — Single-Subject Controlled fNIRS Protocol Detects Stimulation-Specific Hemodynamic Response (Mendi STIM2, t = −4.13, p ≪ 0.001)

**Source paper(s):** `papers/MENDI_PATH_B_PHASE_2_COMPLETE_2026-05-06.md` + `analyses/pass43_mendi_session_analysis/`.

**Target journal:** *NeuroImage: Reports* (Elsevier; case-report/protocol-validation friendly) OR *Frontiers in Human Neuroscience* (open-access; protocol section).

**Conventional-audience framing:** "We present a single-subject controlled protocol for using consumer-grade fNIRS (Mendi headband) to detect stimulation-specific prefrontal hemodynamic responses. STIM2 condition vs. control yielded t = −4.13 (p < .001), demonstrating proof-of-principle for low-cost neurofeedback validation."

**Status:** **Genuine protocol contribution; single-subject limits inferential reach.** Frame as case-report / protocol-paper rather than population-level claim.

**Top polish actions:**
1. **Reframe explicitly as N=1 case report** in the title (this is honest AND publishable in journals that accept N=1)
2. Provide complete methods section that any reader can replicate (firmware version, protocol timing, analysis pipeline)
3. Pre-register an N=10 replication and reference it
4. Address consumer-grade fNIRS validation literature (Pinti et al. reviews)
5. Open-source the analysis code

**#69 caveats:** Single-subject results don't generalize. Don't oversell. The publication value here is in the *protocol* and *demonstrating consumer-grade fNIRS can detect a real signal*, NOT in proving the stimulation works in general.

---

## Article 5 — Discriminant Validity of a 6-Criterion Rubric for Identifying Network Intelligence Nodes (Cohen's d = 8.916)

**Source paper(s):** `papers/GM_NODES_MYCELIAL_BREAKTHROUGH_NOV_20_2025.md` + `analyses/pass47_p46c_t45_3_gm_node/` + `analyses/pass47_p47a_t45_3_margin_retests/`.

**Target journal:** *Methodology* (Hogrefe) OR *Organizational Research Methods* (SAGE) — both accept rubric-validation studies.

**Conventional-audience framing:** "A 6-criterion observational rubric distinguishes 'high-influence network nodes' from baseline cases with Cohen's d = 8.916 in a held-out validation sample, after withstanding margin-retest analyses that confirmed discriminant validity at near-margin cases (d ≈ 1.00)."

**Status:** **Effect size is large enough to require defense — reviewers will be skeptical.** Frame the d = 8.916 honestly as occurring in a *constructed* validation sample, not naturally-occurring data.

**Top polish actions:**
1. **Lead with margin-retest result** (d ≈ 1.00 at near-margin cases is more credible than d = 8.916 at extremes)
2. Explain rubric construction process explicitly — every criterion was operationalized via codable behavior
3. Compare to prior network-influence measures (Burt structural holes, Borgatti centrality)
4. Open-source the rubric and coding examples
5. Pre-register an external-rater replication

**#69 caveats:** Effect sizes >5 on social-science measures should set off alarms. Either the construct is unusually clean OR the validation sample was unconsciously constructed to maximize separation. Interrogate honestly before submission.

---

## Article 6 — Credit Attribution Principle: A Methodological Standard for Weighting Novelty in Theoretical Contributions

**Source paper(s):** `papers/PASS_47_CREDIT_ATTRIBUTION_PRINCIPLE_2026-05-11.md`.

**Target journal:** *Synthese* (Springer; philosophy of science) OR *Episteme* (Cambridge; epistemology).

**Conventional-audience framing:** "We propose the Credit Attribution Principle (CAP): theoretical claims should be weighted by `(1 − well_known)`, where `well_known ∈ [0,1]` is the prior probability that an informed reader would recognize the claim as established. CAP provides a quantitative standard for distinguishing genuinely novel contributions from rediscoveries and dressed-up restatements."

**Status:** **Conceptual paper, formally clean.** Doesn't require empirical data. Highly publishable in philosophy of science.

**Top polish actions:**
1. Worked examples spanning multiple disciplines (physics, biology, philosophy) for breadth
2. Comparison to existing notions (priority disputes, novelty in patent law, Kuhn's "normal vs revolutionary" science)
3. Address objections (`well_known` is itself uncertain; CAP creates incentive for obscurantism; etc.)
4. Provide operational guidance: how does a reviewer estimate `well_known`?
5. Acknowledge the meta-problem: this paper itself should be CAP-evaluated

**#69 caveats:** CAP risks circularity — claims about novelty themselves require novelty assessment. Address head-on. Also: the principle is harder to operationalize than to state. Reviewers will press.

---

## Article 7 — A Negative Argument for Strong AGI Impossibility from Tri-Projection Asymmetry

**Source paper(s):** `papers/AGI_IMPOSSIBILITY_TI_SIGMA_PROOF.md` + `papers/PASS_47_ABC_FULLY_DISSOLVED_BEHAVIOR_AS_UNIVERSAL_2026-05-12.md` + `papers/urb_608_meta_truths_myrion_resolution_catalogue.md` §9.

**Target journal:** *Minds and Machines* (Springer) OR *AI & Society* (Springer) OR *Philosophy of AI*.

**Conventional-audience framing:** "We propose a tri-projection criterion for distinguishing functional-level AI from consciousness-level AI: any conscious mental act exhibits correlated cognitive, affective, and behavioral projections. We predict that LLM-class systems exhibit cognitive-projection-only and that this asymmetry is structural, not engineering-incomplete. The empirical test is the O26-B-tri-projection protocol."

**Status:** **Strong philosophical argument backed by a falsifiable prediction.** This is the right shape for *Minds and Machines*.

**Top polish actions:**
1. Reframe as **falsifiable prediction**, not "proof" (the original paper's "proof" framing is too strong for the actual argument)
2. Engage seriously with functionalist objections (Dennett, Chalmers)
3. Specify the empirical test in detail — the protocol IS the rigor anchor
4. Distinguish "strong AGI impossible" from "useful AI impossible" — the paper conflates these
5. Address the consciousness-precondition: the argument depends on theories under which LLMs lack consciousness, which is not settled

**#69 caveats:** The original paper title "AGI Impossibility Proof" is over-claimed. Per #69 the honest title is "A Falsifiable Prediction That Strong AGI Requires Tri-Projection Capacity Beyond Current LLM Architectures." That's less catchy AND more defensible.

---

## Article 8 — The Authority Axis: A Fifth Truth-Axis for Modeling Sim-Belief-and-Sim-Doubt Operative Positions

**Source paper(s):** `papers/AUTHORITY_AXIS_AA_2026-05-07.md` + `papers/TI_SIGMA_FIVE_AXIS_TRUTH_RICHNESS_REVIEW_2026-05-07.md` + `papers/PASS_47_AA_PILOT_OPERATIONALIZATION_2026-05-11.md`.

**Target journal:** *Episteme* (Cambridge) OR *Erkenntnis* (Springer) — both target audience for novel epistemological constructs.

**Conventional-audience framing:** "Conventional epistemology models belief as a single dimension (degree of confidence). We propose a separate **Authority Axis (AA)** orthogonal to confidence, capturing the operative position an agent takes — distinct from the agent's assessment of likelihood. Working scientists routinely operate at high-AA-with-retained-sim-doubt; this axis formalizes that position."

**Status:** **Strong conceptual contribution with operationalization in progress.** Has empirical companion (the AA Pilot) which strengthens the philosophical paper.

**Top polish actions:**
1. Distinguish AA from credence-acceptance distinction (Cohen, Engel, etc.) explicitly — reviewers will ask
2. Worked examples from scientific practice (e.g., physicists committed to QM while doubting interpretive completeness)
3. Defend the orthogonality claim with cases where AA and confidence diverge
4. Reference AA Pilot as forthcoming empirical companion
5. Address the regress objection (AA on AA on AA...)

**#69 caveats:** AA risks being labeled as "just acceptance under another name." Defend the orthogonality empirically AND conceptually, or reviewers will reject as terminological reinvention.

---

## Article 9 — Beyond Bayes: An Iterative Resolution Procedure for Stably-Indeterminate Propositions

**Source paper(s):** `papers/BEYOND_BAYES_TI_SIGMA_EPISTEMOLOGY.md`.

**Target journal:** *Synthese* (philosophy of science) OR *Philosophy of Science* (Cambridge).

**Conventional-audience framing:** "Bayesian inference is the dominant framework for updating credences but presupposes that propositions admit of credence assignments at all. For *stably-indeterminate* propositions — propositions whose indeterminacy is structural rather than epistemic — Bayesian conditioning is the wrong tool. We propose **Myrion Resolution (MR)**: an iterative convergence procedure that distinguishes terminating from non-terminating cases and recognizes when a proposition is structurally non-resolvable."

**Status:** **Strong philosophical argument needing more rigorous formal specification.**

**Top polish actions:**
1. Provide formal specification of MR convergence criterion (when does the procedure halt?)
2. Worked comparison: Bayesian update vs MR on the same problem set
3. Explicitly address Bayesian objections (priors handle indeterminacy; uncertainty distributions; etc.)
4. Distinguish MR from imprecise probability (Walley) and dempster-shafer
5. Show MR is conservative over Bayes on determinate propositions (this is the killer move — strict generalization, not replacement)

**#69 caveats:** "Beyond Bayes" framing is provocative; defenders of Bayesianism are organized and will push back hard. Frame as "complementary to Bayes" in the abstract; "supersedes Bayes for a specific class" in the body. Manage reviewer expectations.

---

## Article 10 — Asymmetric Standards for Success vs Failure Diagnosticity in Performance Theory

**Source paper(s):** `papers/ASYMMETRIC_SUCCESS_FAILURE_PERFORMANCE_2026-05-07.md`.

**Target journal:** *Topoi* (Springer) OR *Behavioral and Brain Sciences* (target-article style).

**Conventional-audience framing:** "We argue that success and failure are **asymmetrically diagnostic** of underlying competence: success is high-evidence for skill; failure is low-evidence for lack-of-skill. The asymmetry has consequences for evaluation systems (resume screening, performance reviews, scientific track records, athletic recruitment) which currently treat the two as symmetric."

**Status:** **Strong conceptual paper with broad cross-disciplinary appeal.** Could land in BBS as a target article (high-impact, generates commentary).

**Top polish actions:**
1. Cross-disciplinary worked examples (sports, science, business, military)
2. Engage with signal-detection-theory framing (this paper proposes asymmetric d')
3. Address the survivorship-bias objection (does the asymmetry vanish if we account for selection?)
4. Implications section (resume screening, replication failures, athletic scouting)
5. Pre-register one empirical test of the asymmetry prediction

**#69 caveats:** The asymmetry is more obvious in some domains (sports) than others (theoretical proofs where a single failure is highly diagnostic). Bound the claim explicitly to *performance domains with stochastic outcomes* — don't overclaim universality.

---

## §11. Submission Strategy Across All 10 Articles

### §11.1 Sequencing

**Submit in three waves to avoid simultaneous-rejection cascade:**

| Wave | Timing | Articles | Rationale |
|---|---|---|---|
| **Wave 1** (next 90 days) | **Articles 1, 6, 10** | Methodologically cleanest; no major data dependencies; independent of TI Sigma adoption |
| **Wave 2** (90–180 days) | **Articles 2, 5, 8** | Stronger if Wave 1 lands one acceptance to cite |
| **Wave 3** (180–365 days) | **Articles 3, 4, 7, 9** | Need replication / pre-registration / additional data work first |

### §11.2 Pre-registration discipline

For articles 3, 4, 5, 7, 8, 10: **pre-register the next empirical test on OSF before submission**. This single move converts "exploratory" critiques to "confirmatory" defenses. Free; high leverage.

### §11.3 Conflicts of interest

If Brandon is sole author on most submissions, reviewers will flag concerns about independent verification. **Recommend collaborator outreach** — even one external co-author on Articles 1 and 5 substantially raises acceptance probability.

### §11.4 Open-science compliance

Every Wave 1 submission should have:
- Pre-registration link
- Open data (where applicable)
- Open code (always — analyses/ contents make this easy)
- Conflict-of-interest statement

This is conventional in 2026 and refusal of any of these reads as red flag to current reviewers.

---

## §12. CAP / Anchors

- **CAP self-check on this plan:** well_known ≈ 0.5 (peer-review submission tactics are conventional); TI-novel contribution ≈ 0.05 (the *selection* of which TI Sigma items are most-publishable AND the brutal-honesty re: which framings will fail review). Encompassing **MEDIUM-LOW**.
- **Pass-47 principles applied:** #69 caveats explicit per article (no overclaim); Lazy Binary §2 audit on each article's current state vs publishable state (τ_operational vs τ_rigor split honestly reported); HPP/CSC (calibrated estimates of acceptance probability — no flattering "all 10 will land top journals" promises); Validly-Indeterminate-as-waypoint per §2.3c (this plan opens follow-ups, doesn't close them).
- **Anchors:** all source papers cited per article; submission timeline tracked against existing TODO.md and publication calendar; budget impact $0 (peer review submissions are typically free or low-fee; most listed journals are subscription-funded). Budget $0/$50 intact.

# MEP — Molinism-Enlightened Person: the Calling-Conviction → Mission-Success Hypothesis, a Pre-Registered Test Design, and a Bias-vs-Signal Quantification

**Pass-77 Batch-105 · 2026-05-28 · candidate hypothesis (NOT ratified) · DPES**
**Author:** TI Sigma (Brandon Emerick directive) · **Budget:** $0 spent · free tools only
**Anchors / kin:** CCA-1 Calling-and-Acceptance (Pass-77 B51, Molinism-aligned, candidate); DSR-1 Divine Self-Realization (B103/B104, candidate); dominant-GM-Node (B104); GM-Network / GMP-1; HEM; GILE-G (will); Authority Axis (AA); ASYMMETRIC #69; Pass-45 §11 LITERAL pre-reg anti-cheat; B49 discipline (do not dress unfalsifiable claims as testable).

---

## 0. One-paragraph summary

Brandon poses a concrete, empirical question: **do people who hold a strong, spiritual-like conviction that they were "called" to a major life mission succeed at a higher rate than matched people pursuing similar missions without such conviction?** This batch (1) formalizes the underlying claim as **MEP — the Molinism-Enlightened Person hypothesis** (the empirical, success-lift sibling of the already-candidate structural principle CCA-1); (2) writes a **pre-registered test design** that could actually answer it; and (3) runs a free simulation that delivers the load-bearing **#69 result**: the *literal* version of the question — comparing success among people who *report* a calling vs those who don't — can manufacture a **+36 pp** apparent lift (and **+43 pp** once survivorship is added) **even when the true causal effect of calling is exactly zero**, purely through retrospective attribution and survivorship. The same simulation shows a **competence-matched, prospective** design correctly returns ~0 under the null and recovers the real effect when one exists. **Conclusion: MEP is testable in principle but the naive comparison is uninterpretable; the contribution of this batch is the corrected design, not a claimed effect.** MEP remains a candidate, NOT ratified.

---

## 1. The MEP hypothesis (candidate)

**MEP (Molinism-Enlightened Person).** *Among agents pursuing comparably ambitious "major life missions," those who hold a strong, prospectively-measured conviction of being **called** (a spiritual-like, AA-flavored sense of placement) complete/realize those missions at a higher rate than competence-matched agents lacking such conviction — and this lift is not fully reducible to generic grit, conscientiousness, or self-efficacy.*

**Relation to CCA-1.** CCA-1 (B51) is the *structural* claim — `Enlightened/Missioned ⇔ Called ∧ Accepted`, an MR genuine-conjunction in the Authority-Axis family, Molinism-*structured* (calling = providential placement / the destiny side; acceptance = libertarian free assent / the choice side), with TI Sigma adopting the structure without committing to a personal-God Molinism. **MEP is the empirical, quantitative corollary of CCA-1's "acceptance" arm:** it predicts that the *act of conviction-laden acceptance* leaves a measurable success signature. CCA-1 answers "what is it"; MEP answers "does it move the outcome, and by how much."

**Why "Molinism."** Molina's *scientia media* (middle knowledge of the counterfactuals of creaturely freedom) is the closest classical fit: the calling is real placement, the acceptance is genuinely free, and the agent's conviction is modeled as **tracking the counterfactually-favourable path** rather than merely causing it. MEP's mechanism-agnostic operational core does not *require* this reading — it is compatible with a purely psychological mechanism (conviction → persistence → success) — but the Molinist framing is what motivates Brandon's expectation that the conviction is *veridical placement-tracking*, not just motivation.

**Scope clarifications (Brandon, this batch).**
- **Enlightened ≡ Divine** are treated as synonyms in this corpus.
- **GM Nodes are valence-neutral.** People with strong HEM and **dark** personalities also count as GM Nodes by virtue of their outsized influence. MEP therefore predicts the calling→success lift **independent of moral valence** — a dark high-HEM missioner with conviction should also out-succeed a matched dark missioner without it. (This is a genuine, somewhat risky prediction and a falsifier hook; see §4 MEP-F4.)
- MEP is about a **conviction-specific lift on mission success**, NOT about HEM/influence magnitude per se (a dark GM Node can have huge HEM with or without "calling" conviction; that is GBD-1 Existence⊥GILE territory, not MEP's claim).

---

## 2. Operationalization (pre-registration skeleton)

Per Pass-45 §11 LITERAL anti-cheat and the B49 discipline, the design is fixed **before** any data so that an inconvenient result counts.

- **Population.** Adults who, at a baseline time *t₀*, publicly commit to a "major life mission" (operationalized via a fixed ambition threshold: e.g., found-an-org / publish-a-body-of-work / effect-a-named-social-change — registered taxonomy, not chosen post hoc).
- **Exposure (measured at t₀, prospectively).** Strong spiritual-like calling conviction, via a pre-specified scale (e.g., established "sense of calling"/vocation items + a conviction-intensity item), dichotomized at a pre-registered cut. **Critical: exposure is recorded before outcomes are known, to block attribution bias.**
- **Outcome (measured at t₀+Δ).** Mission realized vs not, on pre-registered, mission-type-specific success criteria.
- **Matching / adjustment.** Competence & grit proxies (track record, conscientiousness, self-efficacy, resources, domain) — **MEP must survive adjustment for these** (else it collapses into known constructs; MEP-F3).
- **Estimand.** Competence-matched success-rate difference (pp) and adjusted odds ratio, exposure→outcome.
- **The two designs and why only one is valid:**
  - ❌ **Retrospective self-report** (ask successful vs unsuccessful people whether they "felt called"): *confounded by reverse causation* — success rewrites the narrative. The simulation in §3 shows this can fabricate the entire effect.
  - ✅ **Prospective matched cohort**: exposure fixed at t₀; this is the only design that can test MEP.

---

## 3. Simulation — can the naive comparison manufacture the effect? (the #69 result)

`analyses/mep_calling_success_2026_05_28/mep_calling_success_sim.py` (seeded, numpy-only, N=400,000, base success-rate ≈6.9%, calling prevalence 15%, INDETERMINATE band ε=±2 pp). Felt calling is assigned **independently of competence** (the conservative assumption — calling is not a hidden ability proxy).

| Scenario (TRUE calling effect = **0**) | Measured lift | Verdict |
|---|---|---|
| (a) **Felt** calling, **prospective** (no bias) | **−0.09 pp** | within ±2 pp band — correctly ~0 |
| (b) **Reported** calling, **retrospective** (P(report\|success)=0.60, P(report\|fail)=0.10) | **+36.17 pp** (41.0% vs 4.9%) | **SPURIOUS — pure artifact** |
| (c) (b) **+ survivorship** (notable-only = all successes + 5% of failures) | **+42.65 pp** | **SPURIOUS — pure artifact** |
| (d) **FIX:** competence-matched **prospective** estimator | **−0.06 pp** | within band — correctly ~0 |

| Scenario (TRUE effect present, g_logit=0.70) | Measured lift |
|---|---|
| Felt-calling prospective lift | **+6.90 pp** |
| Competence-matched prospective lift | **+6.91 pp** — **recovers the real effect** |

**Headline.** With a true causal effect of **zero**, the *literal* form of Brandon's question (compare success among those who *say* they were called vs those who don't) returns **+36 pp**, rising to **+43 pp** under survivorship. The mechanism is entirely **reverse causation** (winners retro-narrate a calling) plus **survivorship** (we only hear about the notable). The matched prospective estimator returns ~0 under the null and **+6.9 pp** under a genuine effect — it is the design that distinguishes signal from artifact.

**Existence proof, not an effect-size estimate (#69).** The +36 pp / +43 pp figures are **illustrative of the phenomenon, not a universal quantity** — their magnitude depends on the assumed attribution and survivorship parameters. A sensitivity sweep (5 seeds × 4 attribution settings, true effect still 0) confirms the *qualitative* claim is robust: the spurious retrospective lift stays large and positive across **every** seed and setting (range **+10.6 to +58.5 pp, mean +33.9 pp**; smallest case is the weakest-bias setting P(report|success)=0.40 / P(report|fail)=0.20). The claim being defended is therefore "the naive design *can* manufacture a large lift from nothing," which is all that is needed to disqualify it — not that the lift is always exactly +36 pp.

**What this does and does not show.** It does **not** show MEP is false — it shows the *naive evidence cannot bear on MEP either way*. A real-world finding that "the called succeed more" is, by itself, **fully consistent with zero true effect**. This is the corpus's standing anti-cheat in action: the obvious confirmation is the artifact.

---

## 4. Falsifiers (OPEN)

- **MEP-F1 (no prospective lift).** In a prospective, competence-matched cohort, the calling-conviction group shows **no** higher mission-success than matched controls (adjusted lift ≤ ε). REFUTES MEP.
- **MEP-F2 (fully bias-explained).** Any apparent lift in available (retrospective) evidence vanishes once reverse-causation and survivorship are controlled — i.e., the effect is the §3 artifact. REFUTES the empirical MEP (leaves CCA-1's structural claim untouched).
- **MEP-F3 (not calling-specific / construct-redundant).** Any surviving lift is **fully mediated** by generic grit / conscientiousness / self-efficacy, with conviction adding nothing incremental. REFUTES MEP's "not reducible to known constructs" clause.
- **MEP-F4 (valence-dependence — risky prediction).** If the lift appears **only** for prosocial/light missions and is **absent for dark high-HEM GM Nodes**, then "calling conviction" is not a valence-neutral success amplifier as claimed; MEP's GM-Node-generality fails (scope must retreat to light missions). REFUTES the general MEP.
- **MEP-F5 (Molinism-structure, internal).** If a defensible operational MEP requires the conviction to be *causal-only* (pure psychology) with no coherent counterfactual-placement reading, the "Molinism" label is decorative and should be dropped (downgrade to a plain calling→persistence claim). Internal-consistency falsifier in the B51/CCA-1 family.

Per the B49 discipline: **MEP-F1–F4 are empirically decidable in principle but require prospective data that does not currently exist**; they are therefore honestly flagged as *designed-but-unrun*, not as passed. MEP-F5 is decidable now by analysis.

---

## 5. CCC-changeability annotation (Brandon, this batch) — relation to DSR-1

Brandon clarifies the **GM-Network / DSR-1 developmental-theology** picture:
- CCC's GILE **can be outweighed** by other i-cells in principle, but it is **extremely unlikely** any i-cell outweighs the original CCC in **overall GILE-HEM — HEM particularly** — *except perhaps a near-universally-recognized figure* (Jesus, the Buddha named as the calibre required).
- Nonetheless a **voluntary change in who is CCC — the ultimate being — CAN occur.** CCC-identity is in-principle transferable, not metaphysically frozen.

This is consistent with and **sharpens DSR-1** (theology-as-developmental; "measured-ρ is the current CCC standard *until now*") and with **TOF-1 R1** (CCC as finite/elevable maximal-derivative rather than an absolute floor). It is logged as an **annotation/stance**, **not** minted as a new principle (anti-inflation, per the B51 HAI-1-corollary precedent). It also tightens **DSR-1-F1 (the identity problem)**: if CCC-identity is voluntarily transferable and HEM-dominated, the operational criterion for "is this attractor CCC?" must be defined over **HEM-weighted GILE**, with the bar set near universally-recognized exemplars — a concrete (if very high) anchor for the otherwise-unsolved A2 criterion.

---

## 6. Honest literature calibration (#69)

The psychological building blocks MEP leans on are real and well-studied — **sense of calling / vocation**, **grit**, **self-efficacy**, **internal locus of control** — and each has documented associations with persistence and achievement. **What the corpus does NOT have, and this batch does not fabricate, is a prospective, competence-matched, calling-vs-control study of *major-mission* success.** Direct evidence on Brandon's exact contrast is scarce precisely because the easy (retrospective) version is the one §3 shows to be uninterpretable. The uniqueness-honest position: the *constructs* are not novel; MEP's distinctive, riskier contribution is (a) the **valence-neutral GM-Node generality** (dark high-HEM nodes included), (b) the **incremental-over-known-constructs** clause, and (c) the **Molinist placement-tracking** reading — all three are what F3/F4/F5 are built to break.

---

## 7. Status & deltas

- **MEP: candidate hypothesis — NOT ratified** (pace-discipline #69; empirical falsifiers designed-but-unrun). Canonical TI Sigma principle count **unchanged at 79**.
- Candidate backlog: **DSR-1, MEP**.
- CCC-changeability: **annotation to DSR-1 / GM-Network**, not a new principle.
- New vocabulary: **MEP**; **calling-conviction artifact (reverse-causation + survivorship)** flagged as a standing confound class.
- Files: this paper + `analyses/mep_calling_success_2026_05_28/` (`mep_calling_success_sim.py`, `mep_results.json`).
- Counters: Pass-77 papers 78→79; meta-collapses 43 (unchanged); refinement counters (CGP-1 2 / MR 15 / PT 1) unchanged.
- $0 spent.

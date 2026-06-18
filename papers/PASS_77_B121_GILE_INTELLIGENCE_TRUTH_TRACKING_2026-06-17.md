# Pass-77 B121 — GILE-Intelligence Truth-Tracking (GIT-1): the "redeeming factor" that lifts credentials into truth, and why it must be measured prospectively to stay falsifiable

**Date:** 2026-06-17 · **Batch:** Pass-77 B121 · **Status:** introduces **GIT-1 (CANDIDATE, NOT ratified)** + refines CRD-1b · **Canonical principle count: UNCHANGED 79** (candidate; refinements/candidates do not increment).

**Anchor for:** Brandon's challenge that the B120 CRD-1b "truth prior = WEAK" verdict was built on the *wrong construct of intelligence*. Package: `analyses/pass77_b121_gile_intelligence_truth/`.

---

## 0. The challenge (Brandon, verbatim intent)

> *"The proper definition of intelligence as defined by GILE: Rationality, Creativity, Altruism (Loving orientation), and Environmental integration. BY DEFINITION, a truly GILE-intelligent person with the credentials and OVERALL experience in contemplating a position (in writing AND dialogue) could **not** only weakly predict truth. GILE intelligence **IS** 'strong orientation toward truth.' GILE intelligence is the **one redeeming factor that LIFTS the other three factors** — regardless of controversy, there MUST be a high likelihood of truth given sufficient time contemplating the problem and the competence to solve it. 'True quacks' are lacking in one or more GILE components even though their cognition may be complex and sufficient at mere problem-solving."*

This is **two claims welded together**. One is a correct, important repair of B120. The other is a definitional move that, taken literally, breaks falsifiability. This paper accepts the first, disarms the second, and runs the test.

---

## 1. What B120 actually measured (and where it was wrong)

The B120 CRD-1 sim assigned the maker of a heterodox claim four traits — *volume, controversy, credentials,* and **intelligence** — and found the truth-prior **WEAK**. But the "intelligence" trait there was **generic problem-solving g / IQ**. Brandon is right that this is the wrong construct:

* **Nobel disease** (Pauling on vitamin C, Montagnier on water memory, Josephson on psi) is the empirical proof that **raw *g* does not immunize** against being confidently wrong. High IQ, catastrophically wrong.
* So CRD-1b's "WEAK" is **honest for `{volume, controversy, credentials, raw-g}`** — but it never tested **GILE-intelligence**, which is a *different and richer* construct.

**Mapping note (stated, not smuggled).** Canonical **GILE = Goodness, Intuition, Love, Elegance** (E formerly "Environment," kept as a gloss = "context of an agent's most-sacred values"). Brandon's intelligence-specialized reading uses four working faces:

| Brandon's face | GILE pillar it loads on | operational proxy in the literature |
|---|---|---|
| **Rationality** | Intuition (convergent) + Goodness (intellectual honesty) | actively open-minded thinking; rationality-disposition (Stanovich) |
| **Creativity** | Intuition (divergent) | hypothesis generation / fluency |
| **Altruism (loving orientation)** | **Love (L)** | epistemic good-faith / "scout mindset" (Galef) |
| **Environmental integration** | **Elegance/Environment (E)** gloss | openness, updating, dialogue (Tetlock's "fox") |

This slightly **re-reads the G and I pillars** as epistemic-good-faith + rational/creative insight; the L and E mappings are clean. The mapping itself is offered for Brandon's ratification.

---

## 2. The literature is on Brandon's side — the active ingredient is *not* g

A targeted survey confirms the truth-tracking signal lives in exactly the GILE faces, not in *g*:

* **Stanovich — rationality ≠ intelligence ("dysrationalia").** IQ barely predicts resistance to **myside / motivated reasoning**; *rationality dispositions* (actively open-minded thinking) do. → the **Rationality** face genuinely tracks truth and is **separable from g**. This *is* the quack mechanism: high g, low rationality-disposition.
* **Tetlock — foxes > hedgehogs** (*Expert Political Judgment*). Forecasters who **integrate many views and update** (foxes) are better calibrated than high-conviction single-big-idea hedgehogs. → the **Environmental-integration** face tracks truth. (Note: B120 used Tetlock to show high conviction is *worse*; the complement — *integration is better* — is the same finding read forward.)
* **Galef — scout vs soldier mindset.** Truth-seeking *motivation* (good-faith, ego-out-of-the-way) predicts accuracy. → the **Altruism/good-faith** face.
* **Grossmann — wise reasoning** (intellectual humility, recognizing the limits of one's knowledge, integrating perspectives) predicts better judgment and forecasting. → Environmental-integration + Goodness-humility.

So the rationality-science literature **vindicates Brandon's decomposition**: what protects against being a confident-but-wrong "quack" is precisely rationality-disposition + openness/integration + epistemic good-faith — **the GILE faces — not raw cognitive horsepower.**

---

## 3. The trap that must be disarmed (#69)

Brandon's stronger phrasing — *"GILE-intelligence **IS**, by definition, strong orientation toward truth"* — cannot be accepted **as a definition**:

* If truth-orientation is **inside the definition**, then "GILE-intelligence predicts truth" is **circular** — true by stipulation, empirically empty.
* Worse, it becomes **unfalsifiable via No-True-Scotsman**: every quack who turned out wrong is retroactively relabelled *"not **truly** GILE-intelligent."* That move can absorb any counterexample, which is exactly the disease #69 exists to prevent.

**The fix (the whole methodological point of GIT-1):** convert the claim into its **prospective, outcome-blind, pre-registered** form. Score the four GILE faces **without knowing whether the person turned out right**, *then* test whether the composite predicts vindication. That version is testable — and it is the version simulated here.

**And the ceiling is capped by the corpus's own principles.** **RTI-1** (irreducible law-errancy / residual tralseness) and **TRG-1** (reality is *tralse*, not *true*) entail that even maximally GILE-aligned cognition only **leans** toward truth — a strong lean, **never certainty**. So Brandon's *"high likelihood / redeeming lift"* is accepted; his *"MUST / certainty"* is bounded. His framework disciplines his own prediction.

---

## 4. The simulation (`gile_intelligence_sim.py`, seed 20260617, N=400k)

Deterministic, numpy-only, **no primary data** ($0). It is a **structure model**: it *builds in* a partial GILE→truth correlation and then checks what follows. **It cannot prove GILE predicts truth in the real world** — it shows (a) internal coherence + the quack-paradox resolution, (b) the multiplier is identifiable, (c) the gap between the falsifiable and the unfalsifiable definitions. All coefficients are disclosed in `meta`. (Same discipline as the MEP #69 calling-success bias-sim.)

### 4.1 Q1 — generic *g* is a WEAK truth predictor (reproduces CRD-1b)
| | value |
|---|---|
| AUC(generic g) | **0.699** |
| P(vindicated \| top-quartile g) | **0.158** (base 0.080) |

A modest lift only — and that modest lift exists *only because g is built to correlate r≈0.30 with rationality/creativity*. Raw cognition barely moves the truth-prior. **CRD-1b stands for raw-g.**

### 4.2 Q2 — prospective GILE-intelligence is a STRONG predictor
| | value |
|---|---|
| AUC(GILE, prospective outcome-blind) | **0.862** |
| P(vindicated \| top-quartile GILE) | **0.246** (lift ×3.1 over base) |
| P(vindicated \| top-decile GILE) | **0.376** |
| max realized P(vindicated), any agent | **0.850** (RTI-1 cap; never 1.0) |

The truth-prior moves from **WEAK → MODERATE** at the broad top quartile, and toward **STRONG** at the extreme (top-decile 0.376; the genuinely rare high-GILE × high-resource agent reaches 0.310 at the stratum level and individuals approach the 0.85 ceiling). This is the honest, calibrated form of Brandon's prediction: **not "always right," but a large, real lift that the raw-g profile never produces** — capped below certainty by RTI-1.

### 4.3 Q3a — the quack paradox, resolved
Among **high-g** people, comparing those who turned out **wrong (quacks)** vs **right (sages)** on each *prospective, outcome-blind* GILE face:

| GILE face | quack (z) | sage (z) | gap |
|---|---|---|---|
| Rationality | +0.246 | +1.094 | **+0.848** |
| Creativity | +0.315 | +0.720 | +0.405 |
| Altruism / good-faith | −0.067 | +0.387 | +0.454 |
| **Environmental integration** | **−0.140** | **+0.731** | **+0.872** |
| **GILE composite** | **+0.120** | **+1.294** | **+1.174** |

**Exactly Brandon's prediction.** Same high raw cognition; the quacks are **deficient on ≥1 GILE face — most sharply Environmental-integration (they don't update / engage dialogue) and Rationality (motivated reasoning).** The composite gap is **+1.17 SD**. "Complex cognition sufficient at mere problem-solving" coexists with low GILE — that *is* the quack.

### 4.4 Q3b — the multiplier ("the redeeming factor that lifts the others")
Effect of high vs low **credentials + contemplation-time**, stratified by GILE tercile:

| stratum | resource effect (hi − lo) | P(vindicated): hi / lo |
|---|---|---|
| low GILE | **−0.001** | 0.004 / 0.005 |
| mid GILE | +0.032 | 0.047 / 0.015 |
| **high GILE** | **+0.237** | **0.310 / 0.073** |

**Credentials + time convert into truth almost only when GILE is high.** At low GILE, more credentials and more contemplation buy **nothing** (≈0) — the over-credentialed, prolific, deeply-contemplative crank. At high GILE the same resources add **+0.24**. This is precisely Brandon's "one redeeming factor that **lifts** the other three." It is an **interaction**, and it is identifiable.

### 4.5 Q4 — the circularity trap, quantified
| GILE definition | AUC | status |
|---|---|---|
| prospective, outcome-blind (GIT-1) | **0.862** | **FALSIFIABLE** — strong but bounded |
| circular ("by definition = truth-orientation," peeks at outcome) | **1.000** | **UNFALSIFIABLE — not evidence** |

The "by-definition" version predicts **perfectly by construction** and is worthless as evidence (it has merely renamed the outcome). GIT-1 uses **only** the prospective score.

> ⚠️ **ERRATA / RELABEL (B122, 2026-06-18).** The framing of this Q4 as a *"circularity trap"* and the line "a tautology vs a theory" **over-reached and is withdrawn.** What this AUC=1.000 result actually demonstrates is **measurement contamination** (scoring the predictor from the outcome — halo/survivorship/hindsight), **not** that GILE's *definition* is circular. The proof: applying the *identical* outcome-peeking to **generic g** inflates *its* AUC to **0.991** too (B122 D2) — so the artifact is a **universal property of contaminated measurement**, construct-agnostic, not a defect of GILE. Brandon's GILE→truth claim is **substantive**, structurally identical to "g predicts income" / "creativity predicts patents." The correct label is the **hindsight-contamination trap**; the only standing requirement is to score GILE **outcome-blind** (the same standard g-research meets). See `papers/PASS_77_B122_GIT_1_SUBSTANTIVE_NOT_CIRCULAR_2026-06-18.md`.

---

## 5. GIT-1 stated (CANDIDATE, NOT ratified)

> ⚠️ **Read first:** GIT-1 is a **hypothesis**, and every quantitative effect size quoted below and in §4 is **simulation-conditional, not an empirical estimate.** The numbers characterize a structure model whose GILE→truth correlation is built in; they are NOT real-world measurements. GIT-1 advances to ratification only after GIT-1-F1/F2 are met on real data.

> **GIT-1 — GILE-Intelligence Truth-Tracking (CANDIDATE, NOT ratified; Pass-77 B121).**
> When "intelligence" is operationalized as the **GILE tetrad faces** — Rationality (actively open-minded thinking), Creativity (generativity), Altruism (epistemic good-faith / loving orientation, GILE-L), Environmental-integration (openness, updating, dialogue; GILE-E/Environment gloss) — and is measured **prospectively and outcome-blind**, it predicts eventual truth **far more strongly than generic problem-solving g**, lifting the truth-prior from **WEAK toward MODERATE-to-STRONG**.
> * **Multiplier clause ("redeeming factor"):** GILE-intelligence acts as a *multiplier* on credentials + contemplation-time. Without it those resources do **not** convert into truth (the over-credentialed crank); with it they do. The lift is an **interaction**, not an additive bonus.
> * **Quack clause:** a "true quack" has complex cognition / high raw *g* but is **deficient on ≥1 GILE face** (typically Environmental-integration or Rationality). High *g* + low GILE = confident error (Nobel disease).
> * **Anti-contamination clause (the load-bearing one; corrected B122):** GILE-intelligence must be scored **independently of the truth outcome**. ⚠️ *Note (B122): this is an **anti-contamination** requirement, NOT a claim that the trait→truth definition is "circular." GIT-1 is substantive — same form as "g predicts income." The illegitimate move is letting the outcome leak into the score (which inflates **any** predictor, g included). No-True-Scotsman (retroactively relabelling failures) stays barred. See `papers/PASS_77_B122_GIT_1_SUBSTANTIVE_NOT_CIRCULAR_2026-06-18.md`.*
> * **Ceiling clause (RTI-1/TRG-1):** even perfect GILE-intelligence only **leans** toward truth; residual tralseness forbids certainty. "High likelihood," never "must."

**Relation to CRD-1 (refines CRD-1b).** CRD-1b's "truth prior = WEAK" **stands for `{volume, controversy, credentials, raw-g}`**. GIT-1 carves out **GILE-intelligence** as the *one* trait-cluster that genuinely lifts the truth-prior — reconciling CRD-1b's honesty with Brandon's correct intuition. CRD-1a (hearing prior = MODERATE) is untouched. The Lakatos validation-phase bound (UGI-1) still applies: a strong prior is not a proof.

---

## 6. Falsifiers (pre-registered, OPEN)

* **GIT-1-F1 (the real test):** if **prospectively-scored, outcome-blind** GILE-intelligence does **not** predict vindication better than generic *g* in a real labeled cohort of heterodox claims, GIT-1 fails.
* **GIT-1-F2 (anti-contamination; relabelled B122):** if the GILE→truth signal **survives only** when scoring is allowed to peek at the outcome (i.e., outcome-blind scoring kills it), the effect was **measurement contamination**, not construct, and GIT-1 fails. *(B122: this is the contamination test, not a "circularity" test — see `papers/PASS_77_B122_GIT_1_SUBSTANTIVE_NOT_CIRCULAR_2026-06-18.md`.)*
* **GIT-1-F3 (multiplier):** if credentials/contemplation lift truth **equally** at low and high GILE (no interaction), the "redeeming factor that lifts the others" claim fails.
* **GIT-1-F4 (quack decomposition):** if true quacks do **not** score lower on ≥1 prospective GILE face than vindicated mavericks **matched on g**, the quack-paradox resolution fails.
* **GIT-1-F5 (ceiling):** if any defensible cohort shows a GILE-intelligence stratum with vindication ≈ certainty (≈1.0), the RTI-1 ceiling clause fails (and TRG-1 takes a hit).

---

## 7. Honest limitations

1. **No primary data.** The sim *builds in* the GILE→truth correlation; it demonstrates **structure, identifiability, and the circularity gap**, not a measured real-world effect. GIT-1-F1 is the obligation.
2. **Mapping is provisional.** Reading G/I as epistemic-good-faith + rational/creative insight extends the canon; awaiting Brandon's ratification.
3. **Construct measurement is the hard part.** The entire weight of GIT-1 rests on whether the four faces *can* be scored reliably and outcome-blind. If they can't, GIT-1 is untestable in practice (distinct from false).
4. **Survivorship re-entry risk.** Calling the historical greats "GILE-intelligent" *because* they were right re-imports the B120 illusion. Only prospective scoring avoids it — which is why F2 is load-bearing.

---

## 8. One-paragraph plain-language summary

Brandon's point lands: the earlier write-up tested the wrong kind of "smart." Raw IQ/problem-solving power does **not** make a heterodox thinker likely to be right — history is full of brilliant people who were confidently wrong (Pauling, cold fusion, water memory). But **GILE-intelligence** is a different thing: being **rational** (open to changing your mind), **creative**, **loving / good-faith** (truth over ego), and **integrated with your environment** (you listen, update, argue it out). The research on rationality backs this — what protects you from being a confident crank is open-minded updating, not horsepower. The simulation shows that if you grade those four qualities **before** you know who turned out right, they predict truth **much** better than raw smarts, they **resolve the quack puzzle** (quacks are smart people missing one of the four — usually they won't update), and they act as a **multiplier**: credentials and years of thinking only turn into truth when the four qualities are present. **Two honest catches**, both required to keep it real: (1) you can't *define* GILE-intelligence as "being right" and then claim it predicts being right — that's circular and unfalsifiable (the simulation shows that cheat scores a fake 100%); you have to grade it blind. And (2) even perfect GILE-intelligence is a *strong lean*, never a guarantee — the corpus's own RTI-1/TRG-1 say reality is tralse, not certain. So: yes, GILE-intelligence is the redeeming factor that lifts the others toward truth — measured honestly, and short of certainty.

---

*Anchor paper. Package: `analyses/pass77_b121_gile_intelligence_truth/` (`gile_intelligence_sim.py`, `make_figs.py`, `gile_intelligence_results.json`, `fig1_g_weak_gile_strong.png`, `fig2_quack_paradox_and_multiplier.png`).*

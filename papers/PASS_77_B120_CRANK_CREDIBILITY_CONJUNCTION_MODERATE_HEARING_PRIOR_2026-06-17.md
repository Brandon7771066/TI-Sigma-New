# Pass-77 B120 — Crank Credibility as a Conjunction: a MODERATE *hearing* prior, a WEAK *truth* prior (CRD-1 refinement)

**Date:** 2026-06-17
**Batch:** Pass-77 B120
**Status:** Refinement of CRD-1 (CANDIDATE, NOT ratified). Canonical principle count **UNCHANGED 79** (refinement of an unratified candidate; no ratification, no new principle).
**Anchor for prior version:** `papers/PASS_77_B119_TRALSE_THEOLOGY_DARK_TRIAD_INDETERMINACY_WORSHIP_HEM_AND_ASYMMETRIC_EPISTEMICS_2026-06-17.md` (CRD-1 originally stated there as "WEAK Bayesian evidence").
**Analysis package:** `analyses/pass77_b120_crank_credibility/` (`crank_credibility_sim.py`, `crank_credibility_results.json`, `fig1_truth_weak_hearing_moderate.png`, `fig2_survivorship_illusion.png`).

---

## 0. The prompt (Brandon, 2026-06-17)

> "Publishing **large volumes** of work in a **highly controversial** subject while demonstrating **high intelligence** and/or **credentials** is *not mild* evidence that the person should be listened to. The weight of all **4 variables together** is **MODERATE** evidence in their favor that they should **at least be listened to**. The evidence should back this up if it is true — test it against history and survey what already exists."

This is a direct challenge to CRD-1 as written in B119, which graded the same signal as "**WEAK** Bayesian evidence of a defensible position." Per #69 (brutal honesty; over-skepticism is as much a discipline failure as uncritical acceptance), the challenge is taken seriously and tested, not waved away.

The result is a **split**, and Brandon is **partly right**: his claim is correct for the question he actually asked ("at least be listened to") and the original CRD-1 wording was right for a *different* question ("is the position true"). Conflating the two was the error on both sides.

---

## 1. The two questions the four traits get asked (and why they have different answers)

The single biggest clarification is that "should be listened to" and "is probably right" are **not the same question** and do not get the same answer from the same evidence.

| | **Q-TRUTH** | **Q-HEAR** |
|---|---|---|
| Question | Is the heterodox claim *correct*? | Should the person *at least get a hearing*? |
| Quantity | P(vindicated \| 4-trait profile) | decision: is a hearing the +EV action? |
| Driven by | likelihood ratio of the traits | LR **×** asymmetric payoff (missed Wegener ≫ cheap hearing) |
| Verdict | **WEAK→moderate** | **MODERATE & justified** |

CRD-1 splits accordingly:

* **CRD-1a (hearing / generation-phase prior) — strengthened to MODERATE.** The conjunction of the four traits, combined with the **asymmetric payoff** of inquiry, makes "grant this person a hearing" a positively-justified decision, not a grudging mild concession. This is the reading Brandon defends, and it survives.
* **CRD-1b (truth / validation-phase prior) — stays WEAK.** The same four traits lift the probability the *claim is actually true* only modestly; it remains a minority probability. Credentials + controversy + volume + intelligence do **not** make a heterodox position likely-correct.

Both halves remain **bounded by UGI-1**: a hearing is the generation/airing phase; it never substitutes for the validation phase. (See §5 anti-cheats.)

---

## 2. Survey of existing work (what is already known)

A literature survey (8 search threads) confirms there is a large, mature body of relevant scholarship. CRD-1 is **not** novel territory; the contribution here is the explicit *hearing-vs-truth* decomposition and the conjunction quantification.

**Evidence that skepticism toward heterodoxy is real and costly (supports CRD-1a):**
* **Azoulay, Fons-Rosen & Graff Zivin (2019), *AER* 109(8):2889–2920, "Does Science Advance One Funeral at a Time?"** — after a superstar's unexpected death, outsider (non-collaborator) publications in the field rise markedly and are disproportionately influential. Incumbent gatekeeping demonstrably suppresses heterodox entry. This is the strongest empirical leg under "the heterodox deserve a hearing they're not getting."
* **Planck's principle** ("science advances one funeral at a time") — the qualitative claim Azoulay et al. partially confirmed.

**Evidence that the four traits do NOT track truth (supports CRD-1b / bounds CRD-1a):**
* **Galileo Gambit** + **Sagan's rebuttal** (*Broca's Brain*, 1979): "They laughed at Galileo… but they also laughed at Bozo the Clown." Being mocked/controversial is *not* evidence of correctness — controversy is the one trait with **zero** discriminating power once you condition on a claim already being heterodox.
* **Nobel disease / Nobelitis** (Wikipedia s.v.; Basterfield et al.): impeccably credentialed, certifiably brilliant laureates (Pauling on vitamin C, Montagnier on water memory, Josephson on psi) endorse pseudoscience. **Credentials + intelligence do not immunize.**
* **Merchants of Doubt** (Oreskes & Conway, 2010): a *handful of credentialed, prolific, contrarian* scientists weaponized exactly this 4-trait profile to defend *wrong and harmful* positions (tobacco, acid rain, ozone, climate). The profile is **present in the wrong column too** — the invisible denominator.
* **Tetlock** (*Expert Political Judgment*, 284 experts / 28k forecasts): high-conviction "hedgehogs" are **less** accurate than low-conviction "foxes." The confident-single-big-idea profile correlates with *worse* calibration, not better.

**The demarcation discriminator that actually works (the validation phase):**
* **Lakatos** (progressive vs. degenerating research programmes) and **Laudan**: the real separator between a Wegener and a crank is **whether the programme generates novel, risky, confirmed predictions over time** — not credentials, volume, intelligence, or controversy. This is the operational content of UGI-1's validation phase.

**The honest gap (#69):**
* **No clean quantitative base rate exists.** No peer-reviewed study has sampled a defined population of heterodox claims and computed a vindication percentage. Any "X% of mavericks were right" figure is survivorship-contaminated. This is *why* the empirical leg here is an explicit confound/decision simulation rather than a fabricated statistic.

---

## 3. The quantification (`crank_credibility_sim.py`)

A deterministic, numpy-only Bayesian + decision model. **No primary data** ($0 budget); following the #69 discipline of the MEP calling-success bias-sim, it quantifies *confounds and decisions*, not a fake effect size. N = 400,000 simulated heterodox-claim-makers; base rate of eventual vindication π = 0.08; four z-scored traits with honestly-chosen class-conditional means:

* **credential-in-domain**: modest positive signal (Δμ = 0.45)
* **intelligence**: modest positive signal (Δμ = 0.45)
* **volume**: ~null, *slightly negative* (Δμ = −0.08 toward the wrong column — cranks are prolific too; Lotka/graphomania)
* **controversy**: **zero** signal (we already conditioned on the claim being heterodox)

### 3.1 Q-TRUTH — weak, and honest about *which* traits carry it

| evidence used | P(vindicated) |
|---|---|
| base rate (any heterodox claim) | 0.080 |
| **volume alone** | **0.074** ← *below* base rate |
| **controversy alone** | **0.080** ← *equal to* base rate (no information) |
| credential alone | 0.120 |
| intelligence alone | 0.120 |
| **all 4 together (event-level P(vindicated \| profile rule))** | **0.154** |

The conjunction (**0.154**, the event-level posterior for the all-4 profile rule) beats every singleton — it is genuinely **super-additive** — but the lift is carried entirely by **2 of the 4 traits** (credential + intelligence). Volume and controversy contribute nothing (or slightly less than nothing). And 0.154 is still a **minority** probability: the profile roughly *doubles* the odds of being right but leaves the claim **more likely wrong than right**. → **CRD-1b stays WEAK** (charitably "weak→moderate"). True likelihood ratio of the full profile ≈ **2.09×**.

*(Two posterior summaries appear in `crank_credibility_results.json` and must not be confused: the **event-level** posterior for the profile rule = **0.154** — the decision-relevant headline used throughout — and the **within-profile mean of per-sample posteriors** = 0.162, a coarser summary that slightly over-weights individuals deep inside the profile region. The argument uses 0.154.)*

### 3.2 Q-HEAR — moderate, and *justified* (the part Brandon is right about)

Decision rule: grant a hearing iff `P(vindicated) > c_hearing / V_true_idea` (listen when the expected value of catching a true heterodox idea exceeds the cheap cost of a hearing).

| value : cost of a missed true idea vs a hearing | threshold | bare base rate clears? | **4-trait profile clears?** |
|---|---|---|---|
| 10 : 1 | 0.100 | ✗ (0.080) | **✓ (0.154)** |
| 50 : 1 | 0.020 | ✓ | **✓** |
| 200 : 1 | 0.005 | ✓ | **✓** |

At a modest 10:1 asymmetry the **base rate alone fails but the 4-trait profile clears the bar** — this is exactly where the conjunction earns its keep. At realistic higher asymmetries even a bare heterodox claim deserves a hearing, and the profile clears comfortably. → **CRD-1a = MODERATE & justified.** Brandon's "at least be listened to" is the defensible reading; the strength comes mostly from the **asymmetric payoff**, *amplified* by the conjunction.

### 3.3 Q-BIAS — why the intuition feels stronger than the truth (survivorship)

The reason "brilliant prolific credentialed mavericks are usually right" *feels* obvious is an **inverse-probability error sharpened by survivorship**. The illusion is **derived** from an explicit, **disclosed** fame-selection model (not a hardcoded number): a vindicated thinker is remembered as a *celebrated legend* with probability rising in their profile strength (`remember_logit = −1.0 + 1.3·z(profile strength)`), so the famous-maverick set is selection-biased toward competence.

**Honest finding (the model corrected an earlier overclaim):** the illusion does **not** inflate the rare full **4-way conjunction** — that conjunction stays rare even among legends (selecting on it gives inflation < 1×). The survivorship illusion operates on the **competence sub-signal** (credentials + intelligence), which is exactly what the "they were *all* brilliant" intuition actually tracks:

* Among celebrated vindicated mavericks, the fraction that are impressive (`P(impressive | celebrated)`) = **0.383** — the number the hero-surveyor *sees*.
* But the decision-relevant truth is the **event-level** `P(vindicated | impressive)` = **0.175** — far lower.
* The **invisible denominator** — equally brilliant, credentialed heterodox thinkers who were simply **wrong** (Pauling on vitamin C, Pons & Fleischmann, Blondlot's N-rays, Montagnier, Josephson, the Merchants-of-Doubt cohort) — never makes the highlight reel.

Derived inflation factor ≈ **2.2×** (0.383 perceived / 0.175 true), under the disclosed fame-selection strength (magnitude scales with that strength). This mirrors the corpus MEP #69 bias-sim, where a retrospective, denominator-free design manufactured an inflated apparent effect. (See `fig2_survivorship_illusion.png`.)

### 3.4 Historical case table — both columns have all four traits

| Vindicated **with** all 4 traits | Permanently-wrong **with** all 4 traits |
|---|---|
| Wegener (continental drift) | Pauling (vitamin-C megadosing) |
| Marshall & Warren (*H. pylori*) | Pons & Fleischmann (cold fusion) |
| Boltzmann (statistical mechanics) | Blondlot (N-rays) |
| Semmelweis (handwashing) | Montagnier (water memory) |
| McClintock (transposons) | Josephson (psi / quantum mysticism) |
| Prusiner (prions) | Merchants-of-Doubt cohort (tobacco/climate) |
| Chandrasekhar (stellar collapse) | (many more, mostly forgotten) |

**The table is the whole argument in one image:** credentials + intelligence + volume + controversy populate *both* columns. The four traits justify a **hearing**; only the **Lakatosian validation phase** (novel, risky, confirmed predictions) sorts the left column from the right.

---

## 4. Restatement of CRD-1 (refined)

> **CRD-1 — Crank Defensibility / Reputational-Stake & Conjunction Asymmetry (CANDIDATE, NOT ratified; refined Pass-77 B120).**
> The conjunction of {sustained costly reputational stake, in-domain credentials, demonstrated high intelligence, large heterodox output} splits into two priors that must never be conflated:
> * **CRD-1a (hearing prior) = MODERATE & justified.** Combined with the asymmetric payoff of inquiry (a missed true heterodox idea ≫ the cheap cost of a hearing), the conjunction makes *granting a hearing* a positively-justified decision. Super-additive over any single trait. This is the defensible reading of "should at least be listened to."
> * **CRD-1b (truth prior) = WEAK.** The same conjunction lifts P(claim is actually true) only modestly (≈ doubling of low base-rate odds; remains a minority probability). Controversy carries **zero** truth-signal (Galileo-Gambit/Bozo); volume carries **none-to-negative**; only credentials + intelligence carry the modest lift.
> **Bound (UGI-1):** CRD-1a raises the *generation/airing-phase* hearing-prior; it **never** substitutes for the validation phase (Lakatos: progressive novel-prediction record). **Anti-cheat:** the hearing decision is sensitive to hearing-cost — when a platform is itself harmful (Merchants-of-Doubt regime, high c_hearing), the +EV calculation flips and CRD-1a does **not** license amplification.

---

## 5. Anti-cheats & #69 caveats

1. **No fabricated base rate.** The "no clean vindication statistic exists" finding is reported as a limitation, not papered over. The sim quantifies *structure and decisions*, not a measured effect size.
2. **Hearing ≠ validation (UGI-1 bound).** CRD-1a is explicitly the cheap-airing phase. It cannot be cited to call a position *true* or to skip falsification.
3. **Cost-sensitivity bound (the Merchants-of-Doubt carve-out), operationalized.** CRD-1a's "grant a hearing" verdict is a decision gate `P(vindicated) > c_hearing / V_true_idea`, and `c_hearing` is **not** a constant — it must be set from the *externality class* of the venue and the *domain risk tier* before the gate is applied:
   * **Externality class** — (a) *private/cheap* (read the preprint, take the meeting): `c_hearing ≈ 1`, gate easily cleared → hearing granted. (b) *amplifying* (mass platform, press megaphone, policy table): `c_hearing` scales with audience × actionability. (c) *harm-loaded* (anti-vax, denialism with a megaphone — the Merchants-of-Doubt regime): `c_hearing` can exceed `V_true_idea`, so the threshold rises **above 1.0** and **no** posterior can clear it → hearing *not* granted at that venue (a private hearing may still be).
   * **Domain risk tier** — for public-health / safety-critical domains the cost of an *amplified wrong* hearing carries the externality onto third parties, raising `c_hearing` further; for low-stakes theoretical domains it stays near the cheap floor.
   The principle therefore licenses *cheap, private, generation-phase* hearings broadly, but **never** bad-faith amplification — the gate self-closes exactly where harm dominates.
4. **Controversy is the weakest leg, by design and by data.** Conditioned on heterodoxy, controversy is non-discriminating (Sagan/Bozo). Any future statement of CRD-1 must not let "highly controversial" do persuasive work it cannot bear.
5. **Symmetry with the corpus's own skepticism discipline.** This refinement *raises* a prior; #69 requires the same brutal honesty raising it as lowering it. Hence the explicit WEAK truth-prior and the survivorship demonstration sit beside the strengthened hearing-prior.

---

## 6. New / updated falsifiers (pre-registered, OPEN)

* **CRD-1-F1 (carried, OPEN):** original reputational-stake leg — if costly stake shows *no* association with eventual defensibility in any defined cohort, CRD-1's stake component fails.
* **CRD-1-F2 (carried, OPEN):** if the four traits' conjunction does **not** exceed the best single trait in a real labelled cohort, the "super-additive conjunction" claim fails.
* **CRD-1a-F3 (NEW, OPEN):** if, in a domain with a *defensible* hearing-cost estimate, the 4-trait profile posterior does **not** clear the +EV hearing threshold at any plausible asymmetry, CRD-1a's MODERATE grade fails.
* **CRD-1b-F4 (NEW, OPEN):** if a denominator-complete cohort shows P(vindicated | 4-trait profile) ≥ 0.5, CRD-1b is *too weak* and must be upgraded (Brandon's stronger reading would then hold for truth as well).
* **CRD-1-F5 (NEW, OPEN):** if controversy or volume show a *positive* truth-LR in a denominator-complete cohort, the "weakest legs" claim fails.

---

## 7. Cross-links

* **UGI-1** (`papers/PASS_77_B114_UGI_1_...md`) — the generation-vs-validation two-phase bound that CRD-1 is subordinate to.
* **MEP / #69 bias-sim** (`analyses/mep_calling_success_2026_05_28/`) — the survivorship/retrospective-inflation methodology reused here.
* **B88 amateurism** (`papers/PASS_77_B88_AMATEURISM_...md`) and **B89 heterodox economics** (`papers/PASS_77_B89_HETERODOX_ECONOMICS_...md`) — prior corpus treatments of expertise limits and "endorsement ≠ proof."
* **IPA-1** (B119) — individual↔population inference asymmetry; the survivorship trap here is a special case.

---

## 8. One-paragraph plain-language summary

Brandon said that someone who writes a lot, on a controversial topic, while clearly smart and credentialed, deserves at least to be *listened to* — and that this is moderate, not mild, evidence. He's right about the **listening** part and the original write-up was wrong to call it merely "weak." But "deserves a hearing" and "is probably correct" are two different questions. The four traits, plus the fact that missing a real Wegener is far costlier than a cheap hearing, make **giving them a hearing** a genuinely sensible, moderate-strength decision. They do **not** make the person **likely right** — history is full of brilliant, credentialed, prolific, controversial people who were flatly wrong (Pauling on vitamin C, cold fusion, the tobacco/climate doubt-merchants), and we only remember the brilliant ones who turned out right, which fools our intuition into overrating the *competence* signal by roughly two-fold. So: listen, yes (moderate); believe, not yet (weak) — and the only thing that ever settles which camp someone is in is whether their ideas make new, risky predictions that come true.

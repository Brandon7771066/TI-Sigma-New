# PASS-77 B146 — Survivorship Bias as a (Possibly/Likely) **Pseudo-Fallacy**: Memory-Selection Conditioning (SPF-1)

**Date:** 2026-06-25
**Status:** ONE candidate (**SPF-1**, with sub-results SPF-1a/SPF-1b), **NOT ratified**. Canonical principle count **unchanged at 79** (a candidate mints no principle).
**Type:** Epistemics / statistics — a *demarcation*, not a new metaphysics. Companion to IPA-1 (B119), HAN-1 (B144), SM-1 (B145).
**Author input:** Brandon Emerick — "survivorship bias is not so much a fallacy after all," because memory generally retains your *most seriously-invested* attempts **whether they were right OR wrong**; TI Sigma Statistics says humans are *correct* to count only their serious attempts and not the nulls. **Hinges on the quality of the person's memory.**

---

## 0. One-paragraph statement

The thing usually condemned as **survivorship bias** is selection on the **outcome** (you see only the winners and forget the losers, then generalize). That remains a genuine fallacy and the corpus keeps using it as such (Ch. 4 "vindicated mavericks"; MEP/#69 bias-sim). **But the folk move the author is defending is different in kind.** "I only count the times I *seriously tried*" is selection on a **pre-outcome variable** — confidence / depth of investment — *not* on the outcome. **If** memory is **outcome-symmetric** (it retains the seriously-attempted *failures* about as faithfully as the seriously-attempted *successes*), **then** estimating "what happens when I genuinely commit?" from remembered serious attempts is **statistically unbiased** — it is correct **reference-class conditioning**, and calling it "survivorship bias" is a **misdiagnosis: a pseudo-fallacy.** The whole thing therefore **hinges on memory quality**, exactly as the author said: memory quality = the degree to which retention is outcome-symmetric. That premise is empirically **contested both ways** (real evidence for *and* against), so the honest verdict is the author's own hedge — **possibly/likely a pseudo-fallacy**, regime-dependent, with the memory-symmetry premise as the live falsifier.

---

## 1. The two selection axes (the whole move in one distinction)

A recalled set of attempts can be filtered on either of two variables:

| | Selection variable | When it happens | Effect on "P(success \| I seriously try)" |
|---|---|---|---|
| **Axis A — null-exclusion** | confidence / seriousness | **before** the outcome | **Harmless.** Changes *which question* you answer (population → serious-conditional); the serious-conditional answer is the **correct** one for "what happens when I commit?" |
| **Axis B — outcome-asymmetry** | the outcome itself (win vs loss) | **after** the outcome | **The actual culprit.** Forgetting the serious *failures* more than the serious *wins* inflates the estimate. This is real survivorship. |

The canonical survivorship fallacy (Wald's WWII bombers — armor the planes that came back, forgetting the ones that didn't; **Wald 1943**) is an **Axis-B** error. The author's defended move ("count serious attempts, ignore nulls") is an **Axis-A** operation. **Conflating the two is the pseudo-fallacy**: a critic hears "I'm only counting my serious tries" and reflexively shouts "survivorship!", when the only thing that *would* be survivorship is Axis-B forgetting — which Axis-A does not entail.

This is **exactly the distinction B144 already paid for** in HAN-1's "ignore-nulls-honestly" toy: *"only pragmatic attempts included" = exclude non-attempts/low-confidence noise from the denominator (✓), NOT delete committed misses (✗).* SPF-1 is the **memory-side companion** of that result: B144 assumed you keep the committed misses; SPF-1 asks the empirical question *do you actually remember them?* — and shows that the answer is the only thing that matters.

---

## 2. The candidate

### SPF-1 — Survivorship Pseudo-Fallacy / Memory-Selection Conditioning (CANDIDATE, not ratified)

> **Survivorship bias is a genuine fallacy only when the selection is on the outcome (Axis B). When a person conditions on a *pre-outcome* variable (seriousness/confidence) and their memory of seriously-attempted outcomes is *outcome-symmetric*, the resulting estimate of the serious-conditional success rate is unbiased — so the "survivorship bias" charge is a pseudo-fallacy. The claim is therefore conditional on outcome-symmetric memory ("memory quality"), an empirically contested premise.**

**SPF-1a (null-exclusion ≠ inflation).** Excluding non-serious attempts ("nulls") from the denominator is legitimate **reference-class conditioning**, not a bias. It correctly answers the conditional question and is silent on the population question. The error that masquerades as it is deleting committed **misses** — a *different* operation (Axis B).

**SPF-1b (bias is monotone in outcome-asymmetry α).** Define **α ∈ [0,1]** = the degree to which retention favors wins over losses (**α = 1 − memory quality** for this purpose). Inflation of the recalled serious-success rate is ~0 at α = 0 and rises monotonically with α. The pseudo-fallacy holds in the **α ≈ 0 regime**; genuine survivorship is the **α large** regime. There is a finite crossover α\* — so the claim is a **regime statement, not an absolute** ("not *so much* a fallacy," precisely).

**Status:** "possibly/likely a pseudo-fallacy." The **logic** is established (Section 4). The **empirical premise** (real human memory is outcome-symmetric for seriously-invested attempts) is contested (Section 3) and is the falsifier (Section 5).

---

## 3. Is memory outcome-symmetric? — the crux, taken **both ways** (#69)

The entire candidate rides on whether real memory keeps confident *failures* as well as confident *successes*. The honest position is that the psychology literature genuinely **cuts both ways**; we present the strongest of each.

**FOR symmetry / for the author (failures are *not* preferentially forgotten):**
- **Zeigarnik effect** (Zeigarnik 1927): *interrupted / unfinished / failed* tasks are remembered **better** than completed ones — a direct mechanism by which serious misses stay vivid.
- **Negativity bias in memory** ("bad is stronger than good," Baumeister, Bratslavsky, Finkenauer & Vohs 2001; Rozin & Royzman 2001): negative outcomes are often encoded *more* strongly than positive ones — if anything tilting α *negative* (toward remembering losses), the opposite of survivorship.
- **Flashbulb / emotional-intensity encoding** (Brown & Kulik 1977): high-arousal events — and a seriously-invested attempt is high-arousal — are preferentially retained **regardless of valence**.

**AGAINST symmetry / against the author (wins preferentially retained, or confidence corrupted):**
- **Self-serving attribution bias** (Miller & Ross 1975): successes are claimed as one's own doing and remembered; failures are externalized and minimized — a direct α > 0 mechanism.
- **Rosy retrospection** (Mitchell, Thompson, Peterson & Cronk 1997): past episodes are recalled more positively than experienced.
- **Hindsight bias** (Fischhoff 1975): recalled *prior confidence* is distorted toward what actually happened — this corrupts the very selection variable SPF-1 relies on (see SPF-1-F3).
- **Flashbulb *inaccuracy*** (Neisser & Harsch 1992, the *Challenger* study): vividly-held, high-confidence memories can be substantially **wrong** — high recall-confidence ≠ accurate record.

**Honest net.** There is real evidence that serious failures are *not* simply forgotten (Zeigarnik, negativity bias) **and** real evidence that recall is win-tilted or confidence-corrupted (self-serving bias, hindsight). The net sign of α is **person- and domain-specific and unresolved**. That is precisely why the verdict is the author's hedge — *possibly/likely* a pseudo-fallacy — and why memory quality is the explicit hinge. We do **not** assert real human α ≈ 0; we assert the **conditional**, and name the test that would settle it for any given person/domain (Section 5). (Reference-class subtlety throughout: Hájek 2007, "The reference class problem is your problem too.")

---

## 4. What the simulation establishes (logic, not empirics)

Harness: `analyses/pass77_b146_survivorship_pseudo_fallacy/survivorship_checks.py` (fixed seed; **no numerology, no load-bearing recurring constant**). It is a **method/logic demonstration** — it proves the conditional and quantifies the regime; it makes **no** claim about real human memory. Predictions are pre-registered in the file's docstring. All checks **PASS**:

- **Stipulated world:** population success rate **0.370**; **TRUE P(success | serious) = 0.550** (target); P(success | non-serious) = 0.250 — so the reference classes genuinely differ.
- **SPF-1a:** dropping nulls moves the estimate from the population 0.370 to the serious-conditional **0.550** (gap **+0.180**) — a *change of question*, the correct one; and with α = 0 the remembered-serious estimate recovers the target to **|err| = 0.0003**. Null-exclusion is conditioning, not inflation.
- **SPF-1b (core table):** inflation vs α —

  | α (= 1 − memory quality) | recalled rate | inflation |
  |---|---|---|
  | 0.00 | 0.5498 | **+0.0002** |
  | 0.10 | 0.5988 | +0.049 |
  | 0.20 | 0.6279 | +0.078 |
  | 0.30 | 0.6591 | +0.110 |
  | 0.50 | 0.7294 | +0.180 |
  | 0.70 | 0.8202 | +0.271 |
  | 0.90 | 0.9315 | +0.382 |

  At **α = 0 the survivorship inflation is ~0** (pseudo-fallacy regime); it then climbs monotonically to **+0.38** (genuine survivorship). Finite crossover **α\* ≈ 0.05** (inflation first exceeds 2%) — the claim is a **regime**, not an absolute.
- **SPF-1-F3 anti-cheat (hindsight):** if "serious" is defined by **retrospectively recalled** confidence that is itself inflated for wins (Fischhoff), the estimate inflates by **+0.061 even at α = 0**, because the selection variable has silently become *post*-outcome. ⇒ **The confidence that defines "serious" must be *prospectively logged*, never recalled.**

**What this does and does not show.** It shows the *if-then* is mathematically real and isolates α as the sole driver. It does **not** show real memory has α ≈ 0. That is the empirical frontier.

---

## 5. Falsifiers (all OPEN)

- **SPF-1-F1 (the decisive empirical test).** In a **pre-registered, outcome-blind** prospective study — log confidence/seriousness *before* each attempt, then later measure recall of each outcome — if **win-retention significantly exceeds matched loss-retention** (estimated α > α\*) for a person/domain, then survivorship correction **is** warranted there and the pseudo-fallacy claim **fails** for that case. (This is the same validate-phase falsifier B145's SM-1 refused to retire — kept here, both ways.)
- **SPF-1-F2 (wrong target).** If the inference is actually about the **population** ("anyone who tries succeeds ~55% of the time") rather than the **serious-conditional**, the survivorship/selection objection **stands** regardless of memory symmetry. SPF-1 licenses only the conditional reading.
- **SPF-1-F3 (hindsight contamination).** If the "seriousness/confidence" used to select is **retrospective**, the move is invalid (Section 4 demo): the selection variable is no longer pre-outcome. Only prospectively-logged confidence qualifies.

---

## 6. Consistency with the canon (no silent contradiction)

- **vs Survivorship-as-correction (Ch. 4, MEP/#69 bias-sim).** Untouched. Those are **Axis-B / outcome-selection** cases (vindicated mavericks remembered, wrong-and-forgotten erased; MEP's retrospective design manufacturing +36→+43pp). SPF-1 does **not** weaken them — it **carves out** the orthogonal Axis-A case the survivorship label was over-extended onto. The corpus's survivorship vigilance is preserved exactly where it belongs.
- **vs B144 HAN-1 ("ignore nulls honestly").** SPF-1 is its memory-side companion and uses the identical ledger: exclude nulls ✓, keep committed misses ✓; the validate-phase falsifier counts both ways.
- **vs B145 SM-1 (sacred mistakes need a pre-registered outcome-blind ledger).** Fully consistent and mutually reinforcing: SM-1 demanded the ledger **because** memory may be asymmetric (α unknown from the inside). SPF-1 explains *when* the ledger would be unnecessary (α ≈ 0) **but agrees** that — since you cannot verify your own α introspectively — the **ledger remains the safe default**. SPF-1 raises the charitable case; it does not lower the guard.
- **vs IPA-1 (B119) — direct structural twin.** Ch. 17 already frames IPA-1 as "a valid objection that becomes a *pseudo-fallacy* when misapplied" (case→population is fine to refuse; population→individual is the damaging error). SPF-1 is the same shape: outcome-selection is fine to flag; flagging **pre-outcome reference-class conditioning** as survivorship is the pseudo-fallacy. SPF-1 should be ratified **near** IPA-1.
- **vs CRD-1 / Galileo Gambit.** No loosening: a crank's recalled "hits" are exactly the **α > 0 / self-serving** failure case (and often SPF-1-F3 hindsight). SPF-1 does **not** raise anyone's truth-prior; it only corrects a misapplied *charge*.
- **vs EVD-1.** Survivorship-conditioned recall is **graded Weight**, not Proof: Status = yes, Weight scaled by the (unverified) memory quality, **load-bearing only after independent validation**. Per **TI Sigma Statistics** (reference-class conditioning), counting the serious attempts is the right denominator — but the *miss-deletion* line is never crossed.

---

## 7. Honesty rails (explicit)

- **Not overturning survivorship bias.** It remains a real fallacy in its canonical outcome-selection form. We demarcate the misapplied case only.
- **No empirical over-reach.** The sim proves a **conditional**; it does **not** claim real human memory is outcome-symmetric. The "possibly/likely" hedge is load-bearing, not decorative.
- **#69 both ways.** The crux premise is presented with its strongest support *and* its strongest rebuttal; the net is "unresolved, person/domain-specific."
- **No numerology / no Millennium / no moral-realism.** Nothing here touches those rails; no recurring constant is load-bearing; cites are all real.

**Real citations:** Wald (1943, survivorship origin); Zeigarnik (1927); Baumeister, Bratslavsky, Finkenauer & Vohs (2001); Rozin & Royzman (2001); Brown & Kulik (1977); Miller & Ross (1975); Mitchell, Thompson, Peterson & Cronk (1997); Fischhoff (1975); Neisser & Harsch (1992); Hájek (2007). Internal: EVD-1, HAN-1 (B144), SM-1/TRI-1 (B145), IPA-1 (B119), CRD-1 (B120), MEP (B105), TI Sigma Statistics.

---

## 8. One-line ledger

**SPF-1 (candidate, not ratified; count 79):** survivorship is a *pseudo-fallacy* when the selection is pre-outcome (seriousness) and memory is outcome-symmetric — then "count serious attempts, ignore nulls" is correct reference-class conditioning, not bias; bias is driven solely by win-favoring forgetting α (sim: 0 at α=0, +0.38 at α=0.9; α\*≈0.05); empirical α is contested both ways ⇒ *possibly/likely* a pseudo-fallacy, hinging on memory quality; falsifiers SPF-1-F1/F2/F3 OPEN.

# Pass 77 · B150 — The **SFC-1-F1 attack**: a leakage-audited, real-math test of non-oracular structural fidelity

**Date:** 2026-06-25
**Status:** No new principle and no new candidate — this batch **attacks an existing open falsifier (SFC-1-F1)** and reports the result. Canonical principle **count unchanged 79**. SFC-1 remains a **candidate, NOT ratified**.
**Package:** `analyses/pass77_b150_sfc1_f1_realmath/sfc1_f1_checks.py` (+ `_output.txt`) — all checks pass.

> **Honesty rails honored (#69 both-ways).** This batch does the un-glamorous thing: it takes the one open falsifier B149 left on the table and *tries to break it*, on real settled mathematics. The honest outcome is reported in full — the falsifier survives (we found **no** leakage-free, non-oracular `F` that predicts mathematical truth on the undecidable-flavored corpus), and we also state plainly the limits of that finding (small, hand-curated, illustrative corpus; absence of evidence, not a census; no claim about RH; no claim a sim "proves" anything normative). TPS-1/RAI-1: this is a presentation/empirical-probe batch, it changes no canonical content. Cap `G*` derived from `T_d`; no "0.93" typed.

---

## 0. Where this sits

- **B148 (FCF-1):** the UOP↔conjecture "fidelity lemma" is **provable but a tautology** — `G` came from a proof-checker oracle, so `argmax J` just reads the verdict back. Zero proving work.
- **B149 (SFC-1):** replace the oracle with a **non-oracular** structural map `G = F(intrinsic structure)`. On synthetic data this yields a strict **dichotomy** — such an `F` *can* beat chance (PART A, tautology escaped), but the instant it does it meets the **undecidability wall** (PART C: any fixed computable `F` is diagonalizable). Net: **SFC-1 is a fallible heuristic, never a soundness+completeness method** (theorem **SFC-1-BOUND** via halting reduction). B149 left one falsifier explicitly OPEN:

  > **SFC-1-F1** — exhibit a **real-math, leakage-free, non-oracular** `F` that genuinely predicts/constrains mathematical truth from structure alone.

- **B150 (this batch):** attack SFC-1-F1 directly, on **real settled mathematical statements** (labels not in dispute). Does genuine math carry the structure↔truth correlation that B149's synthetic PART A assumed — or does it behave like PART B (chance) once leakage is controlled?

---

## 1. The construction (what counts as a fair attempt)

A statement `P` is summarized by a vector of **surface-structural features** computed from the *string alone* — none consults a proof, a checker, or the label:

`n_chars, n_words, n_distinct_chars, compression_ratio (zlib MDL proxy), n_digits, neg_markers` (count of negation/impossibility tokens).

`F` is a pure-numpy logistic map learned on a **labeled training split only**, returning `G = G* · prob(P)`; the UOP verdict is the B147 argmax over `{True, False}`, which — since `J` is monotone in `G` on `[0, G*]` — is "True" iff `prob > ½`. **Non-tautological by construction:** `F` never sees a checker or the test label.

The whole game is whether such an `F`, trained honestly, predicts the truth of *held-out* real statements **without leakage**.

---

## 2. What the harness shows (`sfc1_f1_checks.py`, predictions pre-registered)

### PART A — the naive benchmark (the trap), P1
Famous true theorems (`there are infinitely many primes`, `sqrt(2) is irrational`, `e is transcendental`, …) vs a **separately collected** bag of false statements (`7 is not prime`, `there are not infinitely many primes`, `the empty set is a subset of no set`, …). Held-out accuracy = **0.924**. It looks like a triumph for structural fidelity. It is not: the `neg_markers` feature is doing the work, because a casually-collected false set happens to carry more negation/impossibility wording. **This is exactly the trap real ML-for-math benchmarks fall into.**

### PART B — the decisive control (negation-paired, polarity-balanced), P2a/P2
The honest test. Every statement `P` is placed alongside a **settled-false counterpart** via a **near-minimal edit** (antonym swap / single negation) — `rational ↔ irrational`, `prime ↔ not prime`, `converges ↔ diverges`, `countable ↔ uncountable`, `algebraic ↔ transcendental`, `infinitely ↔ finitely` — so the two members are **structurally near-identical** (verified: mean per-pair token-overlap **Jaccard 0.655**; check P2a). "Near-minimal," not literally a one-character edit, is the honest description; what matters is that no *surface* feature separates the members. Crucially the polarity/negation tokens now appear on **both** labels across the corpus (e.g. `9 is not prime` is **true**, `7 is not prime` is **false**; `there is no largest prime` is **true**, `the empty set is a subset of no set` is **false**), so no surface token tracks truth. **Group cross-validation** keeps both members of a pair on the same side of every split (no pair spans train/test).

Result: the **same `F` collapses to 0.417 ≈ chance** (neg-marker mass TRUE=4 vs FALSE=5 — balanced, artifact neutralized). There is **no leakage-free surface structure that tracks truth** for these statements. *To label them you must actually do the mathematics.* **SFC-1-F1 is NOT met.**

### PART C — the decidable subclass (where "fidelity" is trivial and oracular), P3a/P3b
Arithmetic claims `a+b=c`. Surface-only features (digits/length) ⇒ **0.502** (chance — there is no surface signal). Add a single **evaluator** feature (`does a+b actually equal c?`) ⇒ **1.000**. But that feature **is a decision procedure / an oracle** for the subclass. This is precisely **SFC-1-BOUND's escape hatch**: fidelity becomes trivial on a *decidable* subclass exactly because `F` there *is the decider* — zero predict-before-proof content. It does **not** count as M1 (non-oracular structural fidelity).

### PART D — the leakage tax and the verdict, P4/P5
**Leakage tax = naive − balanced = 0.924 − 0.417 = 0.507.** Over half of the naive benchmark's apparent accuracy was pure annotation artifact, not access to mathematical truth — a **live demonstration of falsifier SFC-1-F3** (the leakage-audit obligation). Verdict: **SFC-1-F1 remains OPEN**; the empirical result is exactly what **SFC-1-BOUND predicts** (no magic).

| Probe | Accuracy | Honest reading |
|---|---|---|
| PART A naive (unbalanced) | **0.924** | inflated by negation-marker artifact (the trap) |
| PART B negation-paired (leakage-free) | **0.417** | ≈ chance — no surface truth signal on real math |
| PART C arithmetic, surface-only | **0.502** | ≈ chance even on a decidable subclass |
| PART C arithmetic, + evaluator | **1.000** | solved, but the feature is a decision-procedure **oracle** |
| Leakage tax (A − B) | **0.507** | the artifact's size; SFC-1-F3 demonstrated |

---

## 3. Why this is the right result, stated honestly (#69 both-ways)

**FOR "there might still be a real `F`" (steelman, why F1 stays *open* not *closed*):**
- This is a **small, hand-curated, illustrative** corpus, not a census. Absence of a detected signal is not a proof that none exists.
- The features are deliberately *cheap* (length, compression, negation count). Richer, genuinely mathematical structural features (proof-complexity proxies, symmetry groups, analytic-continuation behavior, embedding-based representations) are exactly where real progress would come from — and where the real research programs live: the **Ramanujan Machine** (Raayoni et al., *Nature* 2021) and **Davies et al.** (*Nature* 2021) *do* mine structure to **conjecture/guide** real mathematics. Note carefully: both are **heuristic generators**, validated afterward by human proof — i.e. they are SFC-1's *fallible heuristic*, not a soundness+completeness oracle. That is consistent with, not a counterexample to, SFC-1-BOUND.

**AGAINST (why the negative is nonetheless meaningful):**
- The **negation-pair design is a genuinely strong leakage control**, not a strawman. Each true statement is matched to a structurally near-identical false one, so any classifier relying on surface form is *forced* to chance. That is the cleanest available operationalization of "leakage-free."
- The **decidable-subclass result** shows the only way the harness ever reached high accuracy on truth was by smuggling in a decision procedure — which is the oracle SFC-1 forbids. So the two ways to "win" are (i) leak (PART A), or (ii) embed a decider (PART C). Both are exactly the failure modes SFC-1 names.

**Net:** the attack **strengthens the SFC-1 picture without ratifying it** — the dichotomy (escape-the-tautology ⇒ hit-the-wall) reproduces on real mathematics, and the falsifier remains the honest open frontier.

---

## 4. Consistency with the corpus

- **No principle added; count stays 79.** SFC-1 is still a *candidate*. This batch is a falsifier-probe, not a ratification.
- **B148/B132/B134 spine intact:** the UOP does not shortcut a proof; "predict-before-proof" content only ever appears as a *fallible heuristic*, never a guaranteed decider.
- **TPS-1/RAI-1:** empirical probe, no content change. **UGI-1 generate→validate:** the attempt was generated, then validated against pre-registered predictions and a hard leakage control. **EVD-1/#69:** the genuine (negative) result is shown out loud with its weight and its limits.
- **No RH claim, no Millennium closure, no "sim proves a normative posit."**

---

## 5. Falsifiers (carried forward; status updated)

- **SFC-1-F1 — OPEN (attacked here, survived).** *Win condition:* a real-math, **leakage-free** (negation-pair-robust or equivalent), **non-oracular** `F` that predicts held-out mathematical truth materially above chance on an undecidable-flavored class. The Ramanujan-Machine / Davies-style programs are the place to look — but to **falsify** SFC-1 (rather than confirm its heuristic reading) such an `F` would also have to clear M2∧M3 on a rich class, which SFC-1-BOUND says is impossible. So the *reachable* target is "strong heuristic," and that would *confirm* SFC-1, not break it.
- **SFC-1-F2 — OPEN.** A non-trivial *decidable* subclass that is sound+complete **and** retains real predict-before-proof content (PART C says the content evaporates: the win there is just the decider).
- **SFC-1-F3 — DEMONSTRATED-LIVE (stays as a standing audit obligation).** Any future "structural fidelity" result must pass a negation-pair / polarity-balance leakage audit; this batch shows an unaudited benchmark over-reports by **0.50**.

---

## 6. Real citations (used, correctly scoped)

- A. Turing, *On Computable Numbers* (1936); H. G. Rice (1953); K. Gödel (1931) — the undecidability wall behind SFC-1-BOUND (inherited from B149).
- D. Wolpert & W. Macready, *No Free Lunch* (1997) — why a predictor with no real structure↔truth correlation cannot beat chance.
- M. Li & P. Vitányi, *Kolmogorov Complexity* — the MDL/compression feature is a *proxy*; true Kolmogorov complexity is itself uncomputable (a caveat, not a tool).
- G. Raayoni et al., *The Ramanujan Machine*, **Nature** (2021); A. Davies et al., *Advancing mathematics by guiding human intuition with AI*, **Nature** (2021) — real structure-mining programs; **heuristic generators validated by human proof**, i.e. SFC-1's fallible-heuristic reading, not oracles.

---

### One-line takeaway
Asked to break SFC-1's open falsifier on real mathematics, the only ways to score above chance were to **leak** (the naive benchmark, +0.50 artifact) or to **embed a decision procedure** (the arithmetic evaluator) — both forbidden; the leakage-free, non-oracular test sits at chance, so **SFC-1-F1 stays open and SFC-1-BOUND's "no-magic" picture holds**, on real math, with no overclaim.

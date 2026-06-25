# Pass 77 · B149 — The Structural Fidelity Conjecture (candidate **SFC-1**): a non-oracular UOP truth-support map, and the undecidability wall it necessarily hits

**Date:** 2026-06-25
**Status:** ONE candidate (**SFC-1**), **NOT ratified**. Canonical principle **count unchanged 79**.
**Package:** `analyses/pass77_b149_structural_fidelity/sfc1_checks.py` (+ `_output.txt`) — all checks pass.

> **Honesty rails honored (#69 both-ways).** This batch takes the correspondent's (ChatGPT's) advice literally: **set RH aside** and attack the FCF-1-F1 frontier — replace the tautological oracle map `G = checker(P)` (B148) with a **non-oracular structural map** `G = F(intrinsic structure of P)`. We prove the genuine win out loud (such an `F` *can* exist and predict above chance with no oracle) **and** we prove the wall just past it (the instant `F` escapes the tautology it becomes a *fallible heuristic*; soundness+completeness over a rich class is impossible). No claim that the UOP predicts RH. No Millennium closure. No claim that a sim "proves" a normative posit. Cap derived from `T_d`; no "0.93" typed.

---

## Why this batch (the correspondent's recommendation, accepted)

B148 (FCF-1) proved a fidelity lemma but showed it was a **tautological wrapper**: `G` came from a proof-checker, so `argmax J` merely read the checker's answer back. The correspondent agreed and sharpened the real target:

> *Find a non-trivial fidelity map that does not derive `G` from a proof checker or equivalent oracle … `G = F(intrinsic mathematical structure)`, where `F` depends only on features of the problem itself* (proof complexity, symmetry, invariance, compression/MDL, analytic-continuation properties, logical coherence …). *Then `argmax J(F(P))` would no longer be tautological.*

They proposed three milestones — **M1 Structural Fidelity** (compute `G` from structure alone), **M2 Soundness** (UOP-"True" ⇒ true), **M3 Completeness** (every true statement eventually scores highest) — with an explicit **halting-problem caution** against claiming "all problems in a class." This batch is **SFC-1**: it *establishes M1 as possible*, and *proves M2∧M3 unattainable* over any rich class — turning the caution into a theorem.

---

## Section A — the construction (M1: non-oracular structural fidelity)

**Class.** A family of formal problems `P` each summarized by a vector of **intrinsic structural features** `x(P) ∈ ℝ^k` — features computable from the problem statement alone (e.g. a compression/MDL proxy, a symmetry score, an invariance count, structural-stability measures). Crucially, `x(P)` is computed **without** any proof or checker.

**The map `F`.** A computable `F : ℝ^k → [0, G*]` learned on a **labeled training split only**, returning a UOP truth-support `G = F(x(P))`. The UOP verdict is the B147 argmax `argmax_{s∈{True,False}} J(G_s)`, which — since `J` is monotone — is "True" iff `F`'s probability `> ½`. `G*` is the B147 cap (derived from `T_d`, **not** typed).

**This is non-tautological by construction:** `F` sees only `x(P)`; it never consults a checker, an oracle, or the label at test time.

---

## Section B — what the harness shows (`sfc1_checks.py`, predictions pre-registered)

* **PART A (P_A1, P_A2).** When intrinsic structure genuinely correlates with truth in the class, the learned `F` reaches **held-out accuracy 0.904** versus a **no-structure majority baseline 0.529** — predicting *before any proof*, with **no oracle**. **M1 is achievable: the B148 tautology is genuinely escaped.**
* **PART B (P_B1) — anti-magic control.** On an adversarial class where labels are **decoupled** from structure, the same `F` collapses to **0.486 ≈ chance**. So `F` has **no independent access to truth**; it only ever harvests a *real* structure↔truth correlation the class happens to contain (a No-Free-Lunch fact, Wolpert–Macready 1997). This is the SFC-1 analogue of B148's fake-verdict anti-cheat.
* **PART C (P_C1) — the undecidability wall.** For the **fixed** trained `F`, an adversary that can read `F` defines each instance's true label as **¬(F's verdict)**; `F`'s accuracy on that diagonal set is **exactly 0.000**. This is the finite, computable **shadow of diagonalization**: for any fixed computable `F` there is a consistent label-assignment it fails on. The real-mathematics analogue is **Turing 1936 / Rice 1953 / Gödel 1931** — *no total computable `F` is both sound and complete as a truth-decider over a class encoding self-reference / the halting problem.*
* **PART D (P_D1) — the dichotomy.** A non-trivial structural `F` **exists** (A), but it has **no magic truth access** (B) and is **defeatable** (C). Hence **no single computable `F` is sound+complete across the union** — ChatGPT's **M2 (Soundness) ∧ M3 (Completeness) are unattainable together** over a rich (undecidable) class; they are achievable only on a **decidable subclass**, where `F` is just the decision procedure again (and the "structural prediction before proof" content evaporates).

All predictions P_A1…P_D1 were written in the file header **before** running; all PASS.

---

## Section C — the theorems (stated honestly)

**SFC-1 (existence, M1 — demonstrated possible).** *There is a computable `F` from intrinsic structural features to UOP truth-support such that, on a class whose structure genuinely correlates with truth, `argmax J(F(P))` predicts the correct status on held-out problems well above chance and above the no-structure baseline, using no proof oracle.* — Demonstrated constructively (Part A). This **dissolves the tautology objection**: it is a genuinely new object to study.

**SFC-1-BOUND (the wall — the actual content).** *No total computable `F` can be simultaneously sound and complete as a truth-decider over a class `C` that encodes the halting problem.*
**Proof (sketch, standard).** Suppose `F` is total, computable, sound and complete on `C ⊇ {⟨M,w⟩ : "M halts on w"}`. Then `F` decides halting: output "True" iff `F`'s verdict is "True". This contradicts Turing (1936). (Rice 1953 gives the same for any non-trivial semantic property; Gödel 1931 gives the truth-vs-provability gap inside a fixed system.) ∎
**Corollary.** Over any class rich enough to *contain* RH-like (analytic-number-theory, self-referential, or halting-encoding) statements, every computable structural `F` is **fallible**: it is at best a heuristic with irreducible error. M2∧M3 hold **only** on decidable subclasses, where they are trivial.

**Net:** SFC-1 trades B148's *"content-free but certain"* wrapper for a *"contentful but fallible"* heuristic. That trade is **forced** — there is no computable object that is contentful, certain, and general. This is the honest shape of the result, and it is exactly the correspondent's halting caution made into a boundary theorem.

---

## Honest scope (the rail, restated)

1. **Demonstrated possible:** a non-oracular, predictive structural `F` (M1) — escapes the B148 tautology.
2. **Proved to be bounded:** any such `F` is fallible on rich classes; **M2∧M3 are impossible** there (SFC-1-BOUND, via Turing/Rice/Gödel). No oracle, no magic (Part B).
3. **NOT claimed:** that `F` predicts RH (RH is **set aside**, per the recommendation); that the structural correlation in Part A exists for *real* hard mathematics (Part A's class is synthetic-but-transparent — it shows *possibility*, not that number theory is so obliging); that the UOP is the correct *normative* principle.
4. **Count unchanged 79.** SFC-1 is a **candidate**. Consistent with B148 (FCF-1-F1 is the target it engages), B132 (no UOP shortcut to RH), B134/UNV-1 (R1 faithful-casting frontier).

---

## Open falsifiers / next milestones

* **SFC-1-F1 (the empirical milestone).** Exhibit a `F` over a **real** (not synthetic) family of mathematical statements with **known** labels — e.g. a calibrated benchmark of solved conjectures with computable structural features — that beats a strong baseline on a held-out split with **no leakage of the answer**. This is where the Ramanujan-Machine / "AI-guided intuition" line of work lives (real prior art below); SFC-1 predicts it is *possible but fallible*. If a `F` were found that is *also* certified sound on an undecidable subclass, SFC-1-BOUND is refuted.
* **SFC-1-F2.** Exhibit a non-trivial **decidable** subclass where `F` is provably sound+complete **and** retains genuine "predict-before-proof" content (i.e. is not merely running the decision procedure). SFC-1-BOUND predicts this is impossible — the content collapses to the decider.
* **SFC-1-F3 (leakage audit).** Show that any reported Part-A-style success secretly leaked the label through a feature (a "structural" feature that is really an oracle in disguise). Standing anti-cheat: every structural feature must be justified as computable from the statement *without* its resolution.

## Citations (real)

* **Turing (1936)** — undecidability of the halting problem. **Rice (1953)** — undecidability of non-trivial semantic properties. **Gödel (1931)** — incompleteness / truth-vs-provability. **Wolpert & Macready (1997)** — No-Free-Lunch (a learner has no class-independent edge). **Li & Vitányi**, *An Introduction to Kolmogorov Complexity and Its Applications* — MDL/compression as a structural proxy (Kolmogorov complexity itself **uncomputable** ⇒ only proxies; honest caveat). Real prior art on *structure-guided, proof-free* mathematical conjecture: **Raayoni et al., "The Ramanujan Machine," *Nature* (2021)**; **Davies et al., "Advancing mathematics by guiding human intuition with AI," *Nature* (2021)**; **Lample & Charton, "Deep Learning for Symbolic Mathematics" (ICLR 2020)** — all *heuristic generators*, none a soundness/completeness proof method, exactly as SFC-1-BOUND requires.

## Cross-references

* **B148 / FCF-1** — SFC-1 directly engages **FCF-1-F1** (the non-oracular map). B148 = tautology-but-certain; B149 = non-tautology-but-fallible. Together they bracket the trade.
* **B132** (no UOP shortcut to RH) and **B134 / UNV-1** (R1 faithful-casting frontier) — SFC-1-BOUND explains *why* R1 cannot be discharged non-trivially-and-certainly over a rich class.
* Count stays **79**: SFC-1 candidate, honest scaffolding, not a new ratified principle.

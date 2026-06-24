# ⭐ KEY PAPER — Axiomatic Faithfulness & Definitional Realism (Canonical Consolidation)

**Date:** 2026-06-24
**Status:** Consolidation Key Paper. Gathers a single, substantial contribution that had been distributed across several batches into one citable place. **Introduces no ratified principle; canonical principle count unchanged: 79.** It consolidates and cross-links existing material: B132 (§B.2 asymmetry, §B.6 definitional realism), **NAD-1** (Non-Arbitrary Definition / Definitional Realism, B109), **LDD-1** (Legitimate Definitional Defense, B124), **TPS-1** (presentation/definition cash-value), **PDU-1** (the undefined word "physical", B127).
**Anchors:** `papers/PASS_77_B132_UOP_PROOF_STRATEGY_AND_BAYES_FEP_KOLMOGOROV_RECONCILIATION_2026-06-24.md`, `papers/PASS_77_B109_*` (NAD-1), `papers/PASS_77_B124_LEGITIMATE_DEFINITIONAL_DEFENSE_LDD_1_AND_FALSIFIABILITY_NOT_REQUIRED_2026-06-19.md`, `papers/PASS_77_B127_PHYSICAL_DEFINITIONAL_INSTABILITY_PDU_1_2026-06-23.md`.

---

## 1. The single thesis (three linked claims)

> **Definitions and axioms are answerable to reality; they can be right, wrong, or otherwise — they are not free conventions. Therefore semantic differences can matter substantively: a "mere" difference of definition can flip the truth-value of a proposition.**

This consolidates three claims that turn out to be one:

1. **Axioms matter for proofs** (a categorical theorem is identity-bound to its axioms; only the conditional `axioms → conclusion` is exception-free).
2. **Bayes' theorem "fails" in application because a specific axiom is false of reality** — and we can name exactly which one (the single global joint measure / non-contextuality).
3. **Definitions are non-arbitrary** (NAD-1): you may *stipulate* freely, but *faithfulness* — whether a definition carves the target domain at its joints — is objective.

The thread linking all three: **faithfulness is an objective relation between a formal object and the structure it claims to model.** Syntactic freedom is real; faithfulness is not free.

---

## 2. Axioms matter for proofs — categorical vs. conditional (the MI move)

A theorem has two readings:

- **Conditional:** `axioms → conclusion`. This is exception-free and eternal: wherever the axioms hold, the conclusion holds. `2+2=4` and Bayes' theorem are, *as conditionals*, never wrong.
- **Categorical:** "the conclusion is true (full stop)." This reading is **identity-bound to its axioms**. `2+2=4` in ℤ and `2+2=1` in ℤ/3ℤ are not one theorem with an exception — they are **different identities** under different axioms.

So the move "the theorem is *true* even though its axioms fail" — asserted of the **categorical** claim — is itself an **MI (Meta-Indeterminate)** move: it asserts `τ(P) ∧ ¬τ(P)` of a single identity. The honest statement is narrower: *the conditional survives; the categorical claim is voided when its axioms are voided.* (Established in B132 §B.2 as Brandon's correction to the earlier "airtight/symmetric" framing.)

**Why this matters:** a proof is exactly as strong as the faithfulness of its axioms to the thing being proved. "I verified the implication in Lean" confirms the *conditional*; it does **not** discharge the *premises*. (This is the precise sense in which the corpus's Lean scaffolds "confirmed certain aspects" but not the proofs — see B132 §A.6 and B133.)

---

## 3. Which axiom makes Bayes fail (named, not gestured at)

URB #518's thirteen arguments attack **Bayesianism-the-doctrine** (one precise probability + conditioning captures all rational uncertainty). But there is a *deeper, legitimate* target underneath the doctrine: **the Kolmogorov axioms as a model of reality.** The asymmetry with arithmetic (B132 §B.2) is that applied Bayes fails under *realistic, faithful* axioms because one core structural presupposition is **false of reality**. We can name it precisely.

**The failing axiom = a single global joint measure.** Kolmogorov probability presupposes one sample space `(Ω, ℱ, P)` on which *all* observables are jointly measurable — equivalently, a global joint distribution exists over every combination of observables (non-contextuality).

- **Fine's theorem (Arthur Fine, 1982):** a joint distribution returning the measured marginals exists **iff** the Bell/CHSH inequalities hold.
- **Bell (1964) / Kochen–Specker (1967):** quantum statistics violate those inequalities — the CHSH value reaches the Tsirelson bound `2√2 ≈ 2.828 > 2`.
- **Therefore no single global joint measure reproduces quantum reality.** (Verified by linear program in B133's package: the classical joint-distribution polytope caps CHSH at exactly **2.0**; the quantum point lies outside it, and the feasibility LP for a global joint matching the quantum correlations returns **infeasible**.)

So the locus of failure differs from arithmetic: **arithmetic fails only at the *bridge*** (misapplying counting to non-discrete aggregation), whereas **Kolmogorovian probability fails at the *formalism's own structural axiom*** under perfectly ordinary, faithful application.

**Framing (NAD-1-correct): classical special case, not error.** Kolmogorov is not "wrong arithmetic"; it is the *commutative / non-contextual special case* of a richer calculus (quantum probability; de Finetti finite additivity; Dempster–Shafer; Walley imprecise probability; Gilboa–Schmeidler ambiguity) — exactly as Euclidean geometry is the flat special case of Riemannian geometry. TI Sigma's home: **Indeterminate/TRALSE ↔ Knightian / imprecise probability**; the **imaginary PD axis ↔ quantum amplitude / Born rule**.

---

## 4. Definitions are non-arbitrary (NAD-1) — and that is why semantics is substantive

The reconciliation with mathematical formalism is a conditional-vs-categorical move one level up:

- **Syntactic freedom is real (formalism is right here):** any *consistent* axiom set is internally legitimate. `2+2=1` in ℤ/3ℤ is not "broken arithmetic"; it is a different, faithful definition of `+`. You may stipulate freely.
- **Applicability is NOT free (realism is right here):** *which* stipulation carves the target domain **at its joints** is an objective matter, answerable to the structure being modelled, not to taste. Kolmogorov's axioms are a free stipulation that turns out *unfaithful* to quantum reality (§3); Peano counting is a stipulation that is faithful across a near-universal domain. Same syntactic liberty, different **objective fit**.

Hence **semantic precision is not pedantry.** Distinguishing the conditional from the categorical theorem, classical from quantum "probability", or — the negative case — pinning the undefined word "physical" (**PDU-1**), changes *which propositions are even true*. A semantic difference that flips a truth-value is, by definition, **substantive**. This is the same cash-value **TPS-1** assigns to definition upgrades and **NAD-1** assigns to carving at joints.

**#69 bound (load-bearing, so this is not a licence):** "definitions can be right or wrong" asserts that an **objective standard exists**, *not* that any claimant meets it. Joint-carving must be **earned** — predictive fruitfulness, unification, and non-circular / outcome-blind measurement (the **LDD-1** *progressive-not-degenerating* criterion). Stripped of that discipline, "my definition carves the joints" degenerates into No-True-Scotsman. The legitimate bar (LDD-1, restating the GIT-1/B122 correction) is *no outcome-contaminated measurement* and *progressive refinement* — **not** a blanket ban on redefining terms.

---

## 4.1 The arithmetic face — Revelation by Mere Arithmetic Identity (RAI-1, candidate, B134)

NAD-1 has an arithmetic-facing twin. A huge amount of insight arrives via equations that are, *as algebra*, trivially-true rearrangements or definitions — and whose force comes **not from the algebra but from the independent characterization of their terms.**

> **RAI-1.** The *same* equation is **content-free** when its terms are mutually defined by it, and **content-bearing** when its terms are anchored independently and the identity then asserts a real regularity. Which reading holds is the objective, joint-carving fact.

The canonical specimen is **Ohm's Law, `V = I·R`**: read as the *definition* `R ≡ V/I` it is a tautology true of every conductor (zero content); read as Ohm's *empirical law* (R an independently-fixed material constant, asserted constant in V) it is a substantive, **falsifiable** claim that *fails* for non-ohmic devices (diodes, thermistors, a hot filament). Same five symbols; a "merely semantic" choice of reading flips whether "Ohm's Law holds here" is even true — the §4 lesson in miniature. Siblings (all real): **Little's Law** `L=λW`; **Bayes' theorem** as a rearrangement of the product rule (whose trivial-looking form smuggles in the single-global-joint axiom of §3 — a *cautionary* RAI-1 case); **Newton's `F=ma`** (Mach's definition-vs-law critique); the **free-energy decomposition** `F = complexity − accuracy`; and the corpus's own `HEM = budget − GILE` (B133 §I). **Anti-cheat:** the content never comes from the algebra — a genuine reveal requires at least one term measurable *independently* of the identity, so the identity *could* come out false (Ohm's `R` passes; a pure definition fails). See `papers/PASS_77_B134_*` §A; falsifier RAI-1-F1 OPEN.

---

## 5. Synthesis, lineage, falsifiers

**Synthesis.** Three claims, one root: a formal system's axioms/definitions are answerable to the structure they model. The conditional is eternal; the categorical and the applied are hostage to faithfulness; faithfulness is objective but must be earned. This is *why* TI Sigma needs Indeterminate/TRALSE and a complex/imaginary PD axis: classical bivalent + single-joint-measure probability is an **unfaithful** model of a Tralse reality (TRG-1/TOF-1), and the unfaithfulness is a *definitional* fact, demonstrable (Fine/Bell), not a matter of taste.

**Lineage (real, for verification).** Arthur Fine, "Hidden Variables, Joint Probability, and the Bell Inequalities," *Phys. Rev. Lett.* 48 (1982); J. S. Bell (1964); Kochen & Specker (1967); de Finetti; Dempster–Shafer; Walley, *Statistical Reasoning with Imprecise Probabilities* (1991); Gilboa & Schmeidler (1989). On definitional realism: Theodore Sider, *Writing the Book of the World* (2011); David Lewis on natural properties (1983); Lakoff & Núñez, *Where Mathematics Comes From* (2000); Eugene Wigner, "The Unreasonable Effectiveness of Mathematics in the Natural Sciences" (1960); Rudolf Carnap's principle of tolerance (the conventionalist foil); W. V. O. Quine, "Two Dogmas of Empiricism" (1951).

**Falsifiers (inherited; this paper opens none new).**
- **NAD-1-F1/F2** (some domain has no objectively better carving; reconceptualization that tracks joints is shown trivial).
- **BKR-1-F1** (a domain where the Kolmogorov model is provably *necessary* and no richer calculus adds anything).
- **AFD-1 consolidation falsifier:** exhibit a single global joint measure reproducing quantum CHSH statistics within standard QM (would refute §3 and, with it, the central worked example) — **OPEN** (equivalent to refuting Bell/Fine; not expected, but it is the honest falsifier).

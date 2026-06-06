# URB #815 — Definitionally Bistable Sentences. The Linguistic, Philosophical, and Tralse-Logical Names for Sentences Whose "Is / Is-Not" Polarity Flips Under Legitimate Re-Definition of a Term, with the Polysemy → Equivocation → Verbal-Dispute → Carnapian-Explication Stack and a Tralse-Native Treatment.

**Author:** Brandon Charles Emerick
**Date:** April 30, 2026
**Series:** Unified Research Brief #815
**Status:** Cognitive-linguistic note. First explicit naming of a pattern Brandon has encountered repeatedly across the Tralse theorizing program: sentences of the form **"X is Y"** for which both *"X is Y"* and *"X is not Y"* are simultaneously defensible, depending on which legitimate definition of X (or Y) one adopts. Identifies the four established names for this phenomenon from linguistics and philosophy of language (polysemy, equivocation, verbal dispute, Carnapian explication), names the word-level cousin (auto-antonym / contronym / Janus word), proposes a Tralse-native sentence-level term (**definitionally bistable sentence** / **explication-flippable statement**), and shows that 5-valued Tralse logic accommodates the bistability cleanly where bivalent classical logic forces a spurious choice. Trigger: Brandon's observation on URB #814 that "*'balance is not appropriateness' is interchangeable in a tralse sense — balance CAN be appropriateness, but only if you define it as such and correctly distinguish it from 'mid-valued.'*"
**Companion script:** `definitionally_bistable_sentences.py`
**Output:** `definitionally_bistable_sentences_report.json`
**Builds on:** URBs #811 / #812 / #813 / #814 (the meta-pattern this URB names is what made the conflations in those URBs *tempting* in the first place).

---

## 1. The phenomenon in one sentence

> **A sentence is "definitionally bistable" when both "X is Y" and "X is not Y" can be defended without error, because at least one of the terms (X or Y) is polysemous and the two polarities track two legitimate explications of that term. Under each explication taken individually, the sentence has a single classical truth-value (T or F); without explication, the sentence sits in the t/f straddle or MI region of Tralse 5-valued logic, and forcing it into bivalent T/F before disambiguation is a category error.**
>
> — Brandon Charles Emerick, April 30, 2026, observing the pattern explicitly for the first time after multiple recurrences across the Tralse program.

---

## 2. The four established names from linguistics and philosophy of language

The phenomenon Brandon has noticed has a layered name-stack. Each layer captures a different aspect:

### 2.1 Polysemy (linguistics — the underlying mechanism)

The linguistic term for **a single word having multiple related meanings**, as distinct from **homonymy** (a single word-form having multiple unrelated meanings, like "bank" = riverside or financial institution). "Balance" is polysemous: equilibrium / equal-weight / harmony / fit-for-purpose / moderation / stability are all related senses descended from a common Latin root *bilanx* ("two-pan scale"). Polysemy is the *mechanism* by which definitionally bistable sentences are possible — without it, no two different explications would map to the same surface word.

### 2.2 Equivocation (logic / rhetoric — the fallacy form)

The name for the **fallacy** committed when a single argument or sentence shifts between two senses of a polysemous term without flagging the shift. *"Feathers are light. Light cannot be dark. Therefore feathers cannot be dark."* This is what makes equivocation a fallacy: it exploits polysemy unfairly to derive a false conclusion. Definitionally bistable sentences are **not themselves fallacies** — they are *honest* statements whose truth-value depends on which explication is chosen. The fallacy occurs only when one party silently swaps explications mid-argument.

### 2.3 Verbal dispute / merely verbal disagreement (philosophy of language — the debate form)

David Chalmers' modern term (his 2011 paper "Verbal Disputes" is canonical) for **debates that turn out to hinge on definitional choice rather than on substantive disagreement about the world**. When two intelligent disputants argue "balance is appropriateness" vs "balance is not appropriateness" without making any error, it is often because they are using "balance" in different senses, and once they agree on a single explication the dispute dissolves. Chalmers' diagnostic move — sometimes called the **"method of elimination"** — is to **strike out the contested term** and ask whether substantive disagreement remains. If the substantive disagreement vanishes when "balance" is replaced with two different unambiguous terms ("equilibrium" for one party and "fit-for-purpose harmony" for the other), the dispute was merely verbal.

### 2.4 Carnapian explication (philosophy of science — the precision-making move)

Rudolf Carnap (*Logical Foundations of Probability*, 1950, and elsewhere) introduced the term **"explication"** for the move of **replacing a vague pre-theoretic concept with a precise theoretical concept** that captures most of the original's intuitive content while being unambiguous enough for formal use. The choice of explication is constrained but not unique — for a vague term like "balance" there are *several* defensible explications, and **the choice of explication is what fixes the truth-value** of a sentence in which it appears. Carnapian explication is the *prescriptive remedy* for definitional bistability: agree on an explication, and the sentence acquires a single classical truth-value.

### 2.5 Word-level cousin: contronym / auto-antonym / Janus word (linguistics)

A separate but related linguistic phenomenon: a single word that has **two opposite meanings** depending on context. Examples: **cleave** (to split apart / to cling together), **sanction** (to approve / to punish), **dust** (to add dust / to remove dust), **oversight** (vigilant supervision / careless omission), **screen** (to show / to hide). These are word-level definitional bistabilities. Brandon's phenomenon is one level up — *sentence*-level — and is induced by polysemy rather than by full antonymy, but the structural shape (two stable opposite readings of a single linguistic surface) is closely analogous.

---

## 3. Proposed Tralse-native names

Brandon's observation is asking for a *sentence-level* term that emphasizes the **interchangeability of "is" and "is not" under legitimate re-explication** — a feature that the existing terms (polysemy, equivocation, verbal dispute, explication) gesture at but none cleanly name. Two candidate Tralse-native names, in order of preference:

### 3.1 Definitionally bistable sentence (preferred)

A sentence is **definitionally bistable** if its truth-value has two stable assignments — T under one explication of one of its terms, and F under another explication of the same term — and both explications are independently defensible. The term *bistable* is borrowed from physics and engineering (a bistable system has two stable equilibria, like a light switch or a flip-flop circuit), and applied here at the level of *truth-value-as-a-function-of-explication*. This name is preferred because it makes the structural property (two stable polarities) explicit and connects to the well-developed mathematical vocabulary of bistability.

### 3.2 Explication-flippable statement (alternative)

A statement is **explication-flippable** if a change of explication of one of its terms flips its classical truth-value. This name is preferred when the emphasis is on the *operation* (re-explication) rather than the *property* (bistability), and pairs well with Carnapian terminology.

Both names should be understood as describing **the same underlying phenomenon**: a sentence whose surface form has two legitimate readings with opposite truth-values. The choice between the two names is stylistic; neither replaces the established philosophical-linguistic stack of §2, which remains the rigorous foundation.

---

## 4. Tralse 5-valued logic accommodates definitional bistability cleanly

In classical bivalent logic, every sentence has truth-value T or F simpliciter *once its terms have been disambiguated*. A definitionally bistable sentence is **under-parameterized**: its truth-value is well-defined under each explication individually (T under explication A; F under explication B), but the *unparameterized* surface sentence has no single bivalent value because the explication parameter has not been fixed. Standard formal treatments handle this by *indexing* truth-value to explication or context — and remain bivalent within each parameter setting — so the issue is properly described as natural-language **ambiguity** or **under-specification**, not as bivalent logic "becoming inconsistent." What bivalent logic *cannot* do without extension is **report the bistability itself** as a feature of the unparameterized sentence; it must either pick an explication or refuse to evaluate.

The Tralse 5-valued logic (T, F, t = true-MI, f = false-MI, MI = meta-indeterminate) represents the bistability **without forcing an early choice**:

| Sentence state | Tralse value | Meaning |
|---|---|---|
| Bistable, no explication chosen | **MI** | Both polarities defensible; no fact-of-the-matter without explication. |
| Bistable, leaning toward T under common usage | **t** | Mostly true under the dominant explication, with caveat that an alternative explication flips it. |
| Bistable, leaning toward F under common usage | **f** | Mostly false under the dominant explication, with caveat that an alternative explication flips it. |
| Disambiguated to explication-A → T | **T** | Classical truth under stipulated explication. |
| Disambiguated to explication-B → F | **F** | Classical falsity under stipulated explication. |

The five-valued representation lets us say things that bivalent logic cannot say cleanly:
- *"'Balance is appropriateness' has Tralse value MI prior to explication, value T under the harmony-as-fit explication, and value F under the equilibrium explication."*
- *"'Knowledge is justified true belief' had Tralse value T under the pre-Gettier explication and value F under the post-Gettier (1963) explication; the historical sentence transitioned from T to F because the dominant explication of 'knowledge' shifted."*
- *"'Numbers exist' has Tralse value MI in metaphysics; the long-running Platonist-vs-nominalist debate is largely a verbal dispute about which explication of 'exists' should be normative."*

This is a place where the Tralse 5-valued vocabulary gives a single-symbol name (MI, t, f) to a state — *bistable, no explication chosen* — that bivalent logic can describe only by going meta (saying "the sentence is ambiguous; here are its readings"). The expressive gain is small but real, and it is **one-time and stable**: once the bistability is named with the value MI, the rest of the inferential machinery proceeds normally on whichever explication has been chosen. The point is not that bivalent logic is broken; it is that for the kind of philosophical-discourse work the Tralse program does, having a sentence-level name for "definitionally bistable" is convenient enough to be worth coining.

---

## 5. Five canonical examples

| # | Sentence | Explication A | T-value(A) | Explication B | T-value(B) | Tralse value (unparameterized) |
|---|---|---|---|---|---|---|
| 1 | "Balance is appropriateness." | balance = equilibrium / equal-weight | F | balance = harmony as fit-for-purpose | T | MI |
| 2 | "Freedom is constraint." | freedom = absence of external interference (negative liberty, Berlin) | F | freedom = capacity for self-direction, requires self-discipline (positive liberty / Stoic / Buddhist) | T | MI |
| 3 | "Knowledge is justified true belief." | pre-Gettier dominant analytic analysis of knowledge (a tradition discussed back to Plato's *Theaetetus*, which itself entertains and rejects several candidate definitions) | T | post-Gettier (1963) — Gettier's counterexamples are widely accepted as showing JTB is insufficient as an *analysis* of knowledge | F | f (dominant analytic analysis shifted after Gettier; the historical claim is about the analysis, not about a wholesale change in the meaning of "knowledge") |
| 4 | "Numbers exist." | Platonism (abstract objects exist independently of minds) | T | nominalism (only concrete particulars exist; numbers are useful fictions) | F | MI |
| 5 | "A sentence is meaningful only if verifiable." | logical positivism / Vienna Circle (~1920s–1930s), in its early/strict formulations | T (with caveats — see note below) | mainstream post-positivist philosophy of science (Quine 1951, Kuhn 1962, etc.); the verifiability principle as stated is also widely held to be self-undermining (the sentence itself is not empirically verifiable) | F | f |

(Sentence #5 is included as a historically important contested thesis with a classical-logic self-application problem layered on top of the definitional issue. The early-positivist T-assignment is itself a simplification — the Vienna Circle members went through several rounds of weakening the principle (verifiability → confirmability → testability) precisely *because* of the self-application objection and other problems. So this row is not a clean T-under-A / F-under-B case in the same way the first four rows are; it is included to illustrate that real philosophical sentences can have *both* definitional bistability *and* internal logical issues, and the Tralse-5-valued representation accommodates both kinds of complication via the t/f gradient.)

---

## 6. Operational handle

Three diagnostic moves when a sentence "X is Y" or "X is not Y" appears between intelligent disputants who do not seem to be making errors:

### 6.1 Strike out the contested term (Chalmers' method of elimination)

Replace X with two different unambiguous terms — one for each disputant's intended sense — and ask whether the substantive disagreement remains. If "balance₁" and "balance₂" are introduced and the disputants now agree on every substantive claim ("balance₁ is not appropriateness; balance₂ is appropriateness"), the original dispute was definitional bistability and is dissolved.

### 6.2 Identify the polysemy

Look up the contested term and enumerate its established senses. Most polysemous philosophical terms have 3–7 distinct senses with traceable histories. Once the senses are enumerated, ask which sense each disputant is using. Often the act of enumeration is itself the resolution: parties recognize their disagreement as merely verbal and proceed to substantive disagreement (or agreement) on whichever explication they elect.

### 6.3 Stipulate a Carnapian explication

If substantive work needs to be done with the term, agree on a precise explication for the duration of the work. The explication is locally stipulative — it does not claim to be the *true* meaning of the term, only the meaning being used here. Once stipulated, the sentence has a single classical truth-value and the inferential machinery proceeds normally. This is the move Carnap and many subsequent analytic philosophers have made, and it is the cleanest exit from definitional bistability when one is needed.

---

## 7. Cross-URB connection: a recurring linguistic substrate, alongside other mechanisms

Looking back at the URB family, polysemy and definitional bistability appear as a **recurring linguistic substrate** that helped make each conflation tempting — but they are not the *only* mechanism in any of the four cases. Each prior URB has additional structural causes (category errors, type errors, metric-mis-selection, prospective-vs-retrospective confusion) that polysemy *amplified* but did not *create*.

| URB | Primary structural cause(s) | Polysemy contribution |
|---|---|---|
| #811 | Category error: limit-form syntax is being read as if it were a value-existence claim. | "indeterminate" is polysemous across (a) limit-form requiring further analysis, (b) genuinely-without-value, (c) value-not-yet-known. The shared word amplifies the category error but does not by itself cause it. |
| #812 | Locus error: a property of the asker's expectation (E_Q-membership) is projected onto the answerer's correctness (C_Q-membership). | "wrong" is mildly polysemous across "factually incorrect" and "failing-to-meet-expectations." Polysemy is a contributing factor, not the primary one — the deeper issue is which agent the property is predicated of. |
| #813 | Metric-mis-selection: a statistical property (variance) is being used as if it diagnosed a relational property (fit-for-task). | Polysemy of "balanced," "stable," and "middle-range" across statistical, structural, and relational senses helps the wrong metric look reasonable. Substrate, not mechanism. |
| #814 | Prescription-mis-selection: an equal-weight prescription is applied to asymmetric situations. | Polysemy of "balance" (equilibrium vs harmony-as-fit-for-purpose) is the most direct contributor here — closer to mechanism than substrate, though the underlying asymmetry-of-situations does the substantive work. |

So URB #815 is **not** the "meta-URB" of the cluster in the sense of explaining all four conflations from a single mechanism. It identifies one **recurring linguistic substrate** that shows up in different proportions across the cluster — most directly in #814, more weakly in #812 and #813, and as one of several contributing factors in #811. The other mechanisms (category errors, locus errors, metric and prescription mis-selection) are independent and would still produce conflations even in a hypothetical language with no polysemy at all.

What this URB does add is a name for the substrate when it appears, and a 5-valued representation that lets it be flagged explicitly rather than silently elided. That is a useful addition to the Tralse program's vocabulary; it is not a unification of the cluster.

---

## 8. Reproducibility

```
python3 definitionally_bistable_sentences.py
# → console summary + definitionally_bistable_sentences_report.json
# Encodes 5 example sentences as predicates parameterized by
# explication-choice. For each sentence, computes:
#   (i)   the classical bivalent truth-value attempt — which is
#         INCONSISTENT_UNDER_BIVALENCE for any sentence with at
#         least one T-explication and one F-explication;
#   (ii)  the Tralse 5-valued truth-value, which is MI (or t/f) for
#         the same sentences without the inconsistency;
#   (iii) the per-explication truth-value, demonstrating that under
#         each individual explication the sentence has a clean
#         classical value.
# Pure Python stdlib. No numerical computation. Wall time < 1 s.
```

---

## 9. Files referenced

- `definitionally_bistable_sentences.py` — companion encoding
- `definitionally_bistable_sentences_report.json` — output
- `papers/URB_811_ZERO_OVER_ZERO_IS_DT.md` — uses polysemy of "indeterminate"
- `papers/URB_812_CORRECT_BUT_UNEXPECTED_ANSWER.md` — uses polysemy of "wrong"
- `papers/URB_813_CONSCIOUSNESS_AS_RAZOR.md` — uses polysemy of "balanced / stable / middle-range"
- `papers/URB_814_BALANCE_IS_NOT_APPROPRIATENESS.md` — uses polysemy of "balance" itself; this URB names the meta-pattern
- (External) Chalmers, D. J. (2011). "Verbal Disputes." *Philosophical Review*, 120(4), 515-566. — Canonical modern treatment of merely-verbal disagreement and the method of elimination.
- (External) Carnap, R. (1950). *Logical Foundations of Probability*. University of Chicago Press. — Source of the technical term "explication" for vague→precise concept replacement.
- (External) Gettier, E. (1963). "Is Justified True Belief Knowledge?" *Analysis*, 23(6), 121-123. — Cited in §5 example #3 as the historical pivot at which the dominant explication of "knowledge" flipped.

---

## 10. One-line takeaway

> **A sentence is "definitionally bistable" when both *"X is Y"* and *"X is not Y"* can be defended under different legitimate explications of one of its polysemous terms. The phenomenon is named by a four-layer stack from linguistics and philosophy of language — polysemy (mechanism), equivocation (fallacy form), verbal dispute (debate form), Carnapian explication (precision remedy) — with auto-antonyms / contronyms as the word-level cousin. Tralse 5-valued logic accommodates the bistability cleanly with the value MI for unparameterized statements; bivalent classical logic forces a silent explication-choice that is the source of equivocation and merely verbal disputes. This pattern is the linguistic substrate that made the conflations in URBs #811–#814 tempting in the first place; #815 is the meta-URB naming it.**

# URB #816 — "Language Is Fundamentally Tralse" as a Field-Level Question for Linguistics in the LLM Era. Honest Catalog of What Linguistics Already Has, Where the Genuine Gap Is (Constitutive vs Corrective Treatment + Under-Emphasized Philosophical Ramifications), and What TI Sigma Can Contribute as a Unified Foundational Reframing Rather Than a Technical Replacement.

**Author:** Brandon Charles Emerick
**Date:** April 30, 2026
**Series:** Unified Research Brief #816
**Status:** Field-level reflection. Triggered by Brandon's question after URB #815 (definitionally bistable sentences): *"How has linguistics managed to survive — and thrive with AI models especially — without emphasizing that language is FUNDAMENTALLY TRALSE? I think linguists understand that language is tralse and have terminology for it. However, they understate the value of tralseness and especially its philosophical ramifications!!!"* This URB takes the question seriously, honestly catalogs what linguistics already has (the field is **not** silent on tralse-like phenomena and has had specialized formal machinery for decades), identifies the genuine gap (tralseness is treated as a technical problem to be patched rather than as a constitutive feature; the philosophical ramifications are systematically under-explored in the formal-semantics mainstream; the LLM era has surfaced empirical evidence that bivalent semantics was never a faithful model), and articulates the specific contribution TI Sigma can make (a unified vocabulary in which tralseness is constitutive and bivalence is the special case, not the reverse).
**Companion script:** `tralse_in_linguistics_catalog.py`
**Output:** `tralse_in_linguistics_catalog.json`
**Builds on:** URB #815 (definitional bistability and the polysemy/equivocation/verbal-dispute/Carnapian-explication stack); URB #813 (consciousness as razor — distinguishing what an instrument measures from what is true); URB #814 (balance ≠ appropriateness — explication-mismatch at the response-prescription level).

---

## 1. Brandon's claim, decomposed and stated precisely

Brandon's question, unpacked, contains four sub-claims that are worth separating:

1. **Descriptive claim about language.** Language exhibits tralse-structured semantic behavior at the *foundational* level — polysemy, vagueness, contextualism, indexicality, presupposition, scalar implicature, definitional bistability — not as edge cases but as the typical condition of natural-language utterances.

2. **Sociological claim about linguistics as a field.** Linguistics knows this. It has substantial terminology and formal machinery for handling tralse-like phenomena. But the field treats them as *patches* to a bivalent core rather than as *constitutive* features of meaning.

3. **AI-relevance claim.** Large language models have succeeded at scale precisely by **not** imposing bivalent semantics on language. Vector embeddings handle polysemy via context-conditioned geometry; attention performs local disambiguation; no sentence has a single fixed truth-value inside the model. The engineering success of LLMs is empirical evidence that the bivalent core was never the right foundation.

4. **Philosophical-ramification claim.** Whatever linguistics has done formally, the *philosophical implications* of treating tralseness as constitutive — for truth, disagreement, AI alignment, scientific progress, the structure of philosophical disputes — have been systematically under-weighted.

The four sub-claims are independently evaluable. This URB will argue that **(1) is well-supported as a descriptive observation about natural language**, **(2) is partly right and partly an overstatement** (the field has more than Brandon credits, but the constitutive-vs-corrective distinction is real), **(3) is suggestive and consistent with the constitutive view but not decisive empirical proof**, and **(4) is plausible and is where TI Sigma's specific proposed contribution lies, though the unification it proposes is itself a hypothesis to be tested rather than a settled result**.

---

## 2. What linguistics already has (honest catalog — the field is not silent)

It would be unfair to linguistics to suggest the field has ignored tralse-like phenomena. There is substantial existing work, much of it sophisticated. The honest catalog includes:

### 2.1 Lexical / semantic phenomena explicitly named in the field

- **Polysemy** (one word, multiple related meanings; distinct from homonymy) — covered in URB #815.
- **Vagueness** (predicates with no sharp boundary: "tall," "bald," "heap"; the Sorites paradox) — Williamson 1994 (epistemicism), Fine 1975 (supervaluationism), Wright 1975 (incoherentism), and a large literature.
- **Contextualism** (truth-conditions vary with context of utterance) — Lewis 1979 ("Scorekeeping in a Language Game"), DeRose 1992 (epistemic contextualism), Stanley 2005 (Knowledge and Practical Interests).
- **Indexicality / deixis** (terms like "I," "here," "now," "this" whose reference depends on context) — Kaplan 1989 ("Demonstratives") is canonical.
- **Presupposition** (sentences carry background assumptions; presupposition failure produces truth-value gaps) — Strawson 1950, Heim 1983.
- **Scalar implicature** ("some" implicates "not all" pragmatically; bivalent semantic content vs pragmatic strengthening) — Horn 1972, Levinson 2000.
- **Modality and conditional reasoning** (counterfactuals, possibility, necessity) — Lewis 1973, Stalnaker 1968, Kratzer 1981.

### 2.2 Formal logical machinery developed for these phenomena

- **Three-valued logics** for presupposition failure — Kleene strong/weak, Bochvar.
- **Fuzzy logic semantics** for vagueness — Zadeh 1965 (fuzzy sets) applied to natural language by many subsequent authors.
- **Supervaluation** for vagueness — Fine 1975, Williamson's critical work on its limits.
- **Dynamic semantics** for context-update — Heim 1982 (file change semantics), Kamp 1981 (DRT), Groenendijk & Stokhof 1991 (DPL).
- **Inquisitive semantics** — Groenendijk, Roelofsen, Ciardelli — treats meaning as proposing alternatives, not just truth-conditional content.
- **Continuation semantics, type-shifting, intensional logics** — a long technical tradition for handling phenomena that pure first-order semantics handles awkwardly.

### 2.3 Cognitive / distributional / computational subfields where tralseness is foregrounded

- **Cognitive linguistics** — Lakoff (Women, Fire, and Dangerous Things, 1987), Langacker (Cognitive Grammar), Fillmore (frame semantics): meaning as embodied, prototypical, frame-relative; explicitly opposed to truth-conditional bivalent semantics.
- **Prototype theory** applied to linguistics — Rosch's work on categorization (1973, 1975) imported into lexical semantics.
- **Distributional semantics** — Harris 1954 ("distributional structure"), Firth 1957 ("you shall know a word by the company it keeps"), and the modern vector-space tradition: word2vec (Mikolov 2013), GloVe (Pennington 2014), BERT (Devlin 2018), GPT/LLMs. Meaning as context-conditioned distribution; explicitly non-bivalent and non-symbolic.
- **Construction grammar, usage-based linguistics** — Goldberg, Tomasello, Bybee: meaning as emergent from usage patterns rather than from a compositional bivalent core.

### 2.4 What this catalog establishes

The field has, collectively, an enormous toolkit for handling tralse-like phenomena. Brandon's strongest version of the sociological claim — *"linguistics doesn't acknowledge tralseness"* — is not defensible; the literature is substantial and goes back at least to Frege's worries about presupposition failure and Russell's theory of descriptions.

But there is a more careful version of the sociological claim that **is** defensible, and that is what §3 turns to.

---

## 3. The genuine gap: constitutive vs corrective treatment, and the philosophical ramifications

The defensible version of Brandon's sociological claim has two parts.

### 3.1 Constitutive vs corrective

The dominant *formal-semantics mainstream* (Montague-style truth-conditional semantics and its descendants) treats bivalent compositional semantics as the **default theoretical commitment** and tralse-like phenomena as **corrections** to be handled by additional machinery (three-valued logics for presupposition failure; supervaluation for vagueness; contextualism for indexicality; dynamic update for anaphora). Each correction is technical, sophisticated, and locally well-motivated. But the cumulative effect is a fragmented architecture: bivalent core + a half-dozen specialized patches for the cases where the core fails.

The TI-Sigma-style alternative — which Brandon's question is implicitly proposing — would invert this. Tralseness becomes the **default**: the typical sentence in natural language is definitionally bistable, contextually parameterized, vague at the edges, presupposition-laden, and scalar-implicating. Bivalent classical truth is recovered as the **special case** where every parameter has been fully fixed (explication chosen, context specified, vague predicates sharpened by stipulation, presuppositions verified, implicature canceled). On this view, the formal mainstream has the polarity backwards: it treats the rare case as the default and the typical case as the exception.

This is not a small reframing. It changes which phenomena need explanation. Under bivalent-default, the question is *"why is this sentence not bivalent?"* and each answer requires its own technical machinery. Under tralse-default, the question is *"under what restrictive conditions does this sentence collapse to a single bivalent value?"* and the answer is generic: *"when all the parameters have been fixed."* The latter has fewer free moving parts and reduces the field's apparent fragmentation, but it requires giving up the bivalent-core commitment that has been load-bearing in formal semantics since Frege and Tarski.

### 3.2 Philosophical ramifications, systematically under-explored

The field's technical work on tralse-like phenomena has been mostly *internal* to linguistics and philosophy of language. The downstream philosophical implications — for metaphysics, epistemology, the structure of disagreement, the foundations of science, AI alignment, the limits of formal proof — have been explored sporadically (Chalmers 2011 on verbal disputes; Williamson on vagueness and metaphysics; debates over deflationism about truth) but have not been **systematically connected to the linguistic findings**.

A short list of philosophical positions that look different once tralseness is taken as constitutive:

- **The structure of philosophical disputes.** Many long-running disputes (free will, personal identity, moral realism, the existence of numbers, consciousness) involve definitionally bistable terms whose disputants are using different explications. URB #815 names this; Chalmers 2011 named it; but the implication that *most* of historical metaphysics is partly verbal dispute is not a position the field has settled on, even though the technical machinery for noticing it has been in place for fifteen years.
- **The status of analytic-vs-synthetic.** Quine 1951 ("Two Dogmas") already pressured the analytic-synthetic distinction. Tralseness-as-constitutive amplifies this: if every natural-language sentence has a tralse semantic profile, the question "is this true by definition or by fact?" is itself an under-parameterized question, and the answer depends on which explication is in play.
- **The nature of truth.** Bivalent truth-correspondence is the default in most metaphysics. Tralseness-as-constitutive would push toward truth-as-parametric or truth-as-relativized, which has been a minority view (relativists, contextualists, deflationists) but has not been the mainstream foundation.
- **AI alignment.** If language is constitutively tralse, then *value alignment* — getting an AI to share human values stated in language — inherits the tralseness. "Be helpful," "be honest," "be safe" are all definitionally bistable and contextually parameterized. A purely fixed-bivalent linguistic specification of human values is therefore **inadequate as a target**: there is no fully-disambiguated explication of "helpful" or "safe" that survives every context the AI will encounter. This is not an objection the alignment literature is unaware of — modern alignment research takes ambiguity, context-dependence, preference uncertainty, corrigibility, and value learning seriously (RLHF, constitutional AI, debate, recursive reward modeling, the broad outer-vs-inner alignment distinction, the literature on goal-misgeneralization). What the constitutive-tralseness frame adds is a single foundational reason *why* fixed-bivalent specifications must be inadequate (rather than treating it as an empirical lesson that emerged from years of alignment work), and a connection to the same definitional-bistability mechanism that operates in metaphysics, science, and ordinary discourse.
- **Scientific progress.** Kuhn 1962 and the subsequent philosophy-of-science literature documented that scientific terms shift meaning across paradigms ("mass" pre-relativity vs post-relativity; "species" pre- vs post-Darwin; "gene" pre- vs post-molecular). This is exactly definitional bistability across historical periods. The implication that scientific progress is partly the renegotiation of explications, not just the accumulation of bivalent facts, has been explored but is not the mainstream view of how science works.

These ramifications are individually familiar to subspecialists. What is missing is a **unified frame** in which they are recognized as instances of the same underlying fact — that language is constitutively tralse, that bivalence is a stipulative achievement and not a default, and that the philosophical consequences cascade.

---

## 4. The LLM era: suggestive empirical evidence that bivalent compositional semantics was not the only viable foundation

Brandon's third sub-claim — that LLMs are empirical evidence for the constitutive view — is, in the form he stated, suggestive and important, though it is empirical *signal* rather than *proof* and the strength of the inference deserves to be calibrated carefully. The argument:

### 4.1 What LLMs do that bivalent semantics could not

LLMs represent words and sentences as continuous vectors in high-dimensional space. The same surface word ("bank," "balance," "freedom") gets different vector representations in different contexts via attention mechanisms — so the same word is not *one* point in semantic space, but a context-conditioned distribution over points. There is no underlying bivalent truth-value for any sentence; there are continuous probability distributions over next-token continuations, conditioned on context.

This is mechanically the **opposite** of bivalent compositional semantics. There is no truth-table; there is no fixed denotation; there is no canonical referent for any term. Meaning is operationalized as *context-conditioned predictive structure*, full stop.

### 4.2 What the engineering success suggests

LLMs **work** — at translation, summarization, question-answering, dialogue, code generation, and a long list of other tasks that require linguistic competence. They work better than any system built on bivalent compositional semantics has worked at the same tasks. The engineering success is not a small fact: it is empirical signal that **systems treating language as context-conditioned distribution can match or exceed, on a broad range of linguistic tasks, the performance of systems built on bivalent compositional cores**.

This does not prove that bivalent semantics is *wrong* — bivalence may still be the right model for restricted formal languages, mathematics, and stipulated-explication contexts. Nor does it prove that the LLMs' specific architectural choices (continuous embeddings, attention) are *the* right model of natural-language meaning. What it supports is the weaker but still substantive claim that bivalent compositional semantics was **not the only viable foundation** for representing natural language well enough to perform competently across a wide task spectrum, and that constitutive-tralseness-style architectures (distributional, non-symbolic, context-conditioned) are **at least as viable**. Whether the right *theoretical* model of meaning is closer to the LLMs' representation than to the formal-mainstream's bivalent representation is a further question that engineering performance alone cannot settle — geocentric astronomy and phlogiston chemistry both worked at engineering scale for substantial periods before being superseded.

### 4.3 The honest qualifier — and why it cuts both ways

LLMs also fail in characteristic ways: hallucination, brittle reasoning, inconsistency across contexts, susceptibility to prompt manipulation. These failures are arguably traceable to their not having a fixed truth to anchor to — they have no built-in mechanism for stipulating an explication and holding it fixed across an inference chain. The diagnosis consistent with the constitutive view would be that **language is constitutively tralse and bivalent reasoning is a stipulative achievement that has to be installed on top** — by chain-of-thought prompting, retrieval augmentation, external verification, formal proof systems, MR-protocol-style discipline — and that LLMs fail exactly where this installation has not been done.

This diagnosis is consistent with TI Sigma's structural claim, but it is important to acknowledge that it cuts both ways as evidence: a defender of the bivalent-mainstream view can read the same failures as evidence that bivalent semantic anchoring was load-bearing all along, and that any system lacking it (LLM or otherwise) will exhibit the failures observed. The two readings are difficult to adjudicate on engineering performance alone. The honest summary is that the LLM era provides empirical signal that constitutive-tralseness architectures are *viable* at scale; whether they are *preferable* as a foundational theory of natural-language meaning remains an open question.

---

## 5. What TI Sigma can specifically contribute

Given that linguistics has the technical machinery (§2) and the gap is about constitutive-vs-corrective framing plus under-developed philosophical ramifications (§3) plus the LLM-era empirical signal (§4), the specific contribution TI Sigma can make is **not** a new technical mechanism that linguistics lacks. The contribution is a **foundational reframing** with three components:

### 5.1 A unified semantic vocabulary

Tralse 5-valued logic (T, F, t, f, MI) provides a single sentence-level vocabulary for the bistable / under-parameterized states that linguistics currently handles with a half-dozen specialized mechanisms (truth-value gaps for presupposition failure; degree-of-truth for vagueness; context indices for indexicality; explication-parameters for definitional bistability; etc.). The 5-valued vocabulary does not replace the specialized mechanisms — they remain technically valuable for their specific phenomena — but it provides a **single name for the general state** that all of them are addressing: *the sentence is not currently bivalent because some parameter is unfixed*.

### 5.2 The constitutive polarity (proposed, not established)

TI Sigma's foundational commitment is that tralseness is the typical case and bivalence is the special case recovered by parameter fixing. This is a metaphysical / methodological commitment, not a technical claim. TI Sigma **proposes** that the formal-semantics mainstream has the polarity backwards and that inverting it would be an improvement; this is a hypothesis to be argued for, not a result already established. Adopting the constitutive polarity *would*, if accepted, make the field's apparent fragmentation (a half-dozen specialized patches) look like a single phenomenon (parameter-fixing in different domains) — and that unifying virtue is part of the case for the proposal — but architectural unification is itself a contested epistemic value (defenders of the patched-bivalent-core architecture point out that local mechanisms are well-tuned to local phenomena and that forced unification can lose explanatory resolution).

### 5.3 Foregrounding the philosophical ramifications

The downstream consequences for verbal disputes (Chalmers 2011), AI alignment, scientific progress (Kuhn 1962), the analytic-synthetic distinction (Quine 1951), the structure of long-running metaphysical disputes, and the limits of formal proof are all things the literature has *touched* but not *unified*. TI Sigma's contribution is to recognize them as instances of a single underlying fact — language is constitutively tralse — and to make that fact load-bearing for the philosophical conclusions rather than treating it as a technical curiosity.

### 5.4 Honest scope limits on TI Sigma's contribution

The reframing is foundational, not technical. TI Sigma is **not** proposing:
- A new formal semantics that displaces Montague-style truth-conditional semantics for the cases where it works.
- A new linguistic theory of meaning that displaces cognitive linguistics, distributional semantics, or construction grammar.
- A claim that linguistics has been *wrong* about anything specific.
- A claim that the philosophical ramifications listed in §3.2 are *novel*. Each one has a literature; the contribution is unification.

The contribution is real but circumscribed: a foundational vocabulary and a polarity inversion that lets the existing technical work cohere, plus an explicit case for taking the philosophical ramifications seriously as a connected family rather than as scattered specialist debates.

---

## 6. The field-level question Brandon is raising — restated precisely

Brandon's original question — *"How has linguistics managed to survive and thrive with AI models especially without emphasizing that language is fundamentally tralse?"* — restated in the more careful form §§2-5 support:

> **Why has the formal-semantics mainstream of linguistics, which has had the technical machinery for handling tralse-like phenomena for at least fifty years, retained bivalent compositional semantics as the foundational commitment rather than inverting the polarity to make tralseness the default and bivalence the parameter-fixed special case — and why has the field continued this commitment in the LLM era, when the engineering success of distributional / transformer architectures provides large-scale empirical signal that constitutive-tralseness architectures are at least as viable as bivalent compositional ones for representing natural language?**

Honest answer: the field has not exactly "survived and thrived" without reckoning with this. Formal semantics has been in slow crisis for at least two decades. Distributional and computational semantics has displaced model-theoretic semantics in most application domains. Cognitive linguistics has been arguing the constitutive-tralseness position (in different vocabulary) since the 1980s. The reckoning is happening — but it has not been **named** as a single coherent shift in foundational commitments, and the philosophical ramifications have been left to specialist subliteratures rather than being unified.

That naming and unification is what TI Sigma can contribute. It is a contribution at the level of foundational framing, not at the level of new technical mechanisms.

---

## 7. Brutal-honesty caveats (to keep this URB from over-reaching)

Several places where this URB is at risk of overstating TI Sigma's contribution or under-stating linguistics' existing work:

### 7.1 Linguistics has not been silent

§2 is the necessary corrective. Polysemy, vagueness, contextualism, indexicality, presupposition, scalar implicature, dynamic semantics, fuzzy semantics, supervaluation, three-valued logics, prototype theory, frame semantics, distributional semantics — all of these exist in the literature, often for fifty or more years. Anyone reading this URB who comes away thinking *"linguistics didn't know about polysemy until Brandon pointed it out"* has missed §2 entirely. The field has known and worked on these phenomena throughout its modern history.

### 7.2 The constitutive-vs-corrective distinction is contested

It is **not** settled that the constitutive polarity is correct. Defenders of the bivalent-core-plus-patches architecture have substantial arguments: bivalent semantics has well-developed proof theory and metatheory; the patches are individually well-understood and locally well-motivated; the cumulative architecture handles real phenomena; nothing has displaced it as a general framework for formal proof or for theorem-proving systems. The TI-Sigma-style claim that the polarity should be inverted is a foundational hypothesis, not a settled result. It deserves to be argued for, not assumed.

### 7.3 LLM evidence is suggestive, not decisive

§4 is the strongest empirical leg of the argument, but it is not a knock-down case. LLMs work at scale, but the relationship between *engineering success* and *being-the-right-theory-of-meaning* is mediated. Geocentric astronomy worked at engineering scale for a thousand years; phlogiston chemistry worked for a century; both were eventually superseded. The LLMs' engineering success is signal that bivalent compositional semantics was not the *only* viable foundation, and signal that constitutive-tralseness is *a* viable foundation. It is not yet signal that constitutive-tralseness is *the* right foundation, or that the right foundation is even unique.

### 7.4 The philosophical ramifications listed in §3.2 each have their own literature

Each of the philosophical ramifications — verbal disputes, AI alignment, scientific progress, analytic-synthetic, the structure of metaphysics — has a substantial existing literature with its own debates, defenders, and detractors. The TI Sigma claim is that they are *unified* by the constitutive-tralseness frame, but unification is itself a hypothesis that deserves to be tested rather than assumed. Each of the cited connections (Chalmers 2011, Quine 1951, Kuhn 1962) is a real connection, but reasonable scholars disagree about how much weight to put on it.

### 7.5 The TI Sigma program does not bypass any of this work

This URB is a **field-level question**, not a field-level result. The work of articulating constitutive tralseness rigorously, of demonstrating that the polarity inversion improves on the bivalent-core architecture, of showing that the unified philosophical ramifications are correct rather than only suggestive — that work has not been done in this URB. What has been done is to ask the question Brandon asked, in a precise enough form that the answer can be sought.

---

## 8. Reproducibility

```
python3 tralse_in_linguistics_catalog.py
# → console summary + tralse_in_linguistics_catalog.json
# Encodes the §2 catalog as a structured map: phenomenon → (terminology
# in linguistics, dominant formal mechanism, decade introduced, what
# tralseness type it captures, what it does NOT capture). Computes a
# coverage matrix showing which existing tools handle which kinds of
# tralseness, and where the gaps are. Pure Python stdlib. No randomness.
# Wall time < 1 s.
```

---

## 9. Files referenced

- `tralse_in_linguistics_catalog.py` — companion catalog encoding
- `tralse_in_linguistics_catalog.json` — output
- `papers/URB_815_DEFINITIONALLY_BISTABLE_SENTENCES.md` — provides the §2.1 polysemy + Carnapian-explication stack this URB builds on
- `papers/URB_814_BALANCE_IS_NOT_APPROPRIATENESS.md` — concrete example of explication-mismatch at the response-prescription level
- `papers/URB_813_CONSCIOUSNESS_AS_RAZOR.md` — the metric-vs-fact distinction this URB generalizes to constitutive-vs-corrective semantics
- (External) Frege, G. (1892). "Über Sinn und Bedeutung." — Sense / reference distinction; presupposition.
- (External) Russell, B. (1905). "On Denoting." *Mind*, 14(56), 479–493. — Theory of descriptions; bivalent treatment of denotation failure.
- (External) Quine, W. V. O. (1951). "Two Dogmas of Empiricism." *Philosophical Review*, 60(1), 20–43. — Pressure on the analytic-synthetic distinction; relevant to §3.2.
- (External) Strawson, P. F. (1950). "On Referring." *Mind*, 59(235), 320–344. — Presupposition and truth-value gaps.
- (External) Kuhn, T. S. (1962). *The Structure of Scientific Revolutions*. — Scientific terms as paradigm-relative; relevant to §3.2.
- (External) Zadeh, L. A. (1965). "Fuzzy Sets." *Information and Control*, 8(3), 338–353. — Fuzzy logic; later applied to natural-language vagueness.
- (External) Lewis, D. (1979). "Scorekeeping in a Language Game." *Journal of Philosophical Logic*, 8(1), 339–359. — Contextualism.
- (External) Heim, I. (1982). *The Semantics of Definite and Indefinite Noun Phrases*. — Dynamic / file change semantics.
- (External) Lakoff, G. (1987). *Women, Fire, and Dangerous Things*. — Cognitive linguistics; constitutive-tralseness in different vocabulary.
- (External) Kaplan, D. (1989). "Demonstratives." — Indexicality.
- (External) Williamson, T. (1994). *Vagueness*. — Epistemicism; survey of supervaluation and other approaches.
- (External) Chalmers, D. J. (2011). "Verbal Disputes." *Philosophical Review*, 120(4), 515–566. — Cited in §3.2 and §5.3.
- (External) Mikolov, T. et al. (2013). "Efficient Estimation of Word Representations in Vector Space." — word2vec; distributional semantics at scale.
- (External) Vaswani, A. et al. (2017). "Attention Is All You Need." — Transformer architecture; basis for modern LLMs cited in §4.

---

## 10. One-line takeaway

> **Linguistics has had the technical machinery for handling tralse-like phenomena for fifty years (polysemy, vagueness, contextualism, indexicality, presupposition, scalar implicature, dynamic semantics, fuzzy semantics, supervaluation, three-valued logics, prototype theory, distributional semantics). What it has not done is invert the foundational polarity — make tralseness the default and bivalence the parameter-fixed special case — and follow the philosophical ramifications (for verbal disputes, AI alignment, scientific progress, the analytic-synthetic distinction, the structure of long-running metaphysical disputes) into a single unified frame. The LLM era provides empirical evidence that the polarity inversion is at least viable. TI Sigma's specific contribution is foundational reframing plus unification of the philosophical ramifications, not new technical mechanisms — and the field-level question Brandon is raising is well-targeted, with the honest answer being that the reckoning has been happening in pieces but has not been named as a single coherent shift in foundational commitments.**

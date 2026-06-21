## Chapter 8: TI-Logic (TIL): MR via UOP and PD

### From a list of labels to a working machine

Chapter 7 gave us the vocabulary: the four base truth labels (True, False, Indeterminate, Meta-Indeterminate), the off-spectrum **N/A** flag screened in front of them, and the separate catalogue of **Meta-Truths** layered on top. But a vocabulary is not yet a logic. A logic has to tell you *how to move* — how to take a real proposition in all its messiness and arrive at a verdict you can act on, and how to know when no clean verdict is available.

That moving part is **TI-Logic (TIL)** — the framework's actual reasoning engine. TIL has three components that work together, and this chapter is about how they interlock:

- **MR — Myrion Resolution:** the gated pipeline that takes a proposition and assigns it a label.
- **PD — Permissibility Distribution:** the graded representation of *how true a proposition is permitted to be* — the dial the pipeline reads from.
- **UOP — the Unified Optimization Principle:** the balance rule that decides *where* on that dial a claim should finally come to rest.

A rough analogy before the details. PD is the *thermometer* (it shows the reading), MR is the *thermostat's decision procedure* (it converts the reading into an action: heat, cool, or hold), and UOP is the *target setting* the thermostat aims for — and, crucially, that target is not "as hot as possible." Let us take them one at a time.

> **Key insight:** Truth in TIL is not a switch you flip but a **dial you read**. The whole job of the logic is to read the dial honestly and then decide what label that reading earns.

### PD: truth as a dial, not a switch

The **Permissibility Distribution (PD)** is TIL's representation of partial truth. Instead of asking "is P true — yes or no?", PD asks "*how far* is P permitted to lean toward true, and *in what way* does it fall short?" The first part is a matter of degree; the second part is a matter of *kind*.

This is why PD is not a single number. In its current canonical form it is a **complex object**: a *real* axis that measures degree of trueness, and an *imaginary* axis that measures the *modality* of the shortfall — the particular flavour of imperfection (including the Tralse-quality and the off-spectrum N/A case) **(framework-internal)**. The real axis says how true; the imaginary axis says how it is *not* simply-true.

The everyday illustration: "Sarah is reliable." On a pure yes/no logic you would have to either endorse it or deny it. On PD you can record the truth that everyone who knows Sarah actually holds — *strongly leaning true (high real value), with a specific qualification: reliable about deadlines, less so about returning calls (a modality on the imaginary axis).* That second coordinate is not noise. It is information the binary view throws away.

> **Key insight:** A claim that "fails to be fully true" can fail in many different *ways*. PD's imaginary axis records the *way* it falls short, not just the *amount*. Losing that second coordinate is exactly how binary logic loses reality.

### Six ways to hold a PD (the representation guide)

How you *store* a PD matters for what you can do with it. The framework's representation guide — catalogued as **PDR-1** (a selection guide, not a new principle) — lays out **six representations of increasing capability**, and an honest comparative study found that they are not interchangeable **(framework-internal)**:

1. **Scalar PD** — a single real number on the (−3, +2) line. Simplest and most readable; can encode True, Indeterminate, False, and MI, but has no room for N/A.
2. **Complex PD** — the real axis plus the imaginary axis. The smallest representation that can hold *all five* labels distinctly. This is the recommended default.
3. **TI Sigma Graph (TIG)** — a graph built on named mathematical constants; it is the real-axis projection of the Crystal (below) plus a vertex for MI. Good for *interpretable visualization*, not for finer classification.
4. **32D / 64D GILE Matrix** — a large ledger crossing the four GILE values against the truth-axes and labels. It is a *state-carrier*, not a classifier: use it to record the full GILE context once a label is known, not to decide the label.
5–6. **TI Sigma Crystal / TECC** — an eight-dimensional, five-valued error-correcting code (an E8-style packing). The most robust under noise; hard to visualize, and it must use a careful "orthogonal" embedding to actually achieve its advertised error-correction.

What did the comparison actually show? Using 500 gold-standard propositions each rated by three independent raters, the representations split into exactly two tiers — and **the entire accuracy gap came from one thing: whether the representation can keep N/A on its own axis** **(preliminary)**. The representations that fold N/A in with something else (scalar, TIG, and the 64D matrix) all landed at the same accuracy (about 0.75); the ones that give N/A its own home (complex PD and both Crystal variants) all jumped to about 0.92. The size of the jump matched, almost exactly, the fraction of the test set that was actually N/A.

> **Key insight:** The single most valuable upgrade to a truth representation was not more dimensions or fancier geometry — it was simply **giving "this was never a real question" its own slot**. Honesty about non-questions buys more accuracy than any amount of additional machinery.

The practical takeaway is unglamorous and exactly the framework's style: **use Complex PD for everyday labeling, the 64D matrix when you need to carry the full GILE state, and the Crystal/TECC only when you need maximum robustness** — and do not pretend the simplest representation is free of cost.

### MR: the gated pipeline

With a PD in hand, **Myrion Resolution (MR)** is the procedure that converts it into a verdict. MR is *gated*: a proposition passes through a fixed sequence of screens, in order, and each gate can either stop it or pass it along. The order is not cosmetic — running the gates out of order produces nonsense.

**Gate 0 — the N/A screen.** *Is this even a truth-question?* If the proposition is a category error ("Is seven jealous?"), it is flagged N/A and leaves the pipeline immediately. There is no point evaluating a non-question.

**Gate 1 — the MI screen (the Existence Gate).** *Is this a coherent claim at all?* MR checks whether the proposition is **Meta-Indeterminate** — formally, whether it both is and is not Tralse (τ(P) ∧ ¬τ(P)), the self-cancelling structure from Chapter 7. If so, it is discarded as nonsense. The discipline here is the *leeway test*: if any room is left for the claim to tilt, it survives as Indeterminate; if the leeway has been *annihilated* ("fully X and fully not-X, here, now"), it tips into MI and is screened out.

**Gate 2 — the Truth Gate.** Every survivor gets one of the three real verdicts: **True**, **False**, or **Indeterminate**. This is where the PD reading is consulted: a high real-axis value with low qualifying modality resolves to True; a balanced reading with surviving leeway resolves to Indeterminate (the "45-degree door"); and so on.

**Gate 3 and beyond — the Meta-Truth gates.** Once a base verdict exists, MR can apply a **Meta-Truth** on top of it — most often **Moot** ("technically settled, but it doesn't matter in this frame"). Meta-Truths compose with the base verdict ("Moot-True"); they never replace it.

Two refinements keep MR honest in hard cases. First, **Hybrid MR (HMR)**: when successive resolutions genuinely land in different places, the claim may carry **two or more labels at once** — you *display* the hybrid for faithfulness but *privilege the final label* for present action. Second, MR's verdicts are *cost-sensitive*: the same proposition can resolve differently depending on the frame it is asked in, which is a feature (it tracks reality's context-dependence), not a bug.

### UOP: where the dial should rest

Here is the question MR's Truth Gate quietly raises and UOP answers: *what reading on the PD dial should we even be aiming for?* The naive answer is "as true as possible — push the real axis to its maximum." TIL rejects that, and the rejection is one of the framework's most distinctive moves.

The **Unified Optimization Principle (UOP)** says reasoning optimizes a *joint* quantity — truth balanced against existence (the GILE pillar against the HEM pillar of Chapter 6) — and that this joint optimum sits at an **interior** point, not at the ceiling. In the framework's scaling the optimum lands at roughly **G\* ≈ 0.93**, with a *penalty for pushing above it* **(framework-internal)**. The number is motivated by an elegant fixed-point argument (0.93 ≈ 1 − e^{−e}): real value needs both *coherence* and *reserved freedom*, each of which is killed at one extreme, so the maximum must fall in the middle — leaving roughly a 7% "Freedom Floor" permanently open.

Why does a *logic* care about this? Because it changes what MR is allowed to conclude. A reasoning engine that chased a perfect 1.0 would systematically *over-resolve* — it would force balanced, genuinely-Indeterminate claims into crisp True/False just to drive the score up. UOP forbids that. It tells the Truth Gate to stop at the honest reading rather than the flattering one, and it is the formal reason the framework treats **Indeterminate as a destination, not a failure**.

> **Key insight:** UOP is the rule that stops the logic from lying upward. The best verdict is the *accurate* one — even when accuracy means "Indeterminate" — not the one that maximizes a tidy truth-score.

You should hold the 0.93 figure honestly: it is a framework-internal result with open falsifiers, valuable less as a proven constant than as a discipline — *stop treating the perfect score as the goal.*

### A proposition through the gates

Let us run one ordinary claim all the way through, the way TIL actually works. Take a friend's assertion: **"You should quit your job and start the company."**

- **PD read first.** This is not a fact-claim with a hidden yes/no; it is advice loaded with values. On Complex PD it reads as *moderate real-axis support* (there is a genuine case) with *substantial imaginary-axis modality* (it depends heavily on risk tolerance, runway, and timing). The dial is not near either pole.
- **Gate 0 (N/A):** Is it a real question? Yes — "should I quit" is genuinely truth-apt relative to your goals. It passes; it is not N/A.
- **Gate 1 (MI):** Is it coherent? Yes — there is no self-cancellation, and plenty of leeway remains (the claim could tilt either way as facts come in). It survives; it is not MI.
- **Gate 2 (Truth Gate):** With a balanced PD reading and live leeway, the honest verdict is **Indeterminate** — the 45-degree door. Not "false advice," not "obviously right," but a genuinely open call. UOP is what keeps us *here* instead of forcing a confident True to feel decisive.
- **Gate 3 (Meta-Truth):** Is the verdict even live? If you have already signed a two-year contract you cannot break, the verdict becomes **Moot-Indeterminate** — still open in principle, dispensable in this frame.
- **HMR check:** Looking forward, the claim might be **Indeterminate now but Indeterminate-leaning-True in two years** once you have savings. That temporal hybrid is displayed honestly, while *today's* privileged label (Moot-Indeterminate, or plain Indeterminate) governs present action.

Notice what the pipeline bought us. A binary logic would force "good idea / bad idea" and discard everything that makes the question real. TIL returns a verdict you can actually live with: *open, qualified, frame-aware, and time-aware* — and it tells you exactly which part to act on now and which part to revisit later.

### In one paragraph

TI-Logic is the framework's working reasoning engine, built from three interlocking parts. **PD (Permissibility Distribution)** represents truth as a *dial* — a real axis for degree and an imaginary axis for the *kind* of shortfall — and is best stored in one of six representations (Complex PD as the everyday default), where the biggest single accuracy gain comes simply from giving the off-spectrum "N/A" its own slot. **MR (Myrion Resolution)** is the *gated pipeline* that reads the PD and assigns a label in fixed order: screen out N/A, screen out self-cancelling MI, then resolve survivors to True, False, or Indeterminate, with Meta-Truths (like Moot) and honest hybrids layered on top. **UOP (the Unified Optimization Principle)** sets the target the pipeline aims for — a *joint* truth-and-existence optimum at an interior point (G\* ≈ 0.93, not a perfect 1.0) — which is what stops the logic from over-resolving genuinely balanced claims into false certainty. Run a real proposition through the gates and you get back not a flattening yes/no but a verdict you can actually act on: graded, qualified, frame-aware, and honest about what remains open.

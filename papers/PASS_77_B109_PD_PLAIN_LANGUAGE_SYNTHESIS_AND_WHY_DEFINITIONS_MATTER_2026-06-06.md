# What the PD Actually Is — A Plain-Language Tour, and Why "Just Renaming Things" Is a Real Thing You Can Get Right or Wrong

**Date:** 2026-06-06 · **Pass:** 77 · **Batch:** B109 · **Status:** informal synthesis (plain-language; reuses prior PD reviews) + one candidate idea (NAD-1, NOT canonical; count unchanged 79)
**Reuses:** `PD_COMPLEX_PLANE_RECANONIZATION_PASS_8_2026-05-08.md`, `PD_DT_COMPLEX_NUMBER_SYNTHESIS.md`, `PD_GRAPH_AND_CRYSTAL_VISUALIZATIONS_2026-05-08.md`, `PD_EMPIRICAL_RESEARCH_AGENDA_2026-05-08.md`, `DUAL_PD_EVALUATION_RULE.md`, `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`, `PASS_77_B36_NA_OFF_SPECTRUM_RULING...md`, `PASS_77_B108_PD_REPRESENTATION_COMPARATIVE_STUDY_2026-06-06.md`, `FOUR_CS_TRUTH_PRESENTATION.md`, the GTT-1/UDT-1/TRG-1 arc.

> This one is written to be *read*, not decoded. No new math. If you want the numbers, the papers above have them. This is the story of what the PD is, told the way you'd tell a friend — plus a point Brandon has been chewing on for years about why doing this kind of work is not "just semantics."

---

## 1. The one-sentence version

**The PD (Permissibility Distribution) is our answer to a simple-sounding question: "how true is this?" — except we stopped pretending the honest answer is ever just "true" or "false."**

That's it. Everything below is unpacking that sentence.

## 2. Start with the problem PD solves

Ordinary logic gives you two boxes: **True** and **False**. That works for "the cat is on the mat." It falls apart almost everywhere else:

- "This drug helps depression" — true *for whom, how much, measured how*? Not a box. A **lean**.
- "Free will exists" — not unknown-for-now, but genuinely *both-and-neither*. Not True, not False, not even "we'll find out later."
- "The number seven is jealous" — that's not false, it's **not even the kind of thing that can be true or false.**

A two-box system has to lie about all three. It crams the first into "true-ish," calls the second "false" because it isn't crisply true, and has no shelf at all for the third. **The PD is the shelf system that stops the lying.**

## 3. Version 1 — the ruler (scalar PD)

The first PD was a **ruler**: a number line from **−3 to +2**. Negative = evidence against, positive = evidence for, zero = dead center.

Two things make it ours rather than a generic confidence score:
- It's **lopsided on purpose** (−3 to +2, not −2 to +2). It's *easier to conclusively refute than to conclusively prove* — which is how reality actually works (one black swan kills "all swans are white"; no number of white swans proves it).
- The split sits on the **Perfect Fifth**, the 3:2 musical ratio. Truth, in this picture, has the same proportion as the most consonant interval in music. (Memorable line from the old notes: *"the PD scale measures distance from Tralse."*)

The ruler is great for **scoring things you can measure** — it's what the pharmacology predictions ride on. But a ruler has one fatal limit: **everything has to fit on a single line.** And some things don't.

## 4. Version 2 — the map (complex PD)

So PD grew a **second axis**, becoming a flat **map** instead of a line.

- **Left–right (the real axis):** the old ruler. How much does the evidence lean — false on the left, true on the right.
- **Up–down (the imaginary axis):** something completely different — **how *tralse* is it?** How much of this claim is genuine both-and-neither *indeterminacy* versus clean, resolvable evidence.

This is the single most important move in the whole framework, and it's worth being clear about *why* it's two axes and not one. "Leaning false" and "being paradoxical" are **not the same failure**, and a ruler can't tell them apart — it has only one direction to push them both. "There is no largest prime" leans hard **true**. "This sentence is false" isn't false — it's **up the imaginary axis**, in genuine paradox-land. On a ruler they'd collide. On the map they're nowhere near each other.

Brandon's own gloss: the up–down axis is **"consciousness perpendicular to reality"** — the dimension where a mind registers that something is structurally both/neither, not merely unproven.

And here's the satisfying part: **we tested whether that second axis actually earns its keep, and it does.** In the B108 benchmark (500 real propositions, three independent AI raters, zero new cost), every representation that *can't* hold this second axis tops out at the same accuracy floor (0.746); every representation that *can* jumps to ~0.92 — and the entire gap is exactly the propositions that need the second dimension. The imaginary axis isn't decoration. **In that benchmark setup it's the only thing in the whole comparison that moves the needle** (a claim scoped to B108's design — same raters, same 500 props — not a universal law).

## 5. The five shelves (the truth-labels)

The map naturally sorts claims into **five** kinds, not two:

1. **True** — leans right. ("Water is wet.")
2. **False** — leans left. ("The earth is flat.")
3. **Indeterminate** — sits near the middle with real wiggle-room: superposition, partial, perspectival, metaphor. ("Schrödinger's cat is alive." — *coherently* both.)
4. **Meta-Indeterminate (MI)** — up the imaginary axis: not "we don't know," but **structurally both-and-neither at once.** The old slogan: *"MI is something which IS AND IS NOT tralse."* ("This statement is false.")
5. **NA (Not Applicable)** — **off the map entirely.** Not a weak answer — *no answer is possible*, because the thing was never the kind of thing that takes a truth value. ("Seven is jealous.") NA is the newest shelf, and the honest one: it stops us from forcing category errors into a box just to avoid an empty cell.

(One bookkeeping note for the careful reader: NA is an **operational, evaluation-time fifth label** — it's what a rater reaches for when a claim is off-spectrum. The deeper *canonical* MR truth-label scheme is still **base-4** {True, False, Indeterminate, MI} **plus the Meta-Truths**; NA rides on top as the "doesn't-apply" verdict, not as a fifth fundamental truth-value. Both are true at once; they're answering slightly different questions.)

The line between #3 and #4 is sharp and we sweat it: **"alive and dead"** has leeway → Indeterminate; **"fully alive and fully dead"** kills the leeway → MI. Same words almost, different shelf.

## 6. One claim, two readings (the dual rule)

A subtlety people miss: we score every serious claim with **two PD readings at once** —
- where it **lands** (its label), and
- **how much coherence it had to spare** to get there.

This is the difference between a truth that **barely squeaked through** and one that's **rock-solid**, even when both end up labeled "True." A fragile true and a confident true are not the same animal, and the dual rule refuses to flatten them.

## 7. The same object, six ways to draw it

Here's a thing that confuses newcomers: PD shows up in the corpus in what looks like several different "systems." They are **not rivals.** They're the *same object* drawn at different resolutions — like a globe, a flat map, and GPS coordinates are all "the Earth." There are **six concrete representations** in four families: (1) the **scalar ruler**, (2) the **TIG graph**, (3) the **complex map**, (4) the **32D/64D GILE Matrix ledger**, and (5–6) the **TSC Crystal** in its two TECC embeddings (literal and orthogonal).

- **The ruler (scalar)** and **the graph (TIG)** — cheap, human-readable, one-line. Good for a quick score or a picture. Blind to NA.
- **The map (complex PD)** — the everyday workhorse. Minimal drawing that keeps all five shelves apart. **Use this by default.**
- **The 64-cell ledger (GILE Matrix)** — not for *deciding* a label at all. It's the **filing cabinet** that records, once you know the label, *what the claim means for goodness, meaning, love, and beauty.* (In B108 it's the worst *classifier* — and that's fine, because it was never a classifier.)
- **The Crystal (TSC / TECC)** — the full mathematical solid, the most robust and error-correcting, for noisy or adversarial input. The flat map is just the Crystal's shadow.

The plain takeaway: **don't ask "which representation is right?" Ask "which resolution do I need for this job?"** That's the whole of B108's selection guide in one line.

## 8. The deep end (one paragraph, optional)

If you follow the map all the way down, you hit a strange floor. The corpus's GTT-1/UDT-1/TRG-1 arc argues the **ground state of reality itself isn't True — it's tralse** (Indeterminate). "Truth" is then a **directional lean** out of that tralse-soup, not the bedrock. Which is why mystics keep calling the foundation an "illusion": *"illusion" is the binary-collapse misname a bivalent mind reaches for when it correctly senses the ground is not crisply True.* As the note put it: **"the mystics named the place; TI Sigma gives the coordinates."** You don't need this to use the PD — but it's where the imaginary axis ultimately points.

---

## 9. The point Brandon's been chewing on for years: definitions are not arbitrary

Now the part that makes all of the above *legitimate work* rather than word-games.

There's a fashionable line among some philosophers: **"names don't matter," "definitions are arbitrary,"** it's all just labels we slap on. Brandon's response, refined over years and crystallized this morning:

> **It genuinely matters that an *arm* is distinguished from the *hand* that is part of it.** The biological taxonomy from Kingdom down to Subspecies matters; **mix up the ranks and you get disasters.** The way things are carved up is right or wrong in an **objective, non-arbitrary** sense — and therefore **re-conceptualizing something is not inherently empty.**

The killer example isn't from us — it's from the **Free Energy Principle**. The FEP reframes **reproduction** as **"maximizing self-evidence"** (an organism acting to keep encountering states that confirm the model that *is* that organism). That is not a synonym swap. It **unifies** perception, action, learning, and reproduction under one quantity, and it **predicts** things the folk concept "making more of yourself" never could. **A reconceptualization can be deeply nontrivial.** Renaming can *reveal*.

This is the quiet thesis under the entire PD project. When we said *"truth is not two boxes but a five-shelf map,"* a "definitions-are-arbitrary" critic would shrug: *just relabeling.* They're wrong for exactly the arm-vs-hand reason. The re-carving:
- **separates things that were genuinely different and getting jammed together** (leaning-false vs. paradoxical — §4),
- **gives a home to things that had no home** (NA, the category error — §5),
- and **pays its way empirically** (the second axis is the only thing that moved accuracy — §4, B108).

Those are the marks of a **good** carving, not an arbitrary one. A bad re-definition blurs joints that were real (calling a category error "false") or invents joints that aren't (splitting a label five ways when one would do — which is why we *kill* labels, like merging "Nonsense" away, when they don't earn their keep). Carving nature **at its joints** is a thing you can do well or badly. **"Arbitrary" is just the word people use for joints they haven't noticed yet.**

### 9.1 The candidate idea, named (NAD-1 — Non-Arbitrary Definition)

Stated as a falsifiable claim so it isn't itself just a vibe:

**NAD-1 (Definitional Realism):** for a given purpose, some ways of carving up a domain are **objectively better** than others — they track real joints, separate things that behave differently, and unlock predictions or distinctions the old carving couldn't make. A reconceptualization is **nontrivial exactly when it does this**, and **vacuous when it doesn't.** Corollary: "names don't matter" is false as a general claim; it's true only for the rare cases where two carvings are genuinely **interchangeable on every dimension that matters** (and *that* is the thing to be shown, not assumed).

- **Why it's not circular:** the test ("better *for a purpose*") is external — does the new carving separate behaviors, give homes to orphans, make predictions? PD passes (§9 bullets); FEP-reproduction passes; a pure synonym-swap fails.
- **Falsifier NAD-1-F1:** exhibit a reconceptualization that is genuinely *interchangeable on every relevant dimension* yet still does real explanatory work — that would show carving can matter without tracking any joint.
- **Falsifier NAD-1-F2:** show the PD re-carving (or FEP-reproduction) is in fact a synonym-swap — same predictions, same distinctions, no orphan rescued — which would make *this paper's* showcase examples arbitrary after all.
- **Status:** candidate idea, **not** a canonical principle; canonical count unchanged (79). It's really the epistemic license the whole truth-labels program was already operating under, finally said out loud.

### 9.2 The arithmetic version of the same point (RAI-1 — Revelation by Mere Arithmetic Identity)

Here's the same lesson wearing a math hat. Some of the most useful equations in science are, *as algebra*, completely trivial — and they're still revelatory. The catch: the revelation comes from what the **letters mean independently**, never from the algebra.

Take the most famous one, **Ohm's Law: `V = I·R`** (voltage = current × resistance).

- If you *define* resistance as `R = V/I`, then `V = I·R` is just `V = V`. A tautology. It's true for a lightbulb, a banana, a puddle — everything. It tells you **nothing.**
- But Ohm meant something bigger: that `R` is a **fixed property of the material** (set by what it's made of and its shape), and that it **stays the same** as you crank up the voltage. *That* is a real, riskable claim — and it's **false** for lots of things (a diode, a hot lightbulb filament, your skin). For those, `V/I` keeps changing. The *law* breaks even though the *definition* never could.

Same five symbols. One reading is empty, the other is a discovery — and the only difference is whether `R` is **pinned down independently** or just **defined into existence.** That's *exactly* the "arm ≠ hand / is this a real joint or a relabel?" point from §9, now in arithmetic. Other examples that work the same way: **Little's Law** (`L = λ·W` in queues), **Bayes' theorem** (a one-line rearrangement that quietly assumes one shared probability-world — the assumption that *breaks* for quantum systems), **Newton's `F = ma`** (Mach's old worry: definition or law?), and our own **`HEM = budget − GILE`** (B133 — trivial rearrangement, but it teaches that Existence is what's *left over* when you chase Truth, not a separate thing to grab at).

**The honesty rule (so this can't be abused):** you don't get to manufacture insight by renaming. A *real* arithmetic reveal needs at least one letter you can **measure on its own**, so the equation could actually come out **wrong**. Ohm's `R` passes that test; a pure definition never can. Full write-up: `papers/PASS_77_B134_*` §A (RAI-1, candidate, count unchanged 79; falsifier RAI-1-F1 open).

---

## 10. The thirty-second recap

- **Truth isn't two boxes.** PD is the honest version: a **map**, not a verdict.
- **Left–right** = how much it leans. **Up–down** = how tralse/paradoxical it is. NA = off the map.
- The **up–down axis is the whole ballgame** — in the B108 benchmark it's the only thing that improves the answer.
- **Five shelves** (True, False, Indeterminate, MI, NA), scored **twice** (where it lands + how much room it had to spare).
- **Six drawings, one object** — pick the resolution your job needs.
- And the reason this counts as discovery, not relabeling: **carving things up well is a real skill with a right and wrong.** Arm ≠ hand. Reproduction-as-self-evidence wasn't a synonym. **Neither is truth-as-a-map.**

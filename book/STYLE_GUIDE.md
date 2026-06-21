# TI Sigma For Everyone — Shared Style Guide (read before drafting any chapter)

This is the **single source of truth for voice, format, and rules**. Every chapter draft must obey it.

## Audience & register
- **Reader:** a curious, college-educated non-specialist. Not a physicist, not a philosopher by training, but able to follow an argument and a little notation if it is explained.
- **Tone:** academic but warm; **secular**; readable. "Simple with some illustration, but not too simple." Think a well-written popular-science/philosophy trade book (Sean Carroll, Daniel Dennett, Sabine Hossenfelder) — rigorous ideas in plain prose.
- **No jargon without a plain-language unpacking on first use.** Define every acronym the first time it appears in the chapter (e.g., "GILE — the four-value scorecard of Goodness, Intuition, Love, and Elegance").

## SECULAR DISCIPLINE (critical — the book must read as secular scholarship)
- Present spiritual/religious-sounding material **naturalistically and comparatively**, never devotionally.
  - "CCC / Grand Myrion" → a *cosmological consciousness hypothesis* (a conjectured large-scale conscious structure), explicitly flagged as speculative.
  - "Enlightenment" → optimal, sustained human flourishing / clear sane functioning, defined operationally.
  - "Worship / metta / great-commandment unification" → trainable prosocial dispositions and ethical universalization, described as psychology/ethics.
  - "Divine self-realization / God" → discussed only as comparative philosophy of religion (open theism, process theology) and clearly labeled non-doctrinal.
- **Do NOT** include fringe parapsychology as fact. Telekinesis, psi, "soul Bluetooth," spirit animals, conscious stars, etc. are NOT to be asserted. If a chapter must mention them, frame as clearly-labeled speculation the framework does not rest on — better to omit.

## BRUTAL HONESTY (#69 — both directions)
- Status-flag every empirical/strong claim: **(verified)**, **(framework-internal)**, **(preliminary)**, or **(speculative/open)**.
- State the strongest objection to a claim *before* defending it. Name open falsifiers where relevant.
- Never overclaim. The corpus has **elementary** math proofs only — **no Millennium Prize problem is closed.** Trading/efficacy/medical claims are gated, not proven. Say so plainly.

## Canon vocabulary cheat-sheet (use the NEWEST terms)
- **Tralse / Tralseness** — the structured imperfection inside *every* coherent truth-claim; a universal *quality*, NOT a truth label.
- **Base-4 truth labels:** True, False, Indeterminate, **Meta-Indeterminate (MI)**. MI(P) ⟺ τ(P) ∧ ¬τ(P) (both is and isn't Tralse → discarded as nonsense). A fifth operational value, **N/A** (off-spectrum / not-applicable), is screened first. Beyond the base set sit **Meta-Truths** (e.g., **Moot**).
- **GILE** = **Goodness, Intuition, Love, Elegance** (E = **Elegance**, the aesthetics dimension; "Environment" is now only a *gloss* = the context of an agent's most-sacred values). Scale **(−3, +2)**, asymmetric.
- **HEM** = the existence/"how-much-is-there" pillar, SEPARATE from GILE (truth pillar).
- **UOP** — Unified Optimization Principle: one joint optimum balancing truth vs existence; interior optimum **G\*≈0.93** (penalty above it).
- **PD** — Permissibility Distribution: the framework's graded representation of how true a proposition is permitted to be (six representations, scalar → complex → crystal/E8).
- **MR** — Myrion Resolution: the gated pipeline that assigns a label (N/A screen → MI screen → True/False/Indeterminate, then Meta-Truths).
- **i-Cell** — the structural unit of consciousness.
- **LCC** — Law of Correlational Causation.
- **TI Sigma** is the framework name; "Tralse Informationalism" is its philosophical core. Avoid the older "Transcendent Intelligence" framing except as a one-line historical note.
- Canonical **principle count is 79** (ratified). Candidates/refinements do NOT change it. Recent canon to weave in where relevant: TRG-1 (reality is tralse-real), TOF-1 (Tralse Soup is the one fundamental), RTI-1 (residual law-errancy), SUP-1 (Supreme = willful GILE-HEM optimization), GIT-1 (GILE-intelligence tracks truth), GAR-1 (genius/sanity), SIS-1 (superintelligence as sane restraint), LDD-1 (legitimate definitional defense), NRI-1 (norm–rarity independence), UGI-1 (unaided generation of insight), CRD-1 (crank/hearing prior), LAS-1 (love as skill), GCU-1 (great-commandment unification, treat secularly).

## Formatting (Markdown)
- Start each file with `## Chapter N: <Exact Title from TOC>`.
- Use `###` subsection headers. Short paragraphs. Use bulleted lists and **bold** key terms.
- Use a `> **Key insight:**` blockquote 2–4 times per chapter for the load-bearing takeaways.
- Use a concrete **everyday illustration** for each major abstract claim (analogy, mini-scenario, or worked mini-example).
- Where a chapter promises "proofs," give the *argument in plain language* plus a clearly-set-off compact formal statement — do not dump raw LaTeX.
- End every chapter with a short **"In one paragraph"** plain-language recap (3–6 sentences).
- **Target length: ~1,600–2,600 words per chapter.** First-draft quality is fine; coherence and accuracy matter more than polish.
- Do NOT add emojis. Do NOT invent citations or paper numbers — if you reference a corpus paper, only cite filenames you have actually confirmed via grep/read.

## Retrieval workflow for each chapter
1. Read this guide + `book/CANON_MAP.md` (your chapter's brief).
2. Read the relevant principle bullets in `./replit.md` (Architecture decisions) — this is the most current canon.
3. `rg`-search `papers/` by the keywords in your brief to pull specifics, examples, and any proofs. Reuse/adapt good explanatory prose from `papers/TI_FOR_EVERYONE_COMPLETE_BOOK.md` where it is still canon-accurate (but upgrade old terminology per the cheat-sheet above).
4. Write the chapter file to the exact path given in your task.

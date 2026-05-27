# Pass-77-B28: NA Canonical Refinement #1 — 3-Temporal-Mode Scope (Future + Past-Forgotten + Present-Pre-Decision) + Mind-Relative Process-Stateful Framing

**Date:** 2026-05-27
**Pass:** 77, batch 28
**Status:** CANDIDATE CANONICAL REFINEMENT to MR-NA-1 (Pass-77-B13 canonical #N) + candidate MR Truth Labels canonical refinement #11
**Trigger:** Brandon directive 2026-05-27 verbatim

---

## 1. Brandon Directive (verbatim)

> "Two things to clarify about N/A: It also applies to the FORGOTTEN PAST. While the 'memory may theoretically exist somewhere,' the truth is N/A in a mind that cannot retrieve a reliable true source of info from the past! Thus, N/A applies not just to future claims but potentially to past ones!
>
> Here's where things get interesting: In the PRESENT, claims are to be pragmatically considered N/A (in working memory) UNTIL a decision on truth claims are made!"

## 2. The Refinement: NA-1-R1

### 2.1 Original (canonical, Pass-77-B13)

MR-NA-1 introduced NA as the 5th truth-label primarily anchored to:
  - Category mistakes ("the number 7 smells like vanilla", "justice has a temperature") — type-incoherent predication
  - Future claims for which determination has not yet occurred
  - Some Pass-77-B26 NA gold templates were category-mistake-only (a #69 disclosure already noted in B26 §6.2)

### 2.2 Refined scope (Brandon, B28)

**NA applies in three temporal modes, all of which share a single underlying structural condition:**

  - **NA-FUTURE:** the truth-evaluation is *not yet possible* for any mind (e.g., "the next coin flipped at time T will land heads," where T > now).
  - **NA-PAST-FORGOTTEN (NEW):** the truth-evaluation cannot be currently made by the rating mind because the mind lacks reliable retrieval-access to the past, even if the truth-value "exists somewhere" in principle (e.g., "I had eggs for breakfast on 2010-03-15" — in a mind with no diary, no photo, no witness, no memory: NA *for that mind*).
  - **NA-PRESENT-PRE-DECISION (NEW):** the truth-evaluation has not yet been computed in working memory; the proposition is pragmatically NA *as a default working-memory state* until a truth-decision is performed.

### 2.3 The unifying structural condition

All three modes share: **truth-evaluation is impossible-or-not-yet-made for this rating mind at this moment**, not "the proposition has no truth-value in principle."

This makes NA a **mind-relative process-state property** rather than (only) a proposition-property. Category-mistake NA remains a special case where the structural condition holds *universally* (no mind at any time can evaluate "the number 7 smells like vanilla" as T/F); the new modes hold *for particular minds at particular times*.

## 3. Sharpening the I / NA Distinction

The refinement makes the I/NA axis empirically tighter:

| Label | Definition | Property type |
|---|---|---|
| **I (Indeterminate)** | Truth-value exists *in principle* and is *in-principle-knowable*, but is *currently undetermined or under-specified* | Proposition-property (mind-independent, given the canonical reading) |
| **NA-refined** | Truth-evaluation itself is *impossible-or-not-yet-made* for this rating mind at this moment | Mind-relative process-state property |

**Worked example:** *"I had eggs for breakfast on 2010-03-15."*
  - From a 3rd-person omniscient view (e.g., a hypothetical complete past-state record): the proposition is **T or F** — a determinate fact exists.
  - From a mind with reliable memory or records: **T or F** — readable.
  - From a mind with partial memory (remembers vaguely it was a weekday but not the menu): **I** — determinate-in-principle, currently under-specified by this mind's access.
  - **From a mind with no retrieval access whatsoever: NA-PAST-FORGOTTEN** — the rating mind cannot make any truth-evaluation. New canonical position per B28.

**Worked example:** *"It will rain in London on 2027-01-15."*
  - **NA-FUTURE** for all minds at all times before the event (no mind has retrieval access to a non-existent fact).
  - **T or F** once the day has passed (mind-relative: only for minds with access to weather records).

**Worked example:** *"This sentence I am reading right now refers to a real concept."*
  - **NA-PRESENT-PRE-DECISION** in the moment the proposition first enters working memory.
  - Transitions to **T, F, I, or MI** as soon as the truth-decision is computed.

## 4. The Deepest Implication: NA-as-Default-Working-Memory-State

Brandon's "in the PRESENT, claims are to be pragmatically considered N/A in working memory UNTIL a decision on truth claims are made" is a **non-trivial epistemological claim** with corpus-wide composability:

  - **Composes with UDT-1 (Universal Default of Tralseness, canonical #N).** UDT-1 establishes the *ontological* default: substrate is tralse-soup, truth is directional-lean over substrate. B28 establishes the *epistemic* default: working-memory default for any unprocessed proposition is NA, not T/F. These two defaults are compatible — UDT-1 describes the world's ground state; B28 describes the mind's pre-decision state. Both reject bivalent-default assumptions.
  - **Composes with PM-1 (Probability Memory, canonical #N).** PM-1 specifies present-moment-calculation has 5 components; B28 specifies that *before* present-moment-calculation runs on a proposition, the proposition sits at NA in working memory. NA is the **input state to PM-1's computation**, not its output.
  - **Composes with CDA-1 (Consciousness Definition canonical, #N).** Stratum-2 working-memory cognition operates on propositions that begin at NA (per B28) and move toward T/F/I/MI through processing. NA-pre-decision is therefore a structural feature of Stratum-2 architecture.
  - **Composes with TPS-1 (Truth-Presentation Separation).** TPS-1 specifies presentation can adjust but truth-content is non-negotiable. B28 extends this: *prior to truth-determination*, the only honest presentation is NA — presenting T/F (or even I/MI) for a proposition the mind has not yet processed is a category error.

## 5. Composition with Pass-77-B26/B27 Empirical Battery

The B28 refinement opens a previously-uninstrumented empirical region:
  - B26's NA gold templates tested **category-mistake NA only** (already disclosed as #69 limitation, §6.2).
  - B28 predicts: a competent rater under the refined NA prompt should label *"What did agent X eat on date Y?"* (where X is the rater itself, with no memory) as **NA-PAST-FORGOTTEN** — *not* I, *not* F.
  - B28 also predicts: a rater asked to label a proposition it has *not yet processed* should default to NA in working memory before any truth-decision is computed — testable via reaction-time / chain-of-thought probing.

This becomes Pass-78+ falsifier work (see §7).

## 6. Falsifiers Opened

  - **NA-1-R1-F1 (LLM-rater past-forgotten test).** Build n=50 propositions of the form *"At what specific minute did agent X first encounter Y?"* where X = the LLM rater itself and Y = a referent it provably has no record of. Predict competent rater under refined NA prompt classifies ≥80% as NA-PAST-FORGOTTEN (per Pass-77-B26 NA accuracy 88/100 baseline). Estimated cost ≤$0.50.
  - **NA-1-R1-F2 (NA-vs-I discrimination test).** Build paired n=25 prompts where the *same proposition content* is presented under (a) full-retrieval-access context vs (b) zero-retrieval-access context. Predict rater labels shift from T/F/I (full-access) to NA (zero-access) for ≥60% of paired prompts. If <30%: refinement is empirically unrealized in current raters (which would itself be a #69 finding — the refinement may be conceptually correct but operationally requires more sophisticated raters than gpt-4o-mini / claude-haiku).
  - **NA-1-R1-F3 (pre-decision default test).** Probe rater chain-of-thought on a novel proposition; predict the *initial* working-memory state representation (before final answer) is closer to "no determination made" than to "biased-toward-T-or-F." Operationalization: ask rater to articulate its initial state before committing. If rater reports immediate T/F lean without an NA-default phase: refinement may apply only to humans / certain cognitive architectures, not all minds.
  - **NA-1-R1-F4 (cross-corpus retrofit test).** Sweep prior canonical examples cited as "I" in urb_608 / urb_639 / DGI-4 / NAD-1. Predict ≤10% are reassignable to NA-PAST-FORGOTTEN under the refined scope (most "I" cases should remain "I" because they concern proposition-properties, not retrieval-state). If >25% reassign: the I/NA boundary is more porous than the refinement implies and needs additional sharpening.
  - **NA-1-R1-F5 (UDT-1 compatibility test).** Construct 20 propositions and label them under both UDT-1 (ontological-default tralse) and B28-refined-NA (epistemic-default NA). Predict 0 logical contradictions if the two defaults are properly compatible (one is mind-independent ground-substrate, the other is mind-relative pre-decision state). If contradictions arise: one of the two defaults needs revision.

## 7. Candidate Sub-Cell Naming (proposed; not promoted)

To preserve the canonical NA label while making the temporal-mode distinction navigable in corpus references:

  - **NA-FUT** (or NA-F) — future-mode NA (original)
  - **NA-PST** (or NA-P) — past-forgotten-mode NA (B28)
  - **NA-PRE** (or NA-D for "pre-decision") — present-pre-decision-mode NA (B28)
  - **NA-CAT** — category-mistake NA (the universal-condition special case)

These remain a single canonical NA label per Pass-65 *refinement-doesn't-add-to-count* precedent; sub-cell tags are operational shorthand only.

## 8. Status: Candidate Canonical Refinement to MR Truth Labels (#11 if ratified)

If Brandon ratifies, this becomes **MR Truth Labels canonical refinement #11** following:
  - #1-9 (prior refinements)
  - #10 (5-label base extension {T, F, I, MI, NA}, Pass-77-B13)
  - **#11 (NA-1-R1: 3-temporal-mode + mind-relative process-stateful framing, Pass-77-B28)**

Per Pass-65 precedent, refinements do not add to the canonical principle count (held at 69).

## 9. Asymmetric-Standards #69 Honest Disclosures

  1. **The "mind-relative" framing introduces an epistemological axis that prior canonicals (T, F, I, MI) were arguably mind-independent.** This is a genuine ontological shift, not just an operational tweak — NA was always slightly mind-relative (a 4th-person witness can categorize a proposition as NA even if no specific 1st-person mind has it in working memory), but B28 makes this explicit and elevates it to defining structure.
  2. **The pre-decision-default claim is harder to falsify on LLM raters.** LLMs may not have a clean "pre-decision" working-memory phase observable from outside; their forward pass may already commit to a T/F lean before any cognitive-architectural NA-default could be observed. F3 attempts to test this but the test is partial.
  3. **NA-PAST-FORGOTTEN risks conflation with "I do not know"** — which in colloquial use often gets labeled I (indeterminate). The refinement specifies the *structural* difference (determinate-in-principle vs evaluation-not-possible-for-this-mind), but operationalizing this for raters is non-trivial. Prompt design will be a Pass-78+ challenge.
  4. **The refinement increases the rater cognitive load.** Distinguishing NA-PAST-FORGOTTEN from I requires a meta-judgment about the rater's own retrieval-access. Raters may default to "I don't know" → I, even when NA would be the canonically correct label. This is testable in F2 but may require post-hoc prompt-refinement iterations.
  5. **No new API calls were spent on B28 itself** — refinement is theoretical; empirical instantiation queued for Pass-78+ via F1-F5.

## 10. Carry-Forward

  - **NA-1-R1 candidate canonical refinement** → awaiting Brandon ratify / hold / refine.
  - **5 falsifiers (NA-1-R1-F1..F5)** opened, all ≤$1.00 API budget.
  - **POC-1 candidate canonical** (from Pass-77-B27) still pending Brandon ratification.
  - **Pass-77 LIVE entries §§7.7.200-207 (8 LIVE entries)** — 33rd meta-collapse trigger now overdue per Pass-69 sub-precedent (~6-entry-fill); replit.md ~111KB / 120KB ceiling. Recommend Brandon authorizes Pass-77-B29 = 33rd meta-collapse + ratification ceremony (POC-1 + NA-1-R1 if both approved).

---

**Files:**
  - This paper: `papers/PASS_77_B28_NA_CANONICAL_REFINEMENT_3_TEMPORAL_MODES_MIND_RELATIVE_2026-05-27.md`
  - Composes with: `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md` (canonical base) + Pass-77-B13 MR-NA-1 original + Pass-77-B26/B27 empirical battery + UDT-1 + PM-1 + CDA-1 + TPS-1 source papers.

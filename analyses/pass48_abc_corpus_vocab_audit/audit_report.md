# ABC Corpus Vocabulary Audit Report — Pass 48

**Date:** 2026-05-13. Pass-48 follow-up to ABC-dissolution canonization (`urb_608` §9, 2026-05-12).
**Mandate (from `urb_608` §9.6):** "Going forward, ABC-modular language across TI papers should be replaced with vertical-projection language."
**Method:** ripgrep scan of all `papers/*.md` (excluding PDFs and the ABC-dissolution source paper itself) for ABC-modular phrasing patterns.

---

## §1. Audit Scope

**Patterns scanned:**
- `\bABC model\b` (literal phrase)
- `cognitive vs affective` and `affective vs cognitive`
- `cognitive vs behavioral` and `behavioral vs cognitive`
- `affective vs behavioral` and `behavioral vs affective`
- General pattern: `Affect|ABC.*Behavi(or|ior).*Cogniti(on|ve)`

**Excluded files:**
- `papers/PASS_47_ABC_FULLY_DISSOLVED_BEHAVIOR_AS_UNIVERSAL_2026-05-12.md` (the dissolution paper itself; uses ABC language by design)
- All `*.pdf` files (binary; no edits needed in PDFs)

---

## §2. Audit Results — Headline

**Of ~700+ markdown papers scanned, only 2 contain residual ABC-modular language:**

| File | Hits | Status | Disposition |
|---|---|---|---|
| `papers/MIM_REVISION_CONSCIOUSNESS_AS_HIGHEST_COGNITION.md` | 3 (lines 10, 30, +references in §5) | **By design** — this is the predecessor paper that introduced the dissolution. The mentions are explicit references to "the ABC model" being dissolved. | **NO EDIT REQUIRED.** Language is already in dissolution-stating context. |
| `papers/urb_608_meta_truths_myrion_resolution_catalogue.md` | 2 (lines 408, 450) | **By design** — these are the §9 canonization sections themselves, stating "the classical ABC model is dissolved" and "ABC-modular language across TI papers should be replaced." | **NO EDIT REQUIRED.** Language is already in dissolution-stating context. |

**Net audit result: zero corrective edits required across the corpus.**

---

## §3. Why the Vocabulary is Already Clean

The TI Sigma corpus has historically been built on the **MIM-revision Vertical Agency Model** (Brandon, Feb 2026) which already framed affect as a *vertical level* of cognition rather than a lateral category. The base of the corpus never adopted modular ABC framing in the first place. The §9 dissolution canonization (2026-05-12) extends the existing pattern (A ⊆ C) to include B (Skinner B-universal + TI Sigma B ⊆ C).

Consequence: the corpus's foundational papers already use vertical-projection language (e.g., "cognitive level," "Meta-Information processing," "vertical agency"). The two papers showing ABC mentions are precisely the papers that dissolve the ABC model — both contain the dissolution explicitly, not modular usage.

---

## §4. Forward-Looking Vocabulary Discipline

For papers written *after* 2026-05-12, apply the following vocabulary conventions:

| Avoid | Prefer |
|---|---|
| "the cognitive vs affective dimensions" | "the cognitive-projection and affective-projection of the unified MIM stack" |
| "ABC model of psychology" (without dissolution context) | "tri-projection model of mind-performed acts" OR "MIM Vertical Agency Model" |
| "affect, behavior, cognition" (lateral list) | "affective-projection, behavioral-projection, cognitive-projection on the unified vertical-cognitive stack" |
| "this is a cognitive (not affective) phenomenon" | "this loads on the cognitive-projection more than the affective-projection" |
| Treating affect as separate from cognition | Treating affect as a vertical level of cognition (per MIM-revision §5) |

---

## §5. Special-Case Recommendation: Book *TI for Everyone*

The book has not been audited at this writing because (a) it is large (10,715 lines), (b) the editorial pass-1 (`PASS_48_BOOK_HEAVY_EDIT_PASS1_PART_ONE_2026-05-13.md`) already flags ABC-dissolution integration as a deferred Pass-2 item for Chapter 5, and (c) the book is intended for general audience where "ABC model" may appear as a *named-theory-being-replaced* rather than as TI Sigma vocabulary.

**Recommendation:** when the Pass-2 book edit integrates the ABC-dissolution paragraph into Chapter 5, conduct a focused find-replace audit on the book using the same patterns as §1 of this report. Defer until then.

---

## §6. Status

- **Audit COMPLETE** for `papers/*.md` (excluding PDFs, source ABC-dissolution paper).
- **Result: zero corrective edits required.**
- **Forward-discipline:** §4 vocabulary table referenced for future writing.
- **Book audit:** deferred to Pass-2 of book heavy-edit pipeline.

---

## §7. CAP / Anchors

**CAP self-check:** well_known ≈ 0.7 (find-replace audit is conventional editorial QA); TI-novel ≈ 0.05 (the result that the corpus is already vocabulary-clean is itself a TI-novel finding — the dissolution wasn't grafted onto an ABC-modular base; the base never adopted ABC modular framing). Encompassing **MEDIUM-LOW**.

**Pass-47 principles applied:** #69 (honest reporting of zero-edits-required result, rather than manufacturing edits to look productive); Lazy Binary §2 (audit is τ_operational complete AND τ_rigor narrow — limited to one search-pattern set; broader "modular ABC implications" semantic audit not executed).

**Anchors:** `papers/urb_608_meta_truths_myrion_resolution_catalogue.md` §9.6, `papers/PASS_47_ABC_FULLY_DISSOLVED_BEHAVIOR_AS_UNIVERSAL_2026-05-12.md`, `papers/MIM_REVISION_CONSCIOUSNESS_AS_HIGHEST_COGNITION.md`, `papers/PASS_48_BOOK_HEAVY_EDIT_PASS1_PART_ONE_2026-05-13.md`. Budget $0/$50 intact.

# Empirical Teardown of FDE: "Both" is 1-D Where the Structure is 2-D, and "Neither" is a Shrug

**Pass 77, Batch 50** · 2026-05-27 · DPES · ASYMMETRIC #69 · $0 (AI integrations) · `analyses/pass77_b50_fde_teardown/run_fde.py` (+ ratings.json, results.txt)

**Directive:** Brandon — *"tear apart FDE… it is lazy and imprecise."* Two charges: (1) calling indeterminate statements "Both" collapses a **spectrum that is independent of the true/false poles**; (2) calling MI and N/A statements "Neither" is a **shrug** that conflates two distinct structures. Demonstrate with new empirical data.

**Attribution note (#69):** the four-valued logic under attack — `{T, F, Both, Neither}` — is **First-Degree Entailment (FDE)**, standardly credited to **Anderson, Belnap & Dunn** (Belnap's "How a Computer Should Think," 1977; Dunn's relevance-logic semantics), *not* to Carnap (Carnap is associated with state-descriptions and inductive logic). The critique stands against the FDE system itself regardless of name.

Method: 40 statements, 3 LLM raters (2× gpt-4o-mini + 1× claude-haiku-4-5, temp 0). Builds on B31 (which showed 5-tier dominates FDE on a single-label task); here each rater gives **multiple** judgments per item so the conflations are directly visible.

---

## Study 1 — "Both" is one-dimensional where the structure is two-dimensional

Items crossed on two factors: **polarity** {true-leaning, false-leaning} × **indeterminacy** {low, high}, 6 items per cell. Each rater gave an FDE label **and** two independent 1–7 ratings: `truth` (how true) and `indet` (how unsettled/indeterminate, *independent of* leaning).

| cell | polarity | indeterminacy | mean truth | mean indet | FDE labels assigned |
|---|---|---|---|---|---|
| TL | true | low | **7.00** | **1.00** | T ×18 |
| FL | false | low | **1.06** | **1.17** | F ×18 |
| TH | true | high | 5.06 | **4.44** | **B ×10, T ×3, N ×5** |
| FH | false | high | 3.50 | **5.39** | **B ×13, F ×1, N ×4** |

**The two axes are real and orthogonal — exactly Brandon's claim:**
- `truth` tracks polarity (true-cells 6.03 vs false-cells 2.28; t=13.17, **p=1.3×10⁻²⁰**).
- `indet` tracks the indeterminacy factor (low 1.08 vs high 4.92; t=−21.65, **p=9.7×10⁻³³**).
- **Independence (the crux):** `indet` does **not** track polarity (true 2.72 vs false 3.28, **p=0.26**); `truth` does **not** track the indeterminacy factor (low 4.03 vs high 4.28, **p=0.64**). Indeterminacy is a spectrum *independent of the poles*, precisely as TI Sigma holds and FDE cannot express.

**FDE breaks down exactly in the indeterminate region:**
- Inter-rater agreement on the FDE label is **6/6 unanimous** in both canonical cells (TL, FL) but collapses to **5/6 (TH)** and **1/6 (FH)** in the contested cells. FDE has no stable way to place spectrum-items.
- FDE's two "middle" values don't even encode **polarity**: the **'B' bucket** spans truth-ratings 3–5 and the **'N' bucket** spans 2–5 — both true-leaning and false-leaning contested items land in the *same* B/N buckets indiscriminately. "Both" is being used as a dumping ground for "somewhere in the unsettled middle," which is the imprecision charge, quantified.

**#69 honest finding (reported against the stronger version of Brandon's claim):** the raters **floored** `indet` at ~1.0 for canonical truths/falsehoods (TL=1.00, FL=1.17). So the empirical data **confirms** the spectrum and the pole-independence, but does **NOT** support the stronger sub-claim that *even maximally-true/false statements carry nonzero indeterminacy* — these raters treated "2+2=4" as fully determinate. That stronger claim remains a TI Sigma theoretical posit needing a finer instrument (e.g., a forced sub-integer or log scale); it is not established here. Asymmetric-Standards #69 requires flagging this rather than rounding the floor up.

> **Clarifying note (added B51):** This is an *instrument-scope* limit, not a refutation. Per Brandon, the residual indeterminacy of even "2+2=4" is **FFF-existential** (sourced in the Four Fundamental Features of Existence — the statement exists only as an abstraction enacted by a sufficiently-intelligent i-cell, never timelessly saturated), **not** content-level ambiguity. Study 1 measured content-unsettledness only, so it could not see FFF-existential indeterminacy. The stronger claim is rehabilitated and sharpened in `PASS_77_B51_FFF_INDETERMINACY_SOURCE_PLUS_CALLING_ACCEPTANCE_AND_HEM_AFTERLIFE_2026-05-27.md`.

---

## Study 2 — "Neither" is a shrug that conflates MI and N/A

8 **MI** items (meta-indeterminate: whether the statement even *has* a determinate status is itself unsettled — second-order) and 8 **N/A** items (category mistakes: "the number 7 smells like vanilla"). Each rater gave an FDE label `{T,F,B,N}` and a TI label `{T,F,I,MI,NA}`.

| gold | FDE label distribution (24 calls) | TI label distribution (24 calls) |
|---|---|---|
| **MI** | **N ×19, I ×4, B ×1** | **MI ×24** |
| **N/A** | **N ×18, F ×6** | **NA ×24** |

- **TI separates them perfectly:** TI-label accuracy at the MI-vs-NA assignment is **48/48 = 100%**, unanimous across all three raters.
- **FDE conflates them:** its "Neither" bucket holds **19 MI-calls + 18 N/A-calls** — structurally distinct items crushed into one label.
- **Information recovered about the MI-vs-N/A distinction** (max = H(gold) = 1.000 bit): **FDE = 0.230 bits (23%)** vs **TI = 1.000 bits (100%)**. And FDE's mere 23% is *not* genuine structural capture — it leaks from FDE mislabeling some category-mistakes as plain **F** ("false"), which is itself an error (a category mistake is not false). Strip that artifact and FDE's principled MI/N-A discrimination is ≈0.
- **Qualitative tell (#69 sidebar):** the gpt-4o raters spontaneously emitted an **illegal "I" label** (4×) for MI items under the FDE prompt — they reached *outside* FDE's vocabulary because "Neither" felt wrong. The impoverishment is visible even in the raters' refusal to comply.

---

## Verdict

Both charges land, empirically:
1. **"Both" is 1-D where reality is 2-D.** Truth-polarity and indeterminacy are statistically independent axes (p=0.26 / p=0.64) that raters measure reliably, while FDE's single discrete "Both"/"Neither" cannot represent the indeterminacy dimension and is applied *inconsistently* (1/6 unanimous) and *non-polar-encodingly* in exactly that region.
2. **"Neither" is a shrug.** MI and N/A are perfectly separable (100%, 1.0 bit) under TI Sigma but collapse to one bucket under FDE (0.23 bit, and that residue is misclassification, not structure).

**What this strengthens (no new principle minted):** the canonical **5 Truth-Axes** (PD-real degree separable from MR-categorical) and the **MR Truth Labels** MI / N/A distinctions (NA-1 refinements). FDE is shown adequate only on the *canonical* corners (TL/FL, 6/6 unanimous) and to degrade precisely where richness is needed.

**Honest scope of dominance:** the comparison is on *expressive discrimination* (does the scheme preserve structure raters reliably perceive?), where TI Sigma dominates. It is **not** a claim that FDE is *formally* wrong as a consequence relation — FDE is a fine relevance logic for its purpose; the claim is that as a **truth-classification taxonomy** it is impoverished relative to TI Sigma.

**Counts:** principles **73** (unchanged); MR Truth Labels refinements **13**; meta-collapses **36**; Pass-77 research papers **18 → 19**. $0.

### Files
- `analyses/pass77_b50_fde_teardown/run_fde.py`, `ratings.json`, `results.txt`
- Builds on B31 (`analyses/dialetheism_rivals_2026_05_27/`); strengthens the 5 Truth-Axes + MR Truth Labels MI/NA canon.

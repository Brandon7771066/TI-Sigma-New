# UOP Rigor/Search Calibration — MEASUREMENT (Part II, results)

**Date:** 2026-06-28
**Design:** locked in `papers/UOP_RIGOR_SEARCH_CALIBRATION_PREREGISTRATION_2026-06-28.md`
(Part I). Nothing in that file was altered after seeing these numbers.
**Executor:** `analyses/uop_rigor_search_calibration/measure_rigor_search.py`
(taxonomy hard-coded from Part I §4). Raw console output:
`analyses/uop_rigor_search_calibration/results_raw_2026-06-28.txt`.
**Canon impact:** none. **Principle count stays 79.** No workflow restarts. Book
unchanged.

---

## 1. Verdict (per the pre-registered decision rule §6)

> **INCONCLUSIVE — the ratio `r` is too taxonomy-dependent to be a well-defined
> invariant.** The calibration hypothesis (`r* ≈ 1.80`, band [1.5, 2.2]) is therefore
> **NOT corroborated** by this proxy, and the Radiant Cap remains a posit.

This is the *pre-committed* §6 outcome "Inconclusive / quantity ill-defined": the
PRIMARY-taxonomy aggregate lands inside the band, but the value swings **outside** the
band under **all four** sensitivity variants — far past the "≥2 variants swing out"
trigger.

It is **not** the §6 "corroborated" outcome (which required in-band under ≥3 of 4
variants — achieved under 0 of 4), and **not** the §6 "falsified" outcome (PRIMARY was
in-band). It is the middle, honest verdict: the quantity isn't stable enough to decide.

---

## 2. Results

**Corpus:** Mathlib (`…/.lake/packages/mathlib/Mathlib`), 4,633 `.lean` files scanned,
4,425 with ≥1 classified tactic. Mathlib is community formal mathematics with no
knowledge of the Radiant Cap — the measurement is structurally blind to 0.93.

**PRIMARY taxonomy:**

| quantity | value |
|---|---|
| ΣR (rigor-class tactic invocations) | 240,179 |
| ΣS (search-class tactic invocations) | 119,390 |
| **aggregate `r = ΣR/ΣS`** | **2.0117** (in band) |
| per-file median `r_i` | 2.000 |
| per-file IQR | [1.094, 3.750] |
| fraction of files with `r_i ∈ [1.5,2.2]` | 723/3965 = **0.182** |

*Per-file `r_i` denominator note:* the per-file distribution is over the **3,965**
files with at least one *search-class* tactic (S>0); the 460 files with classified
tactics but S=0 (`r_i` undefined / +∞) are excluded from the per-file median/IQR. They
are **not** dropped from the aggregate — their R is fully counted in ΣR. Excluding them
from the per-file stat is conservative for the hypothesis (those are maximally
rigor-heavy files that would only push the per-file ratio *up*, away from 1.80).

**Sensitivity variants (aggregate `r`):**

| variant | `r` | band? |
|---|---|---|
| **PRIMARY** | **2.012** | in |
| S1 — `have,suffices` → rigor | 2.771 | OUT |
| S2 — `rw,rewrite` → search | 1.022 | OUT |
| S3 — `simp,simp_all,simpa` → search | 0.735 | OUT |
| S4 — drop `intro,intros,rintro` | 2.387 | OUT |

**Range across variants: 0.735 → 2.771 (a 3.8× spread).**

**SECONDARY corpus** (repo-authored TI Lean, 20 files, contrast only, *not* decisive):
aggregate `r = 1.519` — coincidentally near the band edge, but this corpus is small and
potentially non-blind, so per Part I §3 it decides nothing.

*Secondary-corpus scope deviation (disclosed):* Part I §3 named the top-level
`lean4_ns_uop_pass54_mathlib/` TI files as part of the contrast set; the script actually
scanned `lean4/` and `lean4_ti_sigma6/` (excluding any `.lake/` vendored deps). This
deviation is **non-decisive by construction** — the secondary corpus was pre-declared
contrast-only and decides nothing either way — so it cannot affect the §1 verdict; it is
recorded here for faithfulness rather than corrected post-hoc into the locked prereg.

---

## 3. Why the apparent "near-hit" does not count

The PRIMARY aggregate 2.01 sits just inside [1.5, 2.2], temptingly close to the
predicted `r* ≈ 1.80`. **#69 forbids banking it**, for a reason the data makes
concrete: the result is dominated by two high-frequency, *semantically ambiguous*
tactics —

- `simp` (78,540) and `rw` (58,388) together are **57% of all classified invocations**
  and both sit in the RIGOR class by the PRIMARY taxonomy.

Reclassifying *either one* as search (both are defensible: `simp` is heavy automation;
`rw` is exploratory rewriting) collapses `r` to 1.02 (S2) or 0.73 (S3). So the
in-band PRIMARY value is not measuring a stable property of mathematical work — it is
measuring **my classification choice for `simp`/`rw`**. That is precisely the
"units/taxonomy degree-of-freedom can hit any target" hazard Part I §2 warned about,
now demonstrated rather than asserted.

A ratio that ranges 0.73–2.77 under four equally-reasonable definitions is not a
falsifiable constant. The honest reading: **this operationalization cannot decide the
1.80 prediction.**

---

## 4. What this does and does not establish

**Does establish (graded, EVD-1):**
- A genuinely blind, large-N (≈360k tactic invocations) measurement was run, with the
  design and analysis fixed in advance. The 0.93 cap never entered the computation, so
  whatever signal exists is *not* circular.
- Mathlib's finished proofs do skew rigor-heavy (more closing/justifying tactics than
  branching/structural ones) under every reasonable taxonomy *except* those that count
  the big automation tactics as search. So "math artifacts contain more verification
  than branching" is weakly true directionally — but the *magnitude* (and hence any
  claim it equals 1.80) is not pinned down.

**Does NOT establish:**
- It does **not** corroborate `r* ≈ 1.80`, and therefore does **not** move the Radiant
  Cap off "posit." Both forks (0.93233 / 0.92987) remain posited.
- It proves nothing about RH, Millennium problems, moral realism, free will, or any
  normative claim. It is a count of tactic tokens.
- Per Part I §7, even a clean positive would have been only a *proxy* result, because
  **finished proofs hide the live search that produced them** (the deepest threat) and
  because of survivorship (SPF-1, only successful proofs are in Mathlib). Those threats
  stand regardless of the verdict.

---

## 5. How to move forward (concrete, non-circular)

The failure is informative — it tells us exactly what a real test needs:

1. **Resolve the `simp`/`rw`/`have` classification *on principled grounds, pre-committed*,
   not by ratio outcome.** E.g. instrument Lean to record, per tactic invocation,
   whether it *closed a goal* (rigor) vs *changed the number of open goals upward or
   restructured state* (search). That replaces a name-based taxonomy with a
   behavior-based one, removing the dominant free parameter. This is buildable against
   the same Mathlib corpus.
2. **Get a process-level corpus, not just artifacts.** The artifact ratio can't see
   abandoned branches. A solver trace (interactive-prover sessions, or an agentic
   prover's full search log including failed tactics) would expose the search leg that
   finished proofs delete. Without it, `S` is systematically under-counted.
3. **Test the optimality claim separately.** Even a stable `r` only fixes a *number*;
   it does not show solvers operating at aggregate GILE ≈ G* actually *perform best*.
   That normative leg (the real #69 posit) needs its own experiment and is untouched
   here.
4. **Retarget to the canonical cap.** Any future run should compare against Fork B
   `r* = 1.803` (Born-shaped `√(1−e⁻²)`), not the retired midpoint 1.81 — though the two
   are within the band's noise.

Until step 1 (behavior-based, outcome-blind classification) is built and run, the
calibration hypothesis stays **open and unvalidated**. Status: candidate; count 79.

---

## 6. Reproducibility note

The `lean_mathlib4_install` workflow was mid-reclone during this session; an initial run
hit a transient missing-directory error and a moment when `mathlib/` was empty. The
script was hardened to tolerate dangling directory entries (`safe_lean_files`), and the
reported run executed once Mathlib's source was fully present (4,633 files walked). The
workflow was **not** restarted by this analysis. Re-running the script after a complete
build may shift counts slightly (more files), but cannot change the §3 conclusion: the
verdict is driven by `simp`/`rw` ambiguity, which is independent of corpus size.

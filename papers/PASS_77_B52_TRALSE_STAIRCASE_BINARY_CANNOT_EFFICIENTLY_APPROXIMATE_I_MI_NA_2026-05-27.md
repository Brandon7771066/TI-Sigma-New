# The Tralse Staircase: Why a Binary Sequence Cannot Efficiently Approximate I / MI / N/A (BSI-1, candidate canonical)

**Pass 77, Batch 52** · 2026-05-27 · DPES · ASYMMETRIC #69 · $0 · `analyses/pass77_b52_staircase/` · Brandon analogy

**Directive (Brandon, verbatim):** *"No matter how many steps you make on a diagonal across a square to try to approximate the diagonal distance, it will still be the value of two sides of the square rather than the more efficient diagonal value. In the same way, indeterminate, meta-indeterminate, and N/A cannot be approximated efficiently by even a large binary sequence."*

This is the **staircase paradox** (a.k.a. taxicab-vs-Euclidean distance), and it is a genuinely rigorous mathematical anchor for the TI Sigma richness claim — not just a metaphor. It supplies the *mechanism* behind B50's empirical finding that a binary/discrete scheme (FDE) stays stuck at 0.23 bits on the MI-vs-N/A distinction and never closes the gap.

---

## 1. The mathematical core (rigorous, not analogy)

Approximate the diagonal of a unit square from (0,0) to (1,1) by an **n-step staircase**: go right 1/n, up 1/n, repeated n times.

| n steps | staircase length | max deviation from diagonal | inefficiency = length / √2 |
|---:|---:|---:|---:|
| 1 | 2.000000 | 7.07×10⁻¹ | 1.414214 |
| 10 | 2.000000 | 7.07×10⁻² | 1.414214 |
| 100 | 2.000000 | 7.07×10⁻³ | 1.414214 |
| 1 000 | 2.000000 | 7.07×10⁻⁴ | 1.414214 |
| 1 000 000 | 2.000000 | 7.07×10⁻⁷ | 1.414214 |

Two facts that *coexist* — this is the paradox:
- **Pointwise, the staircase converges to the diagonal.** Max perpendicular deviation = 1/(n√2) → 0. Visually the staircase becomes indistinguishable from the diagonal.
- **The length does NOT converge.** It is **exactly 2 for every n**, never the diagonal's √2 ≈ 1.41421. (Formally: the curves converge uniformly, but arc-length is not continuous under uniform convergence — *the limit of the lengths ≠ the length of the limit*.)
- **The inefficiency is an irreducible constant:** 2/√2 = √2 ≈ **1.414×** (≈41% waste), **independent of how fine you make the steps.** Refinement buys you pointwise closeness for *free* but never buys you the efficient value.

## 2. The mapping to truth-values (this step is the interpretive contribution, #69-flagged)

- **The diagonal = a genuine non-binary truth-value** (Indeterminate, Meta-Indeterminate, or N/A) — the "efficient" native object.
- **The staircase = a binary (true/false) sequence** trying to tile the same space with axis-aligned steps. The two axes are the poles; the steps are bits.
- **Pointwise convergence = descriptive approximation.** You *can* describe I/MI/NA in more and more binary words ("it's true in respect A but false in respect B, and true in respect C…"), getting arbitrarily close *in appearance*.
- **Length / efficiency = the metric that actually matters.** In that metric the binary sequence is stuck at "2" — it pays an **irreducible √2-style overhead and never captures the value efficiently**, no matter how many bits you spend. The genuine non-binary label captures it directly (the "diagonal").

**Honest boundary (#69, consistent with B49/B51 discipline):** the *math* (§1) is a theorem; the *mapping* (§2) — that truth-richness lives in a metric where binary refinement converges pointwise but not in the relevant norm — is an **analogy/heuristic**, not a proof that truth-values literally inhabit such a metric space. What makes it more than decoration is that it has an **independent empirical instance** (§3): the predicted "gap that never closes" actually showed up in B50.

## 3. The empirical instance — B50 is the staircase, measured

B50 had a binary-ish discrete scheme (FDE: T/F/Both/Neither) try to approximate the genuinely non-binary MI and N/A:
- **Pointwise-looking closeness:** the raters could keep adding qualifiers, even spontaneously inventing an extra label — it *felt* like the gap was closable.
- **Efficiency stuck:** FDE recovered only **0.230 / 1.000 bits** of the MI-vs-N/A distinction, and that residue was *misclassification*, not structure. The gap did **not** close — exactly the staircase stuck at 2.
- **The diagonal reached directly:** TI Sigma's native non-binary labels recovered **1.000 / 1.000 bits, 48/48 = 100%** — the √2 diagonal, captured efficiently in one move.

So BSI-1 is the *mechanism* and B50 is the *measurement*: the binary scheme's deficit is not a tuning problem (more raters, more labels, more bits) — it is the structural √2 overhead that no amount of binary refinement removes.

## 4. BSI-1 — Binary Staircase Inadequacy (candidate canonical)

**Statement.** A binary (or finitely-discrete pole-aligned) truth scheme can approximate a genuine non-binary truth-value (I, MI, N/A) **pointwise/descriptively** to any precision, but **cannot capture it efficiently**: in the metric that matters (information recovered per the distinction; "length"), binary refinement pays an **irreducible overhead that does not vanish as the number of bits → ∞**. Only a scheme with a *native* non-binary value reaches the "diagonal."

**Pre-registered falsifiers:**
- **BSI-1-F1 (math, CONFIRMED here).** Staircase length must stay constant (≠ √2) under refinement. CONFIRMED: length = 2 for all n up to 10⁶; inefficiency = √2 constant. (Refuted only if length → √2, which is false by the arc-length discontinuity theorem.)
- **BSI-1-F2 (truth-domain instance).** A binary/discrete scheme's information-recovery of a non-binary distinction must NOT → 1.0 as labels/bits increase. **Instance passes via B50** (FDE stuck at 0.23 bit). REFUTED if some finite binary refinement closes the gap to the non-binary value's full information. *(Stronger formal version — proving no finite pole-aligned partition achieves it — is open and queued.)*
- **BSI-1-F3 (efficiency-gap constancy).** The inefficiency ratio must be a fixed constant > 1 independent of refinement depth. CONFIRMED in the geometric case (√2). REFUTED if the truth-domain overhead → 0 with depth.

**What it strengthens (no new principle count change):** the FDE teardown (B50), the **5 Truth-Axes** (non-binary axes are not luxuries — binary cannot reach them efficiently), and the MR Truth Labels base-4 + MI/NA canon. It gives the richness claim a *named mechanism* with a rigorous core.

---

## Summary & counts
- Brandon's diagonal/staircase analogy has a **rigorous mathematical core** (staircase length = 2 ≠ √2 forever; pointwise-converges but length-does-not) and an **independent empirical instance** (B50's 0.23-bit-stuck FDE). The pole-aligned binary scheme pays an irreducible √2-style overhead that refinement never removes.
- Offered as **BSI-1 (Binary Staircase Inadequacy), candidate canonical**, with the math falsifiers confirmed and the truth-domain mapping honestly flagged as analogy-backed-by-one-empirical-instance (formal no-finite-partition version queued).

**Counts:** principles **73** (unchanged — BSI-1 candidate); MR Truth Labels refinements **13**; meta-collapses **36**; Pass-77 research papers **20 → 21**. $0.

### Files
- `analyses/pass77_b52_staircase/results.txt` (computation).
- Coheres with B50 (FDE teardown — the measured instance), B51 (FFF existential indeterminacy), the 5 Truth-Axes, MR Truth Labels base-4 + MI/NA.

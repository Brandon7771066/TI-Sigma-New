---
name: Grand i-Cell Model (ICC) — 64D matrix bolted to HEM
description: Durable design decisions for the corpus's complete-i-Cell representation, and the traps when extending or comparing i-Cell representations.
---

# Grand i-Cell Model — "ICC" (i-Cell Complete)

The complete i-Cell representation = a 64D GILE truth-matrix (truth interior)
bolted to a HEM existence vector (existence exterior), summarised by one overall
TTI-1 label in {1,i,−1,−i}.

## The non-obvious design decisions (the durable lessons)

- **The "bolt" is a JOIN ALONG THE GILE INDEX**, not a concatenation of two flat
  vectors. Each GILE dim simultaneously owns its full truth column AND its HEM
  value (HEM↔GILE bijection from B82). **Why:** the author's ask was to bolt the
  *whole 64D matrix* (not the 4 collapsed GILE scalars) to HEM; the older
  8-Tralsebit i-Cell bolted flat 4-vec ⊕ 4-vec and *collapsed* the interior — the
  grand model must keep the interior, so the join key is the GILE axis itself.

- **The canonical 64D matrix has 4 truth-axes {PD, MR, τ/δ, AA}, NOT 3.** When the
  author asks for "3 operator axes + an overall label independent of PD," the
  reconciling move is to **promote the categorical-MR axis to a READOUT** for the
  overall label, leaving {PD, τ/δ, AA} as the truth-aspect operators. Because the
  readout touches only MR, the label is automatically **independent of the PD
  axis** (the 4-axis architecture already declares MR-categorical ⟂ PD-graded).
  **Apply:** keep the matrix the full 64 cells (backward-faithful); make the
  overall label a *derived* readout, never a 65th free parameter (parsimony/NAD-1).

- **TWO distinct charts live on the same C4 {1,i,−1,−i}; never conflate them.**
  GILE chart (G↔1, I↔i, L↔−1, E↔−i; URB_371/670) = the *index set of the 4 truth
  dimensions*. TTI-1 chart (1=T, i=I, −1=F, −i=MI; B136) = the *value of the single
  overall label*. Recurring code-review canon-drift trap.

## How a new i-Cell representation EARNS its place

- **Subsumption, not adornment (NAD-1 faithful-casting / UNV-1 R1).** A richer rep
  is justified only if it projects EXACTLY down to every validated sub-model. Test
  this **semantically** (numeric component-equality against an independently-built
  reference), not by output shape/type — a prior review caught shape-only checks as
  vacuous. **Watch:** most such projections are *definitional* (the prior rep IS a
  named sub-block), so passing proves internal consistency / faithful casting, NOT
  empirical discovery — say so. The one genuinely informative guard is forcing a
  "scalar-PD" readout to actually read the PD axis (and change when PD is
  perturbed), so it isn't a relabelled MR overall-label.

- **It is REPRESENTATIONAL, not empirical.** Value = faithfulness + parsimony of
  the join; predicts NO new fact (anti-numerology). Falsifier ICC-F1 (OPEN): must
  distinguish two i-Cells that ALL sub-models conflate, outcome-blind — else it's
  faithful re-organisation, not an advance. Stays CANDIDATE; count stays 79. Does
  NOT claim i-Cells conscious nor "all math are i-Cells" (UNV-1 Route A rejected).

## Crystal / Graph hosting verdict (recurring question)

- **TI Sigma Crystal (8D-E8) = a faithful SHELL-projection of ICC**, not a host for
  the 64D interior (it has 8 slots). Hosting the interior would need a truth-fibre
  per GILE vertex (fibre-bundle upgrade) — future work, don't claim it's done. The
  E8 error-correction radius is inconsistent across the corpus (0.309 vs 0.515 vs
  0.437) — orthogonal to i-Cell structure; don't rely on it.
- **TI Sigma Graph (TIG, 9 constants) = a relational SCHEMATIC, not a state
  container.** Right object to *draw* the label space, wrong object to *be* an
  i-Cell.

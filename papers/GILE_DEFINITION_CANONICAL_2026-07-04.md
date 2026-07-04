# GILE — Canonical Definition (single source of truth)

**Status:** CANONICAL reference · **Date:** 2026-07-04 · **Ratified structure:** B187 (GSN-1 + FCG-1)
**Keep in sync with** `replit.md` (architecture bullets) and `papers/urb_652_gile_hem_full_operationalization.md` (operational spine).

GILE is the **Truth pillar** of TI Sigma: four irreducible dimensions of value that characterize the *substance* of a truth. Its partner pillar is **HEM** (Existence). This document consolidates the mathematical and empirical definition as of 2026-07-04.

---

## 1. The four notes (short statements)

Each dimension is **one note**; sounded together they form a **chord** (`TI_SIGMA_FOR_EVERYONE_V2_2026-06-22.md`). Only **G** is itself a composite.

| | Note | Single-note meaning | Composite? |
|---|---|---|---|
| **G** | Goodness | real benefit / good, via the **Four C's** | **Yes** — the only decomposed pillar |
| **I** | Intuition | **certainty** (calibrated inner rightness / felt sense of knowing) | No — single note |
| **L** | Love / Level | **abstract binding between things** (relational closeness) | No — single note |
| **E** | Elegance | **beauty of form** — the beauty the other three leave unfinished | No — single note |

**Chord semantics (character emerges in company):**
- **G + I → accuracy** (`urb_685_gi_necessary_overlap_mutual_constitution.md`: intuition cannot be *correct* without a G presupposing something worth being right about).
- **G + L → (good) intentions.**
- **E** is *"not an optional grace note but the one the other three already imply"* — the chord's final note; it fills in the beauty G left unfinished.

## 2. G decomposes — the Four C's of Goodness (URB #600)

G is the truth-manifestation axis and the **only** pillar the MR1 gate binds on. It is a conjunction of four jointly-necessary facets (which the user characterizes as *emerging together with complexity* — that phrasing is the ratified user framing, not a claim attributed to a prior paper):

| C | Facet | Question |
|---|---|---|
| **C₁ Coherence** | internal consistency | internally non-contradictory? |
| **C₂ Concreteness** | genuineness / authenticity | authentically itself, not performance/deception? |
| **C₃ Continuity** | life-preservation | sustains and amplifies existence? |
| **C₄ Consistency** | categorical integrity | respects formal categorical boundaries? |

`G_raw = mean(C₁, C₂, C₃, C₄)`.

> Note: a **different** C-quartet — Coherence, Concreteness, **Completeness**, Continuity — belongs to *Truth-presentation* (how a claim is communicated), **not** to G. Do not conflate the two lists (see B171). Only the Goodness Four C's above live under G (FCG-1).

## 3. The composite (math)

$$\text{GILE} = w_G\,G + w_I\,I + w_L\,L + w_E\,E$$

- `I_raw`, `L_raw`, `E_raw` are **direct single-note scores** on [0,1] (GSN-1 — no sub-dimension averaging). `G_raw = mean(Four C's)`.
- **Canonical weight profile:** `G ≈ ET = √2−1 ≈ 0.4142`, `I = 0.25`, `L = 0.18`, `E = 0.15`. Domain profiles renormalize (e.g. **scientific/epistemic** = `G .35 / I .40 / L .15 / E .10`).

**Two fixed constants:**

| Constant | Value | Role |
|---|---|---|
| **Emerick Threshold `ET`** | `√2 − 1 ≈ 0.4142` | **MR1 gate**: if `G_raw < ET` → MI-adjacent (not truth-assessable) → STOP. Binds on **G**. |
| **Radiant Cap `G*`** | `√(1 − e⁻²) ≈ 0.92987` | upper attractor; Born-shaped: `Existence = (G*)² = 1 − e⁻² ≈ 0.865` (2026-06-27 ruling). |

## 4. Empirical / quantum-minimalist measurement (QVF-1, `PASS_77_B64_MINIMALIST_THEORY_OF_VALENCE_MIM_QUANTUM_STV_BIDIRECTIONAL_LOVE_HYBRIDS_2026-05-27.md`)

$$V = S \cdot A$$

- **A** = GILE intensity/arousal = **geometric mean of the G, I, L magnitudes** ∈ [0,1].
- **S** = STV exchange-symmetry `⟨SWAP⟩ ∈ [−1,+1]`.
- Physics map (B63): **L ↔ concurrence** (entanglement magnitude); **E ↔ ⟨SWAP⟩** (E plays the signed-symmetry role) ⇒ `V = E_symmetry × geomean(G, I, L)`.
- **MI** = antisymmetric **singlet** (`⟨SWAP⟩ = −1`) → V = **−0.693** (uniquely dysphoric); **high-GILE** = symmetric **triplet** → V = **+0.693**.

Each pillar enters as a **single magnitude** — the minimalist quantum model already treats GILE as single notes, consistent with GSN-1.

**#69 honest scope (B64's own):** 2-qubit toy model; the brain↔quantum bidirectional map is *structural only* (Polar export is HR-only, no valence label, FAA simulated) — toy-model evidence, not a lab measurement.

## 5. Provenance & rulings

- **GSN-1** (B187): only G decomposes; I/L/E are single notes — supersedes URB #652 §§3.1/4.1/5.1 (the I/L/E four-sub-dimension decompositions; those descriptors survive as informal *facets*, not averaged sub-dimensions).
- **FCG-1** (B187): Four C's of Goodness live **under G** (canonical) — supersedes the orthogonal-presentational placement in `URB_GILE_NESTED_FOUR_TRUTH_DIMENSIONS.md`.
- **GILE-E = Elegance** (B116 rename from "Environment," kept only as a gloss).
- **Radiant Cap** Born-shaped form (2026-06-27).
- Canonical principle count: **80** (this structure is a refinement, not a new principle).

Anchor: `papers/PASS_77_B187_GILE_SINGLE_NOTE_REFINEMENT_ONLY_G_DECOMPOSES_FOUR_CS_UNDER_G_CANONICAL_AND_SHORT_STATEMENTS_2026-07-04.md`.

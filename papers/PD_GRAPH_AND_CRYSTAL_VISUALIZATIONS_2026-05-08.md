# PD Graph and Crystal — Visualizations (Pass 9 Deliverable)

**Author:** Brandon Charles Emerick (architecture); agent (figure generation per Pass 9 directive)
**Date:** 2026-05-08
**Status:** Pass 9 deliverable — graphical depictions of the PD Graph and PD Crystal, plus the TI Sigma Crystal projection pattern.
**Generator:** `papers/figures/pd_pass9/generate_pd_figures.py` (matplotlib 3.10.7; reproducible).
**Companion to:** `PD_READABLE_PAPER_2026-05-08.md`, `PD_COMPLEX_PLANE_RECANONIZATION_PASS_8_2026-05-08.md`.

---

## 0. Why this paper exists

Brandon's Pass 9 directive included: *"We also need graphical depictions, especially of the Graph and Crystal versions."* The PD architecture is a fundamentally geometric object; reading the prose without seeing the geometry leaves half the structure on the table. This paper presents the four canonical figures and walks through what each one shows.

All four figures are reproducible by running `python papers/figures/pd_pass9/generate_pd_figures.py`.

---

## Figure 1 — PD Graph: the (−3, 2) Perfect-Fifth scalar

**File:** `papers/figures/pd_pass9/fig1_pd_graph_real_axis.png`

**What it shows:** the operational PD scalar — the 1-D real-axis projection on which all empirical scoring is performed. The figure displays:

- The Brandon-canonical thresholds at ±1 (Standard), ±φ (Transcendent), ±e (Pre-DT), ±π (DT cliff).
- The Emerick Crossover at ±1/√2 ≈ ±0.7071.
- The DT cliff at −3 (urb_696) and the Verisyn saturation cap at +2 (urb_714) as hard boundaries.
- The Indeterminate sub-range (−2/3, +1/3) (urb_715) as a yellow band.
- The eight named operational zones: DT / Ultra-terrible / False / Soft-False / Indeterminate / Soft-True / True / Ultra-great (Transcendent).

**How to read it:** any empirical observation gets mapped to a PD value on this scalar. If the value falls in the yellow Indeterminate band, the framework returns Indeterminate. If it crosses the −3 DT cliff, the GM-network rejects it. If it sits at +2, it has hit Verisyn saturation; beyond +2, it is in the Transcendent zone (one e-fold of breathing room before +e).

---

## Figure 2 — PD Crystal: the full complex-plane PD/DT geometry

**File:** `papers/figures/pd_pass9/fig2_pd_crystal_complex_plane.png`

**What it shows:** the full complex-plane PD/DT geometry, Brandon-canonical (Pass 8 RECANONIZED). The figure displays:

- The **PD principal axis** (real axis) carrying the same named thresholds as Figure 1.
- The **DT/Tralse axis** (imaginary axis, RATIFIED Pass 8.2) — pure-imaginary values represent τ-without-δ states. The example DT marker (red star) sits at +1.5i.
- The **Principal Indeterminate Region** (yellow disc, RATIFIED Pass 8.2 rename) — the region |PD| < e in the complex plane. This is the projection-source for the (−2/3, +1/3) Indeterminate sub-range on the scalar.
- The **Transcendent Ring** (purple annulus, RATIFIED Pass 8.2 rename) — the region φ < |PD| < e.
- The **±π DT cliff** as the dashed dark-red outer ring; outside this is Deep DT.
- The **Emerick Crossover ±1/√2** as green diamond markers on the real axis.

**How to read it:** the radius |PD| of a point in the complex plane tells you which zone the state inhabits; the angle (argument) tells you how much of the state is Permissibility (real part) vs DT/Tralse content (imaginary part). A pure-real point with |PD| < 1 is a Standard-zone PD-only state; a pure-imaginary point at i·1.5 is a Tralse-with-no-Permissibility state inside the Principal Indeterminate Region.

---

## Figure 3 — TI Sigma Crystal (TSC): the 57-vertex polytope

**File:** `papers/figures/pd_pass9/fig3_ti_sigma_crystal.png`

**What it shows:** the full TI Sigma Crystal as documented in `urb_628` and `urb_645` — a 57-vertex geometric structure with **seven concentric rings** at radii encoding all nine primary TI constants {0, 1, i, √2, e, φ, π, C, T}, plus an origin vertex.

| Ring | Radius | Vertex count | TI constant |
|---|---|---|---|
| 1 | C ≈ 0.437 | 6 | Emerick Constant (minimum coherence) |
| 2 | T ≈ 0.934 | 6 | Emerick BEC threshold |
| 3 | 1.000 | 8 | Unit existence |
| 4 | √2 ≈ 1.414 | 8 | Tritone, Bell inequality maximum / √2 |
| 5 | φ ≈ 1.618 | 8 | Golden ratio (aesthetic, self-similar) |
| 6 | e ≈ 2.718 | 10 | Euler's number (exponential growth) |
| 7 | π ≈ 3.142 | 10 | Pi (transcendental, circular) |
| Origin | 0 | 1 | Vacuum / zero |
| **Total** | | **57** | |

**Why the vertex counts matter:** the 8-fold counts in Rings 3–5 are not arbitrary. They predict the **Power-of-8 group coherence** formula 1 − (1 − C)^8 ≈ 0.99 BEC saturation. This is a collective phenomenon that the 2-D Graph cannot derive — it lives natively on the Crystal.

**Phase interpretation** (from urb_645 §2):

| Phase | Condition | TI Truth |
|---|---|---|
| BEC | Global coherence, all rings phase-locked | TRUE |
| Supersolid | Partial coherence, long-range order | TI-Indeterminate |
| FQH | Fractional coherence, emergent | TI entry |
| Mott | Localized, incoherent | FALSE |
| Fragmented | Contradicted by multiple incoherent sources | Double-Tralse |

---

## Figure 4 — Graph ↔ Crystal: the projection pattern

**File:** `papers/figures/pd_pass9/fig4_graph_to_crystal_projection.png`

**What it shows:** a side-by-side panel illustrating the **Graph is the orthogonal projection of the Crystal** principle.

- **Left panel:** the PD Crystal in the complex plane, with five sample points scattered at various positions and dashed projection lines dropping each point onto the real axis.
- **Right panel:** the resulting PD Graph (1-D scalar), showing where each sample point lands after projection. The grayed text at the bottom — *"← Loses imaginary-axis (DT/Tralse) information →"* — is the punch line.

**The relationship in one line:** **The Graph gives you the first moment (real-part) of the Crystal state.** Two different complex-plane states can project to the same scalar position; the scalar projection cannot tell them apart. This is exactly the same relationship as between the TI Sigma Graph and the TI Sigma Crystal: the projection is the empirically-tractable working object; the full object is the mathematical / theoretical object that contains structural information not visible in the projection.

**Practical rule** (after urb_645 §5):

| If the question is about … | Use … |
|---|---|
| Individual PD scoring | The Graph (scalar) |
| Bayesian update on a single data stream | The Graph (scalar) |
| Linear baselines | The Graph (scalar) |
| τ-without-δ vs δ-without-τ separation | The Crystal (complex plane) |
| Phase transitions / discontinuities | The Crystal (complex plane) |
| Cross-domain frequency analysis | The Crystal (full polytope) |
| Power-of-8 coherence | The Crystal (full polytope) |

---

## Reproducibility

```bash
cd papers/figures/pd_pass9
python generate_pd_figures.py
```

Requires `matplotlib` and `numpy` only. All four PNGs are regenerated; no external network access, no API keys, no random seeds. Output is byte-deterministic given the matplotlib version.

The figures use Pass 8.2-ratified vocabulary throughout — DT/Tralse axis, Principal Indeterminate Region, Transcendent Ring, PD principal axis, Emerick Crossover. Any future Brandon-rename of these labels can be applied by editing the strings in the generator script and re-running.

---

## What these figures do NOT show

- They do **not** depict the Pass 8.1 affine projection PD(s) = 5(σ − 1/2) + i·γ/γ_scale onto the Riemann critical strip. That mapping is mathematical-text only and would benefit from a future Figure 5 if Brandon directs.
- They do **not** depict the urb_736 25-threshold table or the LCC / GILE → PD lookup table. Those are tabular not geometric.
- They do **not** animate phase transitions on the TSC. A future deliverable could produce phase-transition animations (Mott → Supersolid → BEC sweep).
- They do **not** depict the AA (Authority Axis) as the 5th truth-axis. The truth-axis space is currently 5-dim and 2-D figures cannot render it; would require a separate diagrammatic treatment.

---

*End of Pass 9 visualizations paper. Open the four PNG files in `papers/figures/pd_pass9/` for the actual graphics.*

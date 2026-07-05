# HEM Dimensions in the 8D Theory — Updated Overview

**Status:** OVERVIEW / EDITORIAL CONSOLIDATION (not a ratification — canonical principle count unchanged at **81**)
**Date:** 2026-07-05
**Supersedes (as the current overview of HEM dimensions):** `papers/HEM_DIMENSIONAL_SYNTHESIS.md` (Dec 2025) — see §7 for exactly what carried over and what was retired.
**Verified against live code:** `lcc_virus_gile_inference.py`, `gsa_core.py`, `bok_harmonics.py` (these define the *operational* HEM dimensions actually computed by the platform).

---

## 0. Honesty preface (EVD-1 / #69)

This document is an **overview**, not a new principle. Three honesty flags apply throughout and are spelled out in §7:

1. **"Spectrum exhaustion" is not a pre-existing term in the corpus.** Before this overview, a full-text search (`rg`) returned **zero hits** for "spectrum exhaustion" / "spectral exhaustion" anywhere in the corpus (the phrase now appears only inside this document and its `replit.md` cross-ref). The real, code-backed metric the phrase most plausibly refers to is **HEM-D3 spectral purity** (`dominant-frequency power / total power`), with the closely related **spectral entropy** used for GILE-I. Rather than invent a definition for a term that did not exist, §3.3 states the actual metrics and notes the terminology gap. If "spectrum exhaustion" is meant to name something *else*, it needs a first definition — it was not in the corpus prior to this document.
2. **The "everything reduces to L × E" thesis of the 2025 synthesis is retired.** Per canon (`replit.md`, LCC composition ruling), the multiplicative `L × E` form was **refuted (B4, multiplicative cancellation)** and replaced by the additive asymmetric-cap UOP composition `J(G,H) = f(G) + g(H)`. The two pillars (Truth = GILE, Existence = HEM) are kept **separate**, not collapsed to one 2D product.
3. **"HEM" has two distinct historical senses.** Current canon: **HEM = the Holistic Existence** pillar/matrix (the "how much is there" existence-content axis; the code calls its scalar the *Holistic Existence Score*). Legacy: in the Nov-2025 `TRALSEBIT_DIMENSIONAL_ARCHITECTURE.md`, "HEM" abbreviated **Heart-EEG-Mendi** (a biometric *device* triad). These are different referents; this overview uses only the current sense.

---

## 1. The 8D structure: 4 GILE + 4 HEM

The "8D theory" is the **two-pillar Being-Optimization model** (the BOK tetrad pair): every i-cell / entity / claim is scored on **eight** dimensions, split evenly into two orthogonal pillars.

| Pillar | Question | Dimensions |
|--------|----------|------------|
| **GILE** (Truth) | *How true / good / right is it?* | G, I, L, E |
| **HEM** (Existence) | *How much of it is there?* | D1, D2, D3, D4 |

- **Cardinality.** `{G, I, L, E, D1, D2, D3, D4}` = 8. This 4+4 split is the E₈ = D₄ ⊕ D₄ signature (`papers/urb_622_empirical_foundations_bok_gile_hem_lattice.md`: E₈ contains two copies of D₄ — one for GILE, one for HEM) and the 8 = 4+4 Dirac structure (`papers/urb_699...`, wing/arm ratio ≈ 1.96 ≈ 2.0). **Honest note:** the 4+4 → E₈ mapping is a *structural* claim (cardinality + lattice signature), not a derivation that reality *must* be E₈.
- **Provenance of the 4-HEM count.** HEM was originally posited as **6D** (D1–D6). `papers/PASS_37_GILE_HEM_8D_IDENTITY_EQUATION_8_CONSTANTS_MAPPING_2026-05-11.md` reduces 6D → 4D by subtracting two overlaps: **D5 (Intrinsic Presence / Vitality)** overlaps GILE-E, and **D6 (L × E coupling)** is an interaction term, not an independent axis. `GILE 4D + HEM 6D − 2 overlaps = 8D`. This reduction is *Pass-37-interpretive*, not Brandon-ratified (the synthesis doc does not state the overlaps explicitly); see PASS_37 §7 C1.

---

## 2. The four HEM (Existence) dimensions — abstract definitions

Each HEM dimension is an **abstract existence axis** that is instantiated by a **domain-specific metric**. The abstract names are stable; the metric changes with the substrate (EEG / i-cell signal vs. market data vs. audio, etc.).

| Dim | Abstract axis | What it measures |
|-----|---------------|------------------|
| **D1** | Physical-Energetic | Energetic robustness / amplitude stability of the signal |
| **D2** | Social-Historical | Contradiction load (the "Tralse meter") — internal/among-sources coherence |
| **D3** | Aesthetic-Structural | Structural cleanliness / spectral purity — how far from noise |
| **D4** | Conscious-Experiential | Rate of coherence change — how fast the state is evolving |

**Numeric identity:** D3 (Aesthetic-Structural) is numerically **== GILE-E** (Elegance), per the B116 rename (`replit.md`; GILE-E = Elegance == HEM-D3). The two pillars stay conceptually separate (Truth vs Existence) even where one HEM dimension shares its number with a GILE dimension.

---

## 3. Mathematical / operational definitions + metrics (as actually computed)

All formulas below are transcribed from `lcc_virus_gile_inference.py` (i-cell / EEG substrate) and `gsa_core.py` (market substrate). Each dimension is a scalar in **[0, 1]**.

### 3.1 HEM-D1 — Physical-Energetic (amplitude stability)

- **Metric (EEG / i-cell):** inverse coefficient of variation of signal magnitude.
  `D1 = 1 − min(CV, 1)`, where `CV = std(magnitude) / mean(magnitude)`.
- **Metric (market, `gsa_core.py`):** volume-weighted price stability (low drawdown + low volatility → high D1).
- **Reading:** high D1 = energetically robust, low-volatility existence; low D1 = flickering / unstable.

### 3.2 HEM-D2 — Social-Historical (contradiction ratio / Tralse meter)

- **Metric (EEG / i-cell):** contradiction ratio across corroborating vs. contradicting resonance streams (the "Tralse meter," URB #619).
- **Metric (market):** 52-week position (institutional-presence / historical-standing proxy).
- **DT gate:** `D2 > 0.65 → Double-Tralse (MI) risk` → pause and flag for human review (MR Level-1 screen).
- **Reading:** D2 is the one HEM dimension that is **inverted** in the aggregate score (high contradiction → low existence quality).

### 3.3 HEM-D3 — Aesthetic-Structural (spectral purity) — *the "spectrum exhaustion" metric*

- **Metric (EEG / i-cell):** **spectral purity** = `dominant-frequency power / total power`.
  `D3 = P(f_dominant) / Σ P(f)`. High D3 = clean, structured, single-tone signal; low D3 = noisy / diffuse.
- **Related metric (used for GILE-I, not D3):** **normalized spectral entropy** of the noise residual — `H = −Σ pᵢ ln pᵢ`, normalized by `ln N`. High entropy = rich multi-frequency structure.
- **Metric (market):** technical-pattern quality (clean-chart proxy).
- **Terminology honesty:** the phrase *"spectrum exhaustion"* does not appear in the corpus. Spectral **purity** (concentration of power in the dominant peak) and spectral **entropy** (spread of power across the spectrum) are the two real, opposite-signed spectral metrics in the code. "Spectrum exhaustion" is *not defined anywhere*; treat this section as the closest verified referent, not as a rename.

### 3.4 HEM-D4 — Conscious-Experiential (coherence velocity)

- **Metric (EEG / i-cell):** `D4 = d(LCC)/dt` — the rate of change of the LCC coherence score.
- **Metric (market):** momentum-of-momentum (second derivative of trend).
- **Scoring shape:** D4 contributes to the aggregate via a **peaked** term — moderate change (≈0.5) scores highest; both static (≈0) and violently changing (≈1) score lower: `contribution = 1 − 2·|D4 − 0.5|`.
- **Reading:** near-zero = crystallized/static; high = rapidly evolving; the healthy zone is moderate evolution.

---

## 4. Aggregation, weights, and constants

### 4.1 HEM Score (Holistic Existence Score)

The two engines aggregate the four HEM dimensions **differently** — not only in weights but in *orientation handling* — because their D2/D4 metrics are oriented differently by domain.

**Market form — ESV (`gsa_core.py`, line ~1082):**

```
ESV = 0.25·D1 + 0.25·D2 + 0.30·D3 + 0.20·D4
```

*No inversion, no peaking* — here D2 = 52-week position and D4 = a momentum sigmoid, both already oriented so higher = better.

**i-cell / EEG form (`lcc_virus_gile_inference.py`):**

```
HEM = clip( [ D1 + (1 − D2) + D3 + (1 − 2·|D4 − 0.5|) ] / 4 , 0, 1 )
```

*Equal weights, with **D2 inverted*** (here D2 = contradiction ratio, so higher = worse) *and **D4 peaked** at 0.5* (here D4 = coherence velocity, healthiest at moderate change).

**Drift note:** the two aggregations are genuinely unreconciled — different weights (0.25/0.25/0.30/0.20 vs. equal 0.25 each) **and** different D2/D4 orientation handling. This traces to the domain-specific D2/D4 metrics (§3.2, §3.4), not to a single canonical HEM-score function. Flagged, not silently harmonized. The **0.25/0.25/0.30/0.20 weights are the `gsa_core` (market) set**; do not read them as inverting/peaking D2/D4.

### 4.2 GILE composite (for completeness — the other pillar)

```
GILE = 0.4142·G + 0.25·I + 0.18·L + 0.15·E     (URB #576 canonical weights)
GILE Truth Score = GILE_composite × HEM_Score
```

**Drift note (three different GILE weight sets in-repo):**
- **Canonical (URB #576):** G .4142 / I .25 / L .18 / E .15 — used by `lcc_virus_gile_inference.py` (`GILE_W`).
- **Market-tuned (`gsa_core.py`, `gile_weights` default):** G 0.20 / I 0.25 / L 0.25 / E **0.30** — a domain profile, **not** canonical (note E is weighted highest here).
- **Legacy (`HEM_DIMENSIONAL_SYNTHESIS.md` §1.1):** G 40% / I 25% / L 25% / E 10% — **superseded**.

Only the URB #576 set is canonical; the `gsa_core` set is a domain-tuned profile and the synthesis set is retired. This cross-engine divergence is flagged, not harmonized.

### 4.3 Threshold constants

| Symbol | Value | Role |
|--------|-------|------|
| **ET** (Emerick Threshold) | √2 − 1 ≈ **0.4142** | GILE-Truth onset; also GILE-G weight |
| **C** (Emerick Constant) | 1/(φ·√2) ≈ **0.4370** | LCC / HEM-Existence threshold |
| **T** (BEC threshold, in code) | 1 − e^(−e) ≈ **0.9340** | Full-coherence / "True" cut in `lcc_virus_gile_inference.py` |
| **G\*** (Radiant Cap) | √(1 − e⁻²) ≈ **0.930** | UOP interior optimum (canonical, `replit.md`) |

**Honest note on the ~0.93 collision:** the code's BEC threshold `T = 1 − e^(−e) ≈ 0.9340` and the canonical Radiant Cap `G* = √(1 − e⁻²) ≈ 0.92987` are **two different constants** that both round to ≈0.93. They are not the same number and were derived differently; memory records that "LCC_RADIANT has two definitions." This overview does not resolve that — it flags it.

---

## 5. HEM measurement zones (True / Tralse / Indeterminate / False)

Carried forward from the 2025 synthesis addendum (still consistent with current canon):

- **True** — high D1/D3, D2 near zero, D4 moderate: intense, coherent, vibrant existence.
- **Tralse** — high D1/D3 but D2 **elevated**: rich existence with *productive* internal tension (generative, not diseased).
- **Indeterminate** — all dimensions mid-range and unresolved: genuine in-between-ness (transition, early recovery), not a failure to categorize.
- **False** — high D2, low D4: contradictory existence that destroys rather than creates (pathological states).

Therapeutic direction (Mood Amplifier): move profiles from Indeterminate/False → Tralse/True by **raising D1, D3, D4-toward-moderate and lowering D2**.

---

## 6. The two HEM D1–D4 labelings (reconciliation)

The corpus contains **two** D1–D4 schemes. Both are real; they are different vintages of the same axes.

| Dim | **Operational** (live code — canonical for computation) | **Original 6D synthesis** (`HEM_DIMENSIONAL_SYNTHESIS.md` §1.3) |
|-----|--------------------------------------------------------|----------------------------------------------------------------|
| D1 | Physical-Energetic (amplitude stability) | Complexity (PAS) — many interacting parts |
| D2 | Social-Historical (contradiction ratio) | Contradiction Ratio — internal coherence |
| D3 | Aesthetic-Structural (spectral purity) | Info Footprint (AMI) — meaningful connections |
| D4 | Conscious-Experiential (d(LCC)/dt) | Relational Meaning — co-created significance |
| D5 | *(folded into GILE-E)* | Intrinsic Presence / Vitality |
| D6 | *(folded — L×E interaction, retired)* | (Interaction Term) L × E coupling |

**Only D2 (Contradiction Ratio) is stable across both schemes.** The operational scheme is what the platform actually computes and is treated as canonical here; the 6D synthesis is preserved as the historical/theoretical origin. Harmonizing the two labelings fully is left **open**.

---

## 7. What carried over vs. what was retired from the 2025 synthesis

**Carried over (still canon):** the 6D→4D reduction rationale (D5/D6 overlaps), the HEM measurement zones (§5), the three-layer truth architecture position (HEM = measurement instrument for the Four Dimensions of Truth), the EAR-irreducibility of HEM vs. GILE vs. Four-C's.

**Retired / superseded:**
- The central thesis "all dimensions reduce to **L × E**" — `L × E` refuted (B4); pillars kept separate; composition is now `J = f(G) + g(H)`.
- The old GILE weights (40/25/25/10) → `.4142/.25/.18/.15`.
- The Nov-2025 Tralsebit **21D/24D "33-bit sacred"** numerology (`TRALSEBIT_DIMENSIONAL_ARCHITECTURE.md`) is **not** canonical dimensional structure; it is a legacy numerological artifact (Masonic/kundalini "33" alignments) and uses "HEM" in the retired *Heart-EEG-Mendi* device sense.
- The stale stub `extracted_equations/HEM_EQUATIONS_EXTRACTED.md` (old 6D V,A,D,W,T,S "ESS→HEM") is an unfilled template, not a definition source.

---

## 8. Open items / falsifiers

- **Terminology:** "spectrum exhaustion" was undefined pre-this-overview — needs a first definition or confirmation it means D3 spectral purity (§3.3).
- **Aggregation drift:** the market ESV (weighted, no D2 inversion / no D4 peaking) and the i-cell/EEG HEM score (equal weights, D2 inverted, D4 peaked) are unreconciled (§4.1) — driven by domain-specific D2/D4 orientation.
- **GILE weight drift:** three GILE weight sets in-repo (canonical URB #576, market-tuned `gsa_core`, legacy synthesis) — only URB #576 canonical (§4.2).
- **Labeling drift:** operational vs. 6D-synthesis D1–D4 (§6) unreconciled.
- **Constant collision:** BEC `T` vs. Radiant Cap `G*` both ≈0.93 (§4.3).
- **Structural, not derivational:** the 4+4 → E₈/D₄ mapping and the 8↔8-constants mapping (PASS_37) are cardinality/structure claims; **none of the 8 individual constant-mappings is empirically established** (PASS_37 §1). ELEG-F1 (GILE-E == HEM-D3) OPEN.

---

## Cross-references

- `book/ch06_gile_vs_hem.md` — canonical conceptual treatment of the two pillars.
- `papers/PASS_37_GILE_HEM_8D_IDENTITY_EQUATION_8_CONSTANTS_MAPPING_2026-05-11.md` — 8D = 4+4 reduction + 8-constants mapping.
- `papers/HEM_DIMENSIONAL_SYNTHESIS.md` — 2025 origin (this doc supersedes it as the *overview*).
- `papers/urb_622_empirical_foundations_bok_gile_hem_lattice.md` — E₈ = D₄⊕D₄ lattice grounding + threshold constants.
- `lcc_virus_gile_inference.py`, `gsa_core.py`, `bok_harmonics.py` — live operational definitions of the 8 dimensions.

---
name: HEM 8D dimensions overview (existence pillar)
description: The 4 HEM existence dimensions, their real code metrics, and the cross-engine drift to state honestly — for any future HEM/8D overview or edit.
---

# HEM dimensions in the 8D theory

8D = 4 GILE (Truth) + 4 HEM (Existence). Canonical overview doc: `papers/HEM_DIMENSIONS_8D_OVERVIEW_2026-07-05.md` (supersedes the Dec-2025 `papers/HEM_DIMENSIONAL_SYNTHESIS.md` as the overview).

## The 4 HEM abstract axes (operational, from live code)
- **D1 Physical-Energetic** — amplitude stability = `1 − min(CV,1)` (EEG/i-cell) / vol-weighted price stability (market).
- **D2 Social-Historical** — contradiction ratio / "Tralse meter" (EEG) / 52-week position (market). DT gate `D2>0.65`.
- **D3 Aesthetic-Structural** — **spectral purity = dominant-freq power / total power**; numerically == GILE-E (B116 rename).
- **D4 Conscious-Experiential** — `d(LCC)/dt` coherence velocity (EEG) / momentum-of-momentum (market).

## Honest flags that MUST accompany any HEM overview
- **"Spectrum exhaustion" is NOT a corpus term** (0 hits pre-overview). The real metric is **D3 spectral purity**; spectral *entropy* (different, opposite-signed) is used for GILE-I. Don't invent a definition for it.
- **Two HEM aggregations, genuinely unreconciled** — NOT just different weights but different D2/D4 *orientation handling*:
  - `gsa_core.py` ESV (market): `0.25·D1+0.25·D2+0.30·D3+0.20·D4` — **no** D2 inversion, **no** D4 peaking (its D2=52W-pos, D4=momentum-sigmoid already higher=better).
  - `lcc_virus_gile_inference.py` (EEG): `[D1+(1−D2)+D3+(1−2|D4−0.5|)]/4` equal weights — **D2 inverted, D4 peaked at 0.5**.
  - **Do not** merge these into one formula (an earlier draft wrongly wrote `0.25·(1−D2)+…0.20·(1−2|D4−0.5|)` — that formula does not exist in either engine).
- **Three GILE weight sets in-repo:** canonical URB#576 `G .4142/I .25/L .18/E .15` (lcc_virus `GILE_W`); market-tuned `gsa_core` `gile_weights` default `(0.20,0.25,0.25,0.30)` = G.20/I.25/L.25/E.30 (E highest!); legacy synthesis `40/25/25/10` (retired). Only URB#576 canonical.
- **Two ≈0.93 constants (collision):** BEC `T=1−e^(−e)≈0.9340` (code "True" cut) vs Radiant Cap `G*=√(1−e⁻²)≈0.92987` (canonical UOP optimum). Different numbers.
- **HEM has two senses:** current = *Holistic Existence* (the pillar); legacy = *Heart-EEG-Mendi* device triad (Tralsebit paper). Use current only.
- **L×E "reduction" thesis RETIRED** (B4, multiplicative cancellation); pillars kept separate, composition `J=f(G)+g(H)`.
- **Two D1–D4 labelings:** operational (code, canonical for compute) vs Dec-2025 6D-synthesis §1.3; only **D2 (contradiction)** stable across both. 6D→4D via D5(→GILE-E)+D6(L×E) folds = Pass-37-interpretive, not Brandon-ratified.
- 4+4→E₈=D₄⊕D₄ (urb_622) is a **structural/cardinality** claim, not a derivation; PASS_37 8↔8-constant map: none of the 8 empirically established.

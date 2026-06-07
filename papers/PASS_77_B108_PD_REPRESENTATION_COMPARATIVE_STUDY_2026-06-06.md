# Pass-77 B108 — Comparative Study of the PD Truth-Representations: When to Use Each, Pros & Cons

**Date:** 2026-06-06 · **Pass:** 77 · **Batch:** B108 · **Status:** empirical study (candidate selection-guide, canonical count unchanged 79)
**Anchors:** `analyses/pass77_b108_pd_truthlabel_link_2026_06_06/` (`compare_representations.py`, `comparison_results.json`); reuses `analyses/fleiss_binary_vs_5tier_1000_2026_05_27/` (500 gold props × 3 raters) + partial `ratings_pd.json` (continuous PD cross-check). Faithful coords from `papers/figures/pd_pass9/generate_pd_figures.py`, `analyses/pass77_b61_maxwell_gile_backward_matrix/b61.py`, `analyses/pass77_b42_crystal_falsifiers/run_falsifiers.py`, `papers/urb_630_tsc_e8_error_correcting_code_five_valued_logic.md`.

## 0. Why this batch (user pivot)

The old scalar PD **(−3, +2)** scale is *superseded* as THE representation: PD is now a **complex** object (real PD-axis + imaginary MI/Tralse axis) integrated with the **64D GILE Matrix**, with **32D**, **TI Sigma Graph (TIG)**, and **TI Sigma Crystal (TSC)** variants. Brandon's directive: **test all variants, decide when each is appropriate, give pros/cons — and reuse prior data.** This study does exactly that with **zero new API calls** (reuses the B26/B63-lineage 500-gold 5-tier rater corpus).

## 1. The six representations (faithful definitions)

| # | Representation | Geometry | Labels it can distinctly encode | Anchor |
|---|---|---|---|---|
| 1 | **Scalar PD** | 1-D real line (−3,+2); thresholds ±1, ±φ, ±e, ±π, Emerick ±1/√2 | T, I, F, MI (**NA off-axis**) | fig1 |
| 2 | **Complex PD** | 2-D: real = PD principal axis, imag = MI/Tralse axis | **all 5** (MI=+e·i, NA=−e·i) | fig2 |
| 3 | **TI Sigma Graph (TIG)** | 9-constant graph {0,1,i,√2,e,φ,π,C,T}, 15 edges, χ=4 (B68); = real-axis projection of the Crystal + the i vertex | T, I, F, MI (**NA off-graph**) | fig4 |
| 4 | **32D / 64D GILE Matrix** | 4 GILE-values × 4 truth-axes × 4 truth-labels = 4³; **NA folded into MI** for closure | 4 (T, F, τ/I, MI; **NA≡MI**) | b61 |
| 5a | **TSC / TECC (table)** | 8-D urb_630 5-valued code, *literal table* (DT/TF collinear) | all 5 | b42 F2 |
| 5b | **TSC / TECC (orthogonal)** | 8-D code, sec-2.2 distinct-axis embedding | all 5 | b42 F2 |

## 2. Method (one apples-to-apples benchmark, reused data)

Each representation is treated as an **encoder**: truth-label → coordinate, with a Euclidean distance. For every gold proposition we take its **3 real rater labels**, map each to its codeword, average to a centroid, and **decode to the nearest codeword**. Because all six share the *same* rater inputs, accuracy differences come purely from the **geometry's separation power**. **#69 fair-denominator handling:** when a representation cannot encode *any* of a proposition's rater labels (e.g. an all-NA triplet under a rep with no NA codeword), that proposition is scored as an **explicit miss**, NOT dropped — so every representation is benchmarked on the **same 500 props** (an earlier draft silently dropped these, inflating the NA-blind reps to 0.903; corrected here). Metrics: representational capacity (log₂ #labels), codeword min-distance → error-correction radius (d_min/2), decode accuracy, per-label recall, NMI / AMI / ARI vs gold, silhouette, and a **controlled noise-robustness Monte-Carlo** whose noise model **is the empirically-measured rater confusion matrix** (reused, seeded; same miss-counting rule).

## 3. Results (n = 500 gold props, same denominator for all reps)

| representation | dim | #lab | cap | d_min | r_corr | acc | NMI | AMI | ARI | sil |
|---|---|---|---|---|---|---|---|---|---|---|
| scalar_PD_1D | 1 | 4 | 2.00 | 1.000 | 0.500 | 0.746 | 0.841 | 0.835 | 0.813 | 0.741 |
| complex_PD_2D | 2 | 5 | 2.32 | 2.000 | 1.000 | **0.918** | 0.837 | 0.830 | 0.809 | 0.771 |
| TIG_graph | 2 | 4 | 2.00 | 1.000 | 0.500 | 0.746 | 0.841 | 0.835 | 0.813 | 0.739 |
| GILE_matrix_64D | 4 | 5† | 2.32 | **0.000** | 0.000 | 0.746 | 0.760 | 0.698 | 0.687 | 0.550 |
| TSC_TECC_table | 8 | 5 | 2.32 | 0.496 | 0.248 | **0.922** | 0.841 | 0.837 | 0.827 | 0.776 |
| TSC_TECC_orthogonal | 8 | 5 | 2.32 | 1.030 | 0.515 | **0.922** | 0.842 | 0.836 | 0.818 | 0.786 |

† 64D lists 5 inputs but NA and MI share one codeword (fold) → 4 *distinct* → NA recall 0.

**The accuracy splits cleanly into two tiers at exactly the NA fraction.** The three reps that cannot keep NA separate — scalar & TIG (no NA codeword) and 64D (NA folded into MI) — all land at **0.746**; the three that natively separate NA (complex, both TECC) all land at **0.918–0.922**. The gap (0.918 − 0.746 = **0.172**) ≈ the **NA share of the gold set** (87/500 = 0.174): the *entire* accuracy difference between the tiers is the NA-handling, nothing else.

**Per-label recall (T / F / I / MI / NA):** T≈0.99, F=1.0, I=1.0 everywhere; **MI≈0.72–0.74 across ALL reps** (a rater-disagreement ceiling on MI, not a geometry artifact); **NA = 0.0** for scalar / TIG / 64D, **0.88** for complex + both TECC.

**Controlled noise robustness (decode accuracy as raters increase 1→3→5→9):**

| representation | 1 | 3 | 5 | 9 |
|---|---|---|---|---|
| scalar_PD_1D | 0.742 | 0.749 | 0.754 | 0.755 |
| TIG_graph | 0.742 | 0.758 | 0.773 | 0.786 |
| GILE_matrix_64D | 0.745 | 0.767 | 0.776 | 0.789 |
| complex_PD_2D | 0.921 | 0.950 | 0.967 | 0.982 |
| TSC_TECC_table | 0.921 | 0.968 | 0.983 | **0.994** |
| TSC_TECC_orthogonal | 0.921 | 0.966 | 0.981 | 0.993 |

**Continuous-PD cross-check** (partial reused ratings, mean PD per gold): T +1.96, I +0.15, F −2.01, **MI −2.60**, NA −1.82. MI sits **next to F** on the real line (gap ≈0.6) — *the* reason 1-D reps confuse MI/F; NA lands in soft-false with no natural 1-D home.

## 4. Findings (#69-honest)

1. **The imaginary axis is the single biggest upgrade — and it is the *only* thing that moves accuracy here.** The two-tier split (§3) is exact: every rep that fails to keep NA on its own axis sits at **0.746**; every rep that adds the imaginary/extra axis to hold NA jumps to **0.918–0.922**, and the gap equals the NA fraction. The imaginary axis also turns *flat* noise-robustness (scalar plateaus at ~0.75 no matter how many raters) into *scaling* robustness (complex 0.92→0.98). The whole "PD needs a real **and** imaginary axis" claim is **empirically vindicated** here.
2. **Scalar PD = TIG on this task** (both 0.746, identical d_min, NMI, AMI, ARI). TIG's quantitative label-separation is identical to scalar (it *is* the real-axis projection of the Crystal). TIG's extra value is **named-constant semantics + the i vertex for MI**, not better classification. Use TIG for *interpretable visualization*, not for accuracy.
3. **The 64D/32D GILE Matrix lands at the same NA-blind floor (acc 0.746) — it is NOT uniquely the worst** (it ties scalar/TIG); it merely fails the *label-decision* task for a different reason: NA is *folded into MI* for 4³ closure (d_min = 0, NA recall 0). Its low NMI/silhouette (0.760 / 0.550) are the honest cost of that fold. **The matrix is a "ledger," not a classifier:** its payoff is the **4 GILE × 4 truth-axis context per label** (goodness/meaning/love/aesthetics state), which this label-only test cannot reward. Don't use 64D to *decide* a truth label; use it to *carry the full GILE state* once the label is known. 32D ≡ 64D on label-separation (differs only in operator structure / U(32)).
4. **The Crystal/TECC is the most accurate and most noise-robust** (acc 0.922, robustness → 0.994 at 9 raters) **and** the only family that natively separates all 5 labels (NA→EV). **BUT** the #69 caveat from B42 stands: under the **literal urb_630 table**, DT(MI)/TF(F) are nearly *collinear* → d_min 0.496, **correction radius 0.248 — below the advertised sin18° = 0.309** (the radius, not d_min, is the quantity that must clear the threshold). Its strong empirical robustness comes from **real rater centroids rarely landing in the MI/F ambiguity zone**, not from the advertised pentagon threshold. The **orthogonal** embedding repairs the geometry (d_min 1.030, radius 0.515) at no accuracy cost — so *if* the Crystal is used for error-correction, the distinct-axis embedding must be specified.

## 5. Selection guide — when to use each

| Use case | Recommended representation | Why |
|---|---|---|
| Quick human-readable scoring / 1-D plot | **Scalar PD / TIG** | cheapest, intuitive; accept that NA & MI/F blur |
| Default truth-labelling that must keep indeterminacy separate from truth-polarity | **Complex PD (2-D)** | minimal rep that holds all 5; robustness scales with raters; d_min 2.0 |
| Carrying full ethical/meaning/aesthetic agent state (UOP optimization, GILE-HEM) | **64D / 32D GILE Matrix** | rich GILE×axis context per label; *not* for label decisions (NA folded) |
| Noisy / adversarial / MI-saturated inputs where robustness & all-5 separation matter | **TSC / TECC (orthogonal embedding)** | best accuracy + best noise-correction; specify distinct-axis embedding |

**Pros/cons one-liners.** Scalar/TIG: + simplest, interpretable / − no NA, no error-correction (flat robustness). Complex: + all 5 with minimal dims, best separation / − loses GILE context, NA placement is a representational convenience (NAO-1). 64D/32D: + full GILE state, algebraic 4³ closure / − ties the NA-blind accuracy floor (0.746), NA≡MI (not for label decisions). TSC/TECC: + most robust, native 5-valued, E8 packing / − 8-D, hard to visualize, *literal table correction radius (0.248) below the advertised 0.309* (must use orthogonal embedding).

## 6. Honest limitations

- The 64D/32D were evaluated at their **truth-label factor only** — we lack per-proposition GILE-dimension and truth-axis ratings, so the matrices' *distinctive* payoff (context) is argued structurally, not measured. A future batch could rate a subset on the 4 GILE dims × 4 axes to populate the full 64 cells (≈$0 with the existing LLM raters).
- MI recall ~0.73 is a **rater ceiling** shared by all reps; it caps every accuracy here and is the real bottleneck, not geometry.
- Label→coordinate maps for NA (complex/TECC) and for graph vertices (TIG) are documented modeling choices, flagged where they go beyond the literal corpus.

## 7. Falsifiers (OPEN)

- **PDR-F1 (imaginary-axis necessity):** a 1-D representation that matches complex/TECC NA-recall and scaling robustness would refute finding #1.
- **PDR-F2 (matrix-context payoff):** populate the full 64D with real GILE×axis ratings; if 64D does **not** beat complex on any *state-dependent* task, its ledger-value claim weakens.
- **PDR-F3 (Crystal error-correction):** demonstrate the literal-table TECC achieving its advertised 0.309 correction radius without the orthogonal re-embedding.

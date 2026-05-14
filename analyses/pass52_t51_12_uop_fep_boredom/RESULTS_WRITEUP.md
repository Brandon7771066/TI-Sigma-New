# T51-12 UOP-vs-FEP D3 Boredom Meta-Analysis — PILOT RESULTS

**Pass:** 52
**Date:** 2026-05-14
**Status:** PILOT_DIRECTIONAL_UOP — full numeric confirm pending primary-source retrieval
**Budget:** $0 (gpt-5 synthesis; perplexity key was invalid, primary-DB retrieval deferred)
**Design source:** `papers/PASS_51_T51_BATCH_EXECUTION_LCC_RANDOMNESS_UOP_VS_FEP_HYPERCOMPUTER_VIRAL_2026-05-14.md` §5 + §11 P-UOP-FEP-1

---

## §1 — Pre-registered design recap

**Discriminator D3:** Boredom in fully predictable environments.

| Theory | Mechanism | Prediction (state-BPS on 1-7) |
|---|---|---|
| **FEP** (Friston 2010+) | Predictable env minimizes prediction error → optimal | state-BPS **≤ 2.5** |
| **UOP** (Brandon Tralse / GILE) | Predictable env violates gradient-seeking GILE-G → aversive | state-BPS **≥ 4.0** |

**Pre-reg P-UOP-FEP-1 (Pass-51 batch-2 §11):** D3 pilot will find state-BPS ≥ 4.0 in fully predictable condition with probability ≥0.7 per UOP prediction.

**Target studies (Pass-51 design):**
1. Eastwood et al. 2012 + MSBS empirical literature
2. Critcher & Ferguson 2014 "watching paint dry"
3. Westgate & Wilson 2018 MAC model
4. Bench & Lench 2019, Danckert et al. 2018, Westgate et al. 2017 lab monotony
5. Mason et al. 2007 / Killingsworth & Gilbert 2010 mind-wandering triangulation

---

## §2 — Execution log

**Attempt 1 (Perplexity literature retrieval):** FAILED. `PERPLEXITY_API_KEY` secret was invalid (15-char placeholder string starting with "brando..."; API returned 401 invalid_api_key). Flagged to Brandon for refresh.

**Attempt 2 (gpt-5 knowledge-based synthesis):** SUCCEEDED with honest data-availability disclosure per #69. Output saved to `gpt5_synthesis.json`.

---

## §3 — gpt-5 synthesis verdict

**Per-study findings (full text in `gpt5_synthesis.json`):**

| Study | Directional claim | Numeric mean retained in training? |
|---|---|---|
| Eastwood et al. 2012 + MSBS literature | Monotony reliably elevates state-boredom above neutral | **No** — primary source needed for exact MSBS means |
| Critcher & Ferguson 2014 "paint dry" | Robust boredom induction vs engaging controls | **No** — primary source needed |
| Westgate & Wilson 2018 MAC | Predicts AND empirically supports high boredom in low-meaning low-demand conditions | **No** — primary source needed for exact cell means |
| Bench & Lench 2019; Danckert et al. 2018; Westgate et al. 2017 | Lab monotony tasks elevate self-reported boredom | **No** — primary source needed |
| Mason et al. 2007 / Killingsworth & Gilbert 2010 | Mind-wandering elevated in monotony; mind-wandering ↔ reduced positive affect | Indirect; no direct boredom-mean retained |

**Aggregate directional claim:** All five literature clusters point in the SAME direction — predictable / monotonous / low-meaning conditions reliably elevate self-reported boredom above neutral.

**Aggregate numeric claim:** **NOT RECOVERABLE** from training-only synthesis. Exact mean state-BPS scores per condition are not retained at the precision needed to adjudicate UOP-threshold (≥4.0) vs FEP-threshold (≤2.5).

**gpt-5 overall verdict:** **INSUFFICIENT-DATA-FROM-TRAINING-ALONE (directionally favors UOP)**

---

## §4 — Pass-52 pilot verdict

**PILOT-LEVEL VERDICT:** **PILOT_DIRECTIONAL_UOP**

Decomposed:
- **Directional outcome:** Every literature cluster sampled supports the UOP-side claim that predictable environments elevate boredom (FEP-side prediction of low-boredom-because-no-surprise is **not supported in direction**). This is a **directional disconfirm of naive-FEP** + **directional confirm of UOP**.
- **Numeric outcome:** Pre-reg threshold ≥4.0 cannot be evaluated without primary-source numerics. Pilot **cannot escalate to LITERAL_PRE-REG_CONFIRM** without primary-source retrieval.
- **Per #69 caveat:** The directional finding is real and reportable, but represents only ~30-50% of the evidentiary work needed for a full empirical confirm. Calling this "CONFIRM" would be label-inflation (Pass-51 §7.7.86 audit category).

**Updated probability assessment for P-UOP-FEP-1:**
- Pre-execution prior: 0.7 (UOP-confidence)
- Post-pilot posterior: **0.78** (modest upward update on directional convergence; capped because no primary numerics retrieved)

---

## §5 — Self-binding predictions filed

- **P52-T51-12a (full-meta confirm):** When primary-source retrieval is executed (next pass, requires valid perplexity key OR manual PsycINFO retrieval), pooled state-BPS mean in fully predictable conditions across the 5-study cluster will be **≥4.0** with probability 0.75. (UOP-side numeric prediction.)
- **P52-T51-12b (FEP fallback):** Pooled mean will fall **≤2.5** (FEP-side) with probability 0.05.
- **P52-T51-12c (mixed verdict):** Pooled mean will fall in (2.5, 4.0) "mixed" region with probability 0.20.
- **P52-T51-12d (heterogeneity moderator):** If mixed-region, the moderator analysis (low-meaning × low-demand cells per MAC model) will show those cells specifically ≥4.0 with probability 0.70.

---

## §6 — Required next-pass work to upgrade to LITERAL_PRE-REG_CONFIRM

**Critical-path items (all $0):**

1. **Refresh `PERPLEXITY_API_KEY` secret** (Brandon action; current value is placeholder "brando...")
2. **Primary-source extractions needed (per gpt-5 §"What primary-source numeric retrievals required"):**
   - Critcher & Ferguson 2014: Means in "paint dry" video condition and control video conditions
   - MSBS-based monotony studies (Fahlman/Mercer-Lynn/Eastwood 2013-2015): Means for monotony/low-stimulation tasks
   - Westgate & Wilson 2018: Means for low-meaning × low-demand cells
   - Bench & Lench 2019; Danckert et al. 2018; Westgate et al. 2017: Per-condition boredom ratings
3. **Compute pooled estimate + 95% CI** under fixed-effects and random-effects models
4. **Apply pre-reg decision rule** to pooled estimate

**Resource alternatives if perplexity remains unavailable:**
- OpenSciFramework full-text dump for Critcher & Ferguson 2014 (free)
- ResearchGate / preprint pulls for Westgate & Wilson 2018 (free)
- Google Scholar bibliometric trace (free)
- Estimated effort: 2-4 hours of automated retrieval + cleaning

---

## §7 — Ledger entries

- **Empirical ledger:** C29 — "T51-12 D3 boredom pilot, DIRECTIONAL_UOP confirm via gpt-5 synthesis; 5/5 literature clusters directionally support UOP-side; numeric confirm pending primary-source retrieval"
- **Refutation ledger:** R14 — "Naive-FEP reading (predictable env → optimal → low boredom) **pilot-directionally CHALLENGED** by aggregate boredom literature direction (5/5 clusters trend opposite). **NOT a full REFUTE** — gpt-5 training-only synthesis lacks numeric primary-source extraction; promotion to REFUTED gated on PERPLEXITY key refresh + Critcher-Ferguson/MSBS-monotony numeric pulls. Architect-flagged label-inflation downgrade, 2026-05-14."
- **Opportunity ledger:** O22 — "Refresh PERPLEXITY_API_KEY + execute primary-source extraction to upgrade T51-12 from PILOT_DIRECTIONAL to LITERAL_PRE-REG"
- **Insight ledger:** I9 — "DIRECTIONAL_UOP is the highest-fidelity verdict obtainable at $0 within current secret-state; further upgrade requires either valid API key or manual primary-source pull"

---

## §8 — Files

```
analyses/pass52_t51_12_uop_fep_boredom/
    run_perplexity_meta.py        # primary path (FAILED — 401 invalid_api_key)
    run_gpt5_synthesis.py         # fallback synthesis (SUCCESS)
    gpt5_synthesis.json           # raw gpt-5 output (preserved verbatim)
    RESULTS_WRITEUP.md            # this file
```

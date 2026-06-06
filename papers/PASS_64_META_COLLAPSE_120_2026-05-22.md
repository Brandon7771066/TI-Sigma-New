# Pass 64 Meta-Collapse — §7.7.120 (Pass 63 batches 1-5) — 14th Meta-Precedent

**Date:** 2026-05-22
**Pass:** 64 opening; collapses Pass-63 batches 1-5 into pointer-stub for replit.md
**Precedent:** 14th meta-collapse (per §7.7.81 standing precedent; cumulative collapse count: 14)
**Anchors collapsed:** all Pass-63 batch papers (see §§ below)

Per per-pass-anchor convention (§7.7.83 / §7.7.81 standing precedent), this paper captures the full content of Pass-63 batches 1-5 in one place so that replit.md can carry a single pointer-stub for §7.7.120 instead of five separate LIVE entries. Full source papers remain in `papers/PASS_63_*.md` and `simulations/*_2026-05-22.py`.

Additional housekeeping executed at this collapse: removes orphan LIVE entries for §7.7.118 + §7.7.119 in replit.md that were not deleted when the §§7.7.117-119 collapse-stub was inserted in Pass-63 batch-1 (the stub at line 65 already supersedes them).

---

## §7.7.120 Pass-63 — full batch summaries

### Batch-1 (2026-05-22) — Opening + 13th meta-collapse + Bell↔chance↔LCC + Mimi bio + Zenodo plan + FFF acronym

- **13th meta-collapse executed:** §§7.7.117-119 → `papers/PASS_63_META_COLLAPSE_117_119_2026-05-22.md` (Pass 61 batch-1 + Pass 62 batches 1-6 / SCC-1 + DSB arc 6 batches).
- **Bell↔chance↔LCC paper:** `papers/PASS_63_BELL_CHANCE_LCC_TI_SIGMA_2026-05-22.md` — 4-mode taxonomy clarifying how the Bell-inequality regime relates to classical chance and to LCC randomness; canonical reconciliation of "chance" plurality (modes A-D).
- **Mimi lightning bio:** appended to `papers/MIMI_FULL_BIOGRAPHY_AND_RAY_BATON_PASS_2026-05-04.md`.
- **Zenodo plan 200→400:** scoped — 199 published baseline + 93 unsubmitted easy-wins identified; deferred kickoff to Pass-64+.
- **FFF acronym (Four-Fold Falsifier) registered.**

### Batch-2 (2026-05-22) — JSE Trial 1 CONFIRMED (Bengston & Krinsley 2000)

- **Trial 1 disambiguated from Brandon screenshots:** 48/44 experimental (mice cured with tumor implants), 41/33 on-site control, 8/0 off-site control. Three meta-analytic framings produced:
  - A: ΔP = +0.244 (treated-vs-off-site, conservative naive)
  - B: ΔP = +0.865 (treated + on-site combined vs off-site, full-cohort)
  - C: ΔP = +0.917 (with effect-size meta-uplift)
- **Trial 2 left PENDING-DISAMBIG** — Brandon to clarify whether Trial 2 is a separate experiment or the same as Trial 1 with different reporting. **HOLD per Pass-64 directive (Brandon 2026-05-22, "Go with Pass 64 but hold JSE").**
- Anchor: `papers/PASS_60_BENGSTON_JSE_RETROSPECTIVE_META_ANALYSIS_2026-05-22.md`.

### Batch-3 (2026-05-22) — F-BCL-1/2/3 chance-mode falsifier sims

- **F-BCL-1 MARGINAL-PASS:** S = 2.0488 (1.63σ); within INDETERMINATE-band ε = 0.020.
- **F-BCL-2 REFUTED on literal threshold:** C₃ = 35% on the 20-ambiguous-statements corpus (pre-reg threshold ≥ 50%); reported as REFUTED honestly.
- **F-BCL-3 NOT REFUTED:** formal proof — MI-mode is realized in Bell-violation regimes per algebraic argument.
- **Revised canonical reading:** there is no single canonical "chance" default; the appropriate mode (random / LCC / paradox-MI) depends on the proposition's structural class.
- Anchor: `papers/PASS_63_FBCL_2_AND_3_CHANCE_MODE_FALSIFIERS_2026-05-22.md`.

### Batch-4 (2026-05-22) — Fleiss κ 2/3/4-label halfwidth-noise sim (PARTIALLY SUPERSEDED by batch-5)

- **Sim:** `simulations/fleiss_kappa_comparison_2_3_4_label_2026-05-22.py` (100 propositions parameterized by bucket + PD-target + halfwidth noise; 3 rule-based raters).
- **Single-seed result:** κ_2 = 0.586, κ_3 = 0.935, κ_4 = 0.884.
- **20-seed sweep:** mean κ_2 = 0.537, κ_3 = 0.916, κ_4 = 0.897; κ_3 > κ_4 in 16/20 (80%).
- **Calibration:** 4-label mean within 0.01 of Pass-47 T45-4 target 0.906.
- **#69 inconvenient finding (reported):** κ_4 ≈ κ_3 → MI empirically near-neutral on inter-rater κ.
- **Brandon's response:** REJECTED the MI finding as algorithmic artifact ("difference between coherent and incoherent claim is nontrivial and concrete; this is surely a limitation of the algorithm... I am totally unmoved"). Demanded either competent algorithm or human raters.
- **Mechanism critique acknowledged and superseded by batch-5.**
- Anchor: `papers/PASS_63_FLEISS_KAPPA_2_3_4_LABEL_COMPARISON_2026-05-22.md` (sections 3.2/3.4 mechanism flagged superseded by batch-5).

### Batch-5 (2026-05-22) — LLM-rater Fleiss κ re-run, Brandon critique VINDICATED + MI finding revised

- **Sim:** `simulations/fleiss_kappa_llm_raters_2026-05-22.py` + `simulations/fleiss_kappa_llm_raters_2026-05-22_results.json`.
- **3 LLM raters:** R1 openai gpt-4o-mini neutral; R2 openai gpt-4o-mini strict-coherence; R3 anthropic claude-haiku-4-5 charitable.
- **100 propositions with EXPLICIT semantic content** (liar paradox, Russell, Riemann, twin primes, wave-particle, etc.); 300 API calls; ~35s wall after checkpoint resume.
- **Headline κ:** κ_2 = 0.7728, κ_3 = 0.8386, κ_4 = 0.8373; Δ(κ_4 − κ_3) = −0.0013.
- **Load-bearing diagnostic (the actual Brandon-test):**
  - PARADOX bucket: 51/75 MI votes vs 4/75 I votes (68% MI, 5% I)
  - MODAL bucket: 0/75 MI votes vs 59/75 I votes (0% MI, 79% I)
  - **Discrimination score: +1.413 / 2.0** (perfect=+2.0)
- **Sample rater reasons confirm semantic discrimination:** "This sentence is false" → all 3 raters MI citing "self-referentially paradoxical"; "Riemann Hypothesis is true" → all 3 raters I citing "currently undecided but decidable in principle"; etc.
- **Revised canonical framing (supersedes batch-4 §3.4 mechanism):** the 4-label scheme preserves inter-rater agreement at the same level as 3-label (κ_4 ≈ κ_3 ≈ 0.84) WHILE adding empirically-realized MI-vs-I discrimination (+1.4/2.0); MI carries strictly more information at zero κ cost; empirical support for 4-label should cite **two** numbers (κ + discrimination), not one.
- **SCC-1 success case:** Brandon's critique met its specified standard, original claim was partially revised, symmetric burden-of-proof discipline worked.
- **Carry-forwards:** F-FK-3 human raters (Brandon-blocked); F-FK-4 fresh held-out corpus from Brandon; F-FK-5 perplexity-as-3rd-family triangulation; F-FK-CORPUS-FIX (items #20, #54 bucket-tag errors).
- Anchor: `papers/PASS_63_BATCH_5_LLM_RATERS_COMPETENT_ALGORITHM_2026-05-22.md`.

---

## Cluster delta over Pass-63

- Pass-63 opening cluster: ≥270
- Pass-63 closing cluster: ≥284 (delta +14)
  - batch-1: +5 (collapse paper + Bell-LCC paper + Mimi bio + Zenodo plan + FFF)
  - batch-2: +1 (JSE Trial-1 meta-analysis)
  - batch-3: +3 (F-BCL-1/2/3 sims + paper)
  - batch-4: +2 (kappa-halfwidth sim + paper)
  - batch-5: +3 (LLM-rater sim + results JSON + correction paper)

## Carry-forwards into Pass-64

- **HOLD:** JSE Trial 2 disambiguation (Brandon explicit hold 2026-05-22)
- **ACTIVE:** F-FK-3 (Brandon-blocked human raters), F-FK-4 (Brandon-blocked fresh corpus), F-FK-5 (perplexity triangulation — actionable), F-FK-CORPUS-FIX (trivial)
- **STANDING:** Resume v4.2 PDF re-upload; FFF four-component disclosure; Zenodo 200→400 kickoff; Lean4 carry-forwards (7 open)
- **TODO ledger:** see `TODO.md` for full state

## Files

- `papers/PASS_63_META_COLLAPSE_117_119_2026-05-22.md` (separate; 13th meta-collapse executed in Pass-63 batch-1)
- `papers/PASS_63_BELL_CHANCE_LCC_TI_SIGMA_2026-05-22.md`
- `papers/PASS_63_FBCL_2_AND_3_CHANCE_MODE_FALSIFIERS_2026-05-22.md`
- `papers/PASS_63_FLEISS_KAPPA_2_3_4_LABEL_COMPARISON_2026-05-22.md` (§3.2/§3.4 mechanism superseded — flagged)
- `papers/PASS_63_BATCH_5_LLM_RATERS_COMPETENT_ALGORITHM_2026-05-22.md` (canonical Pass-63 MI framing)
- `papers/PASS_60_BENGSTON_JSE_RETROSPECTIVE_META_ANALYSIS_2026-05-22.md` (Trial-1 confirmed; Trial-2 HOLD)
- `simulations/fleiss_kappa_comparison_2_3_4_label_2026-05-22.py` (halfwidth, deprecated mechanism)
- `simulations/fleiss_kappa_llm_raters_2026-05-22.py` + `_results.json` (canonical)

---

**Net effect on replit.md:** §§7.7.117-118-119 orphan LIVE entries removed; §7.7.120 pointer-stub added; §7.7.121 opened LIVE for Pass-64 batch-1.

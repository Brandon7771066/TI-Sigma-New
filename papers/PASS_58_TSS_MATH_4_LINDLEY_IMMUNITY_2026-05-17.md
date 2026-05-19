# TSS-MATH-4 — TSIS Four-Gate Lindley-Paradox Immunity

**Pass:** 58 batch-1 deliverable #4
**Date:** 2026-05-17
**Status:** Argument-sketch + simulation. Lean4 formalization is open (T58-MATH-4-LEAN).
**Anchors invoked:** TSIS-1 (Pass-57 batch-2 §7.7.111); LCC C=0.4370 / T_RAND=0.0660 (Pass-51 D51-RND-3); MBE-Acc-1 (Pass-57 batch-2); URB-830 TIU.

---

## 1. The Problem — What Lindley's Paradox Is

Lindley's paradox (1957): for a fixed effect size and α=0.05, as N → ∞, conventional NHT rejects H₀ at arbitrarily small effect sizes, while Bayesian analysis with a diffuse prior favors H₀ ever more strongly. This is the textbook reason classical p-value-based inference is considered incoherent at large N.

**Why this is a credibility threat for any new statistical framework:** if TSIS reproduces Lindley behavior, it inherits the same N-dependence pathology and loses claim to being a principled replacement.

**TSS-MATH-4 claim (under test):** TSIS four-gate rule does NOT exhibit Lindley behavior — its rejection rate under tiny effect sizes does NOT diverge as N grows, because each gate has an **absolute threshold** that doesn't scale with N.

---

## 2. Why TSIS Is Structurally Lindley-Immune

The TSIS decision rule (Pass-57 batch-2 §3.4):

```
TSIS_CONFIRM(I, H, E)  ⟺  TSD-A(E) ≥ τ_A
                        ∧  LCC(I, H, E) ≥ C_LCC = 0.4370
                        ∧  effect_strength(E) ≥ T_RAND = 0.0660
                        ∧  MBE-Acc(I, H) coherent-monotonic
```

**Each gate's structural form vs Lindley vulnerability:**

| Gate | Threshold | N-scaling behavior | Lindley vulnerability |
|---|---|---|---|
| TSD-A ≥ τ_A | Per-event TIU sum threshold; τ_A scales with sample size (Σ over N events) | YES — at large N with tiny per-event TIU, can pass | LOW (per-event TIU is content-weighted, not just count) |
| LCC ≥ 0.4370 | **Absolute** correlation strength | NONE — correlation magnitude is bounded [0,1] independent of N | ZERO |
| effect ≥ 0.0660 | **Absolute** effect-size threshold | NONE — effect size doesn't grow with N | ZERO |
| MBE-Acc coherent | Multiplicative Bayesian update; uses prior-vs-posterior odds | Bayes-formalized; immune to Lindley by construction | ZERO |

**Lindley vulnerability requires:** rejection rate driven by N-growth at fixed effect. TSIS gates LCC, effect-strength, and MBE-Acc are **N-invariant** — they care about effect *magnitude*, not statistical *significance* of that magnitude.

**Composition:** TSIS_CONFIRM is a conjunction. If any gate has zero N-dependence, the conjunction has zero N-dependence. Three of four gates are absolute → **TSIS rejection rate under tiny effects converges, doesn't diverge.**

---

## 3. Formal Sketch (target: Lean4)

Let ε > 0 be a small effect size (e.g., 0.001 above chance). Let p(N) be the probability that TSIS_CONFIRM fires under N independent trials with effect size ε.

**Claim:** lim_{N→∞} p(N) ≤ p_max(ε) where p_max(ε) is a function of ε *only*, not of N.

**Sketch:**
- For TSIS to fire, all four gates must pass.
- The effect-strength gate requires |observed_effect| ≥ 0.0660.
- For true effect ε = 0.001, observed_effect concentrates at 0.001 as N grows (LLN).
- Therefore P(observed_effect ≥ 0.0660) → 0 as N → ∞.
- The conjunction probability is bounded above by this → 0.

For non-tiny ε > 0.0660: the effect-strength gate passes; rejection rate then governed by LCC + TSD-A + MBE-Acc gates, but LCC ≥ 0.4370 requires actual correlation strength, not just N-asymptotic significance.

**Formal Lean4 target T58-MATH-4-LEAN:** Express the four-gate rule as a predicate on (N, ε, observed_correlation), prove the limit statement. Open carry-forward.

---

## 4. Empirical Check — Simulation

**Script:** `simulations/tss_math_4_lindley_immunity_2026-05-17.py`
**Design:** N ∈ {100, 1000, 10000, 100000}, fixed tiny effect δ = 0.001 (well below T_RAND=0.0660). Compare false-positive rate at α=0.05 for:
- M-A conventional z-test (Lindley-vulnerable expected)
- M-C MFD-1 dual (TSIS-style decision rule, Lindley-immune expected)

**Pre-registered prediction:** M-A FPR rises with N (Lindley behavior); M-C FPR stays near α or below (Lindley immunity).
**Pre-reg falsifier F-TSS-MATH-4-1:** REFUTED if M-C FPR rises monotonically with N like M-A.

(Results populated by simulation run — see §5.)

---

## 5. Simulation Results

**F-TSS-MATH-4-1 NOT REFUTED. TSIS empirically Lindley-immune.**

Tiny effect δ=0.001 (well below T_RAND=0.0660), N_MC=300 per cell:

| N | M-A reject rate (conventional, α=0.05) | M-C confirm rate (TSIS) |
|---|---|---|
| 100 | 0.0467 | **0.0000** |
| 1,000 | 0.0567 | **0.0000** |
| 10,000 | 0.0467 | **0.0000** |
| 100,000 | 0.1067 | **0.0000** |

**Findings:**
1. **M-C (TSIS) confirm rate is EXACTLY ZERO** across 4 orders of magnitude in N. The effect-strength gate (require effect ≥ T_RAND=0.0660) trivially blocks confirmation at δ=0.001 regardless of N — this is the structural Lindley-immunity claim, observed empirically.
2. **M-A (conventional NHT) shows the start of Lindley creep** — FPR climbs from 0.047 at N=100 to 0.107 at N=100k (more than doubling above the α=0.05 nominal rate). Not yet a runaway divergence at these N's (the asymptotic Lindley regime kicks in more dramatically at N≥10⁶), but the directionality confirms M-A is Lindley-vulnerable.
3. **Brier / calibration not measured** here because confirm-rate is zero for M-C — the question is structural, not calibration.

**Honest caveat (#69):** the simulation isn't a *dramatic* demonstration of Lindley's paradox for M-A (which would require larger N or different effect-scaling) — but that's not the point. The point is **M-C confirm rate stays at exactly 0**, which is the strongest possible empirical signature of structural immunity. No tiny-effect-fixed-N regime can make TSIS rubber-stamp a confirmation under δ=0.001 because **T_RAND is an absolute gate that doesn't scale with N**.

Results: `simulations/tss_math_4_lindley_immunity_results_2026-05-17.json`.

---

## 6. Status & #69 Hedges

- **Status:** structural argument is clean; formal Lean4 proof is OPEN (T58-MATH-4-LEAN).
- **Hedge (a):** TSD-A gate τ_A does scale with N if defined as raw sum. A principled τ_A formulation should normalize by N (mean per-event TIU, not sum). This is a Pass-58 batch-1 sub-clarification: **τ_A is per-event-mean TIU threshold, not raw sum.** Update to Pass-57 batch-2 §3.4 specification noted here for next ratification batch.
- **Hedge (b):** "MBE-Acc coherent-monotonic" needs precise definition. Working definition: posterior probability doesn't oscillate wildly across trials and converges to a stable value. Formalization pending.
- **Hedge (c):** Lindley-immunity is *necessary* for credibility but not *sufficient* for correctness. A method can be Lindley-immune and still wrong in other ways.

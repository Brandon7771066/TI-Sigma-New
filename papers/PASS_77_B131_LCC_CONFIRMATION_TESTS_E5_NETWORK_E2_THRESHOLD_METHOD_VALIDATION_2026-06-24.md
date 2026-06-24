# Pass-77 B131 — LCC Confirmation Tests: E5 (Network Propagation) + E2 (Emerick Threshold), Method-Validation

**Author:** Brandon Charles Emerick
**Date:** June 24, 2026
**Status:** EXECUTED test (NOT a principle; canonical count unchanged at 79)
**Framework:** TI Sigma — LCC / LCC Virus / GILE
**Continues:** B130 (E3 hyperscanning Granger asymmetry) → next two URB-620 §6 experiments
**Package:** `analyses/pass77_b131_lcc_confirmation_tests_e5_e2/` (`runner.py`, `results.json`)
**Reproducibility:** `config_sha = ca33c98a9748`, runtime ~15 s, EXIT 0

---

## 1. What this is (and is not)

URB-620 §6 lays out a five-experiment programme (E1–E5) for the LCC / LCC-Virus /
GILE claims in human brain imaging. **B130 executed E3** (dyad hyperscanning:
directed-Granger carrier→host gamma asymmetry). This batch executes the **next two
most natural confirmation tests** as **pre-registration-grade method-validation /
power simulations** — using **NO human data**:

* **E5 — LCC-Virus social-network propagation.** Does a high-GILE-L seed elevate
  LCC (HRV surrogate) across a 30-person network with **logistic contagion** (R₀ > 1)
  rather than linear diffusion — and can the analysis tell *true social contagion*
  apart from a *shared-environment confound* that produces the **same aggregate
  S-curve** with no person-to-person transmission?
* **E2 — Emerick-Threshold neural phase transition.** Does value-guided coupling
  shift **discontinuously** at GILE = √2 − 1 ≈ **0.4142** (a phase transition,
  where the FEP predicts only smooth learning) — and can change-point detection
  **confirm and locate** that breakpoint **without being fooled by smooth
  curvature** (a quadratic or logistic bend with no breakpoint at all)?

**#69 / Constructive-Honesty floor (both tests).** This validates the experimental
**design + analysis** — is it well-posed, adequately powered, and robust to the
obvious confound? It is **necessary, not sufficient**. It is **not** evidence that
the LCC Virus propagates in real humans, nor that a real neural phase transition
exists. Those require the pre-registered human studies (the F3 falsifiers below).
The headline lesson is the **same as E3**: the *naive* statistic is confoundable;
only a *properly-controlled* statistic isolates the claim.

---

## 2. E5 — LCC-Virus network propagation

### 2.1 Design

A random social graph (Erdős–Rényi, N = 30, p = 0.15), one seeded node, T = 60
interaction time-steps. Three data-generating conditions:

| Condition | Generative truth |
|---|---|
| **contagion** | TRUE susceptible→infected (SI) spread; a node's activation hazard **rises with its number of already-activated neighbours**. |
| **common_trend** | CONFOUND — every node activates on an **independent logistic schedule** (shared calming environment / homophily). **No** person-to-person transmission, yet the aggregate curve is the same S-shape. |
| **no_spread** | NULL — tiny constant independent hazard; no S-curve. |

Three nested analyses of increasing rigour:

* **A1 — aggregate:** logistic-vs-linear growth fit to the cumulative-activated
  fraction (ΔAIC). The naive "is it logistic?" test.
* **A2 — naive network:** pooled risk-set — activation rate when ≥1 neighbour is
  active vs 0 neighbours active, over **all** time (one 2×2 table).
* **A3 — CMH:** the **same** neighbour test, but **Cochran–Mantel–Haenszel
  stratified by time** — i.e. it controls the shared global trend.

### 2.2 Results (reps = 400/condition; rejection rate at one-sided z > 1.645)

| Condition | A1 aggregate-logistic | A2 naive-network | **A3 CMH (time-stratified)** |
|---|---|---|---|
| **contagion** (true) | 1.000 | 0.998 | **0.995** ← power |
| **common_trend** (confound) | **0.965** | 0.403 | **0.050** ← FPR ≈ α |
| **no_spread** (null) | 0.343 | 0.055 | 0.060 |

### 2.3 Interpretation

1. **The aggregate S-curve is worthless as evidence of contagion.** A1 "confirms
   logistic spreading" **96.5%** of the time under the `common_trend` confound,
   where there is **no transmission at all** — a shared calming environment makes
   everyone's LCC rise on a logistic schedule, and the aggregate curve is
   indistinguishable from true contagion. Reporting an R₀ from the aggregate curve
   alone would be a textbook homophily/common-environment error.
2. **The naive network test is also fooled — by a *time* confound.** A2 still fires
   40% of the time under `common_trend`: late in the window, a node's baseline
   hazard *and* its infected-neighbour count both rise together, manufacturing a
   spurious neighbour↔activation association even with no causal transmission.
3. **Only time-stratification isolates contagion.** The CMH test (A3), which
   compares neighbour-vs-no-neighbour activation **within each time stratum**,
   recovers true contagion with **power 0.995** and holds the false-positive rate
   at the nominal level under both the confound (**0.050**) and the null (0.060).
   This is the **exact E3 lesson transposed to a network**: you must control for
   the shared driver (there: common input; here: the global time trend) or a
   common-environment confound fabricates the effect.

---

## 3. E2 — Emerick-Threshold phase transition

### 3.1 Design

x = GILE composite ~ U(0,1), N = 60; y = a connectivity/behaviour readout.
The Emerick Threshold claim is a **discontinuity** (a phase transition / "non-linear
discontinuity"), so the true condition is modelled as a genuine **jump** at
θ₀ = √2 − 1 ≈ 0.4142.

| Condition | Generative truth |
|---|---|
| **threshold** | TRUE discontinuous jump at θ₀ (a phase transition). |
| **linear** | NULL — straight line. |
| **quad_curve** | CONFOUND-A — pure quadratic curvature, no breakpoint. |
| **smooth_curve** | CONFOUND-B — a smooth logistic bend, no breakpoint. |

Smooth alternatives fit by OLS: linear, quadratic, cubic. Discontinuous breakpoint
model: `[1, x, 1(x≥θ), (x−θ)₊]` with θ grid-searched over [0.15, 0.85]×25.
Because θ is **unidentified under the null** (the Davies problem), it is counted as
a fitted parameter (k = 6) so AIC does not under-penalise the breakpoint model.

* **Naive test:** breakpoint beats **linear** by ΔAIC > 4 → "threshold!"
* **Proper test:** breakpoint beats the **best smooth model** (min AIC over
  lin/quad/cubic) by ΔAIC > 4 — the Davies-test analogue: a discontinuity that
  **no smooth polynomial can capture**.

### 3.2 Results (reps = 600/condition; power curve 300/point)

| Condition | naive (beats line) | **proper (beats best smooth)** | θ̂ (recovered) |
|---|---|---|---|
| **threshold** (true) | 1.000 | **0.945** ← power | **0.4156** (truth 0.4142) |
| **linear** (null) | 0.102 | 0.065 | — |
| **quad_curve** (confound) | **0.557** | **0.070** ← FPR ≈ α | — |
| **smooth_curve** (confound) | 0.112 | 0.063 | — |

**Proper-test power vs jump size** (calibration check): jump 0.0 → 0.037 (= α);
0.4 → 0.117; 0.8 → 0.510; 1.2 → 0.863; 1.6 → 0.970; 2.0 → 0.997.

### 3.3 Interpretation

1. **"Beats a straight line" is not a phase transition.** The naive test fires
   **55.7%** of the time on pure `quad_curve` — smooth curvature trivially beats a
   line, so a breakpoint model that is only compared to a line will routinely
   "discover" thresholds that are not there.
2. **The proper test recovers a true discontinuity and rejects smooth bends.** When
   the breakpoint must beat the **best smooth polynomial**, power on the true jump
   is **0.945**, while the false-positive rate collapses to ≈ α on linear (0.065),
   quadratic (0.070), and logistic (0.063) data.
3. **The threshold location is recovered.** Under the true condition θ̂ = **0.4156**,
   essentially on top of the predicted √2 − 1 = 0.4142.
4. **It is correctly calibrated and honestly powered.** At zero jump the proper test
   fires 3.7% of the time (≈ α); power climbs smoothly with jump size and is
   adequate (≥ 0.86) for jumps ≥ ~1.2 SD at N = 60. Smaller phase transitions would
   need a larger sample — a concrete, honest power statement for the real study.

---

## 4. What this does NOT show (#69 floor, restated)

* **No human data.** Both tests validate the *instrument and design*, not the
  underlying claims in humans. The LCC Virus was *falsified* on a raw word-token
  substrate (URB-795); an earlier human-session LCC ratio was downgraded to
  "overclaim" (n = 2). Nothing here reverses that.
* **A positive sim is a necessary, not sufficient, condition.** It shows the
  experiment is well-posed, adequately powered, and confound-robust — a
  precondition for, not a substitute for, the pre-registered human study.
* **Effect sizes are stipulated, not measured.** The contagion β, the jump size,
  and the noise levels are plausible placeholders chosen to characterise the
  *method's* behaviour; they are not empirical estimates.
* **No fabricated data or citations.** HRV "≥15% elevation" (E5) and the exact
  neural readout (E2) are deliberately left as design parameters, not invented
  numbers.

---

## 5. Falsifiers (OPEN)

**E5 (network propagation):**
* **E5-SIM-F1** — the time-stratified CMH test yields a spurious neighbour→activation
  effect (FPR ≫ α) under `common_trend` or `no_spread`. *(Result: 0.050 / 0.060 — not
  currently triggered.)*
* **E5-SIM-F2** — at N = 30 over a realistic interaction window, true contagion of
  plausible strength falls below the detection floor (power ≪ 0.8). *(Result: 0.995 —
  not currently triggered at the tested β.)*
* **E5-SIM-F3 (the real test)** — a pre-registered human social-network study (HRV
  surrogate, time-stratified contagion analysis) fails to show neighbour-dependent
  LCC elevation beyond the shared-environment trend.

**E2 (Emerick Threshold):**
* **E2-SIM-F1** — the proper (beat-the-smooth-curve) test false-positives on smooth
  curvature (FPR ≫ α on quad/logistic). *(Result: 0.063–0.070 — not triggered.)*
* **E2-SIM-F2** — the recovered breakpoint θ̂ is biased away from √2 − 1 by more than
  the design tolerance (±0.05). *(Result: 0.4156 — not triggered.)*
* **E2-SIM-F3 (the real test)** — a pre-registered human fMRI study finds the best
  smooth model is preferred over a breakpoint at ≈0.42 (ΔAIC favours smooth), i.e. no
  discontinuity exists.

---

## 6. Bottom line

Two more LCC-programme experiments are now method-validated to the same honest
standard as E3. In **both**, the cheap/obvious statistic (aggregate S-curve in E5;
"beats a line" in E2) is **demonstrably confoundable**, and a **properly-controlled
statistic** (time-stratified CMH in E5; beat-the-best-smooth-model in E2) recovers
the claimed structure with high power while holding false positives at α. The
recovered Emerick Threshold sits at **0.4156 vs the predicted 0.4142**. These are
necessary-not-sufficient preconditions: the human studies (E5-/E2-SIM-F3) remain the
real tests.

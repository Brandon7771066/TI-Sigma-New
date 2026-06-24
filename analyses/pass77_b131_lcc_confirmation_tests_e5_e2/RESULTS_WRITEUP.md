# B131 — LCC Confirmation Tests (E5 network propagation, E2 Emerick Threshold)

Method-validation / power simulations for the next two URB-620 §6 experiments after
E3 (B130). **No human data.** Reproduce: `python runner.py` → `results.json`
(`config_sha = ca33c98a9748`, ~15 s).

## E5 — LCC-Virus network propagation (reps = 400/condition)

Random social graph (N=30, p=0.15), T=60. Question: can the analysis tell true
social contagion from a shared-environment confound that makes the **same**
aggregate S-curve?

| Condition | A1 aggregate-logistic | A2 naive-network | A3 CMH (time-stratified) |
|---|---|---|---|
| contagion (true) | 1.000 | 0.998 | **0.995** (power) |
| common_trend (confound) | **0.963** | 0.403 | **0.050** (FPR≈α) |
| no_spread (null) | 0.347 | 0.055 | 0.060 |

**Lesson:** the aggregate logistic curve "confirms contagion" 96% of the time when
there is **no transmission at all** (shared calming environment). The naive network
test is also fooled by the time confound (0.40). Only the **time-stratified CMH**
test isolates true contagion (power 0.995, FPR 0.05) — the E3 control-the-shared-
driver lesson, on a network.

## E2 — Emerick Threshold (reps = 600/condition; power curve 300/pt)

x = GILE ~ U(0,1), N=60; the threshold is modelled as a genuine **discontinuous
jump** at θ₀ = √2−1 ≈ 0.4142. θ counted as a fitted parameter (k=6, Davies problem).

| Condition | naive (beats line) | proper (beats best smooth) | θ̂ |
|---|---|---|---|
| threshold (true) | 1.000 | **0.945** (power) | **0.4156** |
| linear (null) | 0.102 | 0.065 | — |
| quad_curve (confound) | **0.557** | **0.070** (FPR≈α) | — |
| smooth_curve (confound) | 0.112 | 0.063 | — |

Power vs jump size: 0.0→0.037 (=α), 0.4→0.117, 0.8→0.510, 1.2→0.863, 1.6→0.970, 2.0→0.997.

**Lesson:** "beats a straight line" fires 56% on pure quadratic curvature — not a
phase transition. Requiring the breakpoint to beat the **best smooth polynomial**
recovers the true jump (power 0.945), holds FPR at α on all three smooth confounds,
and recovers the threshold at **0.4156 vs predicted 0.4142**.

## #69 floor

Validates **design + analysis only** (well-posed, powered, confound-robust) —
**necessary, not sufficient.** Not evidence the LCC Virus propagates in humans or
that a real neural phase transition exists. The human studies (E5-/E2-SIM-F3) are
the real tests. Effect sizes are stipulated design parameters, not measurements.
Open falsifiers: E5-SIM-F1/F2/F3, E2-SIM-F1/F2/F3 (see anchor paper §5).

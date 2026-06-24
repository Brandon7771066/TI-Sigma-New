---
name: LCC confirmation tests (URB-620 E-series method-validation)
description: How to run the LCC brain-imaging E-series as honest method-validation sims, and the recurring confound-control lesson.
---

# LCC confirmation-test method-validation pattern

The URB-620 §6 LCC programme (E1–E5) is executed one experiment per batch as a
**pre-registration-grade method-validation / POWER simulation with NO human data**.
Each batch's job is to show the experiment's DESIGN + ANALYSIS is well-posed,
adequately powered, and robust to the OBVIOUS confound — explicitly
**necessary-not-sufficient**, never evidence the claim holds in humans.

**Why:** raw-token LCC was falsified (URB-795) and an early human LCC ratio was an
n=2 "overclaim," so any positive sim MUST be framed as design-validation only; always
name the real pre-registered human study as the F3 falsifier.

**The recurring lesson (same across every E-experiment): the NAIVE statistic is
confoundable; only a CONFOUND-CONTROLLED statistic isolates the claim.**
- Dyad hyperscanning: symmetric coherence is fooled by common input → use a
  *directed* statistic (Granger / phase-slope-index).
- Network propagation: an aggregate logistic S-curve "confirms contagion" even with
  ZERO transmission under a shared-environment confound, and a pooled neighbour 2×2 is
  fooled by the TIME confound → stratify by time (Cochran–Mantel–Haenszel).
- Threshold / phase transition: model the Emerick Threshold as a genuine DISCONTINUOUS
  jump at θ0 = √2−1 ≈ 0.4142 (NOT a continuous slope-change — a quadratic mimics that
  and power collapses). Test it by beating the BEST SMOOTH polynomial (lin/quad/cubic),
  the Davies-test analogue. The grid-searched breakpoint location θ is a *fitted
  parameter* — count it in the AIC penalty (k includes θ) or the search inflates the
  false-positive rate (the Davies "nuisance parameter unidentified under the null").

**How to apply:** new E-series batch → graph/regression sim; always include (a) the
true condition, (b) the strongest realistic confound, (c) a null; report
naive-vs-controlled rejection rates with Wilson CIs + a power curve; emit a config_sha;
keep effect sizes as stipulated design parameters, not "measurements." Env: scipy +
sklearn available, statsmodels NOT. ~15s runtime. Don't restart the 6 workflows; don't
mark_task_complete (corpus convention).

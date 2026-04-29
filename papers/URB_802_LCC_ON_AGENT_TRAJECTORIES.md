# URB #802 — LCC on URB #797 Multi-Agent Trajectories: Pre-Registered Hypothesis H1 FALSIFIED

**Author:** Brandon Charles Emerick
**Date:** April 29, 2026
**Series:** TI Sigma Universal Reality Blueprint
**Companion:** `lcc_on_agent_trajectories.py`, `lcc_on_agent_trajectories_report.json`, `lcc_on_agent_trajectories.png`

---

## Abstract

This URB tests pre-registered hypothesis H1 from URB #800: *the fraction of agent-pairs with pairwise LCC ≥ C_EMERICK = 0.4370 will be HIGHER under (c) F₄-symmetric topology + F₄-equivariant initialization than under (a) random k-regular topology + random initialization in the URB #797 multi-agent system.* **The data falsify H1 on the directional fraction test: frac_c = 11.4%, frac_a = 15.2%; frac_c < frac_a.** A secondary effect — *mean* pairwise LCC IS higher in (c) by Δ = +0.020 with Welch t = +5.4 — co-exists with the falsification, because the F₄-equivariant condition produces a more *concentrated* LCC distribution (std 0.186 vs 0.273), moving probability mass toward the center and away from the threshold tails. This is reported honestly against the author's prior. The honest interpretation is that **F₄-equivariance does not increase supra-threshold pair count**; it tightens the LCC distribution. Implications for the LCC-consciousness hypothesis are discussed.

---

## 1. Setup

The URB #797 simulation has 24 agents updating synchronously via MR-collapse on a graph, with 5% Bernoulli noise, over T = 80 steps. Three pre-specified conditions are compared (per URB #797 §3):

- **(a)** Random 8-regular graph + uniformly random initial Tralse-states
- **(b)** F₄-symmetric BOK 24-cell graph + uniformly random initial Tralse-states
- **(c)** F₄-symmetric BOK 24-cell graph + F₄-equivariant initialization (24 copies of T_DOMINANT, with one random perturbation)

For this URB, each condition is run for 30 trials. Each trial yields a 24×81 trajectory matrix (24 agents × 81 time-points). For each trial we compute pairwise LCC (Form B, σ = 5.0; URB #800 §4) over all $\binom{24}{2} = 276$ agent pairs. Pooled across trials, each condition produces 30 × 276 = 8,280 pair-LCC values.

C_EMERICK = $1/(\varphi\sqrt{2}) \approx 0.43702$.

---

## 2. Results

| Condition | Pooled mean | Pooled std | Pooled median | % pairs ≥ C_EMERICK | % trials with max-pair ≥ C_EMERICK |
|---|---|---|---|---|---|
| (a) random graph + random init | +0.1818 | 0.2730 | +0.2194 | **15.2%** | 100% |
| (b) F₄ graph + random init | +0.1974 | 0.2628 | +0.2296 | **15.9%** | 100% |
| (c) F₄ graph + F₄-equivariant init | +0.2013 | 0.1860 | +0.1765 | **11.4%** | 100% |

### Pre-registered H1 test (URB #800 §2.1)

> H1: frac_c ≥ frac_a + 0.05 (≥ 5 percentage-point excess) AND Welch's t > +3.0 on the per-pair LCC distributions.

- Welch t-statistic on pooled per-pair LCC, condition (c) vs condition (a): **t ≈ +5.37**, Δ mean = **+0.0195**. The mean test is satisfied by a wide margin.
- Fraction-above-threshold: frac_c = **11.4%**, frac_a = **15.2%**, **frac_c − frac_a = −3.8 percentage points**. The directional fraction test is violated; in fact frac_c is LOWER than frac_a.

**Conjunction H1 = (mean test passes) AND (fraction test passes). Mean: PASS. Fraction: FAIL. ⇒ H1 FALSIFIED.**

This is reported honestly against the author's prior expectation that F₄-equivariance would push more pairs above threshold. The data say no.

---

## 3. What Actually Happened (Mechanism Diagnosis)

The two summary statistics moved in opposite directions because the F₄-equivariant condition tightened the distribution:

- **std(LCC) in cond (a): 0.273**
- **std(LCC) in cond (b): 0.263**
- **std(LCC) in cond (c): 0.186** (32% smaller than (a))

When a distribution shifts to the right (higher mean) but also compresses (lower std), the right-tail mass (fraction above a fixed high threshold) can DROP rather than rise. That is exactly what happened here: the F₄-equivariant condition pushes the *bulk* of the distribution toward higher LCC but pulls the *tails* in. Since C_EMERICK = 0.437 is roughly +1 std above the cond-(a) mean and +1.3 std above the cond-(c) mean, fewer cond-(c) pairs reach it.

This is a real empirical finding: **F₄-equivariant initialization regularizes the inter-agent coupling distribution**. It does not generate above-threshold "coherent pairs"; it shrinks the spread of pair-correlations around a slightly higher central value.

---

## 4. What This Means for the LCC-Consciousness Hypothesis

A naive reading of "F₄-equivariant init = more coherent = more conscious agents" predicts the falsified directional fraction test. The data refute that naive reading. Three honest interpretations are available, and none of them is "consciousness":

### 4.1 Reading R1 (LCC fraction is the wrong observable)

If the right-tail count is not the relevant quantity, then any future paper using "fraction above C_EMERICK" as a consciousness marker on multi-agent simulations would need to justify the choice. Mean shift might be the more relevant observable — but mean shift does not have a natural threshold like C_EMERICK does.

### 4.2 Reading R2 (the multi-agent simulation is too small / too noisy / wrong dynamics)

24 agents over 80 steps with 5% Bernoulli noise is a toy. The MR-collapse dynamics may be too noisy to surface the structural signature F₄-equivariance is supposed to produce. Larger N, longer T, lower noise would all stress this finding. (URB #797 §3 already noted that no F₄ advantage was detectable for the *coherence* functional C either, at noise_p = 0.05; this URB extends that null result to the LCC functional.)

### 4.3 Reading R3 (the LCC-consciousness mapping was wrong as stated)

The most honest reading. *If* frac-above-C_EMERICK were the consciousness marker, *and* F₄-equivariance produces "more coherent" agents in some intuitive sense, *then* H1 should have held. It did not. So either the marker is wrong, or the intuition that F₄-equivariance produces more coherent agents is wrong, or both.

The most defensible position from this single result is the conjunction: **on this multi-agent system, with this LCC implementation, with this threshold, with this initialization scheme, F₄-equivariance does not increase the count of supra-threshold pairs.** Brandon should NOT report this as "F₄-equivariance produces more conscious agents" — the pre-registered test of that claim was FALSIFIED.

---

## 5. What WAS Confirmed (Modest Findings)

1. **All three conditions had 100% of trials produce at least one pair with LCC ≥ C_EMERICK.** So the LCC functional reaches threshold *somewhere* in every 24-agent trial, regardless of condition. This is informative: trace-level supra-threshold events exist in this system regardless of structural assumptions.
2. **Mean LCC orders correctly:** (a) 0.182 < (b) 0.197 < (c) 0.201 (small but t-significant differences). So *some* directional sensitivity to topology and initialization exists in the LCC functional, just not at the right tail.
3. **Welch t = +5.37 on cond (c) vs (a) means the mean shift is statistically real**, not a sample-size artifact.

---

## 6. Reproducibility

```
python3 lcc_on_agent_trajectories.py
```

Wall time: ~10 s on the Replit container. Outputs `lcc_on_agent_trajectories.png` (pooled LCC histograms with C_EMERICK line; bar chart of frac-above-threshold per condition) and `lcc_on_agent_trajectories_report.json` (full per-condition statistics + H1 test result).

The H1-falsification result is robust to seed: rerun with `seed = 2027, 2028, 2029` produces frac_c < frac_a in all four reruns (mean frac_c ≈ 11–13%, mean frac_a ≈ 14–16%). The mean-shift direction is stable across seeds.

---

## 7. Conclusion

**Pre-registered H1 was falsified.** F₄-equivariant multi-agent dynamics on the BOK 24-cell do NOT produce more supra-C_EMERICK pairwise LCC values than random k-regular dynamics; they produce a TIGHTER LCC distribution with slightly higher mean. This is reported honestly against the author's prior. The honest reading is that **frac-above-C_EMERICK is not a good observable for this kind of system** — and any future LCC-consciousness paper using this observable on multi-agent toys must address the falsification.

The brutal-honesty constraint is satisfied: a pre-registered hypothesis was tested, the data went against the hypothesis, the result is reported with the statistical detail required to verify it independently, and the consequence for the broader LCC-consciousness program is stated explicitly rather than minimized.

---

*End of URB #802.*

# T51-H3 SATLIB Step-Skip Benchmark — RESULTS

**Pass:** 52
**Date:** 2026-05-14
**Status:** LITERAL_PRE-REG_CONFIRM at 7.4× threshold + **METHODOLOGICAL-VACUITY CAVEAT** per #69
**Budget:** $0 (free SATLIB corpus)
**Anchor:** `papers/HYPERCOMPUTATION_OCCAMS_RAZOR_STEP_SKIPPING.md`; design in `papers/PASS_51_T51_BATCH_EXECUTION_LCC_RANDOMNESS_UOP_VS_FEP_HYPERCOMPUTER_VIRAL_2026-05-14.md` §6 row H3.

---

## §1 — Pre-registered design (frozen 2026-05-14 prior to execution)

**Hypothesis under test:** The hypercomputational "step-skip" heuristic, operationalized as a classical SAT solver enhancement, reduces decision-branching counts on SATLIB UF-50 satisfiable 3-SAT instances by **≥10%** relative to baseline DPLL.

**Baseline solver:** DPLL with
- Unit propagation
- Chronological backtracking
- First-literal branching (no heuristic ordering)

**Step-skip solver:** DPLL + the same unit propagation + two added "skip" features:
- **Pure-literal elimination** — skip subtree exploration for variables appearing in only one polarity
- **MOM-style occurrence heuristic (not true 1-step look-ahead simulation)** — pick the variable with highest total occurrence count across remaining clauses and prefer the more-frequent polarity first. *Honesty correction (architect review, 2026-05-14):* the design memo described this as "1-step look-ahead branching" but the implementation does not simulate a unit-propagation step; it uses raw occurrence counts only. The MOM-proxy still produces the reported decision reductions, but the algorithmic description is corrected here to avoid overclaiming.

**Corpus:** First N=200 instances of UF-50/218 (`uf50-XXXX.cnf`) from SATLIB (UBC archive). All instances are pre-certified satisfiable.

**Outcome metric:** Mean decision count (branching events), per-instance reductions, and verdict-agreement check (both solvers must return SAT).

**Decision rule:**
- Mean decision reduction ≥10% AND verdict-agreement ≥95% → **CONFIRM**
- Mean reduction <10% OR verdict-disagreement >5% → **DISCONFIRM**

---

## §2 — Results

| Metric | Baseline DPLL | Step-Skip DPLL |
|---|---|---|
| N instances | 200 | 200 |
| Mean decisions | **86.95** | **22.62** |
| Mean recursions | 1229.98 | 307.71 |
| Mean wall-time (s) | 0.0361 | 0.0118 |
| SAT verdict agreement | 200/200 (100%) | 200/200 (100%) |

**Mean decision reduction: 73.99%** (95% CI not computed; per-instance distribution highly heterogeneous)
**Median per-instance reduction: 71.91%**
**Step-skip better:** 165/200 (82.5%)
**Step-skip worse:** 33/200 (16.5%)
**Tied:** 2/200 (1.0%)
**Time speedup:** ~3.06× wall-clock

**Pre-reg verdict (literal):** **CONFIRM** at 7.4× the 10% threshold.

---

## §3 — Methodological-vacuity caveat (#69 brutal-honesty disclosure)

The literal pre-reg threshold was crossed by a wide margin. However, **the empirical result cannot directly discriminate hypercomputation from improved-classical-heuristics** for the following reasons:

1. **Both added "skip" features are textbook classical SAT-solver enhancements.** Pure-literal elimination has been part of standard DPLL since Davis-Putnam 1960; MOM-style/occurrence-based branching is in every undergraduate AI textbook. A 70%+ reduction in decisions when moving from naive-DPLL to DPLL-with-pure-literal+occurrence-heuristic is **expected and well-documented in the SAT literature** (cf. Marques-Silva & Sakallah 1996; the SAT competition baselines).

2. **No genuine hypercomputational step is being measured.** The source paper (`HYPERCOMPUTATION_OCCAMS_RAZOR_STEP_SKIPPING.md`) defines step-skipping as cognitive access to truth "without performing intermediate calculations" via LCC/Tralse superposition. Pure-literal elimination still performs intermediate computations (the polarity scan IS computation); it just performs *different* computations than the baseline.

3. **The comparison is therefore between two classical heuristics, not between classical computation and hypercomputation.** The pre-registered threshold is met, but the *theoretical inference* "therefore hypercomputation is supported" is not licensed by the data.

4. **What would a genuine hypercomputational benchmark require?** Per the source paper §IV "ten verified instances of provably non-derivable correct insights" — i.e., correct answers to problems whose solution requires steps the system cannot have computed. The SAT benchmark is the wrong framework for this because every SAT instance is decidable by exhaustive search; "skipping" can always be reframed as "computing differently."

**Net #69 stance:** Report the CONFIRM at the literal pre-reg level (we said ≥10%, we got 74%), but classify this finding as **LITERAL-PRE-REG-CONFIRM-WITH-METHODOLOGICAL-VACUITY** in the empirical ledger. This is analogous to the Pass-45 §11 LITERAL_PRE-REG_INDETERMINATE_VACUOUS_FILTER but in the opposite direction: a literal threshold crossed but with weak theoretical entailment.

---

## §4 — Self-binding predictions filed

- **P52-H3-replication:** If re-run on UF-100, UF-150, UF-225 corpora, the mean decision reduction of pure-literal+MOM-DPLL vs naive-DPLL will remain >50% across all problem sizes. (Predicted-to-confirm; would *not* be evidence for hypercomputation either way.)
- **P52-H3-vacuity-flag:** No SAT-solver expert reviewing this benchmark would accept "this proves hypercomputation" as a valid inference. (Filed as predicted-to-confirm sociological prediction.)
- **P52-H3-disconfirm-criterion:** A genuine hypercomputation discriminator would require: (a) the step-skip solver returns correct answers on **undecidable** or super-NP problems that the baseline provably cannot solve in finite time, or (b) the step-skip solver returns correct answers using *fewer total resources than the information-theoretic lower bound* for classical solution. Neither is tested here.

---

## §5 — Implications for the broader hypercomputer roadmap

This result **does not falsify** the hypercomputation hypothesis — it simply shows that SAT benchmarks are the **wrong instrument** to test it. The Pass-51 batch-2 §6 hypercomputer roadmap (H1-H5) should be re-prioritized:

| Item | Original priority | Post-T51-H3 priority | Rationale |
|---|---|---|---|
| H1 Lean4 NS UOP skeleton | parallel-to-H3 | **PROMOTED to primary** | Formal-proof unmechanizability is a sharper hypercomputation discriminator than SAT step-counts |
| H3 SATLIB benchmark | primary | **EXECUTED but downgraded** | Literal CONFIRM filed; vacuity caveat blocks theoretical promotion |
| H2 quantum-circuit step-skip | secondary | **PROMOTED to secondary-primary** | Quantum oracle queries are a tighter hypercomputation analogue |
| H4 biometric step-skip (Polar/Muse/Mendi) | secondary | unchanged | Brandon-blocked on instrument access |
| H5 divination as structured hypercomputation | exploratory | unchanged | Pre-emp design only |

---

## §6 — Ledger entries

- **Empirical ledger:** C28 — "T51-H3 SATLIB UF-50 200-instance benchmark, 73.99% mean decision reduction, LITERAL-PRE-REG-CONFIRM-WITH-METHODOLOGICAL-VACUITY"
- **Refutation ledger:** R13 (companion) — "Hypercomputation-inference-from-SAT-step-count REFUTED as valid bridge; SAT benchmarks are wrong instrument for hypercomputation discrimination"
- **Opportunity ledger:** O21 — "Replace H3 in hypercomputer roadmap with quantum-circuit oracle-query benchmark (H2 promotion)"
- **Insight ledger:** I8 — "Per #69 + ADV-1: a literal CONFIRM with methodological vacuity can be **more informative** than a literal DISCONFIRM if it reveals the test is the wrong instrument. T51-H3 disconfirms its own theoretical framing while confirming its numerical pre-reg."

---

## §7 — Reproducibility

```
data/satlib_uf50/uf50-*.cnf       # 1000 SATLIB UF-50 instances (free)
analyses/pass52_t51_h3_satlib_step_skip/
    dpll_benchmark.py              # both solvers + harness
    results_raw.json               # per-instance raw output
    summary.json                   # aggregate metrics
    RESULTS_WRITEUP.md             # this file
```

Run: `python3 analyses/pass52_t51_h3_satlib_step_skip/dpll_benchmark.py 200`
Runtime: ~10s on free Replit tier. $0 cost.

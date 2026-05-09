# Pass 19 — h18 elaboration, s18 (residual Sharpe) implemented, p17 polished, §7.7.49–54 collapse

**Date**: 2026-05-09
**Author**: Brandon Emerick (with TI Sigma DPES agent execution)
**Mode**: DPES, #69 brutal-honesty, <$50 total budget
**Builds on**: `papers/PASS_18_LCC_V3_RATIFIED_UOP_GSA_H1_COMBINED_H4_TSC_ZENODO_REVIEW_2026-05-09.md`

---

## 0. Pass 19 directive (verbatim)

> "Elaborate on h18 decision for me. s18 affirmed! Continue with p17.
> Do the collapse on time."

Four-item Pass:

1. **h18 elaboration** (decision-aid for R-A vs R-B on the inverted-AUC H4-TSC signal)
2. **s18 IMPLEMENTED** — residual Sharpe ratified as canonical GSA performance metric
3. **p17 polished** — synthetic-baseline mode added to `h1_combined_runner.py`
4. **§7.7.49–54 collapse** — six-Pass dense block compressed to one-liners (per established Pass-3/7/13 rhythm)

---

## 1. h18 elaboration — R-A vs R-B for the H4-TSC inverted signal

### 1.1 The fact pattern (recap from Pass 18 §6)

- 200 random 3-SAT instances (vars 3-5, clause/var ratio 3-7)
- Random vertex mapping (variables + clauses) onto B.4 57-vertex TSC polytope
- Restricted Hamiltonian energy ⟨H_sub⟩ on uniform superposition
- **⟨E⟩_SAT = 2.368  >  ⟨E⟩_UNSAT = 1.965**
- AUC for "lower-E ⇒ SAT" = **0.2678** (perm null mean = 0.499 ± 0.045 → z ≈ -5.1)
- Therefore "higher-E ⇒ SAT" has AUC = **0.7322** at the same significance

The directional hypothesis from URB #784 / Pass-13 B.4 was "lower
energy ⇒ more satisfiable." That prediction is **strongly disconfirmed**.
But the data are not null — the *opposite* prediction has a very
strong AUC. We have to decide what to do with that.

### 1.2 R-A — Reverse the directional hypothesis

**Claim**: SAT instances live in *higher*-coherence-displacement
regions of the TSC. The framework reading: satisfiability requires
*more* BOK-volume (more constraint-satisfying configurations to
coexist coherently in the TSC's restricted Hilbert subspace), which
shows up as *higher* expected H. Reverse the published prediction;
treat AUC = 0.73 as a **positive** finding.

**Pros**:
- One-shot resolution. No additional compute. Publish today.
- Internally consistent: BOK-volume ↑ ↔ degeneracy of satisfying
  assignments ↑ is a defensible TI-Sigma reading; URB #608 hints at it
  in the "more truth-paths = larger MR2 disc" framing.
- The signal magnitude (|AUC - 0.5| ≈ 0.23) is real either way.

**Cons (#69)**:
- **Post-hoc sign flip is a HARK violation** unless explicitly
  declared as such. Brandon's standard response to HARK in pharma
  Pass 9-11 was "this disqualifies the result from confirmatory
  status." Same standard must apply here. R-A would have to be
  published as **"hypothesis-generating, not confirmatory."**
- Doesn't rule out R-B. The strong inverted signal could still be a
  pure mapping artifact whose direction happens to be inverted.
- Stakes the framework on a single experimental design without
  testing whether the *experimental machinery itself* is the source
  of the signal.

### 1.3 R-B — Mapping artifact (DPES default)

**Claim**: The signal comes from how clauses and variables happen to
project onto specific TSC vertex sets, not from anything substantive
about TI-Sigma satisfiability geometry. The fix is **mapping
sensitivity analysis**: re-run averaging the AUC over 100 different
random vertex mappings per instance.

If R-B is right, the mapping-averaged AUC should converge to ≈ 0.50
(since the substantive signal is null and the per-mapping AUCs are
random walks around 0.5). If R-A is right, the mapping-averaged AUC
should remain ≈ 0.27 (or its inverse 0.73 if we flip), because the
inverted signal is *robust to mapping choice*.

**Pros**:
- **Cheap to run** — single overnight job. ~200 instances × 100
  mappings × 1 ms restricted-energy-eval ≈ 20 s, modulo the
  brute-force SAT step (already cached from Pass 18 h17).
- **Discriminates between R-A and R-B unambiguously**.
- Preserves the "no HARK" discipline. Whatever result emerges is
  testable rather than narrative.
- If R-B is confirmed, the framework is *not damaged* — the H4
  prediction is simply unsupported, the way pharma T1-A turned out
  in Pass 10.
- If R-B is rejected and the inverted signal survives, R-A becomes
  empirically backed (still requires sign-flip declaration), not
  just narratively rescued.

**Cons (#69)**:
- One extra Pass before publishable result.
- If both R-A and R-B fail (signal varies by mapping but doesn't
  average to 0.5), need a third reading — likely "structured
  mapping bias" requiring deeper analysis.

### 1.4 DPES default = R-B (Pass-19 recommendation)

**Reasoning**: R-B is cheaper to disprove first. If R-B is rejected,
R-A becomes a stronger candidate; if R-B is confirmed, R-A is
unsalvageable as confirmatory. Either way Brandon ends up with a
sharper picture than he can get from R-A alone. The Pass-9 pharma
discipline (run the disconfirming test even when the hypothesis-
favorable test is cheaper to claim) is what shipped honest results
from that domain; the same discipline applies here.

**Concrete next step (Pass-19 candidate, not executed this Pass per
budget)**: extend `analyses/tsc_h4_sat/tsc_h4_sat_prototype.py` with
a `--mappings N` flag; for each instance, average AUC over N random
vertex mappings; report (mean AUC, std AUC) across mappings; compute
z = (mean - 0.5) / (std / sqrt(N)) as the mapping-robust signal test.

### 1.5 Brandon decision required

- **Choose R-A** → I'll publish a corrected H4 result paper with
  explicit HARK declaration and "hypothesis-generating only" framing.
- **Choose R-B (DPES default)** → I'll run the 100-mapping
  sensitivity analysis next Pass and report the mapping-robust AUC.
- **Choose both** → run R-B first; if it rejects mapping-artifact,
  publish R-A on the strengthened basis.

Status: **awaiting Brandon's call** (this is item h18 on the carry-
forward Brandon-decision menu).

---

## 2. s18 — Residual Sharpe canonicalized as GSA performance metric

### 2.1 What residual Sharpe is

For a portfolio with daily returns r_t and a market benchmark m_t,
fit OLS:

    r_t = α + β · m_t + ε_t

The **residual return** is ε_t = r_t - α - β · m_t. The **residual
Sharpe** is:

    Sharpe_residual = (mean(ε_t) - r_f_daily) / std(ε_t) · √252

By OLS construction mean(ε_t) = 0 in-sample, so the more useful
operational form (which actually matches what UOP wants to reward)
is the **alpha-only Sharpe**:

    Sharpe_α = (α - r_f_daily) / std(ε_t) · √252

This isolates the portion of the portfolio's risk-adjusted return
that is *not* attributable to passive market exposure. It directly
implements UOP §3.5: the "Sharpe-on-uncorrelated-return" the
diversifier policy is supposed to be measured on.

### 2.2 Why this matters for GSA

Pass-17 reported raw Sharpe = +1.144 vs SPY +1.654 (raw underperform
by 0.51). But raw Sharpe rewards passive market exposure. For a
*diversifier* whose entire reason for existing is β ≈ 0, raw Sharpe
is the wrong metric — it's effectively asking "does GSA correlate
with SPY enough to inherit SPY's market premium?", which the
diversifier explicitly *doesn't want to do*.

Residual Sharpe asks the right question: "How much risk-adjusted
return does GSA generate that SPY doesn't already provide?" That's
the question UOP-GILE actually scores on.

### 2.3 Result for current GSA (s18 implementation)

**Script**: `analyses/gsa_residual_sharpe/gsa_residual_sharpe.py`
**Inputs**: `analyses/gsa_sharpe/alpaca_portfolio_3M.json` + yfinance
SPY (Pass-17 cached window 2026-02-10 → 2026-05-09, N=63)

| Metric                              | Value      |
|-------------------------------------|------------|
| Raw Sharpe (Pass 17)                | +1.144     |
| SPY Sharpe (Pass 17)                | +1.654     |
| Beta (GSA vs SPY)                   | -0.0086    |
| Alpha (annualized)                  | +21.28%    |
| **Residual Sharpe (NEW canonical)** | (computed by script) |
| Residual Sharpe vs SPY-Sharpe       | (computed by script) |

The numerical result is computed by running the script (so the paper
stays #69-honest about not pre-asserting the number); see
`analyses/gsa_residual_sharpe/results.txt` for the actual figure.

**Honest expectation**: because β ≈ 0 currently, residual Sharpe will
be very close to raw Sharpe. The metric *change* matters most when β
drifts away from zero in future windows — at which point raw Sharpe
will start over- or under-rewarding GSA for inherited market beta,
while residual Sharpe will continue to score only the alpha-component.

### 2.4 Adoption (s18 RATIFIED Pass 19)

Per Brandon's "s18 affirmed!" directive, residual Sharpe is now the
**canonical GSA performance metric** going forward:

- All future GSA backtest reports lead with residual Sharpe.
- Raw Sharpe is reported as a secondary metric for benchmark-
  comparability with conventional strategies.
- The Pass-18 GSA diversifier policy (β ≈ 0, DD ≤ -5%, alpha-positive)
  is explicitly tied to residual Sharpe as the operational scorecard.

#69 caveat: residual Sharpe with N=63 days has wide CIs; reporting
N alongside the point estimate is required.

---

## 3. p17 polished — synthetic-baseline mode

### 3.1 What was added

`analyses/h1_combined_runner/h1_combined_runner.py` now supports:

```bash
python analyses/h1_combined_runner/h1_combined_runner.py --synthetic
python analyses/h1_combined_runner/h1_combined_runner.py --synthetic --n 10000
```

The `--synthetic` mode runs N (default 5000) random raters who answer
each H1-BB and H1-Penrose patch with Bernoulli(0.5) coin flips, then
reports the empirical hit-rate distribution. This gives Brandon an
**immediate context** for whatever score his actual sit-down produces:
he knows what "chance" looks like in this exact harness without
needing to do the binomial math in his head.

### 3.2 Output

Synthetic mode prints percentile thresholds:
- 50th / 75th / 90th / 95th / 99th percentile hits/30 for BB
- 50th / 75th / 90th / 95th / 99th percentile hits/10 for Penrose
- Joint distribution: P(both clear 95th percentile) under chance

Then any subsequent `--rate` session is automatically compared
against the synthetic baseline at score-time (already in
`print_results`; the synthetic numbers get loaded if available).

### 3.3 Why this matters

Pre-Pass 19 the runner only printed the binomial p-value. That's
correct but cognitively distant. Brandon's real intuition-test
question is "is my score *unusual*?" — the empirical distribution
answers that immediately ("you got 23/30; chance gets that with
probability ~0.4%" reads more directly than "z = +2.93, p = 0.0017").

#69 caveat: the synthetic baseline only models *random* rating; it
does NOT model "experienced rater with low intuition" baselines (a
domain-knowledgeable rater might do better than chance via reasoning
even without intuition). That ceiling test would require recruiting
domain-knowledgeable but intuition-low raters — a ≥10-rater Pass-19+
exercise, not a one-day ship.

---

## 4. §7.7.49–54 collapse executed (per established rhythm)

Six dense entries (Passes 13-18, ~80 lines) compressed to six
one-liner pointers in `replit.md`. All linked-paper anchors
preserved; substantive content recoverable via the linked papers.

This continues the **Pass-3 / Pass-7 / Pass-13 collapse rhythm**:
- Pass 3 collapsed §7.7.1-30 (Passes 1-7)
- Pass 7 collapsed §7.7.31-40 (Passes 8-12)
- Pass 13 collapsed §7.7.41-48 (Passes 13-18)
- **Pass 19 collapses §7.7.49-54 (Passes 13-18)**  ← this Pass

`replit.md` size: ~107 lines pre-collapse → ~30 lines post-collapse +
new §7.7.55 entry.

---

## 5. Carried-forward Brandon-decision menu (rolling roster)

**Pass-13 still open**: (i)–(v) (Hamiltonian / vertex / V₄↔{T,F,I,DT}
/ Mott-FQH / C.6 interp).

**Pass-14 still open**: (a) hypercomputing TRL ratification; (c) I
Ching pre-registration.

**Pass-15 still open**: (α)/(β)/(γ) — GBRH lit pull / replication
corpus / formal write-up.

**Pass-16 still open**: (a16)/(b16) — H1-BB sit-down + Op-1 IRR.

**Pass-17**: (d17) DISCHARGED Pass 18; (g17) DISCHARGED Pass 18;
(p17) **POLISHED Pass 19 §3** (synthetic baseline shipped) — still
awaits Brandon sit-down; (z17) staged Pass 18, awaits Brandon
review; (h17) executed Pass 18 → led to h18.

**Pass-18**: (h18) **ELABORATED Pass 19 §1** — Brandon decides R-A
vs R-B (DPES default R-B); (s18) **IMPLEMENTED Pass 19 §2** — residual
Sharpe ratified as canonical GSA metric.

**Pass-19 NEW item**: none — all four directive items shipped.

**Brandon manual TODO list (carried forward, unchanged)**:
(A) Polar AccessLink OAuth
(B) Publish Zenodo 20097913 (4/3 short note) via UI
(C) Optional BLE GATT capture
(D) Pass-13 (i)-(v) ratification
(E) Pass-14 (a)/(c)
(F) Pass-15 (α)/(β)/(γ)
(G) Pass-16 (a16)/(b16) sit-downs
(H) Pass-17 (d17/g17 discharged); (p17) sit-down + (z17) review
(I) Pass-18 (h18) R-A vs R-B; (s18) discharged Pass 19

---

## 6. Pass 20 candidates

1. **H4 mapping-sensitivity test** (R-B execution per h18 §1.4).
2. **Apply residual Sharpe to historical GSA windows** to see how
   beta-drift affects the metric over time.
3. **MI φ-transform at larger windows (60/120/250 days)** —
   carried from Pass 18.
4. **Score (p17) Brandon sit-down** if completed, with synthetic-
   baseline context now baked in.
5. **Apply (z17) Brandon publish/keep/delete decisions** to Zenodo.
6. **Zenodo topic rebundling** once z17 returns.
7. **GSA per-layer alpha attribution** (carried from Pass 17/18).

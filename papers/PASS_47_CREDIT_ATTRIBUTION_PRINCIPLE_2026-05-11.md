# Credit Attribution Principle (CAP) — TI Sigma Project Principle

**Date:** 2026-05-11 (Pass 47)
**Status:** RATIFIED by Brandon. Project-level operating principle.
**Trigger:** Pass-47 §1.C honesty caveat — when a TI Sigma test fails because the failure mode is the well-known Bohigas-Giannoni-Schmit 2×2-Wigner-surmise gap (RMT-textbook), should that count as a "TI Sigma KILL"? Brandon ruled: depends on how well-known the underlying result is. CAP formalizes that ruling.

---

## §1 — The Principle

**TI Sigma receives credit for any empirical pattern it encompasses, weighted by the obscurity of that pattern.**

Formally, for any empirical result R that TI Sigma's framework generates or successfully predicts:

```
credit(R, TI-Sigma) ∝ (1 - well_known(R))
```

where `well_known(R) ∈ [0, 1]` is the degree to which R is established consensus knowledge.

Two anchor points:

- **R is common knowledge** (graduate textbook material, Wikipedia-level, NIST handbook) → `well_known ≈ 1` → TI Sigma receives ≈ 0 credit. Encompassing it is *vacuous* (the "Wigner-BGS-gap" example).
- **R is genuinely obscure or novel** (no consensus, recent niche result, contrarian-but-true) → `well_known ≈ 0` → TI Sigma receives ~full credit for getting it right under its umbrella.

**Intermediate cases earn intermediate credit.** A result known only in a small specialist community (~10² practitioners) earns more credit than one in undergraduate textbooks.

---

## §2 — What CAP is and is not

### §2.1 — CAP IS

- A **credit-distribution** rule for evaluating TI Sigma's empirical wins.
- Symmetric with falsification: TI Sigma also receives proportional **debit** when it fails to encompass an obscure-but-true result, and proportional **less debit** when it fails to encompass a common-knowledge result (because everyone fails to encompass things; no theory contains everything).
- A way to honestly score "how much of reality TI Sigma is grabbing" without collapsing under either over-claiming (encompassing trivia) or under-claiming (refusing credit for synthesis).

### §2.2 — CAP IS NOT

- Not a way to escape KILL verdicts. A result that mechanically falsifies a TI Sigma sub-claim still falsifies it. CAP only governs the *credit weighting* in summary scorecards, not whether kill criteria fire.
- Not a license to claim credit for everything in a textbook. A TI Sigma claim that *predicts* a textbook result was always going to predict it; this is a sanity-check on the framework, not evidence for it.
- Not retroactive — CAP applies to assessments made after 2026-05-11 (Pass 47). Earlier scorecards stand as written.

---

## §3 — Operationalization

When evaluating a result R for credit assignment to TI Sigma:

1. **Determine `well_known(R)`** via one of:
   - `well_known ≈ 1.0`: in widely-used undergraduate textbooks OR Wikipedia front-page-of-topic OR NIST/CODATA handbook.
   - `well_known ≈ 0.7`: in standard graduate textbooks OR a major review article in last 10 years.
   - `well_known ≈ 0.4`: in specialist literature (~10²-10³ practitioners aware) OR a single major paper in last 5 years.
   - `well_known ≈ 0.1`: niche / contested / single-result / no consensus.
   - `well_known ≈ 0.0`: novel — no prior art at all (rare; usually indicates weakness in lit-search rather than true novelty).

2. **Determine TI-Sigma's encompassing strength** for R (how directly the framework predicts it vs. just-being-consistent):
   - **STRONG:** R is a non-trivial prediction of a TI Sigma claim that would be falsified if R were false.
   - **MEDIUM:** R is consistent with TI Sigma but not a unique prediction.
   - **WEAK:** R is post-hoc rationalized into TI Sigma framing.

3. **Credit:** `credit = encompassing_strength × (1 - well_known)`.

4. **Logged in:** scorecard, replit.md ledger entry, and (if material to a paper's claim) the paper itself.

### §3.1 — Worked example: Pass-47 p46-A.C

- R = "GUE Wigner surmise (2×2) deviates from large-N spacing distribution at high N."
- `well_known(R) ≈ 0.85`: BGS 1984 + standard RMT graduate texts. Specialist-textbook-level.
- TI Sigma encompassing strength: **WEAK** (Pass-37 PD-canonical-final claim was "Riemann-connected" — Option C re-interpretation post-hoc rationalizes the BGS gap as a "PD signature," which is post-hoc framing).
- `credit ≈ WEAK × 0.15 = ~0`. **TI Sigma receives essentially no credit for "encompassing" the BGS gap.**
- The KILL verdict for Option C remains in force per Pass-45 §11 (kill criteria mechanical).
- BUT: the KILL is also not a strong falsification, because the failure mode is RMT-textbook, not TI-Sigma-disconfirming. The result is mostly *informationally null* with respect to TI Sigma.

### §3.2 — Worked example: Pass-43 qc25 chi-square uniform-32 = 0.65

- R = "Hadamard-prepared 5-qubit product state on real IBM hardware shows uniform measurement distribution to within hardware noise."
- `well_known(R) ≈ 0.95`: textbook QM, exactly what every quantum-circuits 101 course teaches.
- TI Sigma encompassing strength: **MEDIUM** (Pass-31 D2-HYBRID claim is non-trivially consistent with this; not a unique prediction).
- `credit ≈ MEDIUM × 0.05 = small`. **Pass-43 was honestly logged as "passes-not-strongly-endorses."** This was already CAP-consistent before CAP was named.

### §3.3 — Worked example: Pass-46 qc26 GHZ-5 Mermin |M_5| = 14.535

- R = "GHZ-5 phase state on near-term IBM hardware violates classical LHV bound at ~71σ."
- `well_known(R) ≈ 0.65`: GHZ violations are textbook material (Mermin 1990) but specifically reaching 91% of theoretical max on Heron-class hardware in 2026 free-tier is a recent specialist result.
- TI Sigma encompassing strength: **MEDIUM-STRONG** (D2-HYBRID predicts hardware-realizability of multipartite-entanglement at 5-qubit scale; this is a non-trivial confirmation of that scale-claim).
- `credit ≈ MEDIUM-STRONG × 0.35 ≈ moderate`. **Pass-46 verdict CONFIRM stands; honest credit weighting is moderate not maximal.** The hardware result is real and meaningful for TI Sigma, but not a private TI-Sigma prediction.

---

## §4 — Going forward

All Pass-48+ scorecards, credit summaries, and replit.md ledger entries should annotate non-trivial empirical wins/losses with a rough CAP weighting. Format:

```
[CAP: well_known≈X.XX, encompassing=STRONG/MED/WEAK, credit≈Y.YY]
```

This keeps the corpus honest about *how much* of any individual win is attributable to TI Sigma vs. to background scientific consensus.

---

## §5 — Connection to existing #69 / Asymmetric-Standards-#69

CAP is the natural extension of #69 brutal-honesty into the credit-attribution dimension. #69 prevents over-claiming on the *direction* of evidence (a CONFIRM that should be INDETERMINATE); CAP prevents over-claiming on the *magnitude* of credit (a CONFIRM that is real but trivially-encompassing). Both serve the same goal: making the corpus's empirical scorecard robust to a hostile auditor.

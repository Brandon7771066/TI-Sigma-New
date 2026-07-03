---
name: OET first empirical test (whole-vs-parts on dual-EEG)
description: What the first executed OET test found and why the decisive part couldn't run — so the same untestable test isn't blindly re-run.
---

# OET (Organizational Emergence Theorem) — first executed test

**Claim (B177):** above a coupling threshold τ, `Error(𝒪) < Σᵢ Error(𝒞ᵢ)` — a WHOLE model predicts the near future better than the SUM of independent per-cluster (PART) models, and the gain is *indexed* by LCC coupling crossing τ.

**Credit / novelty split (EVD-1, don't overclaim):** whole-beats-parts / synergy / macro-beats-micro is ESTABLISHED — Hoel-Albantakis-Tononi (PNAS 2013), Williams & Beer (2010, PID), Granger 1969 / Schreiber 2000. OET's ONLY new delta is the **LCC-threshold-indexing** of that gain. So the test that matters is the indexing, not "does whole ever beat parts."

**Design that worked:** two brains = two clusters; PART = AR(own past), WHOLE = VAR(both brains' past); **out-of-sample** one-step MSE (in-sample VAR always ≥ AR ⇒ would rig it); cross-pair surrogate control (both brains hear the same tones ⇒ common input can fake a joint-model win). Harness: `analyses/lcc_oet/`.

**Result on ds007471 (32 pairs, 1278 trials) — honest negative/inconclusive:**
- Raw inequality UNSUPPORTED out-of-sample: theta Δ≈+1e-6 (negligible), beta Δ=−4.95e-4 (whole reliably WORSE OOS). Interaction-specific gain null in theta (p=0.34), negligible-though-sig in beta (+6.2e-5, p=0.0018) but still leaves whole worse than parts. Consistent with B164 common-input dominance.
- **The novelty was UNTESTABLE:** inter-brain PLV floor (C̄≈0.04–0.09); **0/1278 trials reached even the lowest candidate τ=0.414** ⇒ the `C≥τ` cell is always empty ⇒ coupling-indexing can't be evaluated. A "cannot-run-the-decisive-part" outcome (cf. Hilbert–Pólya operator test).

**Lesson / what to do next:** don't re-run the indexing test on a system whose inter-cluster coupling sits far below τ — it will be untestable again. Need a strongly-coupled system (or a finer multivariate coupling estimator) where `C≥τ` is actually populated. OET-F1/OET-F2 remain OPEN; the raw-form failure DOES count as a risky-prediction failure (keeps OET non-goalpost-moving per LCC-UNFALS-F1). Established macro-beats-micro is NOT contradicted.

# DSB-1 — Default-Success-Belief (Candidate Canonical Principle)

**Pass-62 batch-1 · 2026-05-22 · Status: PROVISIONAL pending ratification**

---

## 1. Statement

Under the Universal A Priori (UOP), agents whose decision-policy defaults to (i) prior belief that the task will succeed and (ii) acceptance of strong intuitions before completion of verification, will achieve higher pragmatic-outcome rates than agents whose decision-policy defaults to verification-first / evidence-first inspection — *on tasks where the intuition prior carries informative signal above the noise floor*. Failure outcomes under DSB-1 are evaluated on the pragmatic axis as Moot (MFD-1 §2); success outcomes are evaluated on the TSD-A axis (additive per-event TIU).

Formal compactification:

> **DSB-1.** Let an agent face a task T with prior confidence c ∈ [0,1] and intuition signal i with informativeness I(i; success) ≥ δ. The DSB-1 decision policy commits to action whenever c ≥ τ_c AND |i| ≥ τ_i. The verification-first policy requires k additional samples before commitment. DSB-1 predicts: E[reward | DSB-1] > E[reward | verify-first] when I(i; success) ≥ δ_critical, for some δ_critical determined empirically.

**Critical scope condition.** DSB-1 holds *only* in the informative-intuition regime. In the non-informative regime (I ≈ 0), DSB-1 collapses to overconfidence and is dominated by verification-first. This is the principle's own failure mode and the falsifier landscape is built around locating δ_critical.

## 2. Empirical anchors

- **Bandura, A. (1977, 1997)** — *Self-Efficacy: The Exercise of Control.* Self-efficacy beliefs predict task outcomes net of objective skill, with effect sizes consistently in d = 0.3–0.6 range across meta-analyses. Directly anchors clause (i).
- **Dweck, C. (2006)** — *Mindset.* Growth-mindset interventions show small but replicable effect on persistence and achievement (d ≈ 0.1–0.2 in pre-registered replications; smaller than original claims but non-zero). Anchors persistence-under-failure component.
- **Rosenthal-Jacobson (1968) Pygmalion in the Classroom** — expectancy effect on student outcomes; modern meta-analyses (Jussim & Harber 2005) confirm a modest real effect distinct from confirmation bias.
- **Placebo and expectancy-effect literature** (Benedetti, Kaptchuk) — confidence in outcome causally alters outcome via documented neurobiological mechanisms (opioid, dopaminergic, immune). Provides the mechanistic backbone for clause (i) operating in physical-outcome domains, not just self-report.
- **Klein, G. (1998)** — *Sources of Power.* Recognition-primed decision-making in expert fire commanders, nurses, military: expert intuitions adopted without analytic verification produce better outcomes than analytic deliberation *in the expert-intuition regime*. Anchors clause (ii) and supplies the informativeness-regime boundary.
- **Kahneman, D. & Klein, G. (2009)** — *Conditions for Intuitive Expertise.* Joint paper specifying *when* intuition is trustworthy: regular environment + opportunity for feedback learning. Anchors δ_critical scope condition.

## 3. Relation to existing TI Sigma canon

- **Generalizes ASYMMETRIC theory:** ASYMMETRIC asserts failure-vs-success asymmetric weighting; DSB-1 asserts belief-vs-doubt asymmetric default *prior to* outcome. ASYMMETRIC is the outcome-side asymmetry; DSB-1 is the prior-side asymmetry. They compose.
- **Operationalizes Authority Axis (AA) sim-belief-and-doubt:** AA requires simulating both belief and doubt; DSB-1 specifies which simulation is the *default operating mode* (belief) and which is the *check mode* (doubt). AA without DSB-1 is symmetric and underdetermined; AA with DSB-1 is asymmetric and operational.
- **Composes with APP-1 (active-pragmatism):** APP-1 requires active-engagement; DSB-1 supplies the prior-confidence input that makes active-engagement non-paralyzed.
- **Composes with TSD-1 (Tralse Success Distinction):** DSB-1 + TSD-A naturally pair — high prior confidence produces engagement, successes are weighted additively per TSD-A, failures are weighted Moot per MFD-1.
- **Composes with MFD-1 (Moot-Failure Duality):** DSB-1's pragmatic Moot-on-failure clause is exactly MFD-1's pragmatic axis applied to the prior-action stage.

## 4. Pre-registered falsifiers

- **F-DSB-1-1 (bandit simulation, signal regime):** Synthetic 10-armed bandit, T = 1000 pulls, arm reward distributions with informative prior. DSB-1 agent commits when c ≥ 0.6; verify-first agent samples k = 20 per arm before commitment. DSB-1 predicts cumulative regret ratio DSB-1 / verify-first < 0.85. If observed ratio ≥ 0.85, DSB-1 REFUTED in signal regime. (Run in this pass; see `simulations/dsb1_confidence_vs_verification_bandit_2026-05-22.py`.)
- **F-DSB-1-2 (bandit simulation, noise regime):** Same setup with informativeness collapsed to zero (uniform reward distributions across arms). DSB-1 predicts NO advantage and possibly a deficit (the scope condition). If DSB-1 still wins in pure-noise regime, the principle is *overconfident* — it would be claiming to generate signal from noise. This would REFUTE the informativeness scope condition and force a rewrite.
- **F-DSB-1-3 (empirical scope-boundary test):** In real human-task data (e.g., chess intuition, medical diagnosis, fireground command per Klein), the DSB-1 effect should attenuate to zero or invert in environments lacking the Kahneman-Klein conditions (irregular environment, no feedback loop). If DSB-1 effect persists with same effect size in low-validity environments, the scope condition is wrong and the principle reduces to generic overconfidence bias (Tetlock 2005). DSB-1 REFUTED.

## 5. Honest caveats (#69)

- DSB-1 sits in tension with the prevailing methodological default ("examine evidence first, then commit"). The principle does not claim that default is wrong everywhere — it claims that default is wrong *in informative-intuition regimes* and that the methodological default produces avoidable opportunity cost in those regimes. The empirical question is the relative size of the informative-intuition regime vs the non-informative regime in the domain of interest.
- DSB-1 is N=0 ratified as of this writing. F-DSB-1-1 simulation in this pass is the first falsifier round; the principle needs ≥ 2 more independent falsifier rounds (F-DSB-1-2, -3) plus one human-data anchor before promotion to CANONICAL.
- DSB-1 must not be invoked as a license for overconfidence in domains where the scope condition is unmet. The scope condition is *load-bearing*; without it the principle is the generic overconfidence bias and is dominated by verification-first.
- Author's own use of DSB-1 (Brandon Emerick's operating mode in TI Sigma research) is an N=1 anecdote, not falsifier-grade evidence. Logged in §6 below for transparency.

## 6. Application instance: TI Sigma research mode (N=1, transparency only)

The author has been operating in approximate DSB-1 mode throughout the TI Sigma corpus: prior confidence in the framework's value, acceptance of strong intuitions (e.g., Tralse coinage, MR Truth Labels, GILE-HEM) before complete verification, with failures (e.g., disconfirmed PD-Riemann γ-window, retracted urb_509 §7.4, MBE-via-Pass-37-rubric main-effect death) processed as Moot rather than as global-belief-revising. Documented outcomes during this operating mode include: 100+ open-access papers; 20 machine-verified Lean 4 theorems; Fleiss κ = 0.906 on 4-label rubric; 71σ Bell-inequality result on IBM quantum hardware (qc26 GHZ-5); Global Healthcare Magazine cover feature secured 2026-05-22 (legitimacy verified by author).

This is N=1 and confounded with author skill, domain favorability, and selection effects. It does not discharge any falsifier. It is logged because TI Sigma practice requires transparent declaration of investigator priors per #69.

## 7. Ratification path

- Pass-62: candidate posted (this document), F-DSB-1-1 sim executed (companion `.py`), F-DSB-1-2 sim executed (same script, noise-regime arm).
- Pass-63+: F-DSB-1-3 empirical-anchor test design; second-pass replication of F-DSB-1-1 with different parameter sweep.
- Promotion to CANONICAL: F-DSB-1-1 not refuted in ≥ 2 independent runs + F-DSB-1-2 confirms scope-condition (no advantage in noise regime) + one human-data anchor referenced.

---

**File:** `papers/PASS_62_DSB_1_DEFAULT_SUCCESS_BELIEF_2026-05-22.md`
**Status:** PROVISIONAL · pre-registered falsifiers F-DSB-1-{1,2,3}
**Canonical companions:** ASYMMETRIC, AA, APP-1, TSD-1, MFD-1
**Sim:** `simulations/dsb1_confidence_vs_verification_bandit_2026-05-22.py`

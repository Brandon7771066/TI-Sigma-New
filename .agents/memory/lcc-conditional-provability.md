---
name: LCC conditional provability (Weak vs Strong) + adversarial crack
description: How LCC can/can't be PROVEN — the observational proof-by-contradiction is unsound; only intervention closes it. Use when asked to prove/formalize LCC or defend "correlation⇒causation."
---

# LCC conditional provability (2026-07-02)

After two real-data empirical negatives (ds007471, Depresjon), the corpus stopped fitting the LCC index and asked whether LCC is **provable at all**. The durable results:

## The split (do not conflate)
- **Strong-LCC** = `high synchrony ⇒ direct bidirectional causation`. **RETIRED / unprovable** — a hidden common driver cheaply mimics synchrony.
- **Weak-LCC** = a **valid CONDITIONAL**: `IF common causes, artifacts, autocorrelation, selection, imposed stimuli are all ruled out THEN persistent bidirectional predictive dependence ⇒ causal coupling`. Logically valid; the whole difficulty is *discharging the antecedent*.

## The load-bearing lesson (Theorem 1, proved by counterexample)
**Observational-only "no other explanation possible" is UNSOUND.** You can only condition on *measured* confounders. If the true common cause has any **unmeasured component** `Z₂` (the generic real case), a smooth contemporaneous common driver `Z=Z₁+Z₂` produces spurious *bidirectional* Granger causality that passes EVERY observational guardrail (persistence, bidirectionality, phase+shift surrogates, conditional-on-measured-Z survival, synchronization-potential) while having NO `X↔Y` edge.
**Why:** conditioning on the measured `Z₁` alone leaves the `Z₂`-driven coupling intact; only the *oracle* (full `Z₁+Z₂`) screens off. Observationally you can never certify you measured every common cause. This is a **proof-theoretic** limit, not just a measurement difficulty — sharper than the earlier "naive statistic is always confoundable" (memory `lcc-confirmation-tests`).

## What IS sufficient (Theorem 2, scoped)
Adding **G5 = surgical `do()` perturbation** (`do(X)→ΔY` AND `do(Y)→ΔX`, atomic, no side channel) recovers ground truth on the tested 4-world model class (BIDIR passes, COMMON's `do(X)→ΔY`=0.0). **Caveat:** sufficiency shown on a finite generator family, NOT universal; a "fat-hand" intervention that also perturbs `Z` reintroduces confounding. Interventional soundness is contingent on intervention *quality*.

## Guardrail design gotchas (if you rebuild the sim)
- **Synchronization Potential = necessary-not-sufficient** (both nodes entrainable ≠ coupled to *each other*); never let it license `X↔Y`.
- The **crack must be structural, not tuned**: use an unmeasured *component* of the common cause, not a hand-picked noise level. Tuning proxy noise to force pass/fail is gaming it.
- **G4 (conditional survival) needs a significance test** (shift-null), NOT a `gain>0` threshold — any tiny numerical residual passes `>0`, making G4 a no-op and the oracle never "screen off."
- Common driver must be **smooth (high autocorr) + contemporaneous** to manufacture the hardest case (spurious bidirectional Granger).

## Bell/CHSH tie = RESONANCE, not derivation
The only known regime where correlations certify causal structure *without* measuring every hidden cause is **device-independence** (CHSH `2√2>2`, Fine 1982 no-global-joint-measure — corpus's Contextual-Admissibility). Flag it; do NOT claim a numeric coincidence (the crack is measure-theoretic confounding, no √2 constant involved). A *closed* (non-conditional) LCC would require placing a substrate in a device-independent regime — OPEN (LCC-PROOF-F3).

## Constructive redirect
Mood-Amplifier target is NOT "prove the constants" and NOT static diagnosis. It's B165's Gate-1 positive: **`P` = future-state predictability**. New hypothesis `ΔP, ΔS, Δ(C|Z) → Δmood` under `baseline→stimulation→post` — exercises the ONLY sound arm (intervention) on real data.

Code: `analyses/lcc_conditional_proof/crack.py` (deterministic — fixed per-generator seed offsets, NOT `hash()`; the config hash must cover them or exact fractions drift silently between runs). Falsifiers LCC-PROOF-F1 (find an observational guardrail COMMON fails), F2 (bound interventional sufficiency), F3 (Bell route) OPEN.

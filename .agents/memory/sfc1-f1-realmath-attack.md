---
name: Structural-fidelity leakage audit (negation-pair control)
description: How to honestly probe "can structure-alone predict mathematical truth / quality" and why a negation-paired, polarity-balanced corpus is the decisive leakage killer.
---

# Predicting truth from structure — the leakage-pair audit

**The durable method (reusable for ANY "predict truth/quality from structure" claim).**
- A **naive** benchmark — true items vs a *separately collected* false bag — over-reports massively (a real run hit held-out ~0.92) because the false bag accidentally carries a surface artifact (e.g. more negation/impossibility wording). This is the standard ML-for-math leakage trap.
- The **decisive control is a NEGATION-PAIRED, polarity-balanced corpus**: match every true `P` to a settled-false counterpart via a **near-minimal edit** (antonym swap / single negation: rational↔irrational, prime↔not-prime, converges↔diverges, …) so members are structurally near-identical (verify with token-overlap Jaccard) and negation/polarity tokens land on BOTH labels. Use **group-CV** (a pair never spans train/test). The same `F` then collapses to **chance**. ⇒ no leakage-free surface structure tracks truth; you must actually do the math.
- **Leakage tax = naive − balanced** measures the artifact directly. Always run this audit before believing a structural-fidelity number.
- **Wording rail:** "near-minimal edit / near-identical members (Jaccard-checked)," NOT "differs only in math content" — the latter overstates the control unless every pair is a strict minimal edit, which is hard to guarantee by hand.

**The decidable-subclass escape hatch (don't be fooled).** On a decidable class (e.g. arithmetic `a+b=c`): surface features → chance; add an **evaluator** feature → ~1.0. But that feature **IS a decision procedure / oracle** — fidelity is trivial there ONLY because `F`=the decider (zero predict-before-proof content). High accuracy on a decidable class is NOT evidence for non-oracular structural fidelity.

**Honest verdict pattern.** The only two ways to beat chance are (i) leak, or (ii) embed a decider — both forbidden for a genuine structural map. So a leakage-free non-oracular `F` predicting truth stays the OPEN frontier; the "no-magic" undecidability bound reproduces on real math. **Scope rail:** small hand-curated corpora are absence-of-evidence ILLUSTRATIONS, never a census proving no `F` can exist, and never an RH claim.

**Where the real frontier is.** Ramanujan Machine (Raayoni et al. *Nature* 2021) and Davies et al. *Nature* 2021 mine structure to guide real math — but as **heuristic generators validated by human proof afterward**, i.e. a *fallible heuristic*, consistent with the bound, not a counterexample. The reachable target is "strong heuristic," which confirms rather than breaks the bound.

Builds on `sfc1-structural-fidelity.md` / `fcf1-formal-conjecture-fidelity.md`.

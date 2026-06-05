# Pass-77 B77 — Communication asymmetry: the Asymmetric-Communication Norm (ACN-1) and why "mean what you say" is over-reach

**Date:** 2026-05-28 (Pass-77 batch-77)
**Mode:** DPES · ASYMMETRIC #69 brutal honesty
**Budget:** <$50, $0 spent (local numpy/matplotlib).
**Compute:** `analyses/pass77_b77_communication_asymmetry/run_b77.py` (+`results.json`, 2 figures)
**Status:** ONE CANDIDATE principle (ACN-1). Ratification = Brandon's explicit choice (partner-principle
precedent). Canonical count unchanged **74**.

---

## 0. Source — Brandon insight (2026-05-28, verbatim)

> "'Mean what you say and say what you mean' is essentially wishful thinking for 'neat freaks.' Actual
> conversation is asymmetrical and obligating everyone to such a narrow standard is just plain silly.
> Besides, getting the other person to think for themselves about what was said has merit. Not
> everything should be spelled out to a tee. Moreover, speakers cannot actually customize their
> communication to each person in such an idealistic manner since that would require knowing the
> person's knowledge and thoughts."

---

## 1. ACN-1 — Asymmetric-Communication Norm (CANDIDATE canonical)

**Statement.** Communication is intrinsically **asymmetrical** (speaker intent ≠ listener
reconstruction; the two parties hold different knowledge), so the symmetric ideal "mean what you say /
say what you mean" (MWYS) — full, exhaustive explicitness — is neither attainable nor desirable. The
right target is **sufficient explicitness for the modeled listener**, which (i) is **always below
maximal**, (ii) **depends on the listener**, and (iii) **cannot be perfectly customized** because the
speaker cannot read each mind.

**Four sub-claims (each tied to existing canon):**

- **ACN-1a — Over-explicitness is over-reach.** Spelling everything out past what the listener needs
  carries a real cost (boredom, condescension, wasted effort, disengagement). Explicitness therefore
  has an **interior optimum** — *structurally identical to the UOP 0.93 cap*: just as truth past the cap
  lowers J (B75), explicitness past the listener's need lowers communicative value. MWYS is the
  communicative analogue of "maximize truth to 1.0" — and it is punished the same way.
- **ACN-1b — Productive under-specification.** Leaving interpretive work to the listener has merit:
  it engages their cognition (active reconstruction). This is the **listener exercising WMI-1**
  (identifying the intended idea given sufficient information). "Getting the other person to think for
  themselves" is not laziness — it is invoking the listener's own metacognition.
- **ACN-1c — Customization is bounded (theory-of-mind limit).** Tailoring perfectly to each listener
  would require knowing their knowledge and thoughts; this is impossible, so a speaker necessarily
  communicates to a **model** of the listener, not the listener. The resulting mismatch is an
  **irreducible cost, not a moral failing**.
- **ACN-1d — Sufficiency, not maximalism.** "Back up sources / be explicit when *helpful or necessary*"
  (CEC-1b) is the same **epistemic-sufficiency gate** applied to communication: be as explicit as
  *needed*, no more. ACN-1 is the production-side twin of CEC-1's consumption-side sufficiency.

**Composition:** extends **TPS-1** (truth content fixed; presentation adjusts — ACN-1 says *how much*
presentation/explicitness to deploy); inherits the **UOP/GTT-1 over-reach geometry** (B75 peak-then-
decline); pairs with **WMI-1** (listener as active truth-identifier) and **CEC-1b** (shared sufficiency
gate); bounded by **theory-of-mind** limits (ACN-1c). It is the third member, with CEC-1 and WMI-1, of
a Pass-77 **substance/sufficiency cluster**.

### Pre-registered falsifiers (ACN-1)
- **ACN-1-F1:** If, in comprehension/engagement experiments, maximal explicitness (e=1) reliably
  maximizes *retained, correctly-reconstructed* meaning across listeners, ACN-1a (interior optimum)
  fails. (§2 is a by-construction model; this is the empirical test.)
- **ACN-1-F2:** If optimal explicitness does **not** vary with listener prior knowledge in controlled
  tasks (single e best for all), ACN-1c (listener-dependence / customization value) fails.
- **ACN-1-F3:** If under-specification consistently *harms* outcomes with no engagement/retention
  benefit, ACN-1b (productive under-specification) fails.
- **ACN-1-F4:** If ACN-1's explicitness-sufficiency gate is governed by a *different* threshold than
  CEC-1b/WMI-1's evidence/info gate in a shared-task design, the "single sufficiency principle" cluster
  claim (Pass-77 §unifier) is refuted.

---

## 2. Illustrative demonstration (#69: by-construction, mirrors the UOP peak)

`run_b77.py`: a speaker picks explicitness `e ∈ [0,1]` for a listener with prior knowledge `k ∈ [0,1]`.
Comprehension `U = k + (1−k)(1−e^{−βe})` saturates in e; over-explaining past need incurs a **quadratic
over-reach penalty** `λ·max(0, e−(1−k))²` — the same shape as the 0.93 cap. Value `V = U − penalty`.

**By-construction (#69):** I set the generative model, so the qualitative shapes are the deliverable,
not measured magnitudes. Empirical upgrade: comprehension/engagement experiments vs measured priors.

| finding | numbers | reading |
|---|---|---|
| **Interior optimum, e*<1 (Fig 1)** | optimal e* by listener: k=0.1→**0.93**, 0.3→0.74, 0.5→0.57, 0.7→0.38, 0.9→**0.17** | for every informed listener the optimum is below "spell it all out" — Brandon's "not everything should be spelled out to a tee," derived. |
| **Listener-dependence (Fig 1)** | e* falls monotonically as k rises | well-informed → be terse (let them infer); uninformed → be explicit. **No single e serves everyone.** |
| **Customization impossible (Fig 2)** | idealized per-listener 0.944 vs best broadcast 0.896 → **irreducible loss 0.048** | "speakers cannot customize to each person" is a **quantified bound**, not a failing. |
| **MWYS is strictly worse (Fig 2)** | MWYS maximal (e=1) = **0.499** vs broadcast optimum 0.896 → loses **0.397** | the "neat-freak" standard isn't merely unattainable — it is **actively suboptimal**, scoring far below even a single one-size broadcast. |

The result the model *adds* beyond the verbal insight: MWYS-maximalism doesn't just fail to be ideal —
it is **worse than deliberately calibrated under-explicitness**, by a large margin (0.50 vs 0.90).

---

## 3. Status

- **ONE CANDIDATE principle** (ACN-1) + **4 pre-registered falsifiers** OPEN. **Canonical principle
  count unchanged 74** (candidate awaits Brandon ratification per partner-principle precedent). MR
  refinements 14; meta-collapses 41. Pass-77 papers 48→**49**. $0.
- **Pass-77 substance/sufficiency cluster now 3 candidates:** CEC-1 (B76, consumption-side), WMI-1
  (B76, agent-side), ACN-1 (B77, production-side) — unified by a **single epistemic-sufficiency gate**
  (be as explicit / seek as much / demand as much evidence as *needed*, no more). A joint ratification
  ceremony is the natural Pass-77 next step when Brandon directs.
- **Open hooks:** (1) comprehension/engagement experiments to close ACN-1-F1/F2/F3; (2) the shared-
  threshold test ACN-1-F4 / WMI-1-F3 that would confirm or refute the single-sufficiency-gate unifier.

**Files:** `analyses/pass77_b77_communication_asymmetry/run_b77.py` (+`results.json`,
`fig1_explicitness_optima_per_listener.png`, `fig2_customization_impossibility_cost.png`); this paper.
Anchors: TPS-1, UOP/GTT-1, B75 (over-reach geometry), CEC-1 + WMI-1 (B76), ASYMMETRIC #69.

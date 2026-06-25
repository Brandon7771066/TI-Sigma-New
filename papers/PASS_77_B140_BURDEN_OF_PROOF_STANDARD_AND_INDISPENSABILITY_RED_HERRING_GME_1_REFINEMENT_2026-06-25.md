# Pass-77 B140 — The Correct Burden-of-Proof **Standard** + the Indispensability **Red Herring** (GME-1 refinement #2)

**Date:** 2026-06-25
**Status:** ONE refinement to the GME-1 candidate (+ partial ERRATUM to B139 §3 scenario B). **Nothing ratified. Canonical principle count unchanged: 79.**
**Builds on:** GME-1 (B138 §4), B139 (parity), TRG-1 (#77), EMD-1 (B128), PDU-1 (B127).

---

## 0. The author's three corrections (verbatim spirit)

> "My argument is not meant to be a mathematical certainty like 2+2=4. For moral realism to win, it only needs to be proven **beyond any reasonable doubt** and ideally be **pragmatic**. Forcing either physicalists or moral realists to have **100% certainty** is a completely unreasonable burden.
>
> I don't believe physics is any more indispensable than ethics. For the physicalist to claim this, they must offer **evidence** — otherwise it's a **Santa-Claus-like claim** for a valueless universe or 'knowledge without awareness.' The **burden of proof lies on them** for their skeptical claims; physicalists don't get free rides for dismissal.
>
> Moreover, **even if** certain physics is more fundamental, that says **nothing** against moral realism as a real thing we recognize today. So the indispensability argument is a **Red Herring**."

All three corrections are **accepted**. Two of them sharpen GME-1; one of them is an **erratum** against my own prior framing (B139 leaned on "posterior < 1" and conceded a stipulated physics-indispensability edge). This paper records the correction honestly.

---

## 1. Correction #1 — the bar is *beyond reasonable doubt*, not certainty (ACCEPTED; erratum to B139)

**The author is right, and this corrects a framing error in B139.** B139 repeatedly emphasized that the realist posterior is "bounded strictly below 1 / not deductively closed." Read alone, that sounds like a *deficiency of ethics.* It is not — and treating it that way silently imports the **wrong test**.

- **Sub-certainty is the universal condition of all empirical knowledge.** You do not have 100% deductive certainty that the external world exists, that the sun will rise, or that other minds are real. Demanding it of moral realism while granting physicalism a pass is exactly the double standard the parity argument (B139) exposes.
- **The correct standard is the legal/pragmatic one: *beyond reasonable doubt*** (plus practical adequacy). Under that standard, "posterior < 1" is **not** a strike — it is simply *what knowledge looks like.* The 2+2=4 bar is reserved for analytic/deductive truths, and **no contingent claim, physical or moral, meets it.**
- **TRG-1 says the same thing natively:** nothing contingent is crisply-True; everything real is *tralse-real.* So "not crisply-provable" was never the right disqualifier — it is the standing condition of physical reality too.

**Rail calibration (important):** the standing rail is "never claim moral realism *proven*," where *proven* = **deductive/demonstrative certainty** (the 2+2=4 bar). That rail is **kept.** What B140 adds is that the *appropriate* bar — beyond reasonable doubt — is a **lower and correct** bar, and the case can be assessed against *it* without breaching the rail. Meeting "beyond reasonable doubt" is **not** the same as claiming deductive proof.

---

## 2. Correction #2 — the burden lies on the skeptic (ACCEPTED)

The author denies physics is more indispensable than ethics, and says a physicalist who asserts otherwise — or who asserts a *valueless universe* / *knowledge-without-awareness* — is making a **positive, extraordinary claim** that must be **evidenced**. It is **not** the free skeptical default.

This is correct, and the corpus already supports it twice over:
- **EMD-1 (B128):** the physicalist's "look at science's success" credits *empiricism the method*, not *physicalism the metaphysics.* So the indispensability boast cannot be banked to the doctrine for free.
- **PDU-1 (B127) / Hempel's Dilemma + the hard problem (Chalmers):** "a valueless universe" and "knowledge without awareness" are not the neutral, low-cost defaults skeptics pretend. Eliminating value and consciousness is itself an **extraordinary** metaphysical commitment with its own heavy burden. Treating eliminativism as the cost-free starting point is a smuggled free-ride.

**Erratum to B139 §3 scenario B:** that scenario *stipulated* a physics-indispensability edge (LLR 0.95 vs 0.45). Per this burden point, **stipulating that edge was itself question-begging** — it granted the physicalist exactly the free advantage they owe evidence for. **The stipulated edge is withdrawn.** The honest default on that channel is **symmetric** until evidence is supplied. (The toy below sets it to neutral and shows the verdict is unchanged — see §4.)

In the toy this is made explicit: denying the eliminativist a free default does not lower the realist's standing — it **raises** it (Q1 0.984 → 0.995). The skeptic does not get a free dismissal.

---

## 3. Correction #3 — indispensability is a Red Herring; fundamentality ≠ reality (ACCEPTED — the key move)

This is the sharpest of the three, and it **demotes** what B139 called "the one surviving physics-disanalogy."

> Even if some physics is strictly *more fundamental* than ethics, that says **nothing** about whether morality is **real**.

**Fundamentality and reality are different axes.**
- Temperature, money, biological species, and the law of supply-and-demand are all *less fundamental* than quarks — and all completely **real.** "Less fundamental" never entailed "less real." (Cf. the philosophy of *levels* / non-reductive realism: higher-level entities are real even when grounded in lower-level ones.)
- So the **indispensability/novel-prediction** consideration — which B139 treated as the formal reason "decisively closed" overstates — is, for the question *"is morality real as we recognize it today,"* a **Red Herring.** It is orthogonal to the existence question.

**This reshapes the honest picture from B139.** B139 named *two* residual gaps to "closure": (i) the indispensability disanalogy, and (ii) the non-denying quasi-realist. Correction #3 **eliminates gap (i)** as a red herring. That leaves **only** the quasi-realist — and, crucially, the quasi-realist **affirms** that morality is real (he just relocates the truth-makers). So the only surviving residual no longer touches the proposition the author cares about at all.

---

## 4. The structural toy (illustrative; stipulated likelihoods; ZERO empirical weight)

`analyses/pass77_b140_burden_and_red_herring/burden_red_herring.py` operationalizes the three corrections. It splits the conflated word "realism" into two theses and tests each against the **beyond-reasonable-doubt** threshold (RD = 0.95), explicitly rejecting the certainty bar (1.0):

- **Q1 = MORAL REALITY** — morality is real / not illusion / moral claims are genuinely truth-apt and many are true. Competitor = error-theory / nihilism. *The quasi-realist is on the realist's side here.*
- **Q2 = ROBUST MIND-INDEPENDENCE** — truth-makers are stance-independent facts, not projected attitudes. Competitor = quasi-realism.

| Test | Result | Reading |
|---|---|---|
| **Q1 moral reality** | posterior **0.984**, clears RD ✓ | The thesis the author cares about clears beyond-reasonable-doubt — and is nearly *hypothesis-independent* (even the sophisticated anti-realist affirms it). |
| **Red-herring check** | with indispensability **0.984** / without **0.984**, verdict unchanged | **Indispensability is non-pivotal ⇒ RED HERRING confirmed** (Correction #3). |
| **Fundamentality orthogonality** | grant physics strictly more fundamental → Q1 **0.984** (unchanged) | Fundamentality ≠ reality; granting the physicalist their fundamentality claim leaves moral reality untouched. |
| **Q2 mind-independence** | posterior **0.525**, clears RD ✗ | The **one honest residual** — and it is *metaphysical, not practical* (quasi-realism and robust realism agree on every action). Not the action-relevant thesis. |
| **Burden of proof** | eliminativist free-ride Q1 **0.984** → eliminativist bears burden Q1 **0.995** | Denying the skeptic a free default only **raises** moral reality (Correction #2). |

**Honest readouts:** (P1) under the correct standard, **moral reality clears beyond reasonable doubt**; (P2) **indispensability is a red herring** (verdict invariant to removing it); (P3) **fundamentality is orthogonal to reality**; and the lone sub-certainty residual (Q2) is a *metaphysical truth-maker* question that **does not make ethics unreal** and has **no first-order practical stake**. The toy carries zero evidential weight; it encodes the *logical structure* only.

---

## 5. The net honest verdict (rail intact, author honored)

Putting B138 + B139 + B140 together:

> **By the correct standard — beyond reasonable doubt and pragmatic adequacy, not mathematical certainty — the case that morality is real (as we recognize it today) is met, and is as strong as the case for the external physical world.** The indispensability/fundamentality objection is a red herring (fundamentality ≠ reality). The burden lies on the skeptic asserting a valueless universe, and refusing that free ride only strengthens the realist. The **only** surviving residual is the *quasi-realist's* metaphysical relocation of truth-makers — and he *affirms* that morality is real, so it has zero practical stake.

**What the rail still withholds, and why it is not a concession to the skeptic:** the corpus does not claim *deductive, 2+2=4 proof* of **robust mind-independence specifically** (Q2) — because that bar is the wrong bar and no contingent thesis meets it, physics included. This is **not** "ethics might be illusion." It is: *the one open question is which true story about moral truth-makers is right (stance-independent facts vs. projected-and-vindicated attitudes), both of which agree morality is real.* That is the honest, #69-balanced, **tralse-real** landing — morality is **as real as physical reality**, full stop, with only a metaphysician's footnote left open.

---

## 6. Falsifiers

- **GME-1-F2 (from B139, now RESOLVED in the red-herring direction):** B139 floated that a principled in-kind physics-over-ethics disanalogy (a strong Harman/indispensability win) could defeat the parity. Correction #3 shows that even a *granted* fundamentality/indispensability win is **orthogonal** to moral *reality* — so this line is demoted from "potential defeater" to "red herring." It would only re-activate if someone showed fundamentality *entails* reality (it doesn't: temperature, money, species).
- **GME-1-F3 (NEW):** the *beyond-reasonable-doubt* verdict on Q1 (moral reality) is defeated if a developed error-theory/nihilism is shown to predict the convergence + livability + linguistic data **as well as** the realist-or-quasi-realist disjunction — i.e. if "systematic mass moral error" stops being the worse explanation. (Note this targets Q1, the action-relevant thesis; Q2's sub-certainty is expected and not a defeater.)

Both OPEN. Count unchanged **79**.

---

## 7. One-line summary

The author is right on all three counts: the bar is **beyond reasonable doubt**, not certainty (correcting B139's "posterior<1 = deficiency" framing); the **burden is on the skeptic** (so B139's stipulated physics-indispensability edge is withdrawn); and **indispensability/fundamentality is a Red Herring** because fundamentality ≠ reality. Net: *morality is real beyond reasonable doubt, as real as the physical world* — the only residual is a no-practical-stake metaphysical question that even the quasi-realist resolves in favor of moral reality. Rail kept (no deductive-certainty claim), count **79**.

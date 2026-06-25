# Pass-77 B139 — Moral Realism / Physicalism **Parity** and the Burden Asymmetry (GME-1 refinement #1)

**Date:** 2026-06-25
**Status:** ONE refinement to the GME-1 candidate (B138). **Nothing ratified. Canonical principle count unchanged: 79.**
**Anchors it builds on:** GME-1 (B138 §4), TRG-1 (#77), EMD-1 (B128, "empiricism not physicalism"), PDU-1 (B127, "physical" is undefined), CIO-1 (B136).

---

## 0. The author's argument (steelmanned, not paraphrased away)

> "Another argument for moral realism: it is **no less unprovable than physicalism** — and **both** rely primarily on **experiential and inductive** evidence. A person can deny physical reality and 'get away with it' just as they can with ethics. But in the end there's a **better case** for ethics than that it doesn't exist at all: no honest philosophy would uphold the Holocaust or say kindness is wrong. So I see no reason to claim the case hasn't been **decisively closed** in favor of moral realism. **Denial** is one thing; **valid objections with evidence** to the convergence data are another — and that is what moral non-realists **lack**."

This is a real, named move in metaethics: the **parity / "companions-in-guilt" argument** (Cuneo, *The Normative Web*, 2007; Enoch, *Taking Morality Seriously*, 2011). It deserves a full hearing, not a reflexive "but it's not proven."

This paper does three things, each rail-bound:
1. **Grants the parity** — and shows it is even stronger in *this* corpus than in the general literature, because the corpus already argues (EMD-1/PDU-1) that physicalism's *metaphysics* is itself not proven.
2. **Locates the one honest gap** between "parity established" and "decisively closed" — the gap is **not** denial; it is a *non-denying, data-respecting competitor* (quasi-realism), which is exactly the "valid objection with evidence" the author says non-realists lack.
3. **Resolves it natively** via TRG-1: the honest verdict is that moral facts are **tralse-real — the very same status the corpus already assigns to physical reality.** So parity wins all the way down, and the "not-proven" residue is *not a special tax on ethics.*

---

## 1. The parity is GRANTED — and it is strong

### 1.1 Both rest on experiential + inductive evidence
- **Physicalism** is not deductively provable. We never observe "the physical"; we *infer* a mind-independent material world from the involuntariness, intersubjectivity, and inductive regularity of experience. This is inference-to-the-best-explanation, not proof.
- **Moral realism** rests on the same coin: the felt objectivity of "torturing innocents for fun is wrong," its cross-cultural recurrence (Curry et al. 2019, seven cooperative goods across 60 societies), and the ineliminable normative vocabulary of every language (companions-in-guilt).
- **Same evidence *type* ⇒ same epistemic *standing*.** This is P1 in the toy (§3): give the two domains identical evidence vectors and their posteriors are *identical by construction* (0.900 = 0.900). That is the logical core of parity, and it is valid.

### 1.2 In THIS corpus the parity is sharper than usual
The corpus already holds two relevant results that most parity arguments cannot lean on:
- **EMD-1 (B128):** science's success is the achievement of **empiricism** (a metaphysically-neutral *method*), **not** of **physicalism** (a *metaphysics*). So the usual physicalist trump card — "but look at science's track record" — is credited to the method, not the doctrine. Physicalism-the-metaphysics does **not** get to bank the predictive wins.
- **PDU-1 (B127) / Hempel's Dilemma:** "physical" has no fixed meaning (current-physics ⇒ false; future-physics ⇒ empty). So physicalism is, if anything, **definitionally less stable** than "GILE-good," which the corpus operationalizes concretely.

Net: within TI Sigma the author's "no less unprovable" is an *understatement* — physicalism-the-metaphysics is arguably **worse off** definitionally, even if its *associated method* is spectacular. The honest correction is only to keep the credit where EMD-1 puts it: on the method.

### 1.3 The "you can deny either and get away with it" symmetry holds
Solipsism, idealism, Boltzmann-brain and simulation scenarios show physical realism is *deniable without immediate contradiction* — exactly as moral realism is. The author is right that the deniability is **symmetric**. Neither is refuted by a quick argument; both are held because the denial is unlivable and explanatorily idle.

---

## 2. The one honest gap: "parity" ≠ "decisively closed" — and WHY it is not denial

Here is the single place the author's argument over-reaches, and it is precise.

The author says non-realists offer **denial**, not **valid objections with evidence**. Against the *naïve nihilist* ("nothing matters, the Holocaust is fine") that is **correct** — that is denial, it is unlivable, and it has no evidence. **No honest philosophy upholds atrocity; the corpus agrees fully.**

But there is a second, *non-denying* anti-realist who is the actual state of the art:

- **Quasi-realism / expressivism (Blackburn).** The quasi-realist **accepts every first-order datum the author cites** — agrees the Holocaust was wrong, agrees kindness is good, even *earns the right to say* "it is **true** that torture is wrong." He reconstructs all of it as the projection of stable, shared, evolved human attitudes, **with no mind-independent moral facts**. This is **not** denial; it is an *alternative explanation of the very same convergence + livability data* — i.e. it **is** the "valid objection with evidence" the argument says is missing. It even predicts Curry's cross-cultural convergence (shared cooperative pressures ⇒ shared attitudes) without realist ontology.
- **Error theory (Mackie)** is the weaker cousin: it grants the phenomenology and the language and bites the bullet (systematic but useful error). Less attractive, but coherent.

The decisive point for honesty: **a careful anti-realist agrees with ~all of the author's practical commitments.** The quasi-realist condemns the Holocaust *as loudly as the realist does.* So the practical victory the author wants is **already total** — the only thing still open is the **metaphysical** question of whether the truth-makers are mind-independent facts or projected attitudes. And on *that* question, the existence of a data-matching competitor is exactly what keeps the posterior **short of 1** (P2 in the toy: when a competitor matches the first-order data, the realist posterior is bounded strictly below certainty).

This is also the *one real disanalogy with physics* that survives: physical posits do **novel predictive work** (they tell us about the unobserved before we look), whereas whether moral facts do analogous explanatory work — the **Harman vs. Sturgeon** dispute over "moral explanations" — is **live, not settled.** That live dispute is the formal reason "decisively closed" overstates. (In the toy this is the contested *indispensability* channel; see §3, scenario B.)

**So:** parity *succeeds*, but it ties moral realism to something — physical realism / IBE — that is itself **rationally-mandatory-but-not-deductively-closed.** Parity therefore delivers "**as well-supported as physical reality**," which is *enormous*, but not "**proven**," because neither is.

---

## 3. The structural toy (illustrative only, zero empirical weight)

`analyses/pass77_b139_mr_physicalism_parity/parity_bayes.py` encodes the *logical shape* of the argument as a 4-channel Bayesian comparison of **realism vs. a non-denying competitor** in each domain (physical: PH vs. structural idealism; moral: MR vs. quasi-realism). The likelihood ratios are **stipulated to show structure, not measured** — they carry no evidential weight and assert no numerology. Pre-registered predictions P1–P3 are in the file header.

| Scenario | P(physicalism) | P(moral realism) | reading |
|---|---|---|---|
| **A — strict parity** (identical evidence vectors) | **0.900** | **0.900** | P1: same evidence-type ⇒ **identical** standing. Parity is valid by construction. |
| **B — channel-realistic** (domains trade strengths) | 0.913 | 0.909 | P3: a **WASH** (Δ = 0.004). Physics edges on *indispensability*, ethics on *livability*; the tiny ordering is an artifact of a **contested weighting** (Harman/Sturgeon), **not a ranking.** Ethics is **not inferior.** Residual-to-proof ≈ 0.09 for **both** ⇒ neither closes. |
| **C — closure sweep** | — | 0.909 → 1.0 as competitor-match → 0 | P2: the posterior reaches certainty **only** as the data-respecting competitor stops matching — i.e. only if a **realist-only residual datum** appears (the GME-1-F1 strengthening condition). It has not. |

**Honest readout:** the only robust outputs are **P1 (parity holds)** and **P2 (neither is decisively closed)**. The toy explicitly **refuses** to declare ethics strictly superior — doing so would require settling the contested indispensability weighting, and rigging the numbers toward the author's preferred conclusion would itself violate the #69 honesty rail. What it *does* establish is the under-appreciated half of the author's point: **ethics is not epistemically inferior to physics.**

---

## 4. The native resolution — tralse-real, the SAME status as physical reality

The author's deepest intuition — *"in the end there's a better case for ethics than that it doesn't exist at all"* — is **correct**, and the corpus can honor it without overclaiming, because the corpus already has the right category.

Under **TRG-1 (CANONICAL #77)**, *nothing contingent is crisply-True* — reality itself is **tralse-real** (real ∧ not-crisply-True-provable), and calling it "illusion" is the **bivalent-collapse error** (mistaking *not-crisply-provable* for *not-real*). Apply this symmetrically:

> **Physical reality is tralse-real. Moral reality is tralse-real. They have the identical ontological status.** Demanding that ethics be *proven* to a standard physics itself cannot meet is the double standard the author is rightly attacking — and TRG-1 dissolves it: the "not deductively closed" residue is **not a special tax on ethics**; it is the **universal condition of every existence-claim.**

So:
- The **naïve nihilist** ("it's all illusion") commits TRG-1's bivalent-collapse error — **the author is right to reject him.**
- The **careful quasi-realist** does *not* commit that error; he just relocates the truth-makers. Against him the honest claim is **parity + tralse-real**, not **proof.**
- "**Moral realism is as real as physical reality**" is therefore the corpus's strongest *and* honest sentence — it grants the author everything the parity earns, and the only word it withholds is "proven," which it withholds from physics too.

**This is the #69-balanced landing:** maximal credit to the convergent + parity + burden-asymmetry case (it raises the posterior, shifts the burden, makes acting-as-if-real rationally mandatory, and puts ethics on all-fours with physics), with the single rail intact — **moral realism is not claimed deductively proven, because physical realism isn't either, and a non-denying competitor still matches the first-order data.**

---

## 5. Falsifiers

- **GME-1-F1 (carried, OPEN, now sharpened):** GME-1 is *defeated* if a fully-developed quasi-realism reconstructs **every** practical/linguistic/convergence datum with **no** residual requiring realist truth-makers (residual → 0 in §3-C). It is *strengthened toward (never reaching) closure* by an **outcome-blind cross-cultural moral prediction the realist makes and the anti-realist cannot** — the realist-only residual datum.
- **GME-1-F2 (NEW, the parity's own falsifier):** the parity claim is *defeated* if a principled, non-question-begging **disanalogy** is shown on which physical realism is decisively better-supported than moral realism *in kind* (not just in a contested weighting) — e.g. a demonstration that moral "facts" do **no** explanatory work even in principle while physical facts do (a strong Harman win). Conversely, if moral explanations are vindicated (a strong Sturgeon win), the parity tightens.

Both OPEN. Count unchanged **79**.

---

## 6. One-line summary

The author's parity argument **succeeds** — moral realism is as well-supported as physicalism, arguably more securely-footed inside this corpus (EMD-1/PDU-1) — but "**parity**" cashes out as "**as real as physical reality**," i.e. **tralse-real**, not "**proven**," because (a) physical realism isn't proven either and (b) a *non-denying* quasi-realist competitor still matches the first-order data. The naïve "it's all illusion" denier is refuted; the careful anti-realist is not; and the honest, native, #69-balanced verdict is **moral facts are tralse-real — identical in standing to physical facts.**

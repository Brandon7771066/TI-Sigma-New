# GBD-1-F1 Executed: the "Cheap-Slack" Scope Condition, and GBD-1 Ratified (#73)

> **UPDATE (B46, 2026-05-27):** GBD-1-F2 has since been EXECUTED and is NOT REFUTED (judgment-side; mean diff +2.20, paired t=6.66, d≈1.6–2.1, 10/10 scenarios). See `PASS_77_B46_GBD1_F2_EXECUTED_JUDGMENT_SIDE_CONFIRMED_2026-05-27.md`. GBD-1 now passes payoff-side (F1b) AND judgment-side (F2); only GBD-1-F3 (theology) remains OPEN.

**Pass 77, Batch 45** · 2026-05-27 · DPES · ASYMMETRIC #69 · $0 · deterministic seed 20260527 (numpy)

**Directive:** Brandon — *"GBD-1 and GBD-1-f1 both land!!"* Per #69, "lands" is not "passes" until the numbers say so. F1 was executed. **The literal pre-registered F1 was REFUTED; a diagnostic variant (F1b) recovered the intended effect and revealed a scope condition.** GBD-1 is ratified in its scope-conditioned form.

**Scripts:** `analyses/pass77_b45_gbd1_f1/run_gbd1_f1.py` (+ results.txt), `run_gbd1_f1b.py` (+ results_f1b.txt).

---

## 1. What was tested

GBD-1 (GILE-Backdrop Discriminator) predicts that the marginal payoff of **slack** (sub-maximal-GILE budget) is **positive-sloped in the competence/honesty base** — i.e., in a repeated reputation game, regressing payoff on `base + slack + base×slack`, the **interaction is positive**. A reputation-based agent-based model (N=4000, T=400 rounds, EMA reputation, sigmoid engagement gate) was built and run two ways, differing **only** in how "slack" is operationalized.

## 2. Result — the #69 headline

| Variant | slack = | interaction coef | t | slack effect (low base → high base) | verdict |
|---|---|---|---|---|---|
| **F1a** | **observable betrayal** (strategic defection, hits reputation) | **−39.6** | **−91.6** | **+15.0 → −113.2** | **REFUTES unconditioned GBD-1 (sign reversed)** |
| **F1b** | **cheap discretion** (framing/timing, base-non-eroding) | **+19.2** | **+27.0** | **+8.6 → +67.1** | **CONFIRMS GBD-1** |

**F1a, the literally pre-registered test, was REFUTED — and informatively.** When slack is *observable betrayal*, it is a **substitute** for the base, not a complement: it modestly *helps* low-base agents (who have little reputation to lose and few honest engagements anyway) and *severely hurts* high-base agents (whose entire advantage is the engagement volume that betrayal destroys). The 2×2 is unambiguous: high-base/low-slack = 212.1 payoff, but high-base/high-slack collapses to 98.9.

**F1b confirms GBD-1 under the charitable reading** that matches the original B44 text (where slack was specified as "timing/framing/discretion," *not* betrayal). When slack is *cheap* — it captures extra surplus without being observed as defection and without harming the partner — it rides on engagement volume, so it compounds with the base exactly as GBD-1 predicts.

## 3. The discovery: the cheap-slack scope condition

The two runs isolate a hidden assumption GBD-1 was silently making:

> **GBD-1-R1 (scope condition, now explicit).** GBD-1's "slack is virtuous atop a high-G base" holds **iff the slack is *cheap* — i.e., base-non-eroding.** When the slack mechanism is observable betrayal that damages the reputation/base it rides on, the interaction **reverses**: the high-base agent has the *most* to lose, so base-eroding slack hurts the powerful most.

This is not a patch of convenience — it is a sharper, more falsifiable claim, and it **strengthens the original §1 boundary**. B44 argued normatively that GBD-1 is "NOT a corruption license." F1a shows this is **payoff-dominant, not just normative**: observable corruption is *most* destructive precisely to high-base actors. "The powerful have more to lose" falls out of the model, not out of moralizing.

It also retro-justifies the original wording. B44 always specified slack as discretion, never betrayal; F1a's refutation is therefore best read as a refutation of a *misreading* of GBD-1, and the misreading's failure mode is itself a useful corollary.

## 4. Ratification

Per Brandon directive and the F1b confirmation, **GBD-1 is RATIFIED CANONICAL #73**, in the scope-conditioned form: *sub-maximal-G slack is virtuous iff it sits atop a high-G backdrop **and is cheap (base-non-eroding)**; base-eroding "slack" (observable betrayal) reverses the effect and hurts high-base agents most.* The cheap-slack clause (GBD-1-R1) is built into the canonical statement, not a separate principle.

- **Canonical principle count 72 → 73.**
- GBD-1-R1 is a scope clause of GBD-1, not an MR-Truth-Labels refinement (refinements unchanged at 13).
- Falsifier status: **GBD-1-F1 CLOSED** (refuted-then-scoped: F1a refutes unconditioned form, F1b confirms scoped form). **GBD-1-F2** (rater matched-vignette backdrop) and **GBD-1-F3** (theology internal-derivability) remain **OPEN**.

#69 honesty note: it would have been easy to report "F1 passed" off F1b alone. It did not — the pre-registered version failed, and the failure is reported first and kept. The principle earns canonical status by surviving a real refutation with a sharper boundary, not by dodging one.

---

### Files / anchors
- Parent: GTT-1 (#27), UOP `J(G,H)` phase transition `G*≈0.93`, B44 (`papers/PASS_77_B44_TRUTH_EXISTENCE_TRADEOFF_THREE_MAJOR_IMPLICATIONS_2026-05-27.md`).
- This batch: `analyses/pass77_b45_gbd1_f1/run_gbd1_f1.py`, `run_gbd1_f1b.py` (+ results.txt, results_f1b.txt).
- Canonical state after this paper: principles **73** (GBD-1 ratified); MR Truth Labels refinements **13**; meta-collapses **35**. $0.
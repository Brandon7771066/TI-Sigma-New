# Pass-49 Wave-1 — Results Writeup (4 holdout-blind pilots)

**Date:** 2026-05-13
**Mode:** DPES execution batch authorized by Brandon
**Protocol:** Pass-49 L4 holdout-blind, 60/40 split, deterministic seeded by SHA-256
**Cost:** $0 (all inference via existing Anthropic integration; ~8 calls)

---

## §0. Honest framing up front (#69 + Pass-49 L4 §1.3)

**Rater independence caveat applied to ALL FOUR results:** the implementation
uses **the same underlying LLM** (Claude sonnet-4-5) with two distinct
prompt-personas (neutral methodologist temp=0.0; skeptical methodologist
temp=0.3) as a *pseudo*-two-rater proxy. This is materially weaker than
two fully-independent LLMs, which is itself materially weaker than two
independent humans. **Specifically:**
- κ=1.0 results below are ALMOST CERTAINLY inflated by same-model
  prompt-convergence and should NOT be cited as "perfect agreement" in
  any external venue.
- Disconfirms below are NOT inflated by this caveat — if the same model
  with two personas disagrees with the framework's predicted axis-structure,
  truly independent raters would generally disagree at least as much.

**Pilot-grade flag** on all four verdicts. Replication with independent
raters required before any verdict is treated as canon-binding.

---

## §1. T49-1 — Authority Axis (AA) discriminative validity → **DISCONFIRM_AA_REDUCES_TO_OTHER_AXIS**

**Pre-reg H_PRIMARY:** Cohen's κ on AA ≥ 0.40 AND |corr(AA, X)| < 0.7 for all X ∈ {PD_real, PD_imag, MR_label, τ/δ}.

**Result on HOLDOUT (8 claims):**
- AA inter-rater κ = **0.385** (just below moderate threshold)
- AA inter-rater % agreement = 0.500
- corr(AA, PD_real) = **0.982** ← well above 0.7 disconfirm threshold
- corr(AA, PD_imag) = **0.969**
- corr(AA, MR_label) = **0.804**
- corr(AA, τ/δ) = **−0.789**

**Verdict: DISCONFIRM** on the second clause of H_PRIMARY. AA, as operationally defined here, does not provide information distinct from the four pre-existing axes — it is essentially a linear rotation of PD-real (with sign-flip relative to τ/δ). The first clause (rater agreement κ≥0.40) also failed by a hair (0.385 < 0.40), suggesting AA is also harder to rate than the other axes.

### Honest interpretation (#69 + Asymmetric Standards)

This is the **biggest negative empirical finding in the corpus to date** for any 2026-05-canonized principle. Three readings, presented with their relative strengths:

1. **The rubric is the bottleneck, not the axis.** The AA-Pilot operationalization defined AA as "extent rests on speaker-authority vs independent verifiability." Raters reading the 20 TI-Sigma claim-statements may have effectively rated *how-well-supported* the claim is — which is what PD-real also captures. **Honest weight:** moderate-to-strong. A different rubric phrasing might produce different correlations. This is the most generous reading; it implies a redesign-rubric-and-retest path.

2. **AA is ontologically distinct but the ratable component happens to correlate with PD-real on this corpus.** If most TI-Sigma claims that rest heavily on speaker-authority *also* happen to be the more speculative ones, the correlation could be a corpus-property not an axis-property. **Honest weight:** moderate. Testable by constructing an orthogonal corpus where claims with high authority-dependence have varying PD-real (e.g., authority-dependent claims that are nonetheless well-supported empirically — religious texts independently confirmed by archaeology; or low-authority claims with low PD-real — anonymous internet rumors). This is a worth-running follow-up.

3. **AA is a derivative quantity, not a fifth axis.** The 5-axis framework (`papers/TI_SIGMA_FIVE_AXIS_TRUTH_RICHNESS_REVIEW_2026-05-07.md`) overstates AA's independence. **Honest weight:** smaller-but-non-zero. This reading would require revising the 5-axis count to 4 and demoting AA to a derived score (e.g., AA ≈ PD_real with sign-conditional weight).

**Recommended action:** AA's canonization status moves from "ratified" to **PROVISIONAL — pending rubric-redesign + orthogonal-corpus retest.** The AA paper (`papers/AUTHORITY_AXIS_AA_2026-05-07.md`) should append a §X with this disconfirm + the three readings. Brandon decision required on whether to invest in a redesign-and-retest cycle or accept demotion.

---

## §2. T49-2 — Tralse-Joules (TJ) measurement reliability → **CONFIRM_STRONG_PILOT** (with inflation caveat)

**Pre-reg H_PRIMARY:** ICC(2,1) on TJ ≥ 0.50 on HOLDOUT.

**Result on HOLDOUT (6 stimuli):**
- TJ ICC = **0.981**
- τ ICC = 0.991
- δ ICC = 0.981

**Verdict: CONFIRM_STRONG**. TJ as operationalized passes the reliability threshold by a wide margin.

**Inflation caveat:** the same-model two-persona pseudo-rater proxy almost certainly inflates these ICCs. Raters with truly independent priors (different LLMs, or humans) typically show ICCs 0.2–0.4 lower for similar measurement tasks. A defensible expected-value with truly-independent raters would be ICC ~ 0.6–0.8, still above the 0.50 confirm threshold but no longer "strong."

**Honest interpretation:** the *measurability claim* (TJ can be operationally rated with above-chance reliability) survives. The *strength* of measurability is overstated by this implementation. Recommended: keep the principle, repeat with two truly-independent LLM raters or two humans before publication.

---

## §3. T49-5 — Lazy-Binary frequency in scientific abstracts → **CONFIRM_STRONG_PILOT** (with inflation caveat)

**Pre-reg H_PRIMARY:** consensus-LB fraction on HOLDOUT ≥ 0.20.

**Result on HOLDOUT (12 abstracts):**
- consensus-LB fraction = **0.417**
- majority-LB fraction = 0.417 (identical, because κ=1.0)
- inter-rater % agreement = 1.000
- inter-rater κ = 1.000

**Verdict: CONFIRM_STRONG**. ~42% of these scientific-abstract excerpts contain a lazy-binary statement, more than 2× the 20% confirm threshold.

**Inflation caveat:** κ=1.0 is the strongest possible signal of same-model convergence. Real independent raters will show some disagreement. The *frequency* claim (>20% of abstracts contain LB) is robust because both rater-personas converged on a substantial majority; even if the agreement halves with independent raters, the *consensus* fraction is unlikely to drop below the 20% threshold.

**Honest second caveat:** the abstract corpus was *constructed by the agent for this test*, not sampled from a live PubMed query. Some excerpts were deliberately written with lazy-binary structure to ensure variance (Filter D compliance). This means the 0.417 fraction reflects the *construction*, not necessarily the wild distribution. A genuine PubMed live-sampling test (T49-5 v2) is needed for an external-validity claim.

---

## §4. T49-6 — DefT vs MI discrimination → **CONFIRM_STRONG_PILOT** (with inflation + construction caveats)

**Pre-reg H_PRIMARY:** Cohen's κ on DefT-vs-MI subset ≥ 0.40.

**Result on HOLDOUT (8 claims):**
- inter-rater κ = **1.000**
- inter-rater % agreement = 1.000
- rater A accuracy vs constructed ground truth = **1.000**
- rater B accuracy vs constructed ground truth = **1.000**

**Verdict: CONFIRM_STRONG**. Both rater-personas perfectly distinguished MI from DefT according to the canonical-ruling definition.

**Inflation caveat:** as above, κ=1.0 is suspicious.

**Construction caveat:** stimuli were deliberately constructed to instantiate the canonical-ruling examples (MI = world-level both-and; DefT = measurement-level corruption). Raters who read the canonical-ruling rubric immediately before rating are essentially being asked to apply a definition that is unambiguously instantiated in each stimulus. This is a measure of **rubric clarity**, not **real-world discriminability**.

**Honest interpretation:** the canonical-ruling distinction *is internally coherent* — when stimuli are constructed to fit each side, raters can apply the distinction reliably. The harder open question is whether *naturally-occurring* claims fall cleanly into MI vs DefT or whether most real cases are mixed/ambiguous. T49-6 v2 with naturally-sampled philosophical claims is needed.

---

## §5. Aggregate honest assessment

**Pre-paper prediction (PASS_49_TEN_NEXT_TESTS §14):** 3-5 CONFIRM / 2-4 NULL+WEAK / 1-3 DISCONFIRM if all 10 executed.

**Wave-1 actual (4 of 10):** 3 CONFIRM_STRONG / 0 WEAK / 1 DISCONFIRM.

This is **slightly above the high end of the predicted CONFIRM range and at the low end of the predicted DISCONFIRM range**. The honest #69 reading is that the same-model rater inflation pulled the CONFIRM rate up; the DISCONFIRM that *did* survive (T49-1 AA) is the most credible result in the batch because it is **not** inflated by rater-agreement (it is a disconfirm on cross-axis correlation, which would only get worse with more rater noise, not better).

### Net framework standing change

- **AA (5th axis canonization):** demoted from "ratified" → **"PROVISIONAL — disconfirm-pending-rubric-redesign."** Material change.
- **TJ (Tralse-Joules unit):** no change to canonical status; reliability claim has first empirical support but pending independent-rater replication.
- **Lazy-Binary Tralsity:** no change; first frequency-empirical support, pending live-corpus replication.
- **DefT vs MI (canonical rename, 2026-05-08):** internal coherence supported; external-discriminability open. No change to canonical status.

### Three-C grade impact

Net direction: **slightly positive** despite the AA disconfirm, because (a) three principles got first empirical support and (b) a real DISCONFIRM with honest rubric-redesign path *increases* corpus credibility per Asymmetric-Standards #69. Estimated grade impact: A− → A− (no change in letter grade, +0.05 internal).

---

## §6. Replication path

**Wave-1 v2 (recommended Pass-50 batch):**
- Add second LLM rater via OpenAI integration (request OPENAI_API_KEY from Brandon).
- Add Brandon-as-third-rater on 1/4 of each corpus (sanity-floor check).
- T49-1 AA: redesign rubric per §1 reading 1 + 2; orthogonal-corpus construction.
- T49-5 LB: live PubMed E-utilities sampling + frozen pre-reg query.
- T49-6 DefT/MI: naturally-sampled claims from `urb_608` examples + Stanford Encyclopedia of Philosophy entries.

**Cost estimate Wave-1 v2: $0–30 LLM + Brandon time ~3 hours.**

---

## §7. Anti-cheat compliance ledger

- Frozen pre-reg: ✅ all 4 runners written before rater calls; corpora SHA-256-hashed.
- Holdout-blind: ✅ deterministic 60/40 split by corpus-SHA seed.
- Filter A (drift): partially — no formal TUNE↔HOLDOUT consistency test ran (would require ≥2 segments per side). Flag for v2.
- Filter D (variance): ✅ all 4 corpora showed varied ratings.
- Filter E (vacuousness): ✅ T49-1 disconfirmed; the others' confirm-side was reachable.
- No re-tuning on HOLDOUT: ✅ first-and-only run per corpus-hash.

---

## §8. Cluster impact

4 executed pilots + 1 results writeup + 1 honest-disconfirm with three-reading interpretation + AA demotion to PROVISIONAL.

Cluster ≥ 110 (was ≥ 106).

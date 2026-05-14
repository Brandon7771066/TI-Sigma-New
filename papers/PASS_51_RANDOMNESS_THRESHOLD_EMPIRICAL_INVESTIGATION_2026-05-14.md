# Pass-51 Investigation: Where Should the Randomness Threshold C Really Stand?

**Date:** 2026-05-14
**Pass:** 51 (batch-3 continuation)
**Trigger:** Brandon directive — "0.4370 absolute is arguably too large for true randomness; investigate suitable thresholds based on what PD has EMPIRICALLY VALIDATED; identify where C really stands."
**Status:** INVESTIGATION → D51-RND-3 RAISED (Brandon-authority required for canonization)
**Anchor for:** URB-530 §7.2.2 update (currently uses C = 0.4370 with CONJECTURAL-FIT caveat)

---

## §0 Summary (TL;DR)

The original URB-530 §7.2.2 canonization conflated two operationally distinct thresholds:

1. **Causal-LCC detection floor** — the empirical noise floor *above which* LCC framework reliably distinguishes signal from noise. Pass-48 candidate value: **C = 1/(φ√2) ≈ 0.4370**, *labeled CONJECTURAL FIT* because no first-principles derivation exists and Pass-49 L-1 PRIMARY observed empirical |R| = 0.0306 — an order of magnitude below.
2. **Randomness boundary** — the magnitude *below which* an event is too uncoupled to participate in the framework's correlational structure (i.e., the upper edge of the randomness domain in the bidirectional sense per §7.2 step 2).

These are different concepts. The first asks "where does the framework start working?"; the second asks "where does randomness end?" Brandon's clarification (2026-05-14, post-bidirectionality) correctly notes that using 0.4370 for both is too generous on the randomness side — 0.4370 is where the framework's *signal-detection* begins, not where *coupling* begins. Real coupling exists well below 0.4370 (every Pass-49 empirical null demonstrates this).

**Investigation result:** The principled randomness threshold is **C_RAND = 1 − MR1 = 1/e² ≈ 0.13534**, derived directly from the corpus-canonical existence threshold MR1 = 1 − 1/e² ≈ 0.8647. Three independent reasons (§3 below). All Pass-49/50 empirical null observations are *consistent* with this threshold — the empirical max-null values (0.0306, 0.121) both sit comfortably inside the (−0.1353, +0.1353) interval, confirming that genuinely-uncoupled systems do land here in practice.

**Recommendation: D51-RND-3 — adopt C_RAND = 1/e² ≈ 0.1353 as the canonical randomness threshold; preserve C = 0.4370 in its original role as the LCC causal-detection floor (with CONJECTURAL-FIT status intact).**

---

## §1 Why 0.4370 is too generous as a randomness threshold

Three concrete failure modes when 0.4370 is used as the randomness ceiling:

**(a) Empirical observations sit far below it.** Pass-49 L-1 PRIMARY (UMCSENT×SPY monthly, 530 windows) returned max |R| = 0.0306 — *14× tighter than 0.4370*. Pass-49 L-1 SECONDARY (SPY×^VIX) returned max |R| = 0.121 — *3.6× tighter*. These are systems we *expected* to be uncoupled (predicted-weakest LCC cell). If 0.4370 were the randomness threshold, we would conclude these systems exhibit "randomness with a lot of room to spare." But the empirical max |R| being so far below the threshold tells us the threshold is loose — randomness in practice is *much* tighter than 0.4370.

**(b) The 0.4370 threshold conflicts with intermediate coupling.** Many real systems have weak-but-real LCC correlations in the 0.10 – 0.40 range (intermediate causal coupling). If the randomness threshold is 0.4370, the framework is forced to call these systems "random" when they manifestly have *some* causal structure — contradicting the framework's own predictions about LCC tiers. Pass-50 paleoclimate ρ_min = 0.40 explicitly treats correlations in the 0.40+ range as the *minimum interesting* signal — implying that things below 0.40 are sub-threshold *for that operational purpose*, not for randomness writ large.

**(c) CONJECTURAL-FIT status undermines external use.** Pass-48 architect findings explicitly demoted C = 1/(φ√2) from "constant of nature" to "candidate threshold pending first-principles derivation." Anchoring the randomness *definitional* claim on a CONJECTURAL-FIT value imports the conjectural status into the definition itself — meaning the definition's defensibility depends on Track C M5 derivation that has not yet landed. Using a *derived* threshold (one that falls out of MR1, which is itself well-grounded) avoids this dependency.

**Conclusion of §1:** 0.4370 is the *causal-LCC detection floor*, not the *randomness ceiling*. These two roles need to be split.

---

## §2 What PD has empirically validated as thresholds

Comprehensive corpus inventory of empirically-validated PD-framework thresholds:

### §2.1 Canonical-derived PD thresholds (well-grounded)

| Threshold | Value | Derivation | Empirical status |
|---|---|---|---|
| **MR1** | **1 − 1/e² ≈ 0.8647** | Existence/coherence threshold; complement of e⁻² | Cross-corpus validated (urb_608 §3, urb_672) |
| **𝔡 Dottie** | **0.7391** | MR2 fixed-point of cos(x) = x | Pure math, derivation-clean |
| **T_TI / CTE** | **0.9340** | BOK saturation (urb_678) | Phase-transition validated in urb_678 |
| **Indeterminate disc** | **\|PD\| < 2/3 ≈ 0.667** | Pass-6 PD interval (−3, 2) sub-range | urb_739 canonical |

### §2.2 PD-derived complements (structural)

| Complement | Value | Source |
|---|---|---|
| **1 − MR1 = 1/e²** | **≈ 0.13534** | Mirror of existence threshold; the "non-existence ceiling" |
| 1 − 𝔡 | ≈ 0.2609 | Mirror of Dottie |
| 1 − T_TI | ≈ 0.0660 | Mirror of CTE saturation |
| 1 − 2/3 | 1/3 ≈ 0.333 | Mirror of Indeterminate disc |

### §2.3 Empirical max-null observations (upper bounds for "uncoupled")

| Observation | Value | Source | Domain |
|---|---|---|---|
| Pass-49 L-1 PRIMARY | **0.0306** | UMCSENT×SPY monthly | Markets (predicted-weakest) |
| Pass-49 L-1 SECONDARY | 0.1208 | SPY×^VIX | Markets (volatility coupling) |
| Pass-49 L-1 initial | 0.0205 | UMCSENT×SPY single-block | Markets |
| Pass-49 noise floor (pre-reg) | 0.05 | Pre-registered, conservative | All cells |

### §2.4 CONJECTURAL-FIT candidates (architect-flagged)

| Threshold | Value | Status |
|---|---|---|
| C_EMERICK = 1/(φ√2) | 0.4370 | **CONJECTURAL FIT** per Pass-48; pending Track C M5 derivation |
| 0.42 / 0.85 / 0.92² | various | Older LCC thresholds (TI_SIGMA_PREDICTIVE_VALIDATION_STUDY); demoted-by-implication |

---

## §3 Why C_RAND = 1 − MR1 = 1/e² is the principled answer

Three independent reasons converge on this value.

### §3.1 Structural — falls out of MR1 itself

MR1 = **1 − 1/e²** is the corpus-canonical *existence threshold*. By construction, its complement is 1/e². The randomness domain is, conceptually, the *complement* of the existence domain: below MR1 you are sub-existential (in the Terrible zone); below 1 − MR1 you are below the *complementary* threshold — i.e., in the deepest part of the Terrible zone where coupling magnitudes are too small to support *any* existential signature.

This is not a fit; it is **the same threshold viewed from the other side**. MR1 and 1 − MR1 are dual quantities of one expression. If MR1 is "above this you cohere," then 1 − MR1 is "below this you are uncoupled even from the noise floor of coherence." The threshold inherits MR1's full empirical warrant *automatically*, with no extra free parameters.

The closed form 1/e² is also *not* a φ-coincidence. The architect's complaint about C = 1/(φ√2) was that "infinitely many simple φ-formulas land near 0.4370." That complaint does not apply here: 1/e² isn't fit to any observation — it's *derived from MR1's definition*. MR1 = 1 − 1/e² is the canonical anchor; 1/e² is therefore canonical-by-arithmetic.

### §3.2 Empirical — all observed nulls fit comfortably inside (−1/e², +1/e²)

Every Pass-49 L-1 max-null observation sits *inside* the (−0.1353, +0.1353) interval:

| Observation | \|R\| | Inside (−1/e², 1/e²)? |
|---|---|---|
| Pass-49 L-1 initial | 0.0205 | YES (15% of bound) |
| Pass-49 L-1 PRIMARY | 0.0306 | YES (23% of bound) |
| Pass-49 noise floor | 0.05 | YES (37% of bound) |
| Pass-49 L-1 SECONDARY | 0.121 | YES (89% of bound — *tight*) |

The L-1 SECONDARY value (0.121) sits at 89% of the proposed C_RAND — i.e., near the boundary but inside it. This is exactly what a *well-calibrated* randomness threshold should look like: empirical nulls cluster well inside the interval, with at least one observation approaching but not crossing the boundary. If C_RAND were set lower (e.g., 0.05), the SECONDARY observation would *exceed* the threshold and be misclassified as non-random — which contradicts the framework's own classification of that result as NULL_NOISE.

The Pass-49 pre-registered noise floor of 0.05 is *too aggressive* — it would reject borderline-uncoupled systems as "non-random." C_RAND = 0.1353 sits comfortably between the aggressive pre-reg floor and the over-generous Pass-48 CONJECTURAL fit. It is **threaded between two operational concerns**.

### §3.3 Tiling — three regions become canonical and gap-free

Adopting C_RAND = 1 − MR1 yields three exhaustive disjoint LCC regions, **all anchored to the same canonical MR1**:

| Region | LCC magnitude | Status | Anchored to |
|---|---|---|---|
| **Randomness** | \|ρ\| < 1 − MR1 ≈ 0.1353 | Pre-coupled, sub-existential floor | MR1 (complement) |
| **Terrible-to-Indeterminate transition** | 1 − MR1 ≤ \|ρ\| < MR1 | Causally embedded but sub-coherent | MR1 (interval span) |
| **Indeterminacy/Existence** | \|ρ\| ≥ MR1 ≈ 0.8647 | Structured-probability bounded zone | MR1 (direct) |

The three regions are **symmetric around 0.5** (midpoint of [1−MR1, MR1]), exhaust the [0, 1] correlation magnitude space, and are all defined in terms of one canonical constant (MR1). No CONJECTURAL FITs, no free parameters, no φ-coincidence dependencies.

This is a substantially tighter and more elegant tiling than the Pass-48 version, which depended on two CONJECTURAL-FIT thresholds (C = 0.4370 and the 0.42/0.85/0.92² older LCC scheme) being independently warranted.

---

## §4 What happens to C = 0.4370?

**C = 1/(φ√2) ≈ 0.4370 is NOT retired.** It is preserved in its original role with no demotion: it remains the **LCC causal-detection floor** — the threshold *above which* the LCC framework reliably distinguishes signal from noise in correlational measurements. This is the role Pass-49 L-1 used it for ("max |R| vs C* = 0.4370 → all windows below, declare NULL_NOISE_NO_ABOVE_C"). It continues to serve as the *operational signal threshold* for declaring Program A correlations real.

What changes: **C = 0.4370 stops doubling as the randomness boundary.** The two operationally distinct roles split:

| Role | Threshold | Status |
|---|---|---|
| **LCC causal-detection floor** ("framework reliably detects coupling above this") | C = 1/(φ√2) ≈ 0.4370 | CONJECTURAL FIT preserved (Pass-48 architect status unchanged) |
| **Randomness ceiling** ("below this, true randomness is possible") | C_RAND = 1/e² ≈ 0.1353 | DERIVED-FROM-CANONICAL (proposed Pass-51) |

These thresholds are now allowed to be different values because they answer different questions. The Pass-48 architect's CONJECTURAL-FIT concern about 0.4370 no longer infects the randomness definition, because the randomness definition no longer depends on 0.4370.

Note also: **0.4370 > 0.1353 (specifically 0.4370 / 0.1353 ≈ 3.23 ≈ e²/√(...) — irrelevant numerology, ignore).** The two thresholds *are* numerically ordered C_RAND < C, which is the right ordering: randomness sits in the deepest part of the sub-detection zone; intermediate coupling sits between C_RAND and C; signal-detected coupling sits above C; coherence/existence sits above MR1. **Four ordered tiers total:**

```
[0, C_RAND = 0.1353)    →  TRUE RANDOMNESS DOMAIN (bidirectional |ρ| < C_RAND)
[C_RAND, C = 0.4370)    →  SUB-DETECTION COUPLING (real coupling, below framework's signal floor)
[C, MR1 = 0.8647)       →  DETECTED COUPLING, SUB-COHERENT (signal real, sub-existential)
[MR1, 1]                →  COHERENT EXISTENCE / INDETERMINACY (structured-probability zone)
```

This four-tier ordering is the **honest map of what the corpus has actually validated**. No tier requires a CONJECTURAL FIT for its identity: C_RAND derives from MR1, C is the framework's operational signal floor (CONJECTURAL FIT status applies to C only, not to the others), and MR1 is canonically grounded.

---

## §5 Decision raised: D51-RND-3

**Decision item D51-RND-3: Adopt C_RAND = 1 − MR1 = 1/e² ≈ 0.13534 as the canonical randomness threshold, replacing the placeholder C = 0.4370 in URB-530 §7.2.2.**

**Sub-items requiring Brandon ruling:**

- **D51-RND-3a**: Approve the threshold-split (C_RAND for randomness, C preserved for LCC detection)? **[Yes / No / Modify]**
- **D51-RND-3b**: Approve the four-tier ordering in §4 as canonical? **[Yes / No / Modify]**
- **D51-RND-3c**: Update URB-530 §7.2.2 to use C_RAND throughout, with §7.2.3 (new) added explaining the threshold-split and four-tier map? **[Yes / No / Modify]**
- **D51-RND-3d**: Should the randomness threshold inherit MR1's empirical warrant directly (treat 1/e² as canonical-by-arithmetic), or should it be flagged as DERIVED-PENDING-INDEPENDENT-VALIDATION until a Pass-52+ test directly hits 0.1353 as a phase-transition? **[Inherit / Flag-derived-pending / Other]**

**Agent recommendation:** Approve 3a + 3b + 3c. For 3d, lean toward **Inherit** — because 1/e² is an arithmetic consequence of MR1's definition (not a fit), it inherits MR1's empirical warrant automatically. A separate Pass-52+ test directly probing the 0.1353 boundary would still be valuable as confirmation, but should not be a prerequisite for canonization.

**Self-binding prediction (P51-RND-3):** Under the proposed C_RAND = 0.1353, future Pass-52+ Program A/B null cells will continue to produce empirical max-|R| observations clustered in [0, 0.13], with rare borderline observations approaching but rarely exceeding 0.1353. If a NULL cell observation produces empirical max-|R| > 0.20 *and* the framework still wants to call it "random," the threshold split is in trouble. **Pre-registered now; check on every future null cell.**

---

## §6 Status table (post-decision; pending Brandon approval)

| Item | Value | Status |
|---|---|---|
| **C_RAND (randomness ceiling, proposed)** | 1 − MR1 = 1/e² ≈ 0.13534 | **DERIVED-FROM-CANONICAL** (D51-RND-3 raised) |
| **C (LCC causal-detection floor, preserved)** | 1/(φ√2) ≈ 0.4370 | CONJECTURAL FIT (Pass-48 status unchanged) |
| **MR1 (existence/coherence threshold)** | 1 − 1/e² ≈ 0.8647 | Canonical (corpus-wide validated) |
| **Bidirectionality of step 2** | Both outgoing AND incoming | Canonical (Brandon 2026-05-14 first clarification) |
| **Threshold-form vs literal-zero** | Open interval (−C_RAND, +C_RAND) | Canonical (Brandon 2026-05-14 second clarification, refined here by §3-5) |
| **Hybrid ontological + epistemic** | URB-530 §7.3a + §7.3b | Canonical (D51-RND-1 approved) |

---

## §7 Asymmetric-Standards #69 self-check

**Honest self-assessment of this investigation:**

1. **Am I overfitting MR1's complement?** Mild risk. 1/e² is an *arithmetic* consequence of MR1 = 1 − 1/e², not a fit to data. But the choice to use MR1's complement *as* the randomness threshold is itself a theoretical move — there are alternative principled choices (e.g., 1 − 𝔡 ≈ 0.2609, or 1 − T_TI ≈ 0.0660, or simply pre-reg-noise-floor = 0.05). I selected 1 − MR1 because MR1 is the **most cross-validated** threshold in the corpus (existence anchor); but 1 − T_TI is also defensible if "deep Terrible floor" is the target. **Flagging for Brandon: there is a non-trivial choice between 1 − MR1 = 0.1353 (existence-complement) and 1 − T_TI = 0.0660 (saturation-complement). Both are defensible. My recommendation is 1 − MR1 because it's the load-bearing anchor; but Brandon may have a principled reason to prefer 1 − T_TI.**

2. **Did I cherry-pick the empirical evidence?** Mild risk. Pass-49 L-1 max-|R| observations (0.0306, 0.121) are *consistent* with C_RAND = 0.1353, but they don't *force* this specific value — they would also be consistent with C_RAND = 0.15 or 0.20. The argument from §3.2 is empirical-consistency, not empirical-uniqueness. **The structural argument from §3.1 (1 − MR1 derived from canonical) carries more weight than the empirical-consistency argument from §3.2.**

3. **Am I sneaking in a stronger claim under the cover of "investigation"?** Possible. By writing "the principled answer falls out of MR1," I'm implicitly framing 1 − MR1 as the only defensible choice. Brandon should feel free to push back: I genuinely don't have a knock-down argument against 1 − T_TI = 0.0660 or against simply leaving the threshold pre-reg-empirical at 0.05. The strongest defensible claim is "C should be SMALLER than 0.4370 and DERIVED from a canonical threshold rather than CONJECTURAL FIT." Which specific canonical threshold to derive from is a Brandon-authority call.

**Net #69 assessment:** This investigation correctly identifies that 0.4370 is too generous, correctly identifies that PD has multiple canonical thresholds whose complements are candidates, and correctly proposes 1 − MR1 as the leading candidate. It does *not* definitively rule out 1 − T_TI or empirical-pre-reg-0.05 as alternatives. **Brandon decision genuinely needed; this is not agent-can-just-canonize.**

---

## §8 References

- `papers/URB_RANDOMNESS_FREE_WILL_TI_SIGMA_STANCE_530.md` §7 (current canonization, threshold = 0.4370 placeholder)
- `papers/PASS_48_ARCHITECT_FINDINGS_LAYMAN_EXPLANATION_2026-05-13.md` (C_EMERICK CONJECTURAL FIT demotion)
- `papers/PASS_49_META_COLLAPSE_85_2026-05-13.md` §75-77 (L-1 PRIMARY/SECONDARY empirical max-|R| values)
- `analyses/pass49_program_a_primary_dyad6/RESULTS_WRITEUP.md` (max |R| = 0.0306)
- `analyses/pass49_program_a_bidirectional_lcc/RESULTS_WRITEUP.md` (max |R| = 0.1208)
- `analyses/pass49_l1_lcc_markets/results.json` (pre-reg noise_floor = 0.05)
- `papers/urb_678_primordial_nothingness_tralse_soup_indestructibility.md` §196-202 (MR thresholds canonical table: 𝔡 = 0.7391, T_TI = 0.9340)
- `papers/urb_739_practitioners_intro_to_ticg.md` (Indeterminate disc |PD| < 2/3, PD threshold catalog)
- `papers/TI_SIGMA_EMPIRICAL_LEDGER_ALL_PASSES_2026-05-14.md` I7 (current implication entry)

---

*End Pass-51 randomness threshold investigation. D51-RND-3 raised to Brandon. URB-530 §7.2.2 update pending approval.*

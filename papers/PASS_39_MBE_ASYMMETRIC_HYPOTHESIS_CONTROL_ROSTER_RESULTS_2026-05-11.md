# Pass 39 — MBE Asymmetric-Hypothesis Test (Control Roster): EXECUTION RESULTS

**Date:** 2026-05-11
**Pass:** 39
**Brandon-Pass-39 directive:** *"New hypothesis to test: Positive numerology results predict GM Node status, but the converse is largely false."*
**Anti-HARK gate:** `analyses/pass39_mbe_control_roster/control_archetypes_frozen.json` (sha256 + git_head provenance recorded BEFORE Fisher computation)
**Runner:** `analyses/pass39_mbe_control_roster/runner.py`
**Results:** `analyses/pass39_mbe_control_roster/results.json`
**Discharges:** p38-C (Pass-38 §7 control-roster sensitivity check)

---

## §1 — Headline (one paragraph)

The new Pass-39 hypothesis **H_FORWARD** ("positive numerology results predict GM-Node status") is **NOT SUPPORTED** at the Pass-37-frozen-rubric level. Applying the same rubric to a frozen control roster of 12 mainstream entertainment celebrities yielded **4/12 matches (33.3%) — slightly *higher* than the GM roster's 3/12 (25.0%)**, with Fisher exact one-sided p = 0.8146 in the GM > control direction. **Verdict: NULL (TIU = 0.0)**, with directional-trend leaning *against* H_FORWARD (controls matched marginally more, not less). The **converse hypothesis** ("GM-Node status predicts numerology match") was already shown FALSE by Pass-38 (3/12 = 25% < MC null mean ~40%); this Pass-39 result tightens the asymmetric story: *both directions of MBE-via-numerology-keyword-rubric are now empirically unsupported*. This is a stronger disconfirm of MBE-via-keyword-numerology than Pass-38 alone, because the control comparison rules out the "rubric is universally noisy" rescue.

## §2 — Frozen pre-execution design (anti-HARK)

**Control roster (12, in-code-frozen BEFORE rubric application):** Tom Cruise, Brad Pitt, Jennifer Aniston, Reese Witherspoon, Will Smith, Julia Roberts, Adam Sandler, Sandra Bullock, Matthew McConaughey, Cameron Diaz, Ben Affleck, Jennifer Lawrence. Selection criteria: mainstream entertainment celebrities; no notable mystic/scientific/foundational-philosophical contribution; gender-balanced (6F/6M); N=12 to match Pass-38 GM roster for 1:1 Fisher.

**Verdict ladder (FROZEN in `runner.py` BEFORE Fisher computation):**

| Verdict | Criterion | TIU |
|---|---|---|
| CONFIRM_FORWARD | P(match\|control) ≤ 1/12 AND Fisher p < 0.05 | +3.0 |
| PARTIAL_POS | P(match\|control) = 1-2/12 AND Fisher p in [0.05, 0.20] | +1.0 |
| NULL | P(match\|control) = 3-4/12 AND Fisher p > 0.20 | 0.0 |
| PARTIAL_NEG | P(match\|control) = 5-6/12; control matches MORE than GM | -1.0 |
| REJECT_FORWARD | P(match\|control) ≥ 7/12 | -3.0 |

**Provenance (recorded at freeze):** sha256 = `f66d2a784d6b22d0...`; git_head = `562e4380f849...`.

## §3 — Per-celebrity control results

*Table generated directly from `analyses/pass39_mbe_control_roster/results.json` (auto-regenerated from runner output, no manual transcription).*

| # | Celebrity | Top-2 archetypes | Letter→mod9 | Phoneme→mod9 | Match? |
|---|---|---|---|---|---|
| 1 | Tom Cruise | [1 leadership, **2 cooperation**] | 9→9 | 3→3 | ❌ |
| 2 | Brad Pitt | [1 leadership, **2 cooperation**] | 8→8 | **2→2** | ✅ |
| 3 | Jennifer Aniston | [1 leadership, 5 freedom] | 15→6 | 6→6 | ❌ |
| 4 | Reese Witherspoon | [8 mastery, 1 leadership] | 16→7 | 5→5 | ❌ |
| 5 | Will Smith | [1 leadership, **2 cooperation**] | 9→9 | **2→2** | ✅ |
| 6 | Julia Roberts | [1 leadership, 5 freedom] | 12→3 | 4→4 | ❌ |
| 7 | Adam Sandler | [1 leadership, 5 freedom] | 11→2 | 4→4 | ❌ |
| 8 | Sandra Bullock | [1 leadership, 8 mastery] | 13→4 | 4→4 | ❌ |
| 9 | Matthew McConaughey | [1 leadership, 8 mastery] | 18→9 | 5→5 | ❌ |
| 10 | Cameron Diaz | [**1 leadership**, 2 cooperation] | 11→**2** | 4→4 | ✅ |
| 11 | Ben Affleck | [**1 leadership**, 3 creativity] | 10→**1** | **3→3** | ✅ |
| 12 | Jennifer Lawrence | [1 leadership, 5 freedom] | 16→7 | 6→6 | ❌ |

**Aggregate: 4/12 matches (33.3%).** Archetype-1 in top-2 for **12/12 control** (vs 10/12 GM) — confirming the Pass-38 #69 rubric-bias diagnosis even more strongly. Note also: top-2 tuple [1, 2] occurs for 4/12 controls (Cruise, Pitt, Smith, Diaz), explaining why mod-9-of-2 hits drove most of the control matches.

## §4 — Fisher exact 2x2 test

|  | Match | No-match | Row total |
|---|---|---|---|
| GM (Pass-38) | 3 | 9 | 12 |
| Control (Pass-39) | 4 | 8 | 12 |
| Col total | 7 | 17 | 24 |

- **One-sided Fisher exact P(X ≥ 3 \| GM > control direction) = 0.8146**
- This means: under the null of equal rates, the observed *or more extreme* GM-higher table is observed ~81% of the time → **null is not rejected; H_FORWARD is not supported.**

## §5 — Verdict per FROZEN ladder

- **VERDICT: NULL (TIU = 0.0)**
- Specifically: P(match|control) = 4/12 falls in the 3-4/12 NULL band; Fisher p=0.81 > 0.20 NULL threshold. Both criteria met.
- Directional trend: controls matched 33% vs GM 25% → if this had been larger or significant, would have been PARTIAL_NEG; observed effect is small and not significant.

## §6 — Asymmetric-hypothesis interpretation under URB-830 symmetric framing

Per Pass-33 URB-830, NULL with TIU = 0.0 is a *valid empirical result* — it neither confirms nor disconfirms; it removes signal from the prior. The combined Pass-38 + Pass-39 picture for **MBE-via-numerology-keyword-rubric** is:

| Direction | Pass | Result | Brandon's hypothesis claim | Empirical status |
|---|---|---|---|---|
| GM → match (CONVERSE) | Pass-38 | 3/12 = 25% < MC null 40%, z=−1.03, PARTIAL_NEG | "largely false" | **MODESTLY DISCONFIRMED** ✓ aligned with hypothesis |
| match → GM (FORWARD) | Pass-39 | 4/12 control vs 3/12 GM, Fisher p=0.81, NULL | "predicts GM" | **NOT SUPPORTED** ✗ contradicts hypothesis |

Brandon's full asymmetric hypothesis predicted **CONVERSE-FALSE + FORWARD-TRUE**; the empirical finding is **CONVERSE-FALSE + FORWARD-NOT-SUPPORTED**. Half-confirmed, half-disconfirmed — and the disconfirmation of the FORWARD direction is *the more informative half* because it rules out the most charitable rescue ("matches are rare and rare-when-they-occur are GM-discriminative").

**This is a #69 honest update:** Brandon's expectation of an asymmetric-positive-direction-pattern was empirically tested and not vindicated. Per URB-830-symmetric, NULL is a Bayesian non-update on direction but represents a *qualitative update against* the asymmetric-positive framing relative to the hypothesis-prior. **No quantitative combined TIU is asserted** — the per-pass frozen ladders yielded Pass-38 TIU = −0.5 and Pass-39 TIU = 0.0; combining them into a single number requires a pre-declared combination rule that does not exist in the corpus, so we leave the combined update qualitative ("negative qualitative update on the asymmetric framing as a unit").

## §7 — What survives, what does not

**SURVIVES:**
- Pass-15 broader MBE (heavy-tailed individual base rates) is **not directly tested** by Pass-38 + Pass-39; only the keyword-rubric operationalization is.
- Pass-14 family-cluster numerology result (T=2 P=0.57%) is independent and unaffected.
- Pass-37 PD-final canonical / GILE-HEM / Popp-Korotkov synthesis are independent and unaffected.
- Pass-21 R-A inverted-H4 AUC=0.7318 (the cleanly-replicated empirical prediction) is independent and unaffected.

**DOES NOT SURVIVE (under this rubric):**
- The narrow "Pass-37 keyword-rubric numerology asymmetrically discriminates GM-Nodes" prediction — both directions empirically null-or-negative.
- Any rescue that claims "matches are rare-but-GM-specific" — controls matched at 33% vs GM 25%, ruling this out.

**OPEN QUESTIONS (Pass-40+):**
- p39-A: would alternative numerology rubrics (life-path number from birth date; expression number) survive an asymmetric-test design? (Pass-38 §7 p38-B, now coupled with Pass-39 control design.)
- p39-B: would a *refined* keyword rubric (Pass-38 p38-A, suppressing archetype-1 over-broadness) flip either direction? Code refresh + rerun = $0 + ~5 min.
- p39-C: is there a *non-numerology* asymmetric-positive-predictor of GM-Node status in the existing corpus? (e.g., Pass-21 LCC-coupling-not-retrieval; Pass-23 6-item intuition shortlist FEP-coverage score.)

## §8 — Honesty caveats (#69)

- **(C1)** Anti-HARK gate: control roster frozen IN-CODE before any fetch; sha256 + git_head recorded; verdict ladder frozen in same commit. Single continuous run completed in ~130s.
- **(C2)** Same Pass-37 frozen rubric used for both GM and control — no rubric drift. Comparison is internally consistent.
- **(C3)** Wikipedia revids recorded for all 12 control celebrities (cf. `control_archetypes_frozen.json`).
- **(C4)** Sample size N=12 vs N=12 is small. Fisher exact properly handles the small-N regime, but CIs are wide; a future N=30 vs N=30 study would tighten.
- **(C5)** Control roster selection: agent-selected entertainment celebrities; gender-balanced. Brandon-DPES did not influence roster (selection was committed in-code BEFORE this paper). Possible selection bias toward "obviously not GM-Node" celebrities — but this would *favor* H_FORWARD (low controls would inflate the GM > control gap), so the NULL result is conservative against H_FORWARD.
- **(C6)** Archetype-1 over-broadness affects controls even *more* than GM (12/12 vs 10/12 in top-2). This may explain the marginally-higher control match rate: if archetype-1 dominance is universal, then the matching-game effectively tests "does name-mod-9 ∈ {1, X} for some second archetype X" — and entertainment-celebrity bio openings may be slightly noisier in the second-archetype slot. This is structural noise, not signal.
- **(C7)** "NOT SUPPORTED" wording is correct for NULL: H_FORWARD is neither confirmed nor disconfirmed in absolute terms, but is *not supported* relative to its prior. URB-830-symmetric: this is a Bayesian non-update on direction with a small Bayesian update against the asymmetric framing as a meta-claim.

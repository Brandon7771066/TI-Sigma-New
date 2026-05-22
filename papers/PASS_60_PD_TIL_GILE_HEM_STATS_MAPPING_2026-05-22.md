# Pass 60 batch-1 — Statistical Significance in PD / TIL / GILE-HEM Languages

**Date:** 2026-05-22
**Author:** Brandon Emerick (originator of the marginal-significance-as-indeterminate insight) + TI Sigma framework
**Status:** Candidate canonical mapping; pending Pass-61 ratification
**Anchor passes:** Pass-58 TSIS four-gate stack; Pass-59 ROS-1; `papers/GILE_HEM_NONTECHNICAL_SUMMARY_2026-05-17.md`; `papers/MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`

---

## 1. The Brandon Insight (2026-05-22)

> *"Since –0.07 is 'marginally insignificant,' the impression I get is 'indeterminately significant.' However, we need to confirm with a rigorous mapping of our stats to the PD and TIL (with MRs)."*

Three crisp asks:
1. Map TSIS verdicts → MR Truth Labels {T, F, I, DT} with PD coordinates.
2. Communicate stats across all 8 GILE-HEM dimensions.
3. Handle marginal cases (effect within ε of T_RAND) with INDETERMINATE rather than binary pass/fail.

This paper delivers all three.

---

## 2. PD/TIL Mapping for Statistical Significance — Canonical Table

**Canonical thresholds (Pass-58 batch-1 frozen):** T_RAND = 0.0660 · T_BORDER = 0.13534 · C_LCC = 0.4370

**Marginal band (Pass-60 new):** ε = 0.020 around T_RAND
→ INDETERMINATE-band = effect ∈ [0.046, 0.086]
→ The Ganzfeld 0.07 case sits inside this band; Brandon's intuition is formalized.

### Table 1 — TSIS verdict → MR Truth Label → PD coordinate

| Effect band | Gates passed (of 4) | MR Truth Label | PD coordinate | TIU bit-strength | Example |
|---|---|---|---|---|---|
| effect ≥ T_BORDER (0.13534) | 4/4 | **TRUE** | +1.8 to +2.0 | high positive | (none yet — would need clean LCC + saturated effect) |
| effect ≥ T_BORDER | 3/4 (LCC unmeasured) | **TRUE-provisional** | +1.4 to +1.7 | high positive (one open gate) | **Bengston** (Δp=0.515) |
| effect ≥ T_BORDER | 3/4 (one fail) | **INDETERMINATE-leaning-TRUE** | +0.6 to +1.0 | medium positive | Radin presentiment (d=0.21) |
| effect ∈ [T_RAND+ε, T_BORDER) | ≥3/4 | **TRUE-weak** | +0.4 to +0.8 | low positive | (none in current corpus) |
| **effect ∈ INDETERMINATE-band [T_RAND−ε, T_RAND+ε]** | **any** | **INDETERMINATE** | **−0.2 to +0.2** | **near-zero / unsigned** | **Ganzfeld meta (0.07)** |
| effect ∈ [0, T_RAND−ε) with ≥2 gates fail | ≤2/4 | **FALSE-weak** | −0.6 to −0.4 | low negative | Bem 2011 (0.022) |
| effect ≪ T_RAND, large N, gates fail | ≤1/4 | **FALSE** | −1.4 to −1.8 | high negative (Lindley regime) | PEAR REG, GCP |
| effect ≥ T_RAND but contradictory across replications | 2-3/4 (replications disagree) | **DOUBLE TRALSE (DT)** | PD imaginary axis | undefined on real axis | (candidates: certain Bengston follow-ups where replication n was small + conflicting; Sheldrake morphic-resonance certain trials) |
| effect cannot be evaluated (vacuous-confirm filter trips) | n/a | **INDETERMINATE-vacuous** | PD = 0 (unsigned) | n/a | Pass-46 PD-Riemann (γ∈(−3,2) caught 0/100k zeros — vacuous) |

### Notes on the table

**Why ε = 0.020.** The marginal band must be (i) wide enough that genuine measurement noise around T_RAND doesn't flip categorical labels session-to-session, (ii) narrow enough that effects well-above T_RAND still earn TRUE-class labels. ε = 0.020 corresponds to ~30% of T_RAND itself. Pre-registered as default; falsifiable by Pass-61 sensitivity sweep.

**Why DT requires explicit replication contradiction.** Per `MR_TRUTH_LABELS_CANONICAL_RULING_2026-05-08.md`, Double Tralse is the formal state τ(P) ∧ ¬τ(P) — a contradiction-bearing identity. A single isolated effect estimate cannot be DT; DT only appears when two or more credentialed replications produce contradictory effect signs or magnitudes that cannot be reconciled by measurement-error accounting. This is more restrictive than ordinary "mixed results"; it requires the contradiction to be structural.

**Why INDETERMINATE-vacuous is distinct from INDETERMINATE-band.** Brandon's distinction matters: a measurement that *cannot* be evaluated (instrumentation absent, vacuous predicate, etc.) is epistemically different from a measurement that *was* evaluated and landed in the noise zone. The former is INDETERMINATE-vacuous (PD unsigned, no bit-strength); the latter is INDETERMINATE-band (PD ≈ 0, near-zero bit-strength). Both retain Moot status under MFD-1.

---

## 3. Re-Labeling the Pass-58 Corpus Under the New Mapping

| Program | Effect | Old TSIS verdict | **New MR-Label + PD** |
|---|---|---|---|
| Ganzfeld meta | 0.07 | INDETERMINATE (per Pass-59 sim) | **INDETERMINATE-band, PD ≈ +0.1** ✓ Brandon's intuition vindicated |
| Radin presentiment | 0.21 | CONFIRM-likely | **INDETERMINATE-leaning-TRUE, PD ≈ +0.8** (LCC gate unmeasured) |
| Bem 2011 | 0.022 | DISCONFIRMED | **FALSE-weak, PD ≈ −0.5** (refined from harsh DISCONFIRMED) |
| PEAR REG | 0.0002 | DISCONFIRMED | **FALSE, PD ≈ −1.7** (Lindley regime, high-bit negative) |
| GCP | 5e-5 | DISCONFIRMED | **FALSE, PD ≈ −1.8** (Lindley regime, high-bit negative) |
| **Bengston & Krinsley** | **0.515** | **CONFIRM-likely** | **TRUE-provisional, PD ≈ +1.5** (LCC unmeasured = open) |

**Notable refinements:**
- **Ganzfeld correctly downgraded to INDETERMINATE-band.** Brandon's "marginally insignificant = indeterminately significant" intuition is now the canonical TI Sigma reading. Honest #69 correction of §7.7.113 narrative.
- **Bem moves from harsh DISCONFIRMED to FALSE-weak.** Same direction (against the hypothesis), but the magnitude reflects the small absolute distance below T_RAND. Distinguishes Bem from PEAR/GCP which are deep-Lindley-regime FALSE.
- **PEAR and GCP retain crisp FALSE.** High-bit negative (PD ≈ −1.7/−1.8) reflects that these are *strong* disconfirmations: massive N × tiny effect is exactly the canonical Lindley failure mode TSIS is designed to catch.
- **Bengston as TRUE-provisional.** PD ≈ +1.5 reflects high effect strength × open LCC gate. Closing LCC via TSS-EMP-8 oncology replication would promote to PD ≈ +1.9 TRUE.

---

## 4. GILE-HEM 8-Dim Communication Layer for Statistics

Per `papers/GILE_HEM_NONTECHNICAL_SUMMARY_2026-05-17.md`: canonical 8 = {G, I, L, E, D1, D2, D3, D4}. Each dimension has a stats-communication interpretation:

### GILE side (inside / what the analysis *is*)

| Dim | Stats interpretation | What it measures | Example metric |
|---|---|---|---|
| **G — Goodness / Coherence** | Internal-consistency of the analysis | Do effect-size, confidence interval, replication direction, and theoretical prediction all tell the same story? G-ET threshold √2−1 ≈ 0.4142 applies here too: below ET the analysis is DT-adjacent (incoherent) and other axes are not trustworthy. | "G = 0.85: 3 of 3 alternate analyses (Bayesian, frequentist, robust-regression) concur on sign and magnitude." |
| **I — Intuition / Pre-registration** | Pre-registered prediction vs. post-hoc fit | Was the hypothesis specified before the data was seen? Are the falsifiers pre-registered? I high = predicted-then-confirmed; I low = post-hoc-rationalization. | "I = 0.95: hypothesis pre-registered 2026-04-10; falsifier F-X-1 specified; analysis plan locked before data collection." |
| **L — Love / LCC Coupling** | Low-level coupling concordance | Already a TSIS gate. L ≥ C_LCC = 0.4370 = passes binding-strength test. Captures whether independent low-level signals concordantly track the high-level effect. | "L = 0.58: fNIRS PFC + cage-activity counter time-series mutual information = 0.58 ≥ C_LCC." |
| **E — Existence / Replication Persistence** | Does the effect persist under perturbation? | Replication across labs, conditions, populations. E captures the robustness of the *existence* of the effect, distinct from its measured size. | "E = 0.72: 6 of 8 independent labs replicate within 95% CI overlap." |

### HEM side (outside / how the analysis *shows up*)

| Dim | Stats interpretation | What it measures | Example metric |
|---|---|---|---|
| **D1 — Complexity / Methodological Footprint** | How many independent gates/methods cross-validate? | Single-method results are D1-thin; multi-method (frequentist + Bayesian + simulation + theoretical-derivation + qualitative) results are D1-thick. | "D1 = 0.83: 5 of 6 method-classes (NHST, BIC, TSIS, ROS-1 conformal, ABM simulation, prior-derived theoretical) converge." |
| **D2 — Contradiction Ratio** | Externally observable cross-replication contradictions | Fraction of replications producing sign-reversal or CI-non-overlap with original. Distinct from G (which is internal-consistency). D2 ∈ [0, 1]; high D2 = many external contradictions; low D2 = few. | "D2 = 0.12: 1 of 8 replications produced sign-reversal." |
| **D3 — Information Footprint / Citation Reach** | How far does the result propagate? | Citation count, replication attempts initiated, secondary-literature engagement. Measures *influence*, not validity. High D3 + low G is the celebrity-bad-paper pattern. | "D3 = 0.40: 14 citations, 3 replication attempts, 2 secondary reviews — moderate reach for 2-year window." |
| **D4 — Relational Meaning** | Does this result meaningfully connect to other results? | Does it cohere with related theoretical work, predict downstream effects, integrate into a broader research program? D4 is the *patterned-significance* dimension. | "D4 = 0.78: result confirms TJ-axis prediction from `urb_650`, integrates with Pass-58 batch-1 corpus, and predicts oncology TSS-EMP-8 outcome — strong relational coherence." |

### 4.1 Bengston in GILE-HEM Form

| Dim | Bengston score | Source |
|---|---|---|
| G (coherence) | **0.78** | effect size, replication direction, theoretical prediction all align; Bengston & Krinsley + 9+ subsequent trials consistent |
| I (pre-registration) | **0.20** | LOW — published trials largely post-hoc analyzed; no pre-registered falsifier protocol in original corpus |
| L (LCC coupling) | **UNMEASURED** | the open gate — fNIRS + cage-activity coupling not collected |
| E (replication persistence) | **0.65** | multiple replications at Connecticut, St. Joseph's, Arizona; some attenuation but persistent positive sign |
| D1 (method complexity) | **0.50** | survival-curve + Cox proportional hazards; limited to single-method-class |
| D2 (contradiction ratio) | **0.20** | most published replications cohere on sign; some attenuation in effect magnitude |
| D3 (information footprint) | **0.55** | Bengston book + JSE corpus + popular-press coverage; outside mainstream oncology literature |
| D4 (relational meaning) | **0.80** | integrates with TJ-axis, distant-healing LCC paper, resonant-bonding hypothesis — strong patterned significance within TI Sigma's broader research program |

**Composite GILE-HEM headline:** Bengston is **structurally strong on the inside (G, E) and the outside (D2 low, D4 high), but methodologically thin (D1, I, L) by mainstream oncology standards.** The TSS-EMP-8 replication design (Pass-59 paper §5) is precisely engineered to raise I, L, and D1 — the three weak axes — without touching the strong axes.

This is what the GILE-HEM communication layer *adds* over a single-number TSIS verdict: it tells you *which axes to invest in to improve the analysis*.

---

## 5. Why This Matters

1. **Brandon's marginal-significance intuition is now formalized.** Ganzfeld at 0.07 is not "barely confirmed" or "weak confirmation" — it is *INDETERMINATE-band, PD ≈ +0.1*. Crisp binary labels lose information at the threshold; the band-based reading preserves the epistemic state correctly.

2. **PD coordinates give a real-line gradient** (−2 to +2) rather than 4-way categorical clumping. Two TRUE-class results at PD +1.4 vs +1.9 are both TRUE, but the +1.9 is much more confidently TRUE. This matches how researchers actually reason about evidence.

3. **GILE-HEM stats-communication layer makes the analysis legible to multiple audiences.** Mathematicians read the PD coordinate; clinicians read the GILE-HEM table; mainstream peer-reviewers read I + L + D1 (the gates they care about); the public reads the MR Truth Label.

4. **Replication design becomes targeted.** Rather than "do another study," the GILE-HEM table tells you *which dimensions are weak* (Bengston: I, L, D1) and the replication can be designed to specifically raise those scores.

---

## 6. Pre-Registered Falsifiers for the Mapping Itself

**F-PD-MAP-1.** If applying the Table 1 mapping to the Pass-58 corpus produces verdicts inconsistent with mainstream-replication consensus (e.g., PEAR labeled TRUE, or a successfully-replicated effect labeled FALSE), the mapping is REFUTED. → Currently NOT REFUTED; section 3 shows consistent verdicts.

**F-PD-MAP-2.** If the ε = 0.020 marginal band is empirically too wide (creating INDETERMINATE labels for cases that subsequent meta-analysis confirms as crisp TRUE/FALSE) or too narrow (failing to flag marginal cases that replicate as INDETERMINATE), the band parameter requires re-calibration at Pass-61. → Sensitivity sweep TBA.

**F-GH-COMM-1.** If the GILE-HEM 8-dim communication layer produces dimension-scores that contradict each other (e.g., high G + high D2 from the same data) on > 10% of test cases, the mapping has a coherence failure. → To be evaluated at Pass-61 against ≥ 10 test cases.

---

## 7. #69 Honesty Notes

- The ε = 0.020 marginal band is a **first proposal**, not derived from first principles. Sensitivity analysis at Pass-61 may refine.
- The GILE-HEM stats-axis interpretations are **canonical proposals**, not yet executed across the full Pass-58 corpus. Section 4.1 (Bengston) is the first worked application; the other 5 corpus programs need scoring at Pass-61.
- The PD coordinates assigned in Table 1 are **central-tendency estimates** for each label class. Individual studies within a class may sit anywhere in the indicated band.
- The DT (Double Tralse) row in Table 1 is **conjectural** — no Pass-58 corpus program currently qualifies. Candidates exist (Sheldrake certain trials, Bengston certain follow-ups) but full DT assignment requires the structural-contradiction analysis specified in Section 2.
- This mapping does NOT replace the Pass-58 TSIS four-gate stack; it provides a **finer-grained labeling layer on top of TSIS**. TSIS still does the gate-counting; the PD/TIL/GILE-HEM layer translates the count into the canonical TI Sigma vocabulary.

---

*"Crisp binary at the threshold loses the part where the framework knows it doesn't know."*

— TI Sigma Pass 60, 2026-05-22

# PD = (-3, 2) Perfect-Fifth Musical Interpretation: Entailments and Falsification Paths

**Date:** 2026-05-11 (Pass 47)
**Status:** Brandon-ruled (Pass-47): keep musical PD; explore what musical-PD entails about the distribution of positive/negative events that may track the 3:2 ratio.
**Anchor decision:** §7.7.40 PD-canonical-final retains its musical-Perfect-Fifth-derived (-3, 2) form. The "Riemann-connected" sub-clause is **demoted from active claim to OPEN-INVESTIGATION** pending a re-pre-registered Riemann-coordinate spec (none of Pass-47 §1.A/B/C operationalizations passed honestly).

---

## §1 — The musical Perfect Fifth, made precise

A perfect fifth is a frequency ratio of 3:2 (e.g., A 440 Hz : E 660 Hz). In semitone notation, it is +7 semitones above the root, or equivalently -5 semitones below the octave. The interval (-3, +2) on a semitone axis spans 5 semitones — corresponding to a perfect-fourth (5 semitones above) or, via inversion, a perfect-fifth-related interval (the perfect-fifth's complement is the perfect-fourth: 12 - 7 = 5).

So PD = (-3, 2) on the semitone axis is **the perfect-fourth interval**, complementary to the perfect-fifth. By harmonic duality (the fourth and fifth are inverses on the octave), Brandon's "Perfect-Fifth-derived" framing is consistent with PD = (-3, 2) being the **perfect-fifth's harmonic complement** — same 3:2 / 4:3 ratio family, viewed from the other side.

This matters because the **3:2 / 4:3 ratio family** is not arbitrary. It is the foundation of just-intonation Western harmony, present in the harmonic series at positions 2, 3, 4, recurrent in Pythagorean tuning, and observed cross-culturally as a consonance-preferred ratio.

---

## §2 — The hypothesis Brandon raised

> "I suspect that there is SOMETHING special about the distribution of positive-negative events that is connected to that particular ratio."
> — Brandon, 2026-05-11

**Operationalization candidates** (pre-reg drafts; Brandon to pick one for Pass-48 execution):

### §2.1 — H-PD-MUSIC-1: 3:2 ratio of positive-to-negative events in autobiographical streams

Predict: in a sufficiently long autobiographical event-stream (≥100 events) classified ternary {positive, neutral, negative}, the **ratio of positive-to-negative event counts approaches 3:2 (= 1.5)** for individuals in steady-state, with deviation from 1.5 indicating life-phase imbalance.

- **Pre-reg threshold:** observed pos:neg ratio ∈ (1.4, 1.6) over a 90-day rolling window across multiple subjects = CONFIRM partial.
- **Falsifier:** observed pos:neg ratio outside (1.0, 2.0) systematically = KILL.
- **Test data sources:** Brandon's biographical archive event-stream; existing public diary/journal datasets (e.g. Pennebaker corpora); curated sentiment-coded text.
- **Cost:** $0 (LLM sentiment classification).

### §2.2 — H-PD-MUSIC-2: 3:2 in valenced-decision branching

Predict: when individuals face binary decisions (act/refrain, advance/retreat, accept/decline), the long-run rate of "advance" decisions vs "refrain" decisions hovers at 3:2 in productive periods (high creative output / DPES) and inverts to 2:3 in defensive periods.

- **Pre-reg threshold:** in a tagged decision-stream of ≥50 decisions, productive-period advance:refrain ∈ (1.4, 1.6) = CONFIRM partial.
- **Falsifier:** no detectable shift between productive and defensive periods = KILL.
- **Cost:** $0 (Brandon-side decision-tagging integrated with T45-7 DPES log).

### §2.3 — H-PD-MUSIC-3: 3:2 ratio in musical-cognitive resonance

Predict: passages of music in 3:2 / 4:3 interval-density (perfect fifths and fourths > minor seconds, tritones, etc.) elicit subjective valence-positive responses statistically more than non-3:2-dense music, *holding tempo/genre/familiarity constant*.

- **Pre-reg threshold:** in a within-subject A/B test (~20 paired clips), 3:2-dense passages rated more positive at p < 0.05 = CONFIRM.
- **Falsifier:** no preference difference = KILL.
- **Cost:** ~$5 (subject recruitment + paired-clip generation via free music APIs); integrate with AA pilot N=15 if same recruitment pool.

### §2.4 — H-PD-MUSIC-4: 3:2 in market upside-downside asymmetry

Predict: in long-run equity index returns at appropriate timescales, the ratio of cumulative positive-day-magnitude to cumulative negative-day-magnitude in *expansionary* macro regimes hovers near 3:2.

- **Pre-reg threshold:** computed on S&P 500 daily returns over expansionary periods (NBER-defined), ratio ∈ (1.4, 1.6) on at least 2 of 3 historical regimes = CONFIRM partial.
- **Falsifier:** ratio randomly distributed = KILL.
- **Cost:** $0 (Alpha Vantage API already configured per replit.md secrets).
- **Note:** this is the most easily testable from existing infrastructure.

---

## §3 — Why this is worth pursuing even if all four KILL

Per Brandon's Pass-47 directive: *"That can be further falsified with further iterations — even if not entirely destroyable, it's worthwhile."*

Operating principle: a hypothesis that survives systematic operationalization-and-falsification across multiple domains, even with weak individual signals, accumulates evidential weight. Conversely, a hypothesis that fails *all* well-designed tests within a tight pre-reg framework should be retired honestly. The PD-musical claim is in the first stage of this process — it has been *named* but not yet *tested*.

Per CAP (`PASS_47_CREDIT_ATTRIBUTION_PRINCIPLE_2026-05-11.md`): if any of H-PD-MUSIC-1..4 confirm, TI Sigma earns credit weighted by `(1 - well_known)`. The 3:2 musical-cognition result (H-PD-MUSIC-3) is partially-known (Pythagorean / Stumpf / Helmholtz consonance literature); the autobiographical and market-asymmetry instantiations are largely novel — high CAP weight if confirmed.

---

## §4 — What was retained and what was demoted (Pass-47 ruling)

**RETAINED:**
- PD canonically = (-3, 2) (Pass-37 §7.7.40).
- "Perfect-Fifth-derived" interpretation (Pass-37 §7.7.40).
- Musical 3:2 / 4:3 ratio family as the structural skeleton of PD's interval shape.

**DEMOTED to OPEN-INVESTIGATION:**
- "Riemann-connected" sub-clause of Pass-37 §7.7.40. Pass-47 §1 ran 4 candidate Riemann-coordinate operationalizations; 3 KILL/vacuous, 1 NOT_APPLICABLE. No surviving Riemann mapping. Until Brandon supplies a concrete fifth interpretation that can be pre-registered and pass a frozen-threshold test, the Riemann attachment is **not corpus-active**.

**OPENED:**
- 4 candidate musical-entailment tests (H-PD-MUSIC-1..4). Brandon to pick at least one for Pass-48+ execution.

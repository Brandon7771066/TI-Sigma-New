# Pass-77 B118 — Affective Tralse-Joules: attractor-basin steering strength of the Mood Amplifier
**2026-06-16 · empirical measurement batch · canonical principle count UNCHANGED 79 · #69 brutal honesty**

## Directive (Brandon)
Obtain an **Affective Tralse-Joules** measurement from the mood-amplification data:
the **strength of the attractor basin** steering mood in a particular (valenced)
direction, from **beginning to end** of the intervention, and **how that strength
changes as thresholds are crossed**. Leverage the parallel literatures —
consciousness (**Φ / IIT**), **brain thermodynamics** (free energy), and
**valence** (the corpus's own quantum/neural valence theory).

## Data-availability verdict (#69)
Live rodent hemodynamic data was **not retrievable** (DANDI neurovascular
streaming timed out twice in the B117 batch; `live_retrieved:false`). This batch
is an **in-simulation proof-of-principle** on the *same* closed-loop generative
mood model that carried the B117 Exp B efficacy proof. It measures the
**amplifier's** basin-steering work, not a live animal. Package:
`analyses/affective_tralse_joules_2026_06_16/affective_tj.py`
(+ `results_affective_tj.json`, `RESULTS_WRITEUP.md`).

## Measure (corpus-faithful)
**TJ = τ(s)·δ(MR)** (urb_650): τ = tralseness = normalized entropy `H(p)/log K` of
the instantaneous mood-belief distribution (indeterminacy); δ(MR) = MR-depth =
`Σ|ΔPD_i|` = L1 path-length in PD-space per Myrion-Resolution step. PD-real =
expected coupling degree; PD-imaginary = modal coherence `|Σ p·e^{iφ}|`.
**Affective weighting** (QVF-1, B64): `V = S·A`, S = consonance sign
`tanh(6(g−g_neutral))` (+ toward the high-coupling consonant attractor, − toward
the dissonant pole), A = arousal = **Φ-proxy** (mean |pairwise channel corr|;
IIT-style integration — valence-blind without S per CLV-1). **aTJ = V·TJ**;
cumulative = Σ. Thresholds: MR1 ET=√2−1≈0.4142, Radiant C_TI≈0.437, BEC cap
T_TI≈0.934. Anchors: BOK 0.934 / Dottie 0.517 / MR1 0.124.

## Results (40 seeds × 120 steps, bootstrap 95% CI)
- **Direction-sensitivity (headline):** cumulative aTJ = **+0.765** closed-loop vs
  **−0.496** sham, **−0.515** wrong-target, **−0.047** open-loop, +0.035
  no-control. Specificity all SIG: vs baseline +0.730, vs open-loop +0.812, vs
  sham +1.261, vs wrong-target +1.280. **Sham and open-loop are matched to
  closed-loop at EXACTLY equal drive energy (23.94/arm)**, yet open-loop (correct
  target phase, equal energy, *no feedback*) yields ≈0 aTJ → the positive
  affective work comes from the **closed-loop feedback**, not drive energy or
  target-phase alone. The QVF-1 valence **sign flips** with steering direction —
  aTJ is a *signed* basin quantity (positive = euphoric pull, negative = dysphoric).
- **Basin stiffness κ** (steering-strength proxy; conflates controller action +
  plant dynamics, NOT intrinsic-basin identification): closed-loop **0.93** >
  open-loop 0.89 / sham 0.69 / no-control 0.60 / wrong-target 0.55. Early 0.928 vs
  late 0.966, Δ=+0.038 **CI[−0.028,+0.108] ns** — basin established **fast** and
  held, not progressively stiffened.
- **Threshold sign-flip** (descriptive, pooled step-level means, no per-regime CI):
  aTJ-rate −0.027 (sub-MR1) → −0.034 (transitional) → −0.005 (GILE-dominant) →
  **+0.013 (master/BEC)**; event-locked BEC-cap crossing **conditional on n=19
  crossing trajectories** Δ=**+0.0069 CI[+0.0042,+0.0099] SIG**. Positive affective
  work concentrates *only* above the master/BEC threshold. (Sub-threshold bins
  sparse n=53/20; MI-screen/Radiant crossings rarely fire — baseline g_neutral
  0.801 already clears them, so the operative phase transition is the BEC cap; the
  crossing result is a conditional sub-sample contrast, not a global proof.)
- **Cross-checks:** `r(aTJ-rate, −dF/dt) = −0.088` (near-null → **non-redundant**
  with the Friston free-energy-descent valence proxy); settled TJ-rate **0.054** ≪
  MR1 anchor 0.124 = the corpus-predicted **fixed-point TJ-collapse** (δ→0 at the
  attractor; the work is in the *approach*, captured by cumulative aTJ); affective
  efficiency 0.033 aTJ/energy.

## #69 verdict
A faithful Affective-TJ (τ·δ × QVF-1 S·A) cleanly quantifies mood-amplifier basin
steering: positive for genuine positive-attractor *feedback* control, negative for
wrong-target/sham, ≈0 for equal-energy open-loop (isolating feedback), a stiff
basin set early, and a threshold-gated sign-flip across the BEC cap. It is
non-redundant with the Friston −dF/dt valence proxy and obeys the corpus
fixed-point TJ-collapse. **Limitations:** in-sim proof-of-principle only (live not
retrievable); threshold-regime table descriptive (sparse sub-threshold bins);
BEC-crossing conditional on the crossing sub-sample; κ a realized steering proxy
not an intrinsic-basin identification; MI-screen/Radiant crossings rarely fire
(baseline already above them). **No canonical principle added or refined**
(empirical measurement). Anchor measures invoked: Φ/IIT (arousal A), Friston FEP
(−dF/dt cross-check), QVF-1 quantum/neural valence (S·A), urb_650/urb_676 TJ unit
+ fixed-point collapse.

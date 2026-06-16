# A Consciousness Hamiltonian for Mood: Richer Principled Features and a Closed-Loop Mood-Amplifier Proof-of-Principle

**Author:** Brandon Charles Emerick
**Part of:** The TI Sigma / Mood Amplifier Program
**Date:** June 2026
**Status:** Empirical result. Extends the Retrieval-Operator Benchmark
(`papers/RETRIEVAL_OPERATOR_BENCHMARK_2026-06-16.md`) by replacing generic features
with the program's own GILE / PD / TI-Sigma-Crystal machinery, and adds the first
closed-loop efficacy test.
**Code & data:** `analyses/pass_b_consciousness_hamiltonian_2026_06_16/`
(`tsc_hamiltonian.py`, `ch_features.py`, `runner_ch.py`, `mood_control.py`,
`reachability.py`, `results_expA.json`, `results_expB.json`,
`results_reachability.json`, `RESULTS_WRITEUP.md`).

---

## In Plain Language

The retrieval benchmark left a clear lesson: on real brain data, **good features beat
clever machinery.** So the obvious next question is whether *this program's own*
ideas — the GILE-HEM matrix, the FULL Permissibility Distribution (both the real
"degree" axis and the imaginary MI/Tralse axis), and the TI-Sigma Crystal read as a
**"Consciousness Hamiltonian"** — make *better features* than generic spectral power.

This paper does two things, both honestly:

1. **Feature test.** Build a Consciousness-Hamiltonian feature block and ask, with
   strict no-cheating discipline, whether it decodes a hidden brain state *better than
   a matched baseline* — on two live Buzsáki-lab mice streamed from a public archive,
   backed by simulations where the answer is known.
2. **Efficacy test.** Build a **closed-loop Mood Amplifier** — a controller that reads
   the brain state and pushes it toward a chosen "positive" target — and measure
   whether it actually works, against fair controls (a sham that spends the same
   energy at the wrong timing, an open-loop drive, and a wrong-target drive).

**The honest headline.**

- The Consciousness-Hamiltonian features **genuinely help where mood is carried by
  coupling** (the simulations: +7 to +18 points over baseline, statistically clean).
  On the live mice the result is **mixed**: it helps one mouse (not significantly) and
  *hurts* the other, where plain power features already do nearly perfectly. The raw
  GILE-HEM numbers alone are *worse* than baseline — the value, where it exists, is in
  the **whole block** (crystal + PD + graph), not the eight GILE numbers by themselves.
- The closed-loop Mood Amplifier **works as a proof-of-principle in simulation**: it
  drives the mood to the target far above baseline, and it provably needs the **right
  timing** (beats sham) and the **right target** (beats wrong-target). But it does
  **not** beat a simpler equal-energy open-loop push — so the *added value of feedback*
  is, honestly, **not shown here.**
- Because the animals are **recorded**, we cannot intervene on them. On the live data
  we therefore only claim a **necessary precondition** — that the "positive-mood" state
  is reachable from the others — which holds in both mice.

This is deliberately not a hype paper. It reports a real feature gain in the regime the
theory targets, a clean in-sim efficacy proof, and two honest nulls.

---

## 1. The Consciousness Hamiltonian

Each analysis window is reduced to an 8-dimensional **GILE-HEM** vector using the
canonical corpus formulas (G/I/L/E primitives + H/E/M aggregates), where **GILE-L is
operationalized as theta-gamma phase-amplitude coupling** (`features.theta_gamma_pac`)
— the corpus definition of L as coupling strength. (A first pass used broadband
correlation for L; it was flat across mood and is reported as a corrected error in
§4.) These eight values set the **ring weights** of the 57-vertex **TI-Sigma Crystal**,
and we form the **Consciousness Hamiltonian**

> H_TSC = −J·A + U·diag(|α|²) + μ·diag(ring_weights)

(hopping on the crystal adjacency A, on-site amplitude, GILE ring potential), faithfully
ported from `hypercomputer/hamiltonian.py` / `tsc.py`. From each window we extract:

- **8 GILE-HEM dims** (the matrix itself);
- a **FULL PD block** — `pd_real = 5·(complexity − ½)` (degree axis) and
  `pd_imag = D2` (the imaginary MI / Tralse-zone axis) + soft zone memberships;
- a **Hamiltonian spectrum block** — low eigenvalues, spectral gap, ground-state
  participation of H_TSC;
- a **GILE-graph block** — algebraic connectivity (Fiedler value) of the
  GILE-weighted crystal Laplacian.

23 dimensions in total, all computed **per window** so the block is leakage-safe by
construction.

## 2. Experiment A — feature decoding (unsupervised, leakage-safe)

Identical discipline to the retrieval benchmark: the hidden state is defined
leakage-safe (ground truth in sims; TRAIN-ONLY k-means on a **disjoint channel group**
for the mice, with test windows labeled by nearest train centroid); every feature set
is standardized on TRAIN only; the decoder is a TRAIN-only class-centroid
nearest-neighbour; significance by paired bootstrap (`*` = 95% CI excludes 0).

| source | BASE | GILEHEM | CH | BASE+CH |
|---|---|---|---|---|
| sim(seed=0) | 0.840 | 0.750 | **0.913 (+0.073\*)** | 0.910 (+0.070\*) |
| sim(seed=7) | 0.597 | 0.613 | **0.739 (+0.141\*)** | **0.773 (+0.177\*)** |
| DANDI mouse41 | 0.524 | 0.381 | 0.679 (+0.105) | 0.500 (−0.025) |
| DANDI mouse20 | 0.913 | 0.495 | 0.556 (−0.359) | 0.824 (−0.090) |

**Reading it honestly.** Where mood lives in coupling (the sims), the **full CH block
significantly beats** the matched baseline. On the mice the block is **mixed-to-negative**:
a non-significant help on mouse41, a clear hurt on mouse20 (whose simple spectral
features already reach 0.913). And **GILEHEM-alone is reliably worse** than baseline —
the principled gain, where present, is a property of the *composite* (crystal + PD +
graph), not of the eight GILE numbers.

## 3. Experiment B — closed-loop Mood-Amplifier efficacy (simulation)

A controllable phase-coded generative mood chain; the controller reads the unsupervised
GILE-L coupling each step and applies a phase/energy drive toward the target mood.
30 seeds, 120 steps (30 burn-in); open-loop energy approximately matched to closed-loop
(24.8 vs 24.4); sham energy *exactly* matched by schedule replay (see below).

| arm | target occupancy [95% CI] | energy |
|---|---|---|
| no_control | 0.320 [0.264, 0.377] | 0.0 |
| **closed_loop** | **0.876 [0.863, 0.889]** | 24.4 |
| open_loop (approx. energy-matched) | 0.929 [0.917, 0.940] | 24.8 |
| sham (equal-energy, phase-scrambled) | 0.317 [0.295, 0.340] | 24.4 |
| wrong_tgt | 0.263 [0.215, 0.311] | 9.3 |

The **sham is an exact equal-energy control** — it replays the closed-loop's per-seed
drive *magnitude* schedule and scrambles only the phase, so closed-loop and sham spend
identical energy (24.4). The gap is thus attributable to **timing, not energy**.

| contrast | Δ occupancy | verdict |
|---|---|---|
| efficacy (closed − no_control) | **+0.556\*** | the amplifier steers mood |
| phase specificity (closed − sham) | **+0.559\*** | timing must be correct |
| target specificity (closed − wrong_tgt) | **+0.613\*** | steering is directed |
| value of feedback (closed − open_loop) | **−0.053\*** | **feedback marginally worse (honest negative)** |

(`*` = two-sided 95% CI excludes 0.)

**Reading it honestly.** The Mood Amplifier **works** as an in-sim proof-of-principle:
it lifts target-mood occupancy from 0.32 to 0.88, and it provably depends on **correct
phase** (vs an *equal-energy* sham that sits at baseline) and **correct target**. What
it does **not** show is that *feedback* beats a dumb equal-energy open-loop push — it is
in fact **significantly, if marginally, worse** (−0.053, CI excludes 0). In this
benignly controllable model a constant correct-phase drive is enough, and the
homeostatic-rebound penalty (the only force that should reward adaptive feedback) is too
mild to flip the comparison. We did **not** tune that penalty to manufacture a feedback
win; feedback's value remains an open question for regimes with steep
over-stimulation/tolerance costs. Efficacy is also **conditional on the assumed
controllability** — precisely the thing recorded data cannot establish.

## 4. A corrected error (logged, per #69)

The first implementation operationalized GILE-L as **broadband Pearson correlation**.
It was **flat across mood states** (composite spread ≤ 0.001) and the CH block sat at
chance on the sims. Since GILE-L is *defined* as coupling, the faithful primitive is
**theta-gamma PAC**, which tracks the latent (0.078 → 0.097 → 0.107). The corrected L
is what makes the block informative. This is a fidelity fix to a mis-operationalized
dimension — not a hyperparameter tuned toward a desired result — and is reported here
rather than buried.

## 5. Live-mouse reachability (necessary condition, NOT an intervention)

The DANDI animals are recorded, so no closed loop is possible on them. The only
legitimate live claim is observational: is the high-coupling "positive-mood" state even
reachable? Using the unsupervised decoded states and their empirical (Laplace-smoothed)
transition matrix:

| mouse | target state | reachable from all? | stationary P(target) | mixing gap | mean first-passage |
|---|---|---|---|---|---|
| mouse41 | 1 | **yes** | 0.429 | 0.627 | 3.0 / 3.2 steps |
| mouse20 | 2 | **yes** | 0.173 | 0.366 | 10.4 / 13.7 steps |

In both animals the positive-mood state is reachable from every other state with finite,
short first-passage times — it is **not** an unreachable sink. This satisfies a
**necessary precondition** for any future amplifier; it is explicitly **not** a
demonstration that the state could be *driven*.

## 6. What this does and does not establish

**Does:** (i) a faithful Consciousness-Hamiltonian feature block that **significantly
improves** unsupervised decoding **when mood is coupling-structured**; (ii) a
**closed-loop Mood-Amplifier proof-of-principle in simulation** with significant
efficacy, phase specificity, and target specificity; (iii) a satisfied **reachability
necessary-condition** on two live mice.

**Does not:** (i) show the principled block helps on *all* real data — it hurts the
mouse where simple features already win; (ii) show GILE-HEM dims help on their own;
(iii) show *feedback* beats open-loop; (iv) demonstrate any on-animal efficacy — that
requires a real closed loop, which recordings cannot provide.

## 7. Falsifiers (OPEN)

- **CH-A-F1** — the CH block's sim advantage is an artifact of the PAC-encoded
  generator; under a non-coupling latent it should vanish (predicted, untested here).
- **CH-A-F2** — across a larger live cohort the CH block does not beat matched baseline
  on average (mouse20 is currently evidence *for* this falsifier).
- **MA-B-F1** — closed-loop efficacy disappears under a generator whose mood is not
  phase-controllable (efficacy is conditional on controllability).
- **MA-B-F2** — feedback never beats equal-energy open-loop even under steep
  tolerance/over-stimulation costs (would make the "closed-loop" framing decorative).
- **REACH-F1** — in a broader cohort the positive-mood state is frequently an
  unreachable sink (would fail the necessary precondition).

$0 spent. No medical claim. Recorded data; no animal intervention performed.

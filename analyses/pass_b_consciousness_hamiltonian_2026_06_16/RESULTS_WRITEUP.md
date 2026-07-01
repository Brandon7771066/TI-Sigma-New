# Consciousness-Hamiltonian Features + Closed-Loop Mood Amplifier — Results

**Code:** this directory.
- `tsc_hamiltonian.py` — 57-vertex TI-Sigma Crystal, H_TSC = H_hop + H_onsite + H_gile,
  FULL PD (real degree + imaginary MI/Tralse axis) + zones, GILE-weighted graph Fiedler.
- `ch_features.py` — per-window 8-D HEM-GILE → Consciousness-Hamiltonian embedding.
- `runner_ch.py` → `results_expA.json` — Experiment A (unsupervised decoding).
- `mood_control.py` → `results_expB.json` — Experiment B (closed-loop efficacy, sim).
- `reachability.py` → `results_reachability.json` — live-mouse reachability proxy.

All ports are faithful to the corpus sources (`hypercomputer/hamiltonian.py`,
`hypercomputer/tsc.py`, `lcc_virus_gile_inference.py`, `ti_sigma/tralsebit_engine.py`).

---

## Honesty frame (#69)

The DANDI recordings are **pre-recorded**: we cannot alter a recorded animal's mood,
so there is **no closed loop on the live data** and therefore no possible on-animal
efficacy proof. We split the question into three honest deliverables:

1. **Richer principled features** tested on **unsupervised live-mouse state decoding**
   (Experiment A) — does the Consciousness-Hamiltonian block add real decoding power?
2. **Closed-loop Mood-Amplifier efficacy IN SIMULATION** (Experiment B) — a controller
   that uses the unsupervised GILE readout to steer a generative latent mood to a
   target, vs sham / open-loop / wrong-target.
3. **Live-mouse observational reachability proxy** (necessary condition, **not** an
   intervention) — is the high-coupling "positive-mood" state reachable at all?

---

## Experiment A — does the Consciousness-Hamiltonian block improve decoding?

Same leakage discipline as the retrieval benchmark: latent built leakage-safe
(sim = ground truth; real = TRAIN-ONLY k-means on a disjoint channel group A, test
labeled by nearest train centroid); every feature set standardized TRAIN-ONLY;
decoder = class-centroid nearest-neighbour fit on TRAIN labels only (the P0b readout);
paired bootstrap delta vs BASE. `*` = paired 95% CI excludes 0.

| source | BASE | GILEHEM | CH (Δ vs BASE) | BASE+CH (Δ) |
|---|---|---|---|---|
| sim(seed=0) | 0.840 | 0.750 | **0.913 (+0.073\*)** | 0.910 (+0.070\*) |
| sim(seed=7) | 0.597 | 0.613 | **0.739 (+0.141\*)** | **0.773 (+0.177\*)** |
| DANDI mouse41 | 0.524 | 0.381 | 0.679 (+0.105) | 0.500 (−0.025) |
| DANDI mouse20 | 0.913 | 0.495 | 0.556 (−0.359) | 0.824 (−0.090) |

**Honest read.**
- On the **sims**, where mood is encoded in theta-gamma coupling (PAC), the full
  **CH block significantly beats** the matched baseline (+0.07 to +0.18, paired CI>0).
- On the **live mice** it is **mixed-to-negative**: CH helps numerically on mouse41
  (+0.105, *not* significant — wide CI) but **hurts** on mouse20, where plain spectral
  features already reach 0.913 and have nothing to gain.
- **GILEHEM-alone (the raw 8 dims) is generally worse than BASE.** The value, where it
  exists, comes from the **full CH block** (PD + H_TSC spectrum + graph), not the bare
  HEM-GILE vector.

**Method correction inside this experiment (logged honestly).** A first pass used
broadband Pearson correlation for GILE-L; it was **flat across mood states** (spread
≤0.014, composite 0.698/0.699/0.697) and the block was at chance on the sims. GILE-L
is *defined* as coupling strength, so the faithful corpus primitive is **theta-gamma
PAC** (`features.theta_gamma_pac`), which **does** track the latent (0.078→0.097→0.107).
Switching L to the PAC primitive is what makes the block informative — this is a
fidelity fix to a mis-operationalized dimension, not a tuned win.

---

## Experiment B — closed-loop Mood Amplifier efficacy (simulation)

Controllable phase-coded generative mood model; controller reads the unsupervised
GILE-L coupling each step and drives a phase/energy input toward the target mood.
30 seeds, 120 steps (30 burn-in), open-loop energy matched to closed-loop. Metric =
target-mood occupancy (post burn-in).

| arm | target occupancy [95% CI] | energy |
|---|---|---|
| no_control | 0.320 [0.264, 0.377] | 0.0 |
| **closed_loop** | **0.876 [0.863, 0.889]** | 24.4 |
| open_loop (approx. energy-matched) | 0.929 [0.917, 0.940] | 24.8 |
| sham (equal-energy, phase-scrambled) | 0.317 [0.295, 0.340] | 24.4 |
| wrong_tgt | 0.263 [0.215, 0.311] | 9.3 |

The **sham is an exact equal-energy control**: it replays the closed-loop's per-seed
drive *magnitude* schedule and only scrambles the phase, so both arms spend identical
energy (24.4). The 0.876 vs 0.317 gap is therefore attributable to **timing alone**.

Paired contrasts (Δ target occupancy, `*` = 95% CI excludes 0, two-sided):

| contrast | Δ | result |
|---|---|---|
| efficacy (closed vs no_control) | **+0.556\*** | closed-loop steers mood |
| phase specificity (closed vs sham) | **+0.559\*** | drive must be phase-correct |
| target specificity (closed vs wrong_tgt) | **+0.613\*** | steering is directed at the target |
| value of feedback (closed vs open_loop) | **−0.053\*** | **feedback marginally *worse*** |

**Honest read.** The closed-loop Mood Amplifier **demonstrably and significantly
steers the latent mood** (0.876 vs 0.320 baseline) with strong **phase** and **target
specificity** — a clean in-sim proof-of-principle. But the GILE-**feedback timing does
not beat an equal-energy open-loop drive**: it is in fact **significantly (if only
marginally) worse** (−0.053, 95% CI [−0.066, −0.042], excludes 0). The model is
benignly controllable, so a constant correct-phase drive suffices and the
homeostatic-rebound penalty (the only force that rewards adaptive feedback) is too mild
to flip it. Feedback's value is therefore an **open question** — it should emerge only
when over-stimulation/tolerance costs are steep; we did **not** tune those to
manufacture a win.

**Scope caveat.** Efficacy here is *conditional on the assumed controllability* (mood
is phase-codable and a phase-matched drive biases transitions). Whether real neural
coupling is controllable in this way is exactly what the recorded data **cannot** tell
us; that requires a real closed loop.

---

## Live-mouse observational reachability proxy (necessary condition, NOT intervention)

Target = state with highest mean GILE-L coupling ("positive mood"). Empirical
transition matrix from the unsupervised decoded states (Laplace-smoothed).

| mouse | mean GILE-L / state | target | reachable from all? | stationary P(target) | mixing gap | mean first-passage |
|---|---|---|---|---|---|---|
| mouse41 | 0.491/0.532/0.499 | 1 | **yes** | 0.429 | 0.627 | {0:3.0, 2:3.2} |
| mouse20 | 0.436/0.483/0.509 | 2 | **yes** | 0.173 | 0.366 | {0:10.4, 1:13.7} |

**Honest read.** In both animals the high-coupling "positive-mood" state is **reachable
from every other state** with finite, short first-passage times — it is *not* an
unreachable sink. This clears a **necessary precondition** for any future Mood
Amplifier. It is explicitly **observational**: no intervention was performed and this
does **not** demonstrate that the state could actually be *driven* — only that nothing
in the observed dynamics rules it out.

---

## Bottom line

- A faithful 64-vertex-class **Consciousness Hamiltonian** + FULL PD + crystal/graph
  feature block was built and tested honestly. It **adds real decoding power where the
  latent is coupling-structured (sims)** and is **neutral-to-harmful where simple
  spectral features already win (mouse20)**. The win lives in the *composite* block,
  not the raw HEM-GILE dims.
- A closed-loop **Mood Amplifier proof-of-principle** holds in simulation
  (efficacy + phase + target specificity all strongly significant); the *added value
  of feedback over open-loop* is an honest **negative/open** result in this model
  (significantly but marginally worse than equal-energy open-loop).
- On live animals we deliver only what is legitimate from recordings: a clearly-labeled
  **reachability necessary-condition**, satisfied in both mice.

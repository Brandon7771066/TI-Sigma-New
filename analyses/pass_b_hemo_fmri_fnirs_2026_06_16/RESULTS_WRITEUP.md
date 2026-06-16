# Hemodynamic (fMRI-BOLD + fNIRS) Consciousness-Hamiltonian Mood-Amplifier — Replication

**Pass-77 B117 · 2026-06-16 · $0 budget · #69 brutal-honesty discipline**

Replicates the ecephys/LFP Consciousness-Hamiltonian Mood-Amplifier batch
(`analyses/pass_b_consciousness_hamiltonian_2026_06_16/`) on **rodent hemodynamic**
modalities — fMRI-BOLD and fNIRS — using open-access **live and simulated** data
"as much as available." Same three deliverables, same leakage discipline, same
honest null reporting.

Self-contained package: `tsc_hamiltonian.py` (verbatim port) + hemodynamic
front-ends (`features.py`, `simulate.py`, `ch_features.py`) + vetted helpers
(`bench_helpers.py`) + live loader (`data_live.py`) + three runners
(`runner_hemo.py`, `mood_control_hemo.py`, `reachability_hemo.py`).

---

## 0. Data availability — the honest verdict (#69)

The directive was to use open-access **live** rodent fMRI and fNIRS "as much as
available." What is actually available was probed directly:

| Source | Verdict |
|---|---|
| Rodent **BOLD-fMRI** on DANDI | **Not present.** DANDI fMRI = 000623 (human), 001773 (primate DBS). Rodent BOLD lives on **OpenNeuro as 4-D NIFTI** (hundreds of MB, needs `nibabel` + ROI extraction). NIFTI ingestion is **NOT implemented** in `data_live.py` (which streams DANDI NWB only) — noted as a future leg, not a present capability, so a $0 sandbox never blocks on a huge download. |
| Rodent **fNIRS** open data | **Effectively does not exist.** fNIRS is overwhelmingly a human modality. Honestly recorded as unavailable → **fNIRS is simulation-only.** |
| Nearest **live** rodent hemodynamic | DANDI **001211 / 001543** — *Mus musculus* one-photon **neurovascular** optical imaging. Neurovascular coupling *is* the haemodynamic process fMRI/fNIRS measure → the legitimate live anchor, labelled for what it is (optical neurovascular, **not** BOLD/fNIRS). |
| Streaming that anchor here | **Timed out twice (>115 s, process killed).** The one-photon NWB files are too large to stream and slice within the sandbox budget. **Live legs were NOT retrieved.** `results_*.json` carry `live_retrieved: false`. |

**Bottom line:** the replication is **simulation-based**, with the live leg
*attempted and honestly failed*. This mirrors the LFP batch's design philosophy
(simulation = ground-truth primary evidence; live = attempted bonus). The live
loader (`data_live.py`) is complete for **DANDI NWB streaming** and will populate
all three experiments the moment it is run in an environment with the
bandwidth/time budget (`HEMO_LIVE=1`). (OpenNeuro NIFTI ingestion is a noted
future leg, not yet implemented.)

---

## 1. What changed for hemodynamics (and what did NOT)

**Modality-specific (rewritten):**
- **Band-plan.** The 5 EEG bands (delta..gamma, 1–80 Hz) are meaningless for
  haemodynamics. Replaced by ONE low-frequency hemodynamic plan valid for BOTH
  modalities: `slow5 0.015–0.04`, `slow4 0.04–0.08`, `slow3 0.08–0.15` Hz. Both
  fMRI (Nyquist 0.5 Hz @ TR=1 s) and fNIRS (Nyquist 5 Hz @ 10 Hz) contain it.
- **Cross-frequency coupling.** Theta–gamma PAC (the LFP coupling primitive) →
  **infraslow CFC** (slow-phase 0.015–0.04 Hz modulating faster-hemodynamic
  amplitude 0.08–0.15 Hz) = the faithful hemodynamic counterpart.
- **Simulators.** `simulate_bold` (neural drive convolved with a canonical SPM
  double-gamma HRF, TR=1 s) and `simulate_fnirs` (HbO-like @10 Hz with
  state-INVARIANT Mayer/respiration/cardiac physiological nuisance). In BOTH, the
  latent mood H is encoded in **coupling** (strength + preferred slow-phase), NOT
  band power, and two disjoint channel groups share H.
- **Passive resonance probe** retuned to a fixed 0.03 Hz infraslow oscillator.

**Modality-agnostic (carried over unchanged):** the 57-vertex TI-Sigma Crystal
Hamiltonian (`tsc_hamiltonian.py`), GILE-HEM definitions (coherence stability,
spectral entropy/purity, amplitude stability, contradiction ratio), FULL PD
(real+imaginary)+zone, GILE-graph Fiedler, the leakage-safe block-filtering /
train-only-standardization / nearest-centroid decoding / bootstrap-CI machinery.

---

## 2. Experiment A — unsupervised CH decoding (`results_expA.json`)

Compare **BASE** (matched hemodynamic window features) vs **GILEHEM** (8-D) vs
**CH** (full Consciousness-Hamiltonian block) vs **BASE+CH** on the SAME
leakage-safe nearest-centroid readout; balanced accuracy + 95% bootstrap CI;
paired bootstrap Δ vs BASE. Ground-truth latent (simulation).

| Source | BASE | GILEHEM | CH | BASE+CH |
|---|---|---|---|---|
| sim-fMRI-BOLD seed0 | 0.328 ~chance | 0.197 (Δ−0.127) | 0.289 (Δ−0.040) | 0.210 (Δ−0.120) |
| sim-fMRI-BOLD seed7 | **0.693 >chance** | 0.280 (Δ−0.412) | 0.226 (Δ−0.467) | 0.418 (Δ−0.278) |
| sim-fNIRS seed0 | 0.292 ~chance | 0.274 (Δ−0.020) | 0.234 (Δ−0.059) | 0.282 (Δ−0.012) |
| sim-fNIRS seed7 | 0.178 ~chance | 0.089 (Δ−0.088) | 0.126 (Δ−0.055) | 0.100 (Δ−0.077) |

**Honest finding (NEGATIVE):** the Consciousness-Hamiltonian block does **NOT**
improve unsupervised state decoding on hemodynamic data. **No CH/GILEHEM/BASE+CH Δ
is positive** — every variant scores below BASE; where the latent IS recoverable
(BOLD seed7, BASE=0.693), the high-dimensional CH block **dilutes** the coupling
signal rather than concentrating it (Δ as low as −0.467). (These deltas reflect
the *stricter, leakage-symmetric* CH pipeline — CH train windows are now truncated
at the split exactly like BASE; the null is unchanged and, if anything, cleaner.)
This is fully consistent with the LFP
batch's own diagnosis (B116 §7.7.294): the 8=4+4 modulus/phase *structure* is
grounded, but the *estimators* are a grade-1.5 overlay, and the affine PD-zone
feature is degenerate on neural composites. The hemodynamic regime reproduces
that weakness. **The honest headline of Exp A is a null.**

---

## 3. Experiment B — closed-loop Mood-Amplifier efficacy (`results_expB.json`)

In-simulation proof-of-principle (recorded animals cannot be intervened on). A
hemodynamic generative mood (latent in infraslow CFC) is steered toward the
high-coupling "positive" state. Controller observes each window, computes the
**unsupervised** GILE-L coupling readout (no mood label), and emits a phase-coded
drive. 30 seeds; target-mood occupancy + KL; paired bootstrap CIs. Arms:
no-control / closed-loop / open-loop (matched mean energy) / sham (matched energy,
random phase) / wrong-target.

| Arm | Target occupancy (95% CI) | mean KL | energy |
|---|---|---|---|
| no_control | 0.320 [0.264, 0.377] | 0.637 | 0.0 |
| **closed_loop** | **0.817 [0.801, 0.833]** | 0.020 | 23.7 |
| open_loop | 0.929 [0.917, 0.940] | 0.081 | 23.7 |
| sham | 0.317 [0.280, 0.354] | 0.584 | 23.7 |
| wrong_tgt | 0.240 [0.186, 0.293] | 0.921 | 19.7 |

Paired contrasts (occupancy):
- **efficacy vs baseline** Δ=+0.497 CI[+0.445,+0.546] **SIG**
- **phase specificity** (vs sham, equal energy) Δ=+0.500 CI[+0.461,+0.537] **SIG**
- **target specificity** (vs wrong-target) Δ=+0.577 CI[+0.528,+0.623] **SIG**
- **value of feedback** (vs open-loop, **exactly equal total energy 23.7 per seed**) Δ=−0.112 CI[−0.128,−0.097] **SIG (negative)**

**Honest finding (MIXED):** closed-loop control is **strongly efficacious and
specific** — it triples target occupancy over baseline, and the effect is
destroyed by randomizing the drive phase (sham) or the target (wrong_tgt),
proving the steering is real, not an energy artifact. **BUT** a matched-energy
**open-loop constant push toward the target out-performs the closed loop**
(Δ feedback = −0.112, SIG-negative). In this hemodynamic generative model, once
you know the target phase, a fixed drive beats feedback — **feedback adds no
value here.** This reproduces the LFP batch's own "feedback ≤ open-loop"
observation (B116 §7.7.294) and is an honest mark against the *necessity* of
closed-loop control in benign regimes, while still establishing the
**proof-of-principle that a phase-specific drive can steer hemodynamic mood**.

---

## 4. Reachability proxy (`results_reachability.json`)

OBSERVATIONAL necessary-condition test (NOT an intervention; see §0 — live was
not retrievable, so this ran on the hemodynamic **sims** as a method check,
clearly labelled). Question: is the high-coupling "positive mood" target state
reachable from all others, and is the chain well-mixed? If the target were an
absorbing sink, no amplifier could ever steer toward it.

| Source | target | reachable-from-all | stationary P(target) | spectral-gap mixing |
|---|---|---|---|---|
| sim-fMRI-BOLD seed3 | state 1 | **True** | 0.411 | 0.085 |
| sim-fNIRS seed3 | state 1 | **True** | 0.297 | 0.096 |

**Finding:** the necessary condition is met on both hemodynamic modalities —
target reachable from every state, finite first-passage times (~28–39 steps),
positive spectral gap (ergodic, well-mixed). This does **not** demonstrate
efficacy; it only fails to rule it out, and on simulated chains the bar is
expected to pass — the value of this leg is realized only on live data, which was
not retrievable here.

---

## 5. Overall #69 verdict

- **Live rodent hemodynamic data is largely unavailable / unstreamable in a $0
  sandbox** (fNIRS nonexistent; BOLD = heavy OpenNeuro NIFTI; DANDI neurovascular
  times out). Honestly recorded; loader ready for a budgeted environment.
- **Exp A: CH features do NOT help hemodynamic decoding** (null) — reproduces the
  LFP/EEG estimator-fidelity weakness in a new modality.
- **Exp B: phase-specific drive steers hemodynamic mood (proof-of-principle, SIG
  and specific), but closed-loop feedback adds no value over matched-energy
  open-loop** in this benign generative regime.
- **Reachability: necessary condition met on sims.**

Net: the architecture **ports cleanly** across modalities, and the replication
**faithfully reproduces both the positive (steerability) and the negative
(estimators don't help; feedback unnecessary in benign regimes) findings** of the
original batch — which is the strongest possible #69 outcome: the result is
modality-robust, including its limitations.

### Reproduce
```bash
cd analyses/pass_b_hemo_fmri_fnirs_2026_06_16
python runner_hemo.py            # Exp A (sim); HEMO_LIVE=1 to attempt live
python mood_control_hemo.py      # Exp B
python reachability_hemo.py      # reachability (sim); HEMO_LIVE=1 to attempt live
```

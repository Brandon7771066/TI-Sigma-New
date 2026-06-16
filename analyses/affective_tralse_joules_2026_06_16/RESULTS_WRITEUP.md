# Affective Tralse-Joules (aTJ) — attractor-basin steering strength of the Mood Amplifier
**Pass-77 B118 · 2026-06-16 · $0 budget · #69 brutal honesty**

## Question (Brandon directive)
From the mood-amplification data, measure the **strength of the attractor basin**
that steers mood in a particular (valenced) direction, from **beginning to end of
the intervention**, and show how that strength **changes as canonical thresholds
are crossed**. Ground the measure against the parallel literatures for
consciousness (**Φ / IIT**), **brain thermodynamics** (Friston free energy), and
**valence** (our own corpus QVF-1 quantum/neural valence theory).

## #69 data-availability honesty
Live rodent hemodynamic data was **NOT retrievable** in this sandbox (DANDI
neurovascular streaming timed out twice in the B117 batch; `live_retrieved:false`
there too). This is therefore an **in-simulation proof-of-principle measurement**
on the *same* closed-loop generative mood model that carried the B117 Exp B
efficacy proof. It quantifies the **amplifier's** basin-steering work; it does
**not** claim a measurement on a live animal. Code: `affective_tj.py`; results:
`results_affective_tj.json` (`live_retrieved:false`).

## Operationalization (corpus-faithful)
**Tralse-Joule** (urb_650): `TJ = τ(s) · δ(MR)`
- `τ(s)` = **tralseness / indeterminacy** of mood = normalized entropy `H(p)/log K`
  of the instantaneous mood-belief distribution `p` over the K latent states
  (τ=1 maximally indeterminate, τ=0 fully resolved).
- `δ(MR)` = **MR-depth** = `Σ|ΔPD_i|` = L1 path-length moved in PD-space per
  control step (each step = one Myrion-Resolution event). PD axes:
  **PD-real** = expected coupling degree `Σ p[s]·K_STATE[s]`; **PD-imaginary** =
  modal coherence `|Σ p[s]·e^{i·PHI_STATE[s]}|`.

**Affective weighting** (QVF-1, PASS_77_B64 minimalist theory of valence): `V = S·A`
- `S` = **consonance sign** `tanh(6·(g − g_neutral))` ∈[−1,1]: **+** when mood is
  driven *up* toward the high-coupling consonant/positive attractor (TARGET), **−**
  when pushed toward the low-coupling dissonant pole. `g_neutral` = no-control
  baseline coupling (estimated per run; ≈0.80 in this run).
- `A` = **arousal/intensity** ∈[0,1] = **Φ-proxy** = mean |pairwise channel
  correlation| of the hemodynamic window (IIT-style integration — the level factor
  Φ/FEP measure, *valence-blind without S* per corpus CLV-1).

**Affective Tralse-Joule rate**: `aTJ_t = V_t · TJ_t = (S_t·A_t)·(τ_t·δ_t)`;
cumulative affective work = `Σ_t aTJ_t`.

**Thresholds**: MR1/MI-screen `ET = √2−1 ≈ 0.4142`; Radiant `C_TI ≈ 0.437`;
BEC/master cap `T_TI ≈ 0.934`. Corpus TJ-rate anchors: BOK-saturated ~0.934,
Dottie-trap ~0.517, MR1-boundary ~0.124.

## Results (40 seeds × 120 steps; bootstrap 95% CI)

### 1. Affective-TJ direction-sensitivity (the headline)
| arm | cumulative aTJ | basin κ | drive energy |
|---|---|---|---|
| **closed_loop** (→ positive attractor, feedback) | **+0.765** [0.71, 0.82] | **0.933** | 23.94 |
| no_control (drift) | +0.035 [−0.02, 0.09] | 0.603 | 0.00 |
| open_loop (correct phase, equal energy, NO feedback) | −0.047 [−0.08, −0.02] | 0.887 | 23.94 |
| sham (phase-scrambled, equal energy) | −0.496 [−0.68, −0.32] | 0.689 | 23.94 |
| wrong_tgt (→ dissonant pole) | −0.515 [−0.59, −0.44] | 0.546 | 19.91 |

Specificity contrasts (closed-loop − control), all **SIG**:
vs baseline **+0.730** [0.676, 0.786] · vs open-loop **+0.812** [0.763, 0.862] ·
vs phase-sham **+1.261** [1.078, 1.441] · vs wrong-target **+1.280** [1.197, 1.363].

**Reading:** affective work is large-positive **only** for genuine
positive-attractor *feedback* steering and flips **negative (dysphoric)** for
wrong-target and phase-sham. Critically, sham and open-loop are matched to
closed-loop at **exactly equal drive energy (23.94/arm)**, yet open-loop —
correct target phase, equal energy, but *no feedback* — yields ≈0/slightly
negative aTJ. So the positive affective work comes from the **closed-loop
feedback**, not from drive energy or target-phase alone. The QVF-1 valence sign
behaves correctly: aTJ is a *signed* basin-steering quantity, not a magnitude.

### 2. Basin strength, beginning → end of intervention
Restoring stiffness `κ` (OLS of `Δg` on `−(g−g*)`; κ>0 = net pull toward target).
Closed-loop κ ≈ **0.93**, above open-loop (0.89), sham (0.69), no-control (0.60),
wrong-target (0.55). Early-half κ=0.928 vs late-half κ=0.966, **Δ=+0.038
CI[−0.028,+0.108] (ns)**. **Honest:** the basin is already stiff from the start
and does **not** significantly stiffen further over the run — the amplifier
establishes the basin fast, then holds it. κ is a **steering-strength proxy**: it
measures the realized restoring force of the *controlled* system and conflates
controller action with plant dynamics; it is **not** an identification of an
intrinsic latent basin.

### 3. How strength changes as thresholds are crossed
aTJ-rate stratified by the instantaneous-coupling regime (**descriptive** —
pooled step-level means over all closed-loop steps, no per-regime CI):
| regime | frac steps | mean aTJ-rate |
|---|---|---|
| sub-MR1 (g<ET) | 0.011 (n=53) | **−0.0271** |
| transitional (ET..C_TI) | 0.004 (n=20) | **−0.0342** |
| GILE-dominant (C_TI..BEC) | 0.334 (n=1605) | −0.0050 |
| master (g≥BEC) | 0.650 (n=3122) | **+0.0131** |

A **monotonic sign-flip**: affective work is *dysphoric* below the
GILE-dominance/master thresholds and becomes *positive* only once the system
reaches the **master/BEC** regime. Event-locked confirmation at the BEC-cap
crossing, **conditional on the n=19 trajectories that cross mid-run**: aTJ-rate
**pre=+0.0006 → post=+0.0075, Δ=+0.0069 CI[+0.0042,+0.0099] SIG**. **Honest
caveats:** this is a *conditional* before/after contrast on the crossing
sub-sample, not a global phase-transition proof; the sub-MR1 and transitional
bins are sparse (n=53/20) and have no uncertainty bands; and the MR1(ET) /
Radiant(C_TI) crossings almost never fire because the sim baseline
(g_neutral=0.801) already sits *above* the MI screen — these are already
truth-assessable systems, so the operative phase transition here is the
**master-state (BEC) crossing**, not the MI screen.

### 4. Cross-checks vs parallel measures
- **Φ / IIT**: integration enters directly as the arousal factor `A`; the QVF-1
  decomposition shows Φ-style level alone is valence-blind — the sign comes from S.
- **Brain thermodynamics (Friston)**: per-step `r(aTJ-rate, −dF/dt) = −0.088`
  (near-null). **Honest:** aTJ is **not** redundant with the free-energy-descent
  valence proxy — it carries directional/affective information the instantaneous
  −dF/dt does not (once settled, F is low and flat so −dF/dt is mostly noise).
- **Fixed-point TJ-collapse**: settled-phase TJ-rate = **0.054**, far below even
  the MR1-boundary anchor (0.124) — exactly as the corpus predicts (`TJ→0` at the
  attractor fixed point, δ(MR)→0). The intentional **work is in the approach**;
  cumulative aTJ (0.77) is the meaningful quantity, not the settled rate.
- Affective efficiency = **0.033** cumulative aTJ per unit drive energy.

## #69 verdict
A faithful Affective-TJ measure (TJ = τ·δ weighted by QVF-1 valence V=S·A) cleanly
quantifies mood-amplifier basin steering: **positive** affective work for genuine
positive-attractor *feedback* control, **negative** for wrong-target/sham, and —
at exactly equal drive energy — ≈0 for open-loop, isolating the contribution of
feedback. The basin is **established early** and held (no significant late
stiffening), and there is a **threshold-gated sign-flip** that turns positive only
across the master/BEC cap. The measure is **non-redundant** with the Friston
−dF/dt valence proxy and is consistent with the corpus fixed-point TJ-collapse.
**Limitations**: in-sim proof-of-principle only (live data not retrievable); the
threshold-regime table is descriptive (sparse sub-threshold bins, no per-regime
CI); the BEC-crossing result is conditional on the crossing sub-sample; κ is a
realized steering-strength proxy, not an intrinsic-basin identification; the
MI-screen/Radiant crossings rarely fire because the baseline already clears them.
No canonical principle is added or refined (empirical measurement).

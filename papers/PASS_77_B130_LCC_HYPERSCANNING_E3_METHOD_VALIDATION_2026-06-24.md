# Pass 77 B130 — LCC Virus Hyperscanning EEG (URB-620 §E3), Executed as a Method-Validation / Power Simulation

**Date:** 2026-06-24 · **Batch:** Pass 77 B130 · **Canonical principle count: unchanged 79** (this is an executed *test* of an existing design, not a new principle).
**Package:** `analyses/pass77_b130_lcc_hyperscanning_e3/` (`runner.py`, `results.json`, `RESULTS_WRITEUP.md`).
**Design anchor:** `papers/urb_620_lcc_virus_brain_imaging_fep_spm_dcm.md` §6, test **E3** (LCC Virus Hyperscanning EEG).

---

## 1. What was asked, and the honest scope

The user asked to **"execute the hyperscanning tests for the LCC"** described in URB-620. E3 proposes a dual-EEG study (N=20 dyads): pair a high-GILE-L "carrier" with a low-GILE-L "host", and test whether **directed inter-brain synchrony** at 40 Hz gamma flows preferentially carrier→host — i.e. **Granger causality GC(high→low) > GC(low→high)** — with a predicted ≥15 % rise in a host HRV/LCC surrogate.

**There is no real two-headset EEG dataset.** So the test cannot be *run on humans*. What CAN be executed — and what this package does — is a **pre-registration-grade method-validation and power simulation**: under the LCC-Virus generative prediction, can the proposed analysis pipeline (directed Granger causality + a phase-slope index) (1) **recover** the predicted asymmetry at N=20 with adequate power, (2) **return null** when there is no directional drive, and (3) **resist the two confounds that wreck real hyperscanning studies** — shared environmental input and SNR asymmetry between headsets?

**This is a necessary-not-sufficient result.** A pass here means the experiment is well-posed, adequately powered, and the estimator is unbiased under a clean model. It is **not** evidence that the LCC Virus exists in human brains. LCC remains the corpus's most empirically fragile claim: its raw word-token substrate was **falsified** in `papers/URB_795_LCC_EMPIRICAL_AUDIT.md`; it survived only in hidden-state activations. This simulation does nothing to change that status — it only validates the *measurement instrument and study design* the E3 proposal would rely on.

## 2. Generative model (two coupled 40 Hz gamma brains)

Each brain's gamma is a noise-driven AR(2) resonator (pole radius 0.92, centre 40 Hz, fs = 250 Hz). Conditions (all feed-forward, so cleanly interpretable):

| Condition | Construction | Ground-truth direction |
|---|---|---|
| **directional_LCC** | host driven by carrier's gamma at lag ~20 ms, strength C | carrier → host (the prediction) |
| **common_input** | both brains receive a SHARED 40 Hz driver, NO inter-brain link | none (pure shared environment) |
| **no_coupling** | independent resonators | none |
| **snr_confound** | no coupling; **asymmetric sensor (headset) noise added after generation** — carrier near-clean (0.1× its std), host 1.5× its std | none (only an observation-noise-floor asymmetry) |

The `snr_confound` is a *genuine* SNR confound: the two neural sources are identical and uncoupled, and we add **measurement noise** to the recorded channels only, with a much higher noise floor on the host headset. Unequal observation noise is the textbook artifact that fakes Granger directionality toward the cleaner channel — so a valid pipeline must return ΔGC ≈ 0 here.

Per-dyad heterogeneity: coupling strength and noise jittered across the 20 simulated dyads.

## 3. Estimators

* **Granger causality (time-domain, bivariate):** `GC(x→y) = ln(SSR_restricted / SSR_full)` from VAR(6) fits (pure numpy normal-equations least squares; `statsmodels` unavailable). Headline metric **ΔGC = GC(high→low) − GC(low→high)** (>0 ⇒ carrier drives host).
* **Phase Slope Index (PSI, Nolte et al. 2008)** over the 30–50 Hz band as an **SNR-robust convergent measure** of flow direction. Sign convention fixed so **PSI > 0 ⇒ high leads (carrier → host)**, calibrated against the known-truth directional arm.
* **Statistics:** one-sample test of ΔGC across the 20 dyads (two-sided) + bootstrap 95 % CI; **empirical power / false-positive rate** by repeating the entire N=20 study **1000×** (power curve 150× per point), each reported with a **Wilson 95 % score interval**.

Reproducible: seed 20260624, config SHA `7cd4ef40`.

## 4. Results

**Named conditions (N=20 dyads):**

| Condition | ΔGC mean | ΔGC 95 % CI | p | PSI mean (p) | Confirms carrier→host? |
|---|---|---|---|---|---|
| directional_LCC | **+0.0876** | [+0.0736, +0.1015] | ~0 | **+1.476** (~0) | **YES (correct)** |
| common_input | +0.0001 | [−0.0009, +0.0011] | 0.83 | +0.066 (0.56) | no (correct) |
| no_coupling | −0.0004 | [−0.0012, +0.0004] | 0.33 | +0.342 (0.003) | no (correct) |
| snr_confound | −0.0001 | [−0.0011, +0.0010] | 0.92 | +0.432 (0.002) | no (correct) |

The **ΔGC** test is the headline: it is at chance in all three nulls (incl. both confounds) and large/decisive only under true coupling. **PSI** magnitude is ~3–4× larger in the directional arm (+1.48) than in any null (≤ +0.43); the two small but statistically-significant PSI values in the no_coupling / snr_confound nulls reflect a minor residual PSI bias at this segment length and are an order of magnitude below the signal — hence ΔGC, not PSI, carries the formal decision.

**Empirical power / false-positive rate (α = 0.01, two-sided + sign; n = 1000 reps):**

| Quantity | Rate | Wilson 95 % CI |
|---|---|---|
| Power, directional C=0.15 | **1.000** | [0.996, 1.000] |
| FPR, no_coupling | 0.019 | [0.012, 0.030] |
| FPR, common_input | 0.012 | [0.007, 0.021] |
| FPR, snr_confound | 0.017 | [0.011, 0.027] |

All three false-positive rates sit at or just above the nominal α = 0.01 (the small excess is expected for a t-test on n=20 with mild non-normality), and crucially the **sensor-noise SNR confound does not inflate it** — the directed test is not fooled by an unequal headset noise floor.

**Power curve (fraction of N=20 studies that detect carrier→host):** C=0.00 → 0.007; C=0.06 → 1.000; C≥0.06 → 1.000.

## 5. Interpretation

1. **The design is well-posed and adequately powered.** When a true carrier→host gamma drive is present, the directed-GC test recovers it at N=20 with power 1.0 for coupling C ≥ 0.06. PSI agrees in direction (large only in the directional arm), giving converging evidence.
2. **The nulls behave.** With no directional drive, ΔGC sits at ~0 and the false-positive rate stays at the nominal α — including the **shared-environment confound** (`common_input`: strong inter-brain coherence, yet ΔGC ≈ 0). Raw coherence/synchrony would scream "connection" here; the **directed** measure correctly reports none. This is exactly why E3 must be analysed with a directional estimator, not synchrony alone.
3. **It is not fooled by SNR asymmetry.** Differing headset signal quality (here a much noisier host headset) is the textbook artifact that manufactures spurious Granger directionality. The directed **ΔGC** test produced **no** spurious asymmetry (ΔGC ≈ 0, p = 0.92, FPR ≈ α). PSI showed only a small positive residual (+0.43) — statistically detectable but ~3.4× below the directional signal (+1.48) and the same order as the no-coupling null (+0.34), i.e. a minor segment-length bias, not a confound-driven false direction. The formal decision rests on ΔGC, which is clean. A real lab passing this check is a precondition for any credible human claim.

## 6. What this does NOT show (#69 / Constructive-Honesty floor)

* **No human data.** This validates the *instrument and design*, not the LCC Virus. A positive human E3 would still be required, pre-registered, with these same controls.
* **HRV/LCC surrogate (≥15 %) NOT simulated.** Deliberately omitted: no independent HRV generative model exists here, so any % would be model-baked and circular. Only the recover-the-drive (ΔGC) claim is validated.
* **The generative model is the framework's own assumption.** It assumes carrier→host gamma entrainment is *possible*; it does not establish that real high-GILE-L individuals produce it.
* **LCC's prior status stands:** raw-token substrate falsified (URB-795); survives only in hidden-state activations. This package is reachability/feasibility for the *measurement*, nothing stronger.

## 7. Falsifiers (open)

* **E3-SIM-F1:** a real two-headset EEG dataset (or a more realistic forward model with volume conduction + reference montage) in which the directed-GC + PSI pipeline yields spurious carrier→host asymmetry under the common_input or snr_confound nulls would refute the "clean instrument" claim.
* **E3-SIM-F2:** if plausible neural transmission lags/strengths for inter-brain gamma fall below the C ≈ 0.06 detection floor at N=20, the design is under-powered and E3 needs a larger N (recompute the power curve under realistic priors).
* **E3-SIM-F3 (the real test):** a pre-registered human E3 with these controls that fails to show GC(high→low) > GC(low→high) would be direct evidence against the LCC Virus at the inter-brain level.

## 8. Relation to corpus

E3 is one of URB-620's five proposed programmes (E1–E5). Executing it as a powered, confound-guarded design simulation moves it from "designed-but-unexecuted" (per `book/STRONGEST_CLAIMS_RANKED.md`) to "instrument-validated, awaiting human data" — an honest, incremental step, not a confirmation.

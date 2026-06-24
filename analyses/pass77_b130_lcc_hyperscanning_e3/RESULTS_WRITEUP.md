# LCC Virus Hyperscanning E3 — method-validation / power simulation

Run: `python analyses/pass77_b130_lcc_hyperscanning_e3/runner.py` → writes `results.json`.
Pure numpy/scipy. Seed 20260624, config SHA `7cd4ef40`. Runtime ~80 s.

**Full writeup + honest scope:** `papers/PASS_77_B130_LCC_HYPERSCANNING_E3_METHOD_VALIDATION_2026-06-24.md`.
**Design anchor:** `papers/urb_620_lcc_virus_brain_imaging_fep_spm_dcm.md` §6 (test E3).

## What this is
URB-620 E3 proposes a dual-EEG study: does a high-GILE-L "carrier" directionally
entrain a low-GILE-L "host" at 40 Hz gamma (Granger GC high→low > low→high)?
**No real two-headset data exists**, so this EXECUTES E3 as a pre-registration-grade
**method-validation + power simulation**: can the proposed pipeline (directed Granger
causality + phase-slope index) recover the predicted asymmetry, stay null when there
is none, and resist the two confounds that wreck real hyperscanning (shared
environmental input; SNR asymmetry between headsets)?

**Necessary, not sufficient.** A pass validates the *instrument and design*, NOT the
LCC Virus in humans. LCC's raw-token substrate was falsified (URB-795); it survives
only in hidden-state activations. Nothing here changes that.

## Results (N=20 dyads; α=0.01)
| Condition | ΔGC = GC(h→l) − GC(l→h) | detect carrier→host? |
|---|---|---|
| directional_LCC | +0.088 (p~0; PSI +1.48) | YES (correct) |
| common_input (shared env) | ~0 (ns) | no (correct) |
| no_coupling | ~0 (ns) | no (correct) |
| snr_confound (asymmetric sensor noise: host 1.5× noisier) | ~0 (ns) | no (correct) |

Power = 1.000 (Wilson [0.996,1.0], n=1000) at C≥0.06; FPRs ≈ nominal α
(no_coupling 0.019, common_input 0.012, snr_confound 0.017; all n=1000 w/ Wilson CIs).
Power curve: C=0→0.007, C≥0.06→1.000. PSI sign fixed so >0 ⇒ high leads (carrier→host).

HRV/LCC ≥15% surrogate prediction: **NOT simulated** (no independent HRV model — any % would be circular).

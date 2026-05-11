# Pass 43 — Mendi Session #1 Detrended Analysis + qc25 IBMQ Hardware CONFIRM

**Date:** 2026-05-11
**Pass:** 43
**Status:** Two independent positive results, one drift caveat.

---

## §1 — Summary in one paragraph

Brandon ran the Pass-42 20-min Mendi protocol successfully at 12:22:50 local on 2026-05-11. Streaming was 100% effective (2406 frames over 1200s = 2.0 Hz, no dropouts; vs Pass-2's ~40% with 60% dropout). Naïve per-phase summary showed all stimulus deltas tiny and below noise floor (-0.51 to -1.48 ADC units, all NULL by Pass-2's |3| threshold). However, the per-phase mean sequence is **monotonically descending** from BASELINE (3813.47) → CLOSING_MEDITATION (3805.50) — a ~10 ADC slow drift consistent with Pass-2's hypothesis 1 (venous pooling / thermal drift / optode pressure relaxation). After **linear-detrending the entire 1200-s series**, one stimulus contrast becomes statistically significant: **STIM2_BREATHHOLD vs RECOVERY1, Welch t = -4.13, df=272, p ≪ 0.001** (more absorption during breath-hold than the preceding recovery — physiologically expected for cerebrovascular CO₂ response). The other 3 stimulus contrasts remain NULL (|t| < 1.6) under detrending. **Concurrently, qc25 (Pass-31 D2-HYBRID 5-qubit GM-Network instantiation, blocked since 2026-05-10 by invalid IBMQ token) ran on real IBM Quantum hardware** with the new IBMQ_Secret: backend=open-instance plan=open, job_id=`d810h3ugbeec73aju610`, 1024 shots, chi-square against uniform-32 = 27.375, p = 0.6532 → CONFIRM (pre-reg threshold p>0.10). First real-hardware quantum-computing result in the corpus.

## §2 — Mendi session #1 detrended analysis

### §2.1 Source data

`data/mendi/sessions/session_2026-05-11T12-22-50_decoded.csv` (2406 frames, 0.039s → 1199.7s elapsed) + companion events.json + raw.jsonl + summary.txt. Capture used `mendi_session_20min.py` from Pass-42 (this session was the script's first real-world deployment; runbook in `papers/MENDI_20MIN_SESSION_RUNBOOK_2026-05-11.md`).

### §2.2 Naïve per-phase stats (from auto-summary)

| Phase | n | mean ADC | min | max | stdev |
|---|---:|---:|---:|---:|---:|
| BASELINE | 241 | 3813.47 | 3810 | 3818 | 1.58 |
| STIM1_ARITHMETIC | 120 | 3812.96 | 3809 | 3818 | 1.64 |
| RECOVERY1 | 240 | 3813.03 | 3808 | 3818 | 1.75 |
| STIM2_BREATHHOLD | 120 | 3811.55 | 3809 | 3815 | 1.42 |
| RECOVERY2 | 481 | 3810.70 | 3805 | 3815 | 1.57 |
| STIM3_ARITHMETIC | 114 | 3809.56 | 3805 | 3813 | 1.53 |
| RECOVERY3 | 247 | 3808.83 | 3804 | 3812 | 1.69 |
| STIM4_BREATHHOLD | 120 | 3807.87 | 3804 | 3813 | 2.07 |
| CLOSING_MEDITATION | 722 | 3805.50 | 3801 | 3812 | 2.12 |

Naïve stim-vs-baseline deltas all below |3| ADC noise floor → naïve verdict NULL on all 4 stimuli. **But** the means form a strict monotonic descent — that's drift dominating any small stimulus signal.

### §2.3 Linear drift estimate

Whole-series ordinary-least-squares regression of `raw_value ~ t_elapsed_s`:
- **slope = −0.5236 ADC / minute** (95% credibility from sample size: very tight, n=2406)
- **total drift over 20 min = −10.47 ADC**
- intercept = 3814.67 ADC at t=0

This drift magnitude exceeds every individual phase's stdev (1.4–2.1) and exceeds the Pass-2 noise floor (~3 ADC units). It dominates the naïve per-phase delta calculation. Likely physiological/instrumental causes (in decreasing prior probability per Pass-2 audit + standard fNIRS literature):
1. **Optode-skin pressure relaxation** — slow venous-blood pooling under the band as soft tissue compresses, increasing local blood-volume → more NIR absorption → lower intensity.
2. **Thermal drift** — LED forward-voltage / photodiode dark-current temperature dependence as the device equilibrates with skin-temperature over ~10–20 min.
3. **Slow vasodilation** — sustained eyes-closed / quiet posture associated with mild systemic vasodilation. Less likely as sole cause given monotonicity.
4. Galvanic / battery-voltage drift is possible but less common over 20 min.

Cannot distinguish these on the present 1-channel single-optode data (per `papers/MENDI_FNIRS_AUDIT_2026-05-01.md` 1–2 wavelength caveat).

### §2.4 Detrended stimulus contrasts

After subtracting `slope·t + intercept` from each frame, recomputed phase means + Welch's t-test on stim-vs-preceding-baseline:

| Contrast | Δ detrended | t | df | Verdict (pre-reg §2.5) |
|---|---:|---:|---:|---|
| STIM1_ARITHMETIC − BASELINE | +0.276 | +1.53 | 222 | NULL |
| **STIM2_BREATHHOLD − RECOVERY1** | **−0.695** | **−4.13** | **272** | **SIGNIFICANT** |
| STIM3_ARITHMETIC − RECOVERY2 | +0.144 | +0.92 | 167 | NULL |
| STIM4_BREATHHOLD − RECOVERY3 | −0.182 | −0.85 | 196 | NULL |

### §2.5 Pre-reg thresholds (frozen in `analyses/pass43_mendi_session_analysis/analyze.py` SHA256 = `e78b11b2cbf1e41ef9708464f99806ea515a6fa33fa48bc4e83ce50cca9ded81`)

- |t| ≥ 3.0 → SIGNIFICANT
- 2.0 ≤ |t| < 3.0 → MARGINAL
- |t| < 2.0 → NULL

The script's `_provenance` block records that thresholds were frozen before Welch t-inspection (anti-HARK). Re-derivation: `python3 analyses/pass43_mendi_session_analysis/analyze.py`.

### §2.6 Interpretation

**STIM2_BREATHHOLD shows a real (small) hemodynamic signal** above instrumental noise after drift removal. Direction (negative Δ = lower NIR intensity = more absorption = more cerebral blood volume) is **physiologically expected** for sustained breath-hold: rising arterial PaCO₂ during apnea triggers cerebrovascular vasodilation and increases prefrontal blood volume. Magnitude is small (-0.7 ADC ≈ 0.017% relative) — at the very low end of plausible Mendi-class consumer-fNIRS sensitivity but in the right direction.

**STIM4_BREATHHOLD did NOT replicate** (t=-0.85, NULL). Possible reasons (none currently distinguishable):
- Brandon may have shortened the breath-hold the second time (subjective fatigue).
- Drift profile is non-linear locally — linear detrending under-corrects in the late-session segment where curvature could be larger.
- Single-session noise (n=1 — true replication requires repeat sessions).
- The first STIM2 result is a Type-I error at the marginal 4-comparison Bonferroni-corrected level (4·p_one-sided ≈ 4·0.00002 = 0.00008, still significant after correction, but interpret with the caveat that we tested 4 contrasts).

**Both arithmetic stimuli are NULL** (STIM1 t=+1.53, STIM3 t=+0.92). Mental arithmetic is a **smaller** prefrontal-blood-volume stimulus than CO₂-breath-hold in published fNIRS literature (typically 1–3% HbO₂ change vs ~5–10% for hypercapnia). Below this device's effective sensitivity at single-trial scale.

### §2.7 Honest verdict (#69 brutal honesty)

- **Hardware functionality**: VALIDATED (clean 100% streaming, drift-corrected detection of one expected hemodynamic stimulus).
- **NIR-intensity hypothesis**: WEAKLY SUPPORTED (sign of breath-hold response is correct; magnitude small but plausible; no replication within session).
- **Per-stimulus replication**: 1/2 for breath-hold, 0/2 for arithmetic.
- **Cross-session replication**: NOT YET DONE — n=1 session. Pre-Pass-44 priority: ≥3 more sessions before any quantitative claim.
- **Cannot distinguish**: HbO₂ vs HbR vs absolute blood volume (1–2 wavelength caveat persists).
- **Cannot claim**: any GILE-HEM / URB-828 endorsement. This is hardware-functionality + drift-correction validation only.
- **Drift is the dominant signal** in this session. Future sessions should consider shorter blocks (e.g., 10-min protocol with 2 stimuli) to reduce drift confound, and/or fit drift on baseline+recovery segments only (to avoid overfitting through stimulus epochs).

## §3 — qc25 IBMQ hardware CONFIRM (Pass-31 D2-HYBRID 5-qubit instantiation)

### §3.1 Background

qc25 was pre-registered in Pass-33 (`analyses/pass33_qc25_ibmq_5qubit/runner.py` docstring). Hypothesis: H^{⊗5}|0⟩^{⊗5} produces measurement counts uniform within Poisson noise across 32 = 2^5 computational-basis states on real IBM Quantum hardware. Pre-reg thresholds (URB-830 symmetric framing): CONFIRM if chi-square p > 0.10; REJECT if p < 0.001; PARTIAL otherwise; INELIGIBLE if backend unreachable. Initial Pass-33 run (2026-05-11T00:44:36Z) returned `InvalidAccountError: Unable to retrieve instances. Please check that you are using a valid API token.` → INELIGIBLE_HW_FALLBACK_TO_SIM. Brandon added a fresh IBMQ_Secret to Replit Secrets this turn.

### §3.2 Re-execution result (2026-05-11, after IBMQ_Secret rotation)

- Backend selection: `qiskit_runtime_service` resolved instance `open-instance`, plan `open` (free-tier).
- Job submitted: `d810h3ugbeec73aju610`.
- Wait: well under the 300-s queue timeout.
- Shots: 1024 across 32 measurement classes.
- Returned counts span all 32 outcomes (no missing bin).
- **Chi-square against uniform = 27.375 (df=31), p = 0.6532**.
- Pre-reg verdict: **CONFIRM** (p > 0.10 threshold).
- `ran_on_hw=True`, `hw_error=None`, `fallback=None`.

### §3.3 What this confirms (and what it does not)

**Confirms:** the simplest possible "32-D-complex GM-Network c25 native-state" claim from Pass-31 D2-HYBRID — that the H^{⊗5}|0⟩^{⊗5} preparation, when measured in the computational basis on real superconducting-qubit hardware, behaves as the textbook ℂ^32 quantum-state predicts (uniform distribution over 32 outcomes within shot noise). The chi-square is comfortably above the conservative p>0.10 cut. This is a **necessary** consistency check for any hardware-side claim about GM-Network state-space; it would have been a major blow if it had failed.

**Does NOT confirm:**
- Any **claim about** the Mycelial / GM-Network framework as a model of cognition, biology, or anything outside textbook QM. The test is a textbook QM consistency check; a successful run is consistent with both "GM-Network maps to ℂ^32" and "GM-Network has nothing to do with anything." This run discriminates only between those two hypotheses about hardware functionality, not about world-physics interpretation.
- Any **non-trivial entanglement structure** — H^{⊗5}|0⟩^{⊗5} is a product state. Future qc-passes (qc26+) need entangled preparations (e.g., GHZ-5 with CNOT chain, then Bell-test-like measurements) to probe structure beyond what classical-noise simulators trivially reproduce.
- Any **calibration of GM-Network claim against alternative 32-D models** — chi-square uniform is a single test against one null. Multiple alternative-hypothesis tests (e.g., specific non-uniform structured priors from Pass-31) would strengthen / weaken the CONFIRM in directions the present test cannot resolve.

### §3.4 #69 honesty caveats

- Free-tier IBM Quantum hardware **uses runtime calibration data**. Counts can drift between days; recommended replication = at least 3 independent runs across ≥1 week before promoting from CONFIRM-singleton to CONFIRMED.
- p=0.65 is a "passes the test" not "strongly endorses" result; the textbook prediction is uniform-32 + Poisson, and the test is well-powered to detect gross hardware fault, not subtle structure.
- Backend identity is not in `results.json` (the runner stores `backend: None` post-job); add to qc26.
- Pre-reg amendment A1-qc25 (Pass-33) re queue_timeout=300 was tested and worked at this scale.

## §4 — Open carry-overs (unchanged by Pass-43)

| Item | Status |
|---|---|
| p38-A archetype-1 over-broadness | OPEN |
| p39-A/B/C alternative-rubric / refined / non-numerology | OPEN |
| p40-A through p40-E formal-system match + taxonomy validation | OPEN |
| p41-B re-analyze with full-page biography NLP | PARTIAL (pilot done) |
| p42-B R5 population-aggregation feasibility | OPEN |
| p42-C M1/M2/M3 mechanism distinction | OPEN |
| (NEW p43-A) Cross-session Mendi replication ≥3 more sessions | OPEN |
| (NEW p43-B) qc26 GHZ-5 + entanglement-witness on hardware | OPEN |
| (NEW p43-C) Non-linear (e.g., piecewise-linear or Gaussian-process) drift model on Mendi data | OPEN |
| (NEW p43-D) Re-fit drift on baseline+recovery only (not through stimulus epochs) | OPEN |

## §5 — Anchor artifacts

- `data/mendi/sessions/session_2026-05-11T12-22-50_*` (4 files: decoded.csv, raw.jsonl, events.json, summary.txt)
- `analyses/pass43_mendi_session_analysis/analyze.py` + `results.json`
- `analyses/pass33_qc25_ibmq_5qubit/runner.py` + updated `results.json` (CONFIRM)
- `mendi_session_20min.py` + `.bat` + `papers/MENDI_20MIN_SESSION_RUNBOOK_2026-05-11.md` (Pass-42 deliverables, validated by this session's clean run)

## §6 — Replit.md update

§7.7.79 to be added with concise headline; per-pass detail authoritative here.

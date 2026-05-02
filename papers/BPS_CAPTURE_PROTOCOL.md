# BPS Capture Protocol — URB #828 v2 (Permanent + Live)

**Status:** Gate 3 staging document. Locks the per-trial capture procedure for URB #828 v2.
**Date:** 2026-05-01 PM
**Cost:** $0 (uses Brandon's existing devices)
**Cross-links:** `papers/URB_828_BPS_STACKING_HYPOTHESIS.md`, `papers/BPS_TERM_INTRODUCTION_2026-05-01.md`

---

## 1. Protocol invariants (apply to every trial)

- **Trial timestamp T_k:** wall-clock UTC ISO-8601, recorded to nearest second.
- **Trial environment:** consistent room (Brandon's home office), consistent lighting (overhead + window blinds in fixed position), no other people in frame.
- **Brandon state:** seated, eyes-open baseline 30s before T_k.
- **No agent feedback:** Brandon does not communicate trial-target to agent in any form between sealing and scoring.

## 2. Permanent BPS capture procedure (3 BPS minimum, +1 optional)

### 2.1 DNA-derived genome score (one-time, already complete)

Captured as `mito_snp_score` = 0.9468, `telomere_proxy` = 0.4167, `cpg_promoter_density` = 0.4757 (URB #826 §10.4 / §8.7). Re-used for every URB #828 trial without recapture. Source: `phase_h1_5_genome_derivation.py`.

### 2.2 Face photo (per trial, ~10 sec)

- **Device:** Brandon's phone front camera (consistent across trials).
- **Pose:** straight-on, neutral expression, eyes open, no glasses.
- **Distance:** arm's length (recorded as ~50cm, consistent).
- **Lighting:** room overhead + ambient (consistent).
- **Filename:** `data/urb828/T_k/face_<ISO_TIMESTAMP>.jpg`.
- **Feature extraction (offline, post-trial):** standard 68-landmark face geometry via `face_recognition` (Python, free); normalized to inter-pupillary distance.

### 2.3 Handwriting sample (per trial, ~30 sec)

- **Substrate:** standard ruled paper, ballpoint pen (consistent across trials).
- **Content:** Brandon writes a fixed pangram (e.g., *"The quick brown fox jumps over the lazy dog 2026-05-DD"*) — content is not the BPS, the *style* is.
- **Capture:** photographed under same conditions as §2.2.
- **Filename:** `data/urb828/T_k/handwriting_<ISO_TIMESTAMP>.jpg`.
- **Feature extraction (offline):** stroke-pressure proxy (line-darkness variance), aspect ratio, slant angle, baseline drift, letter spacing — extracted via `opencv` + `numpy` (free).

### 2.4 (Optional 4th permanent) Fingerprint scan

- **Device:** Brandon's phone fingerprint sensor or photo-of-inked-print.
- **Capture:** one-time only (fingerprint is time-invariant; re-scan only if device changes).
- **Filename:** `data/urb828/static/fingerprint_<ISO_TIMESTAMP>.jpg`.
- **Feature extraction (offline):** minutiae count + ridge-orientation histogram via `opencv` + `numpy`.

## 3. Live BPS capture procedure (3 BPS minimum, +1 optional)

### 3.1 Polar H10 RR / HRV (per trial, 60s window)

- **Device:** Polar H10 chest strap, already in §10.6 daily-protocol use.
- **Window:** [T_k − 30s, T_k + 30s].
- **Recording app:** Polar Beat (untethered), syncs nightly.
- **Extraction:** RR intervals → RMSSD, SDNN, mean HR, LF/HF ratio.
- **Filename:** `data/urb828/T_k/h10_<ISO_TIMESTAMP>.csv`.

### 3.2 Pulsoid PPG (per trial, 60s window)

- **Device:** Pulsoid (token already configured).
- **Window:** [T_k − 30s, T_k + 30s].
- **Extraction:** PPG amplitude variance, peak-to-peak interval distribution, perfusion index proxy.
- **Filename:** `data/urb828/T_k/pulsoid_<ISO_TIMESTAMP>.csv`.

### 3.3 Subjective daily log entry (per trial, day-bucket)

- **Tool:** `log_daily_subjective.py` (already built).
- **Fields:** mood (1-10), energy (1-10), focus (1-10), salient-event free-text.
- **Window:** the entry filed within ±2h of T_k.
- **Filename:** appended to `data/subjective_daily_log.csv`.

### 3.4 (Optional 4th live) Oura overnight summary

- **Device:** Oura ring (autonomous nightly capture).
- **Window:** the night preceding T_k (sleep onset → wake).
- **Extraction:** sleep score, HRV (overnight), readiness, body temp deviation.
- **Filename:** harvested by `oura_full_metrics_harvester.py`.

## 4. Trial-target capture (the thing we're predicting)

- **Token-set:** M=5 fixed tokens, chosen by Brandon at pre-registration lock (symbols / colors / valences / concepts — TBD at Gate 2 §10 item 8).
- **Selection:** Brandon shuffles a sealed deck of 5 cards, draws one at T_k, writes the token on a sealed envelope.
- **Storage:** envelope photographed sealed (proof of timing), opened only at scoring.
- **Filename:** `data/urb828/T_k/target_<ISO_TIMESTAMP>.txt` (filed sealed-image first, plaintext-target only after agent prediction is locked).

## 5. Agent prediction capture

- **Procedure:** at T_k + 5 min (allowing physiological windows to complete), agent receives the BPS bundle (no target) and produces one M-multinomial prediction.
- **Lock:** prediction written to `data/urb828/T_k/agent_prediction_<ISO_TIMESTAMP>.txt` *before* envelope is opened.
- **Scoring:** Brandon opens envelope, scores hit/miss, appends to `data/urb828/results.csv`.

## 6. Per-condition trial inclusion

For condition C_i in {C0, C1, C2, C3, C4, C5, C6, C7}, the agent receives only the BPS subset corresponding to that condition (see URB #828 v2 §7.2). All BPS are *captured* every trial; conditions are post-hoc subsets of the same data.

This is the cost-saving design: 1 trial-day yields 1 data-point per condition simultaneously.

## 7. Data integrity

- **Time-of-capture:** every file timestamped from system clock at write-time, cross-checked against device-internal timestamps.
- **No retroactive editing:** files are append-only; corrections filed as new entries with explicit `correction-of:` field.
- **Daily git commit:** `data/urb828/` committed nightly (after envelope-opening) so every trial has an immutable git hash.

## 8. Honest residuals

1. Phone-camera face capture is consumer-grade; sub-pixel alignment may drift across trials. Mitigation: capture template at T_0 + record alignment delta per trial.
2. Pulsoid + H10 may double-count cardiac information. The C0 ML-baseline arm controls for this directly.
3. Single-blind risk: Brandon writes target *and* scores. Mitigation: M=5 token-set and exact-match scoring eliminate fuzzy-match wiggle room.
4. Adderall/Focalin pharmacology covariates are captured per `data/medication_log.csv` and residualized at analysis time.

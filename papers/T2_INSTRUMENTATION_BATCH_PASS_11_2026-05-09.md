# T2 Instrumentation Batch — Pass 11 Status + Executable Next Steps

**Date:** 2026-05-09
**Author:** Brandon Charles Emerick (rig owner); agent (status assessment per Pass 11 directive)
**Scope:** T2-A Mendi fNIRS, T2-B Polar H10 BPS, T2-C EEG band-power asymmetry — three Tier-2 instrumentation items from `papers/PD_EMPIRICAL_RESEARCH_AGENDA_2026-05-08.md`.

---

## TL;DR

| Item | Hardware status | Software status | Data status | Blocker |
|---|---|---|---|---|
| **T2-A Mendi fNIRS** | Owned, BLE-paired | `mendi_ble_client.py` patched Pass 6 (Phase 2 complete) | 0 PD-trajectory sessions captured | Need a structured data-capture protocol + 5 baseline sessions |
| **T2-B Polar H10 BPS** | Owned, BLE-paired | `hardware/POLAR_H10_PULSOID_RECEIVER.py` exists | 7 Polar Flow JSONs (no RR) | Need either AccessLink API enrollment (free) or live BLE GATT capture session |
| **T2-C EEG band-power asymmetry** | Muse owned (`hardware/MUSE_LOCAL_REALTIME.py`) | Local realtime capture rig exists | No PD-stratified sessions | Need the GILE-self-report scale (urb_755) operationalized + 10 paired sessions |

**Net assessment:** all three rigs are *operational*. The blockers are *protocol* (what data to capture, in what order, with what self-report instrument) — not *technology*. This document supplies the protocols and locks the next-session executable scripts.

---

## T2-A — Mendi fNIRS PD-trajectory tracking protocol

### Goal

Test whether Mendi's NIR intensity signal (12-bit ADC at ~1.4 Hz from `bb4` characteristic, decoded Pass 6) varies systematically across self-reported PD states. Per the framework's structural claim: PD = +2 (HRV maximal coherence; Ring-5 BEC) should correspond to *higher and more stable* prefrontal NIR intensity than PD = −1 (DT cliff approach; Fragmented phase).

### Pre-registered hypothesis

**H1:** Within-subject (Brandon as N=1), mean NIR intensity is significantly higher (one-tailed paired t-test, p < 0.05) in PD = +1 to +2 self-reported sessions vs PD = 0 to −1 self-reported sessions, over a sample of ≥ 10 paired sessions per condition.

**H2 (secondary):** within-session NIR variance is *lower* in PD = +1 to +2 sessions (BEC-coherence prediction).

### Capture protocol

**Per session (target: 10 minutes, twice daily):**

1. Pre-session self-report (1 minute): Brandon scores current PD using the urb_755 GILE self-report scale (see T2-C protocol below for the scale instrument); records PD value, time, sleep last night, caffeine, last meal time.
2. Headband on; let baseline stabilize (1 minute).
3. 8-minute structured eyes-closed quiet sit (no specific meditation instruction; minimal movement).
4. Post-session self-report (1 minute): re-score PD; note any state shift.
5. Save raw NIR stream to `data/mendi_pd_trajectory/YYYY-MM-DD_HHMM.json` with header containing pre+post PD scores.

### Locked next-session script (executable today)

```bash
# T2-A capture session — single session
python -c "
from mendi_ble_client import MendiClient
from datetime import datetime
import json, time
pre_pd = float(input('Pre-session PD (−3 to +2): '))
notes = input('Notes (sleep, caffeine, food): ')
m = MendiClient()
m.connect()
samples = []
t0 = time.time()
print('Capturing 8 min...')
while time.time() - t0 < 480:
    s = m.read_one()  # ~1.4 Hz NIR sample
    samples.append({'t': time.time() - t0, 'nir': s})
m.disconnect()
post_pd = float(input('Post-session PD: '))
fname = f'data/mendi_pd_trajectory/{datetime.now():%Y-%m-%d_%H%M}.json'
with open(fname, 'w') as f:
    json.dump({'pre_pd': pre_pd, 'post_pd': post_pd,
               'notes': notes, 'samples': samples}, f)
print(f'Saved {len(samples)} samples to {fname}')
"
```

### Acceptance for T2-A first-pass result

- ≥ 10 paired sessions captured (5 in PD ≥ +1, 5 in PD ≤ 0).
- Within-subject paired analysis run; one-tailed t-test on mean NIR intensity.
- **Honest reporting:** report effect size + 95% CI even if non-significant; #69 forbids non-publication of null results in the corpus.

### Honesty caveats (pre-locked)

- Single-subject N=1 design has limited generalizability; this is a *feasibility + within-subject pilot*, not a publishable claim.
- 1-2 wavelength single-optode fNIRS cannot do Beer-Lambert HbO₂/HbR separation (`MENDI_FNIRS_AUDIT_2026-05-01.md`); the signal is "NIR intensity" not "oxygenation." Body of any future paper must say this explicitly.
- Self-reported PD is the dependent variable's anchor; it is not blinded.

---

## T2-B — Polar H10 BPS hypothesis test

### Goal

The BPS (Baseline-PD-Synchrony) hypothesis (urb-cluster, post-Pass-9): higher self-reported PD correlates with HRV LF/HF ratio closer to φ ≈ 1.618 (the Ring-5 prediction in `T1-D` results). Tests this within-subject, RR-interval-based.

### Blocker (CRITICAL)

The 7 Polar Flow JSONs in `data/polar_h10_export/` do **not** contain RR-interval data — Polar Flow exports give only HR summaries. RR data requires either:

**Option A — Polar AccessLink API (free, official):**

1. Brandon registers a Polar AccessLink developer account at `https://www.polar.com/accesslink-api/`.
2. OAuth Brandon's personal Polar account through the API.
3. Pull the same 7 sessions (or new sessions) with R-R included.
4. Estimated time: 30 min registration + 1 hour API integration scripting.

**Option B — Live BLE GATT capture (already-owned rig):**

`hardware/POLAR_H10_PULSOID_RECEIVER.py` exists. Polar H10 broadcasts RR intervals over BLE GATT (HRM service `0x180D`, characteristic `0x2A37`). The script needs verification that RR is being parsed (not just instantaneous HR).

### Recommended path: **Option A first** (no rig dependency, retroactively recovers the existing 7 sessions).

### Locked next-session checklist (Option A)

```text
T2-B Polar AccessLink setup checklist:
[ ] 1. Register at polar.com/accesslink-api/ (~5 min)
[ ] 2. Receive client_id + client_secret (~immediate)
[ ] 3. Add to Replit secrets: POLAR_CLIENT_ID, POLAR_CLIENT_SECRET
[ ] 4. Run OAuth flow once to get refresh_token; store in Replit secrets
[ ] 5. Implement training_recoveries endpoint pull → returns hr_samples + rr_samples
[ ] 6. Pull 7 historical sessions; save to data/polar_accesslink/
[ ] 7. Compute LF/HF for each via Welch periodogram on RR series
[ ] 8. Pair with retrospective PD self-report (Brandon recalls PD for each session)
```

### Acceptance for T2-B first-pass result

- ≥ 5 sessions with RR pulled and paired with retrospective PD self-report.
- LF/HF computed per session; correlation with PD computed; 95% CI reported.
- If correlation positive and LF/HF ≈ φ at peak-PD sessions: confirmation.
- If null or opposite: honestly reported per #69.

### Honesty caveats

- Retrospective PD self-report is recall-biased; prospective sessions (Option B with concurrent self-report) are stronger but require a future capture window.
- LF/HF is one of many HRV-spectrum metrics; the framework should pre-specify it (or commit to reporting all spectrum metrics).

---

## T2-C — EEG band-power asymmetry (Muse) per-subject pipeline

### Goal

Replicate the framework prediction "EEG band-power asymmetry at 3–4 PD units" (urb_714) on Brandon-as-N=1 across PD-stratified sessions using the Muse 2/S 4-channel EEG.

### Status

Real-time rig exists (`hardware/MUSE_LOCAL_REALTIME.py`, `hardware/MIND_MONITOR_SETUP.py`). Per-subject EEG pipeline scaffolded across urb_738/urb_747/urb_751/urb_755. The blocker has been *the GILE self-report scale* (urb_755) — without a self-report instrument, we cannot stratify sessions by PD.

### urb_755 GILE self-report scale (operationalized for PD scoring, draft)

Scoring sheet, 5 items, each 1–5 Likert; sum = 5–25; PD = (sum − 15) / 5 (range −2 to +2):

1. **Coherence:** "Right now, my thoughts feel coordinated and aligned." (1 = scattered, 5 = perfectly coordinated)
2. **Energy:** "Right now, I have abundant available energy without strain." (1 = depleted, 5 = effortlessly abundant)
3. **Equanimity:** "Right now, I feel emotionally settled — neither suppressed nor reactive." (1 = highly reactive, 5 = settled and present)
4. **Trust:** "Right now, I trust the next thing that arises in my experience without forcing it." (1 = forcing/controlling, 5 = full trust)
5. **Bandwidth:** "Right now, I can hold multiple aspects of a situation simultaneously without overwhelm." (1 = single-track, 5 = multi-aspect with ease)

PD score: subtract 15, divide by 5 → range [−2, +2]. Scores below −2 (sum < 5) impossible by construction; in practice expect typical range −1.5 to +1.5.

This scale is *not validated*; it is a Brandon-N=1 instrument for within-subject stratification only. Any future cross-subject use requires psychometric validation (test-retest, inter-rater).

### Capture protocol

Identical structure to T2-A, with Muse instead of Mendi: pre+post self-report, 8-minute eyes-closed sit, save raw EEG. Use `MUSE_LOCAL_REALTIME.py` to stream + buffer.

### Acceptance for T2-C first-pass result

- ≥ 10 paired sessions (PD ≥ +1 vs PD ≤ 0).
- Compute per-channel band powers (δ, θ, α, β, γ) via Welch.
- Compute frontal-asymmetry index F4 − F3 (or TP10 − TP9 on Muse) for α band.
- Test prediction: PD ≥ +1 sessions show *more positive* (right > left) α asymmetry, consistent with urb_714's "3–4 PD units of asymmetry."
- 95% CI reported regardless of significance.

### Honesty caveats

- Muse 4-channel EEG (TP9, AF7, AF8, TP10) has poor frontal coverage; F3/F4 approximation via AF7/AF8 is acceptable for asymmetry but not for source localization.
- The urb_755 self-report scale is unvalidated; results are within-subject-pilot grade only.

---

## Cross-cutting items

### Capture cadence recommendation

For a 4-week pilot:

- **Mendi:** 2 sessions/day × 28 days = 56 sessions (over-target).
- **Muse:** 1 session/day × 28 days = 28 sessions (over-target).
- **Polar:** 1 RR-capture session/day = 28 sessions; pair with one of the above for tri-modal data.

Cost: $0 marginal (rigs owned); ~30 min/day total commitment. Within Brandon's <$50 budget.

### Tri-modal session protocol (gold-standard)

When Brandon has time for one full session:

1. Pre-session GILE-scale (1 min).
2. Tri-modal start: Mendi headband + Muse + Polar chest strap, all streaming simultaneously.
3. 8-minute eyes-closed sit.
4. Post-session GILE-scale (1 min).
5. Save all three streams with a shared session ID.

**Output:** within-session correlation between NIR intensity, EEG α-asymmetry, and HRV LF/HF; this is the most-information-dense single capture in the framework.

### Data-organization standard (locked)

```
data/
  mendi_pd_trajectory/    YYYY-MM-DD_HHMM.json
  polar_accesslink/        YYYY-MM-DD_HHMM.json (after T2-B Option A done)
  muse_pd_stratified/      YYYY-MM-DD_HHMM.json (after T2-C protocol locked)
  trimodal/                YYYY-MM-DD_HHMM/{mendi,muse,polar}.json (gold-standard)
```

Each file MUST include header fields: `pre_pd`, `post_pd`, `notes`, `subject_id` (always "B" for Brandon-N=1), `session_id`, `instrument_version`.

### Honesty discipline (Tier-2-wide)

- All three pilots are **N=1, within-subject**. Cross-subject generalization requires later replication.
- All three depend on the urb_755 self-report scale, which is **unvalidated**. The scale's reliability is itself a Tier-3 target.
- The framework predicts *direction* (PD ≥ +1 → higher coherence); effect *magnitudes* are not pre-specified, which limits the strength of any positive result. Future versions of these protocols should include pre-registered effect-size targets.

---

## Pass 11 acceptance for T2 batch

This document **defines** the protocols. Capture itself is Brandon-time-dependent. The Pass 11 contribution is:

- Three pre-registered protocols (this document).
- One self-report scale operationalized (urb_755 → 5-item GILE-scale).
- One executable capture script (T2-A).
- One next-action checklist (T2-B Polar AccessLink).
- One data-organization standard.

**Brandon-decision items raised:**

(a) Ratify the urb_755 5-item self-report scale (or revise items).
(b) Choose T2-B path: Option A (Polar AccessLink) or Option B (live BLE GATT).
(c) Commit to a 4-week pilot calendar, OR scope down to a 1-week feasibility test.

---

*End of T2 instrumentation batch document. The rigs are operational; the protocols are locked; the missing ingredient is capture time + Brandon-ratification of the self-report scale.*

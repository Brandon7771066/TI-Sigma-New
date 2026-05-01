# Polar H10 + Phase B Procedure (Brandon-Executable)

**Date:** 2026-05-01 (v2 — Brandon already owns the H10)
**Author:** Replit Agent (DPES autonomous mode), for Brandon Charles Emerick
**Goal:** Unblock the daytime-HRV component of R_intra_em so we can run Phase B at 6-of-6 real input. Add a continuous daytime-HRV channel that varies per day independently from Oura overnight biometrics.

This document is your step-by-step. Follow it in order; nothing requires technical decisions from you.

---

## 0. What you're doing and why

The Phase H-1 FULL-4-of-5 result (§8.7) substituted Oura overnight HRV into the 5th slot. The Phase B preliminary fit (§8.8) ran successfully but the per-day-varying signal in our data is essentially just one feature (Oura overnight HRV + a tiny PPG signature), so the regression had nothing to learn. To genuinely test URB #826 we need a **second per-day-varying signal that's independent of your sleep**: daytime HRV. Your Polar H10 chest strap is the cleanest scientifically-validated source:
- **3-axis ECG**, not optical PPG → far more accurate R-R intervals than wrist devices
- **±1 ms accuracy** at sample-level (validated against medical Holter monitors in 30+ peer-reviewed studies)
- **5 kHz Bluetooth + ANT+** → works with everything
- **Internal memory + RR-interval export** → we get the raw heart-beat-to-heart-beat data, not just a "score"

**Cost from here: $0.** You already own the strap. No new app purchases needed.

---

## 1. ~~Order~~ — already done

You already own the H10. Skip to Section 2. If your strap has been sitting in a drawer:
- **Battery check:** the H10 uses a CR2025 coin cell, lasts ~400 hours of recording. If it's been a year unused, the battery is probably dead — pop it out (small flathead screwdriver on the back of the sensor pod) and replace ($1–2 at any drugstore).
- **Electrode condition:** the fabric strap with the electrodes wears out after about a year of regular use. If yours feels stiff or dry, a replacement strap is ~$15 on Amazon ("Polar Pro Soft Strap"). Optional — try the existing one first; if HR readings are noisy or dropping, that's the sign the strap is dead.

---

## 2. Capture path — choose ONE based on your day

You said: "I want my data throughout the day transferred here." The H10 has internal memory and can record continuously for ~30 hours per session, so **all-day untethered wear is its native use case** — phone optional during the day, sync at night.

Pick the option that matches your daily reality:

### Option A — All-day untethered (RECOMMENDED, matches your stated goal)

This uses the H10's internal memory. The strap records your heartbeat continuously while you wear it; the phone is only needed at end-of-day for sync. **App: Polar Beat (FREE, official, iOS / Android).**

**Setup once:**
1. Install Polar Beat → create free Polar account
2. Settings → Sensors → pair Polar H10 over BLE
3. Settings → Training → enable **"Record without phone"** (this turns on the H10's internal logging)

**Daily routine — ~3 minutes total:**
1. **Morning:** wet electrodes, strap on, double-tap the H10 sensor pod (front face) — the LED pulses confirming recording started. Phone NOT needed.
2. **Wear all day**, take it off in the shower (it's actually waterproof to 30m but the strap dries out faster if you don't), put it back on after.
3. **Evening:** double-tap again to stop recording. Open Polar Beat → it auto-syncs the offline session over BLE → uploads to flow.polar.com → done.
4. **Export the day** (1-min step, Brandon does this part):
   - Open https://flow.polar.com → Diary → click today's session
   - Top-right → "Export session" → choose **TCX** (XML with HR + RR samples) — preferred for HRV computation
   - Save TCX → drop into Replit `data/polar_h10/` (Section A below for exact upload steps)

**Why TCX not CSV:** Polar Flow's CSV export is HR-per-second only. The TCX includes the millisecond-precision RR intervals we need for proper HRV math (RMSSD, sample entropy, DFA-α1). CSV-only would force us to compute HRV from BPM (much noisier — same problem we hit with Oura PPG).

### Option B — Phone-paired all day (if you want live readings on screen)

App: **HRV Logger** by Marco Altini (Welltory) — iOS / Android, $0.

- Open the app in the morning, pair the H10, hit "Start" → leave phone in your pocket
- App streams RR intervals continuously to a local CSV
- End of day: hit "Stop" → "Share CSV" → drop in Replit
- DOWNSIDE: phone Bluetooth must stay paired all day → ~10–15% extra phone battery drain
- UPSIDE: zero post-processing, the CSV is already in the format we want

### Option C — Spot-check morning reading only (fallback if all-day is too much)

App: **EliteHRV** (free) → Morning Readiness mode → 60-sec daily reading. This was the original plan. Less informative than all-day but still gives one daytime-HRV scalar per day. Use only if Options A/B don't fit your routine.

**Pick Option A.** It matches what you asked for, costs $0, and gives the richest signal.

---

## 3. First-day setup with Polar Beat (10 min, do once)

1. **Battery + electrode check** (Section 1) — replace CR2025 if dead, wet electrodes always before wearing
2. **Strap on**, snug, electrodes flat on skin just below pectorals (about 1" below the bottom of your sternum)
3. **Install Polar Beat** → sign up with email (free account)
4. **Settings → Sensors → "Pair new sensor"** → wait for "Polar H10 XXXXXXXX" → tap to pair
5. **Settings → Training → toggle ON "Record training without phone"** (this enables H10's internal memory)
6. **Verify pairing works:** Polar Beat main screen should show your live HR (60–80 bpm at rest)
7. **Test the double-tap-start gesture:** with the strap on, firmly double-tap the front face of the H10 pod (the part with the Polar logo). You should feel a small vibration and see (in Polar Beat) "Recording started." Double-tap again to stop. This is the all-day workflow.

---

## 4. Daily routine — the actual Phase B protocol

**Goal: one all-day TCX file per day, dropped into `data/polar_h10/`.**

| Time | Action | Time cost |
|---|---|---|
| Morning | Wet electrodes, strap on, double-tap H10 to start recording | 30 sec |
| All day | Wear normally. Take off only for showers/swimming if you prefer. | 0 sec |
| Evening | Double-tap H10 to stop recording, take strap off | 15 sec |
| Before bed | Open Polar Beat (phone in BLE range of strap) → auto-syncs | 30 sec |
| Optional: nightly export | flow.polar.com → today's session → Export TCX → drop in Replit | 60 sec |

**Total: ~3 min/day.** The export step can be batched weekly (export 7 TCXs at once on Sunday) if you don't want to do it daily — Polar Flow keeps the data indefinitely.

**Filename:** Polar Flow auto-names exports something like `Brandon_Emerick_2026-05-02_07-14-22.tcx`. Drop as-is into `data/polar_h10/` — I'll parse whatever filename and read the timestamps from inside the TCX itself.

---

## 5. What I'll do with each TCX/CSV

Once you start dropping files, I'll build `polar_h10_loader.py` that:
- Parses Polar Flow TCX (XML — handles `<HeartRateBpm>` + `<ns3:RRIntervals>`) or HRV Logger CSV interchangeably
- Segments your wear day into rolling 5-minute windows (standard HRV epoch length)
- Computes per-window: RMSSD, SDNN, pNN50, LF/HF ratio, sample entropy, DFA-α1
- Aggregates to **per-day daytime-HRV scalar** = circadian-weighted mean of 5-min RMSSD windows excluding workout windows
- Outputs `daytime_hrv_norm` ∈ [0, 1] for the 6th R_intra_em slot
- Time-aligns with your Oura overnight HRV for same-day pairs (Oura covers ~22:00–06:00, H10 covers ~07:00–22:00 — together they cover ~95% of your 24h)

This is identical to how `phase_h1_full4of5.py` currently uses Oura HRV — just a different source covering the missing daytime hours.

---

## 6. Minimum data for Phase B

| Phase B fitting target | Minimum N |
|---|---|
| Within-subject auto-regression on 5 components (current §8.8 baseline) | done at N=6 |
| Within-subject regression with 6 components (incl. H10 daytime HRV) | **21 days** |
| §10.6 strong-form falsification of URB #826 at this subject | **21 days** + locked pre-registration |
| Cross-subject (need N≥2 subjects) | not applicable yet |
| MZ-twin differentiated test (URB #826 §5.1) | not applicable (no twin available) |

**Practical recommendation:** start wearing H10 tomorrow. After 21 consecutive days I'll run §10.6 — the actual URB #826 falsification test — with pre-registered weights and confidence intervals. The §8.8 preliminary fit gives us a baseline to compare against; the H10 data is what makes the test meaningful.

---

## 7. Pre-registration of falsification criterion

**Before** running §10.6 I will lock the criterion in `papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md`:

> If learned w_em components (mito + telomere + cpg + ppg) sum to < 0.10 AND HRV components (Oura overnight + H10 daytime) sum to > 0.85, URB #826 is **falsified at this subject**. If w_em sum > 0.30, URB #826 is **partially supported at this subject**. Anything in between is **inconclusive at this subject**.

This is the asymmetric-standards #69 falsification path: I am committing in advance to a specific result that would falsify URB #826 for you, before we have any data that could prove or disprove it.

---

## 8. Cost summary (revised — strap already owned)

| Item | Cost | Status |
|---|---|---|
| Polar H10 chest strap | $0 | ✅ Brandon already owns |
| Polar Beat (official, all-day untethered) | $0 | ✅ free, App Store / Play Store |
| HRV Logger (alternative, all-day phone-paired) | $0 | ✅ free |
| EliteHRV (fallback, morning-only) | $0 | ✅ free tier sufficient |
| CR2025 battery (if dead) | $1–2 | ☐ check first |
| Replacement strap (if electrodes dead) | $0–15 | ☐ try existing first |
| My work to integrate H10 data | $0 | ✅ I do it once you start dropping files |
| Phase B + §10.6 regression compute | $0 | ✅ runs in CPU seconds |
| **Total to unblock §10.6 falsification test** | **$0–17** | within DPES |

---

## 9. Your TODO checklist (REVISED)

- [ ] **Today:** find the H10 strap, check the battery (CR2025), wet the electrodes, do a 30-second test wear to confirm it still works
- [ ] **Today:** install Polar Beat (free) on your phone if you don't already have it; pair with H10; toggle ON "Record without phone" in Settings → Training
- [ ] **Tomorrow morning:** start your first all-day session (double-tap H10 to start recording, wear all day, double-tap to stop in evening, sync to Polar Beat before bed)
- [ ] **Tomorrow night or Sunday:** export TCX from flow.polar.com → drop into `data/polar_h10/` (Section A below for exact upload steps)
- [ ] **Ping me:** "H10 data is in" once you have ≥ 7 days of TCX files. I'll build the loader and run a 6-component fit.
- [ ] **After 21 days:** I run the pre-registered §10.6 URB #826 falsification test.

---

## A. Operator appendix — exact Replit upload + canonical CSV

**Path A: drag-and-drop in the Replit Workspace file tree (easiest):**

1. In the left-hand file tree, navigate to `data/polar_h10/` (create the folder if missing — right-click → New folder → name `polar_h10`).
2. From your Mac/PC: drag the EliteHRV-exported CSV(s) directly onto that folder in the Replit file tree.
3. The file should appear within a few seconds. Then ping me "H10 data is in" with the filename(s).

**Path B: paste-as-text (if drag-and-drop fails):**

1. Open the CSV on your computer in TextEdit / Notepad / VS Code.
2. Copy the entire contents.
3. In Replit, right-click `data/polar_h10/` → New file → name `eliteHRV_<YYYY-MM-DD>.csv` → paste → save.

**Canonical formats I'll auto-detect:**

**Format 1 — Polar Flow TCX (Option A all-day):**
```xml
<?xml version="1.0" encoding="UTF-8"?>
<TrainingCenterDatabase ...>
  <Activities><Activity>
    <Lap StartTime="2026-05-02T07:14:11Z">
      <Track>
        <Trackpoint>
          <Time>2026-05-02T07:14:11Z</Time>
          <HeartRateBpm><Value>67</Value></HeartRateBpm>
          <Extensions><ns3:RRIntervals>
            <ns3:RR>0.892</ns3:RR>  <!-- seconds -->
          </ns3:RRIntervals></Extensions>
        </Trackpoint>
        ...
```
Just drop the .tcx file as-is. I read everything from inside.

**Format 2 — HRV Logger CSV (Option B all-day):**
```
timestamp,rr_ms,hr_bpm
2026-05-02T07:14:11.234,892,67
2026-05-02T07:14:12.126,907,66
...
```

**Format 3 — EliteHRV CSV (Option C morning-only):**
```
RR Interval (ms)
892
907
884
...
```

**If your export doesn't match any of the above** — just drop the file as-is and tell me which app it came from. I'll write a one-line parser. Polar in particular changes their export format every couple years, so don't worry about matching exactly.

**File-naming convention (recommended, not required):**

```
eliteHRV_2026-05-02_morning.csv
eliteHRV_2026-05-02_afternoon.csv   ← if you do a second daytime reading
```

I'll figure out which is which from the timestamps inside the CSV regardless of filename.

---

## 10. While you wait — what I'll do today

1. Build the Oura full-metrics harvester (T003): pull all 50+ Oura data points for last 30 days
2. Build the PPG biophoton-signature proxy module (T004): use Oura's BPM samples (which come from the ring's PPG sensor) to compute autonomic-cardiovascular complexity features that are analogous to what GDV/Bio-Well claims to measure — without the GDV cost
3. Build Phase B scaffold (T005): regression infrastructure ready for both 5-component (today, Oura-only) and 6-component (post-H10) fits
4. Pre-register §10.5 with the falsification criterion above
5. Run a preliminary 5-component Phase B fit on existing 30-day Oura data and report

Everything in (1)–(5) is $0 and happens this session.

# Polar H10 + Phase B Procedure (Brandon-Executable)

**Date:** 2026-05-01
**Author:** Replit Agent (DPES autonomous mode), for Brandon Charles Emerick
**Goal:** Unblock the daytime-HRV component of R_intra_em so we can run Phase B at true 5-of-5 real input + add a 6th daytime-HRV channel.

This document is your step-by-step. Follow it in order; nothing requires technical decisions from you.

---

## 0. What you're doing and why

The Phase H-1 FULL-4-of-5 result (§8.7) substituted Oura overnight HRV into the 5th slot. To test URB #826 properly we need a **separate daytime stream** that varies independently from your sleep biometrics. The Polar H10 chest strap is the cheapest scientifically-validated source for that:
- **3-axis ECG**, not optical PPG → far more accurate R-R intervals than wrist devices
- **±1 ms accuracy** at sample-level (validated against medical Holter monitors in 30+ peer-reviewed studies)
- **5 kHz Bluetooth + ANT+** → works with everything
- **Open RR-interval streaming** → we get the raw RR data, not a "score"

Cost: ~$80–90 USD. You already approved.

---

## 1. Order

**Polar H10 Heart Rate Sensor (chest strap, M-XXL)**

- Polar website: https://www.polar.com/us-en/sensors/h10-heart-rate-sensor — $89.95 USD (often free shipping)
- Amazon: usually $79–89 USD with Prime
- REI / Best Buy: same MSRP, sometimes 10% off

Pick the **M-XXL** strap unless your chest measurement is under 26 inches (then XS-S).

**Optional accessory (skip if budget tight):** spare strap (~$15) — the electrode strap wears out around 6–12 months of daily use. Wait until you need it.

---

## 2. Capture app — $0 path

You do NOT need Polar Beat (the official paid Polar app). Three free options that export RR intervals:

### Option A — EliteHRV (RECOMMENDED)
- iOS / Android, free tier
- Pairs over BLE in <30 seconds
- Daily 1-min "morning reading" mode → exports RR intervals as CSV
- **Why:** the morning-reading protocol is itself a standardized reproducible measurement. Same time, supine, breath-paced. Perfect for Phase B daily target.
- Download: https://elitehrv.com/

### Option B — OpenHRV (open-source)
- Cross-platform, GPL-licensed, raw RR streaming to file
- More technical setup (Python + bleak BLE library) but $0 and fully scriptable
- Download: https://github.com/OpenHRV/OpenHRV

### Option C — HRV Logger (Marco Altini, by Welltory)
- iOS / Android, free
- Exports CSV with timestamps + RR + HR
- Lighter than EliteHRV, no daily protocol guidance

**Pick A.** EliteHRV's morning-reading protocol gives us the cleanest signal for Phase B.

---

## 3. First-day setup (15 min, do once)

1. **Wet the H10 electrodes** — strip of skin contact patch on the inside, run under tap water 5 sec (this is critical, dry strap = noise)
2. **Strap on**, snug, electrodes flat on skin just below pectorals
3. **Open EliteHRV** → Settings → Sensors → "Add a sensor" → wait for "Polar H10 XXXXXXXX" → tap to pair
4. **Verify HR shows up** in the app (60–80 bpm at rest)
5. **Take your first morning reading**:
   - Sit or lie supine
   - Tap "Morning Readiness" in EliteHRV
   - Breathe slowly (5–6 breaths/min if comfortable; otherwise just relax)
   - 60 seconds total
6. **Export the RR intervals**:
   - Tap the reading → "Share" → "Export RR" → CSV
   - Save to your computer / email it to yourself

---

## 4. Daily session — the actual Phase B protocol

**Once per day, same time (within ±2 hours):**

1. Strap on H10 (wet electrodes first)
2. Open EliteHRV → Morning Readiness → 60-sec reading
3. Export CSV
4. Drop the CSV in this Replit project's `data/polar_h10/` folder (we'll create it once you have data)
   - Filename format: `polar_h10_YYYY-MM-DD.csv` (or whatever EliteHRV exports — we'll handle parsing)

**Optional:** also do an evening reading. More data = better Phase B fit. But the morning one is the canonical daytime-HRV slot for our R_intra_em substitution.

---

## 5. What I'll do with each CSV

Once you start dropping files, I'll build `polar_h10_loader.py` that:
- Parses EliteHRV's CSV format
- Computes RMSSD, SDNN, pNN50, LF/HF ratio, sample entropy, DFA-α1
- Outputs `daytime_hrv_norm` ∈ [0, 1] for the 6th R_intra_em slot
- Time-aligns with your Oura overnight HRV for same-day pairs

This is identical to how `phase_h1_full4of5.py` currently uses Oura HRV — just a different source.

---

## 6. Minimum data for Phase B

| Phase B fitting target | Minimum N |
|---|---|
| Within-subject auto-regression on 5 components | 14 days |
| Within-subject regression with 6 components (incl. H10 daytime HRV) | 21 days |
| Cross-subject (need N≥2 subjects) | not applicable yet |
| MZ-twin differentiated test (URB #826 §5.1) | not applicable (no twin) |

**Practical recommendation:** start daily readings the day H10 arrives. After 21 consecutive days I'll run Phase B regression and report learned weights with confidence intervals.

While we wait for H10 data: I'll run a **pre-fit Phase B today** using just the 30 days of Oura we already have (5 components, no daytime HRV). That will give us a baseline weight estimate to compare against once H10 data lands.

---

## 7. Pre-registration of falsification criterion

**Before** running Phase B I will lock §10.5 in `papers/AGENT_LOCKED_PREDICTIONS_2026-04-30.md` with this criterion:

> If learned w_em components (mito + telomere + cpg) sum to < 0.10 AND HRV components (overnight + daytime) sum to > 0.85, URB #826 is falsified for this subject. If w_em sum > 0.30, URB #826 is partially supported. Inconclusive between.

This is the asymmetric-standards #69 falsification path: I am committing in advance to a specific result that would falsify URB #826 for you, before we have any data that could prove or disprove it.

---

## 8. Cost summary

| Item | Cost | Status |
|---|---|---|
| Polar H10 chest strap | $80–90 | ☐ Brandon orders |
| EliteHRV / OpenHRV / HRV Logger | $0 | ✅ free tier sufficient |
| Spare strap | $15 | ☐ skip until needed |
| Replit work to integrate H10 data | $0 | ✅ I'll do it once data arrives |
| Phase B regression compute | $0 | ✅ runs in CPU seconds |
| **Total to unblock Phase B at 6-of-6 real** | **$80–90** | within DPES budget |

---

## 9. Your TODO checklist

- [ ] Order Polar H10 (~$85)
- [ ] Install EliteHRV
- [ ] When strap arrives: 15-min first-day setup (Section 3)
- [ ] Daily morning reading + drop CSV into `data/polar_h10/`
- [ ] Tell me "H10 data is in" once you have ≥ 7 days

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

**Canonical CSV header I expect (EliteHRV's "Detailed Reading" export format):**

```
timestamp,rr_interval_ms
2026-05-02T07:14:11Z,892
2026-05-02T07:14:12Z,907
2026-05-02T07:14:13Z,884
...
```

Acceptable variants I'll auto-detect:
- Header `RR Interval (ms)` instead of `rr_interval_ms` ← EliteHRV default
- Header `Time` instead of `timestamp`
- No header at all, single column of RR-interval integers (one per line) ← OpenHRV raw export
- Two columns separated by tab instead of comma

If your export looks different, just send me the file as-is and I'll write a one-line parser for whatever EliteHRV gave you.

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

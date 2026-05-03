# Fingerprint Capture Instructions — URB #828 v2 §2.4 (Optional 4th Permanent BPS)

**Status:** Brandon-runnable, ~10 minutes, $0.
**One-time capture only** (fingerprint is time-invariant; re-scan only if the imaging device changes).
**Cross-links:** `papers/BPS_CAPTURE_PROTOCOL.md` §2.4, `papers/URB_828_v2_PRE_REGISTRATION_LOCKED_2026-05-01.md` §2 (C7 condition).

---

## Why we don't use the phone fingerprint sensor

Brandon's phone fingerprint sensor (Touch ID, Pixel Imprint, etc.) is biometric-locked: it produces a hash for unlock authentication and does not export the actual fingerprint image. We cannot extract minutiae or ridge patterns from it for ML feature extraction. So we use **photo-of-inked-print** instead — same method as forensic fingerprinting.

---

## Materials (all on hand or under $5)

- Black ballpoint pen ink, black washable ink pad, OR a black Sharpie + scrap paper to "load" your fingertip with ink.
- White printer paper (standard 8.5×11 letter, plain, no lines).
- Phone camera (consistent with §2.2 face-photo device).
- Damp paper towel for cleanup.

If you don't want to use ink: a graphite pencil rubbed heavily on paper produces a "pencil pad" you can press your finger onto. Clean transfer to white paper with clear tape works as a backup.

---

## Procedure (one-time, ~10 min)

### Step 1 — Prepare the paper

- Place a single sheet of plain white paper on a flat hard surface.
- Label the top with: `BCE FP CAPTURE 2026-05-DD` (today's date).
- Number five regions across the page: 1, 2, 3, 4, 5 — one for each finger of your right hand (thumb through pinky).

### Step 2 — Ink your finger

- Lightly press your right thumb onto the ink pad (or rub a Sharpie tip across the pad of the thumb until it's evenly black). Do not over-ink — too much ink fills in the ridges and destroys the pattern.
- A blot of ink the size of a dime is plenty.

### Step 3 — Print

- Roll your thumb pad onto region 1 of the paper using **gentle even pressure**, rolling from one side of the nail to the other in a single smooth motion. Do not lift, slide, or re-press.
- Lift cleanly. Do not smear.
- Repeat for index (region 2), middle (3), ring (4), pinky (5).
- If a print is blurred, mark it with a small "X" and re-print in an adjacent spot.

### Step 4 — Photograph

- Wait 60 seconds for the ink to dry.
- Photograph the entire labeled sheet under consistent lighting (overhead room light, no direct flash, no shadow from your hand). Hold phone parallel to paper, ~30cm above. Use the phone's grid overlay to keep the page square in frame.
- Take **three photos** at slightly different angles and lighting positions for redundancy.

### Step 5 — Upload

- Transfer photos to your computer (AirDrop, USB, email-to-self, etc.).
- Save into the project folder:
  ```
  data/urb828/static/fingerprint_<ISO_TIMESTAMP>_thumb.jpg
  data/urb828/static/fingerprint_<ISO_TIMESTAMP>_index.jpg
  data/urb828/static/fingerprint_<ISO_TIMESTAMP>_middle.jpg
  data/urb828/static/fingerprint_<ISO_TIMESTAMP>_ring.jpg
  data/urb828/static/fingerprint_<ISO_TIMESTAMP>_pinky.jpg
  data/urb828/static/fingerprint_full_sheet_<ISO_TIMESTAMP>_v1.jpg
  data/urb828/static/fingerprint_full_sheet_<ISO_TIMESTAMP>_v2.jpg
  data/urb828/static/fingerprint_full_sheet_<ISO_TIMESTAMP>_v3.jpg
  ```
  (Either crop each finger into its own file, or just upload the three full-sheet shots and the agent will crop offline. Easier path: just the three full-sheet photos.)

- Commit + push:
  ```
  git pull
  git add data/urb828/static/
  git commit -m "URB #828 fingerprint baseline capture"
  git push
  ```

### Step 6 — Cleanup

- Wash hands with warm soapy water. Ink will come off in 1–2 washes.
- Note the capture date in `data/medication_log.csv` or `data/subjective_daily_log.csv` as a "salient event" for cross-reference.

---

## What the agent does next (offline, no Brandon time required)

1. Crops each finger from the full-sheet photo if individual crops weren't uploaded.
2. Runs OpenCV minutiae extraction (`cv2` ridge-detection + endpoint/bifurcation count).
3. Computes ridge-orientation histogram (8-bin).
4. Stores extracted feature vector in `data/urb828/static/fingerprint_features.json` for use by `urb828_c0_ml_discriminator_skeleton.py` and the live URB #828 prediction pipeline.
5. Reports back: per-finger minutiae count, image quality score, and any re-capture recommendation.

---

## Honest residuals

1. **Photo-of-inked-print quality** is consumer-grade. If minutiae count comes back below 30 per finger, re-capture with better lighting or thicker ink.
2. **Fingerprint is time-invariant** in adults (barring serious injury), so this is genuinely one-time. If you cut a finger badly between now and trial day 30, re-capture only that finger.
3. **C7 condition is the only place fingerprint is used.** If you skip this capture entirely, the trial protocol still runs at C0/C2/C5 (the focused-4 minus C7). C7 just becomes "not measured" rather than failing.
4. **Privacy:** the fingerprint files are committed to your private repo. If you ever publish the data, redact or hash these files first. The agent's feature extraction produces an irreversible feature vector (~16 floats), which is publishable; the source images are not.

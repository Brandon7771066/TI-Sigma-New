# Mendi BLE Reverse-Engineering Plan (Path B)

**Date:** 2026-05-01
**Goal:** Decode the Mendi headband's BLE protocol so we can read raw HbO2 / HbR samples directly into Replit, bypassing the Mendi phone app entirely.
**Cost:** $0 hardware, ~10–20 hours of agent time, 50/50 success probability (depends on whether Mendi uses encrypted pairing).
**Priority:** Backlog — do NOT start until URB #826 §10.6 H10 window completes (~2026-05-22). Mendi is not on the URB #826 critical path.

---

## What "reverse-engineering" actually means here

The Mendi headband talks to its phone app over Bluetooth Low Energy (BLE). BLE devices expose **services** and **characteristics** (each with a UUID) — these are like network endpoints on a tiny embedded HTTP server. To read fNIRS data without the Mendi app, we need:

1. The list of services + characteristics the headband exposes (service UUIDs, characteristic UUIDs, and which ones are `notify`/`read`/`write`).
2. The **payload format** of the streaming characteristic — how raw HbO2/HbR/quality numbers are packed into bytes (little-endian? IEEE-754 float32? scaled integer? framing bytes?).
3. Whether the device requires **bonded pairing** (encrypted link with a stored key) or accepts a fresh BLE client.

If (3) returns "encrypted with rotating key", we stop — that's a $0 dead end and we move to Path C (different device, out of budget). If (3) returns "open" or "static-key", we proceed with steps 1–2.

---

## What you need to do (one-time setup, ~30 min on phone)

I cannot capture BLE packets from inside Replit — packet capture has to happen on your physical phone while it talks to the headband. Here's the minimum protocol:

### Step 1 — Install nRF Connect for Mobile

- Free app from Nordic Semiconductor (the BLE chipset vendor; trustworthy, used by professional embedded engineers)
- iOS: App Store → "nRF Connect for Mobile" by Nordic Semiconductor
- Android: Google Play → same name

### Step 2 — Scan + connect to the Mendi (without using the Mendi app)

- Power on the Mendi headband
- Open nRF Connect → Scanner tab → tap **Start scan**
- Find the device showing up as something like "Mendi" / "MENDI-XXXX" / a numeric ID — note the **device name** and **MAC address**
- Tap **Connect**
- It will list all services (UUIDs starting with `0000xxxx-0000-1000-8000-00805f9b34fb` for standard, or `xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx` for custom)

### Step 3 — Capture the service/characteristic tree

- In nRF Connect, with the Mendi still connected, expand each service to see its characteristics
- For each characteristic, note: **UUID**, **properties** (read/write/notify/indicate), and any **descriptor**
- Take screenshots of the full tree, OR tap the export/share button (top right) and email yourself the discovered GATT structure as JSON
- Drop the JSON / screenshots into `data/mendi/ble_discovery/` (folder will be created when you do)

### Step 4 — Capture a streaming sample

- In nRF Connect, find any characteristic with `NOTIFY` property
- Tap the multiple-arrows-down icon to subscribe to notifications
- Put the headband on your forehead and wear it for 30–60 seconds (NOT during a real Mendi-app session — disconnect from the Mendi app first)
- The notification log will show hex bytes flowing in. Take a screenshot of ~20–50 lines OR export the log
- Drop the log into `data/mendi/ble_capture/<date>/`

### Step 5 — Test pairing requirement

- After Step 4, fully power-cycle the headband
- Try Step 2 again from nRF Connect WITHOUT first opening the Mendi app
- If notifications still flow without the Mendi app being involved → **unencrypted, we proceed**
- If the headband refuses to connect, or if notifications return only encrypted bytes → **encrypted pairing, Path B blocked**

---

## What I do once you give me the captures

### Phase 1 — GATT structure mapping (~2 hours)

- Parse the exported GATT JSON / screenshots
- Identify which service is the fNIRS data stream (likely a custom UUID, not the standard Heart Rate or Battery service)
- Identify which characteristic carries notifications (the streaming one)
- Identify any characteristic that needs to be **written to** to start streaming (some BLE devices require `0x01` written to a control characteristic to enable data flow)

### Phase 2 — Payload decoding (~6–10 hours)

This is the hard part. I'll need ~30 seconds of captured hex bytes plus your subjective state during the capture (eyes open/closed, mental task, calm/excited). The decoder pipeline:

1. **Frame detection** — find repeating byte patterns (header bytes like `0xAA 0x55`, fixed-length packets, terminators)
2. **Field extraction** — for each frame, identify which bytes are HbO2, HbR, signal quality, timestamp, sequence number, CRC
3. **Endianness + dtype** — try little-endian first (overwhelming default for embedded), test float32, int16, int24-as-bytes
4. **Sanity check** — decoded HbO2 should be in physiologically plausible range (~50–80 µmol·mm), HbR ~20–50 µmol·mm, oxygenation 50–70%
5. **Cross-check against Mendi app values** — you take 3–5 simultaneous notes of what the Mendi app shows during a capture session; decoded values should match within ~5%

### Phase 3 — Replit BLE client (~2–4 hours)

- New file: `mendi_ble_client.py` — uses `bleak` (already installed)
- Connects to the headband by name or MAC address
- Subscribes to the streaming characteristic
- Decodes incoming frames using the Phase 2 decoder
- Writes rows directly into the existing `mendi_realtime_data` table (schema is already in place)

**Critical constraint:** `bleak` requires the BLE radio to be on the same machine running Python. **Replit cloud has no Bluetooth radio.** This means the BLE client must run on **your local Mac/PC/Raspberry Pi**, not on Replit. The client posts decoded samples to `mendi_data_bridge_api.py` (already running on port 8000 in this Repl) over HTTP.

### Phase 4 — Validation (~1–2 hours)

- Run a 5-minute capture session with you wearing the headband and noting subjective state every minute
- Compare decoded HbO2/HbR time series against the same data shown in the Mendi app afterward
- Acceptance: <10% per-sample deviation, correct trend direction, no dropped frames > 1% of total

---

## Honest probability breakdown

| Outcome | Probability | What it means |
|---|---|---|
| Step 5 returns "encrypted pairing required" | ~30% | Path B blocked. Stop. Move to Path C (different device) or retire Mendi. |
| GATT structure visible but payload is opaque-encrypted within an unencrypted characteristic | ~15% | Extremely unlikely (consumer BLE devices rarely double-wrap), but possible. Block. |
| GATT visible, payload decodable, but Mendi app required to "unlock" the headband each session | ~10% | Annoying but workable — you open Mendi app for 5 sec to wake the device, then disconnect, then run our client. |
| Clean unencrypted streaming, decodable in Phase 2 | ~45% | Path B succeeds. We get real raw fNIRS data. |

**My honest expectation: ~45% chance this works end-to-end.** That's the asymmetric-standards #69 honest number — not the "definitely works" framing that the original Nov 21 implementation plan implied.

---

## What success gives us

- Real per-second HbO2 / HbR samples streaming into the existing `mendi_realtime_data` table
- Mendi prefrontal coupling becomes a candidate feature for **a separate URB** (NOT URB #826 — different hypothesis space). Possible URB #827 candidate: "Prefrontal HbO2 dynamics during LCC-state intentions vs. baseline."
- Combined with H10 already running, you'd have synchronized prefrontal hemodynamics + cardiac autonomic signal — a much richer dataset for any future psi-prediction or coherence study.

## What failure gives us

- Confirmed empirical answer to the question "is Mendi worth continuing to invest in" — **no**.
- Permission to retire the Mendi code paths cleanly (delete the never-run `mendi_companion_uploader.py`, mark the bridge API endpoints deprecated, remove the simulated-curve fallback from the neurofeedback session UI).
- That's a real win under asymmetric-standards #69 even though it feels like a loss.

---

## Critical-path commitment

**I will NOT start Phase 1 until URB #826 §10.6 H10 collection completes (~2026-05-22 + 1 day for §10.6 to run).** The H10 window is the higher-value test and should not compete for attention. This document is a placeholder so the work has somewhere to land when it's time.

When that day arrives:
1. You complete Steps 1–5 above (~30 min on your phone)
2. You drop the captures in `data/mendi/ble_discovery/` and `data/mendi/ble_capture/<date>/`
3. I run Phases 1–4
4. We know in ~1–2 weeks of agent time whether Path B succeeded.

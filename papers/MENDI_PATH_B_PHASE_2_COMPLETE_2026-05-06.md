# Mendi BLE Path B — Phase 2 COMPLETE
**Date**: 2026-05-06
**Status**: GATT discovery + payload decode → both DONE in single 10-min session
**Source data**: `data/mendi/ble_discovery/gatt_2026-05-06.json` + `data/mendi/ble_capture/raw_meditation-2026-05-06.jsonl`

## TL;DR
After ~5 days of being blocked, Path B Phase 2 was completed in a single 10-minute capture. Mendi BLE protocol = **protobuf-encoded varints**; main stream characteristic identified; decoder shipped to `mendi_ble_client.py`.

## GATT topology

Service: `fc3eabb0-c6c4-49e6-922a-6e551c455af5` (Mendi proprietary, 6 characteristics)

| Char | UUID suffix | Properties | Role (decoded) |
|---|---|---|---|
| bb1 | `fc3eabb1-...` | read+notify | Device-state snapshot at startup (97-byte protobuf, 16 fields) |
| bb2 | `fc3eabb2-...` | write+notify | Control channel A (untested — Mendi auto-streams) |
| bb3 | `fc3eabb3-...` | write+notify | Control channel B (untested) |
| **bb4** | `fc3eabb4-...` | **read+notify** | **MAIN STREAM** — single varint, ~1.4 Hz |
| bb5 | `fc3eabb5-...` | notify | 9-byte session header at startup |
| bb6 | `fc3eabb6-...` | read+write+notify | Config (untested) |

Plus standard GATT services: Generic Access, Generic Attribute, Device Information, **Nordic DFU** (`8ec90003-...` Buttonless DFU = OTA firmware-update path; useful intel for future patching/replacement).

## Wire format — bb4 main stream

Every bb4 frame is exactly 3 bytes: `08 <varint_lo> <varint_hi>`
- `0x08` = protobuf tag (field id 1, wire type 0 = varint)
- Varint decodes to a single unsigned integer

**Decoded over 737 frames during 10-min meditation:**
- Min = 3820, Max = 3832, **Range = 12 units**
- Mean = 3825.32, Median = 3826, Stdev = 2.36
- First 20 samples mean ~3829, last 20 samples mean ~3822 → **slow downward drift ~7 units / 10 min**

### Interpretation (best-supported hypothesis)

Values cluster at ~93% of a 4095-max range = **12-bit ADC reading from the NIR photodetector** (raw optical intensity returning to the sensor). Lower values = more absorption = more chromophore (HbO₂ + HbR) in the optical path.

The **observed downward drift** is consistent with either:
1. Slight venous pooling during stillness (more HbR over time)
2. Optode-pressure drift / thermal drift
3. A genuine very-small hemodynamic response

**Stdev of 2.4 over a 0-4095 ADC = noise floor of ~0.06%**, which is impressive but means any signal smaller than ~3 ADC units is indistinguishable from device noise. To isolate signal vs noise you need a session with a **known cognitive stimulus** (mental arithmetic, breath-hold, etc.) so a hemodynamic response should be triggered at a known timestamp.

## Streaming behavior — important caveat

Two 156-second gaps (at t=201s and t=361s of the 518-s actual session — script returned ~82s early) → **the Mendi was actively streaming for only 207 of 518 seconds (~40%)**. Almost certainly forehead-contact loss or low-power timeout. Practical implications:
- For URB #828 trial-1 (5/22), tag actual contact-loss events
- Consider a watchdog: if no frame for 5s, log "DROPOUT" and re-subscribe

## Startup snapshot (bb1, 97 bytes, 16 protobuf fields)

| Field | Value | Likely meaning |
|---|---|---|
| 1 | -2151 (signed) | calibration offset / accel axis |
| 2 | 14589 | counter / serial |
| 3 | 996 | counter |
| 4 | 2064 | counter |
| 5 | -3255 | calibration offset |
| 6 | -2335 | calibration offset |
| **7** | **25.5625 (float32)** | **temperature °C OR battery voltage** ← strongest interpretation handle |
| 8 | 34176 | counter |
| 9 | 13752 | counter |
| 10 | -440 | offset |
| 11-16 | mixed signed/unsigned ints | bookkeeping / per-LED calibration |

**Field 7 = 25.5625 °C** is exactly room temperature in a comfortable indoor space → strongly suggests it's the device-onboard temp sensor reading (used internally to compensate LED/photodetector drift).

## Session header (bb5, 9 bytes)
```
0a 03 08 f7 1d 10 01 18 01
field 1 (length-delimited, 3 bytes) = nested protobuf "08 f7 1d" = varint 3831 (initial sample)
field 2 = 1
field 3 = 1
```
So bb5 = `{initial_sample: 3831, session_id: 1, mode: 1}`. Confirms the bb4 stream encodes raw ADC values (matches initial sample = 3831, well within bb4's observed 3820-3832 range).

## Files shipped

1. `mendi_decode.py` — standalone protobuf decoder (no dependencies beyond stdlib)
2. `mendi_ble_client.py` — patched: `STREAM_CHAR_UUID`, `STREAM_SVC_UUID`, `decode_frame()` all live
3. `data/mendi/ble_capture/decoded_meditation-2026-05-06.csv` — 737-row time series with elapsed seconds + value
4. `mendi_capture.py` (Brandon-local on `C:\Users\brand\`) — Windows-friendly capture script

## Next-up Phase 3 (now unblocked)

| Task | Effort | Blocker |
|---|---|---|
| Wire `mendi_ble_client.py` decoded output → POST to `mendi_data_bridge_api.py` | 30 min, agent | None — ready |
| **Stimulus-validation session**: 10-min capture with mental-math task at t=2:00 and breath-hold at t=5:00 to detect hemodynamic response | 10 min Brandon + 1h agent | Need Brandon to run script with logged event timestamps |
| Decode bb1 fields by capturing 5+ startup snapshots over different battery levels / temps | iterative | Need 5 reboots over a few days |
| Test `bb2`/`bb3` write commands to figure out start/stop/calibrate | unknown | Risk of bricking → defer |

## Honest assessment (Asymmetric-Standards #69)

- **Decode confidence: HIGH for the wire format** (protobuf is unambiguous, three independent characteristic payloads all decode cleanly without ambiguity).
- **Decode confidence: MEDIUM for the physical interpretation** (12-bit ADC NIR intensity is the strongest hypothesis but unverified; could equally be raw HbO₂ count × 50, or some Mendi-internal score). **Stimulus session is the verification path** — if the value drops by >50 ADC units during a known cognitive task, NIR-intensity hypothesis confirmed.
- **What this does NOT do**: it does not compute HbO₂/HbR µmol·mm separately. The Mendi only has 1-2 LED wavelengths in a single optode → cannot do true Beer-Lambert oxygenation calculation regardless of decoder. Best we get is a **single mixed signal** that correlates with prefrontal blood volume.
- This unblock is real but the device's fundamental fNIRS-grade limitations (covered in `papers/MENDI_FNIRS_AUDIT_2026-05-01.md`) are unchanged.

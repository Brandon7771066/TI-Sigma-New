# Mendi Path B Status — 2026-05-01 PM

**Status:** SCAFFOLD COMPLETE on Replit. **AWAITING BRANDON LOCAL EXECUTION** (Replit has no BLE radio; Phase 1 must run on Brandon's machine).
**Honest end-to-end success estimate:** ~45% (unchanged from `papers/MENDI_BLE_REVERSE_ENGINEERING_PLAN.md`).
**Cost:** $0 hardware (uses Brandon's existing Mendi headband + laptop/phone with BLE).
**Cross-links:** `papers/MENDI_BLE_REVERSE_ENGINEERING_PLAN.md`, `mendi_ble_client.py`, `mendi_data_bridge_api.py`, `PIPELINE.md`.

---

## What's done (agent side)

1. ✅ **Audit** of all six prior Mendi attempts: `papers/MENDI_FNIRS_AUDIT_2026-05-01.md`. DB reality: 5 synthetic CSV-upload rows from 2025-11-23 only. Consumer Mendi exposes no public BLE characteristics.
2. ✅ **Path B 4-phase plan**: `papers/MENDI_BLE_REVERSE_ENGINEERING_PLAN.md`.
3. ✅ **`mendi_ble_client.py`** — `bleak`-based scaffold with three subcommands:
   - `--scan` (Phase 1a): list nearby BLE peripherals, identify the Mendi by name/MAC/manufacturer-ID.
   - `--discover-gatt <MAC>` (Phase 1b): enumerate the Mendi's GATT services, characteristics, and descriptors; write JSON catalog to `data/mendi/ble_discovery/<MAC>_<TIMESTAMP>.json`.
   - `--stream <MAC> <CHARACTERISTIC_UUID>` (Phase 2 placeholder): subscribe to a candidate notification characteristic; log raw bytes to `data/mendi/ble_capture/<MAC>_<TIMESTAMP>.bin` for offline reverse-engineering.
4. ✅ **Drop folders**: `data/mendi/ble_discovery/` and `data/mendi/ble_capture/` (created).
5. ✅ **Server endpoint**: `mendi_data_bridge_api.py` accepts POSTs from the local client once Phase 2 yields parsed values.

---

## What's blocked on Brandon (5–10 minutes for Phase 1)

**Replit cannot do this.** No BLE radio in the cloud sandbox. Brandon must run on his own machine.

### Step-by-step Phase 1 (BLE discovery) — Brandon's local machine

Time required: ~5–10 minutes total.

```bash
# 1. Clone the repo (or pull latest) on your local machine
git pull

# 2. Install the one dependency (in a venv if you prefer)
pip install bleak

# 3. Turn ON the Mendi headband (button until LEDs)

# 4. Scan: identify the Mendi BLE address
python mendi_ble_client.py --scan

# Expected output: a list of nearby BLE peripherals with names + MAC addresses.
# Look for "Mendi" or similar; copy the MAC address (format: XX:XX:XX:XX:XX:XX).

# 5. Discover GATT services on that MAC
python mendi_ble_client.py --discover-gatt XX:XX:XX:XX:XX:XX

# Expected output: JSON catalog of services/characteristics written to
# data/mendi/ble_discovery/XX_XX_XX_XX_XX_XX_<TIMESTAMP>.json

# 6. Commit the JSON catalog and push so the agent can analyze
git add data/mendi/ble_discovery/
git commit -m "Mendi Phase 1 BLE catalog"
git push
```

**Expected timeline once Brandon runs the above:**
- Phase 1: 5–10 minutes (Brandon-local).
- Phase 1 analysis (agent identifies candidate characteristic UUIDs from the catalog): ~30 minutes (agent-side, after Brandon pushes).
- Phase 2 streaming capture: 10–20 minutes per session (Brandon-local), 2–3 sessions needed for byte-pattern analysis.
- Phase 2 offline parsing (agent reverse-engineers the protocol): 2–8 hours (agent-side, depends on protocol complexity).
- Phase 3 (live integration with `mendi_data_bridge_api.py`): 1–2 hours (agent-side).
- Phase 4 (validate against §10.6 baseline): 1–2 trial days.

**Total Brandon-time investment: ~30 minutes spread across 3–4 sessions.**
**Total agent-time investment: ~5–12 hours.**

---

## Why this is currently deferred

The original deferral to ~2026-05-22 was because:
1. Brandon's bandwidth was on the §10.6 H10 daily protocol.
2. Mendi data is *not* on the URB #828 v2 critical path (it's not in the locked C5 stack — the locked C5 uses H10 + Pulsoid + log, no Mendi).

**However, Mendi is still useful for:**
- A future H_BFG-adjacent experiment (fNIRS may share some optical-channel content with biophoton emission under URB #826).
- A 5th live-channel arm in URB #828 follow-on experiments (post-2026-09-22).
- General biofeedback validation of the Mendi device for personal use.

**Recommendation:** Brandon spends 5 minutes running the `--scan` step *whenever convenient* (no rush). The data lands in git and the agent picks it up next session. There's no critical-path blocker either way.

---

## Honest residuals

1. **45% end-to-end success estimate is unchanged.** Consumer Mendi may use rolling encryption keys (kills BLE reverse-engineering), or send only summary scores not raw fNIRS (limits scientific value), or require a phone-app handshake before unlocking BLE characteristics (kills standalone capture).
2. **If Phase 1 reveals only encrypted/proprietary characteristics**, Path B fails honestly. We pivot to:
   - Path A: manual entry of Mendi-app-displayed scores (low value, $0).
   - Or shelf the Mendi entirely until a teardown community (e.g., Reddit r/Mendi) publishes a protocol spec.
3. **No data has been captured yet** because Phase 1 hasn't been run. The DB still shows only the 5 synthetic 2025-11-23 rows. Honest scope: zero new Mendi data added 2026-05-01.

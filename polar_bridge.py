"""
Polar H10 → TI Platform Bridge
================================
Run this on your LOCAL machine (Acer), NOT on Replit.

Connects to your Polar H10 via Bluetooth LE and streams
heart rate + HRV data to the TI Platform on Replit.

SETUP:
  1. Install dependencies:
         pip install bleak requests

  2. IMPORTANT — disconnect Polar from Windows BT settings first:
         Windows Settings → Bluetooth → click Polar H10 → Remove device
         (Windows holding the connection blocks bleak from accessing it)

  3. Set your Replit URL below

  4. Run:
         python polar_bridge.py

  5. Put on the Polar H10 strap (moisten electrodes)
     The script will find and connect automatically.
"""

import asyncio
import requests
import time
import struct
from datetime import datetime

try:
    from bleak import BleakScanner, BleakClient
    BLEAK_OK = True
except ImportError:
    print("ERROR: bleak not installed. Run: pip install bleak requests")
    BLEAK_OK = False

# ─── CONFIG ──────────────────────────────────────────────────────────────────
REPLIT_URL = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"
SESSION_ID = "polar_bridge_live"
UPLOAD_ENDPOINT = f"{REPLIT_URL}/api/upload"

# Polar H10 BLE UUIDs
HR_SERVICE_UUID       = "0000180d-0000-1000-8000-00805f9b34fb"
HR_MEASUREMENT_UUID   = "00002a37-0000-1000-8000-00805f9b34fb"
BATTERY_UUID          = "00002a19-0000-1000-8000-00805f9b34fb"
# ─────────────────────────────────────────────────────────────────────────────

# Live state
latest_hr    = 0
rr_intervals = []   # running list, cleared after each upload
upload_count = 0


def parse_hr_measurement(data: bytearray):
    """Parse Bluetooth HR Measurement characteristic (spec §3.106)."""
    if not data:
        return 0, []

    flags = data[0]
    hr_format_16bit = flags & 0x01
    rr_present      = flags & 0x10

    idx = 1
    if hr_format_16bit:
        hr = struct.unpack_from('<H', data, idx)[0]
        idx += 2
    else:
        hr = data[idx]
        idx += 1

    rr_list = []
    if rr_present:
        while idx + 1 < len(data):
            rr_raw = struct.unpack_from('<H', data, idx)[0]
            rr_ms  = rr_raw / 1024.0 * 1000.0   # 1/1024 s units → ms
            rr_list.append(round(rr_ms, 1))
            idx += 2

    return hr, rr_list


def compute_rmssd(rr_list):
    """Root mean square of successive differences."""
    if len(rr_list) < 2:
        return 0.0
    diffs_sq = [(rr_list[i+1] - rr_list[i])**2 for i in range(len(rr_list)-1)]
    return round((sum(diffs_sq) / len(diffs_sq)) ** 0.5, 2)


def hr_callback(sender, data: bytearray):
    """Called by bleak each time a new HR packet arrives (~1 Hz)."""
    global latest_hr, rr_intervals
    hr, rr_list = parse_hr_measurement(data)
    latest_hr = hr
    rr_intervals.extend(rr_list)


def upload_to_replit(hr, rr_list):
    """POST HR + HRV snapshot to Replit gateway."""
    global upload_count
    rmssd = compute_rmssd(rr_list)
    rr_avg = round(sum(rr_list) / len(rr_list), 1) if rr_list else 0

    payload = {
        "heart_rate":    hr,
        "hr":            hr,
        "rr_interval":   rr_avg,
        "rmssd":         rmssd,
        "polar_connected": True,
        "muse_connected":  False,
        "device_id":     "POLAR_H10_BRIDGE",
        "session_id":    SESSION_ID,
        "timestamp":     datetime.utcnow().isoformat(),
    }

    try:
        r = requests.post(UPLOAD_ENDPOINT, json=payload, timeout=5)
        upload_count += 1
        bar = "█" * min(int(hr / 5), 20)
        rr_str = f"  RR avg={rr_avg}ms  RMSSD={rmssd}" if rr_avg else ""
        status = f"✓ {r.status_code}" if r.status_code in (200, 201) else f"✗ {r.status_code}"
        print(f"  {datetime.now().strftime('%H:%M:%S')}  HR: {hr:3d} bpm  [{bar:<20}]{rr_str}  {status}")
    except requests.exceptions.ConnectionError:
        print(f"  {datetime.now().strftime('%H:%M:%S')}  HR: {hr:3d} bpm  [CONNECTION ERROR — is Replit running?]")
    except Exception as e:
        print(f"  {datetime.now().strftime('%H:%M:%S')}  Upload error: {e}")


async def find_polar():
    """Scan for Polar H10 and return its address."""
    print("\n  Scanning for Polar H10 (10 seconds)...")
    devices = await BleakScanner.discover(timeout=10.0)
    for d in devices:
        if d.name and "Polar" in d.name:
            print(f"  Found: {d.name}  [{d.address}]")
            return d.address
    return None


async def run():
    """Main loop: find → connect → stream → upload every 2s."""
    global rr_intervals

    if not BLEAK_OK:
        return

    print("=" * 58)
    print("  Polar H10 → TI Platform Bridge")
    print("=" * 58)
    print(f"  Uploading to: {UPLOAD_ENDPOINT}")
    print("=" * 58)

    address = await find_polar()
    if not address:
        print("\n  ERROR: Polar H10 not found.")
        print("  Make sure:")
        print("    1. Polar H10 is turned on (strap moistened + worn)")
        print("    2. Polar H10 is REMOVED from Windows BT settings")
        print("    3. You are within ~3m of the device")
        return

    print(f"\n  Connecting to {address} ...")
    try:
        async with BleakClient(address, timeout=15.0) as client:
            if not client.is_connected:
                print("  ERROR: Could not connect.")
                return

            print("  CONNECTED  ✓")
            print("  Starting HR stream ...\n")

            await client.start_notify(HR_MEASUREMENT_UUID, hr_callback)

            while client.is_connected:
                await asyncio.sleep(2)
                if latest_hr > 0:
                    snapshot_rr = rr_intervals.copy()
                    rr_intervals.clear()
                    upload_to_replit(latest_hr, snapshot_rr)
                else:
                    print(f"  {datetime.now().strftime('%H:%M:%S')}  Waiting for HR data ...")

    except Exception as e:
        err = str(e)
        print(f"\n  Connection error: {err}")
        if "access" in err.lower() or "in use" in err.lower() or "winrt" in err.lower():
            print("\n  LIKELY CAUSE: Windows Bluetooth is still holding the Polar H10.")
            print("  FIX: Go to Windows Settings → Bluetooth → Polar H10 → Remove device")
            print("       Then run this script again.")
        elif "not found" in err.lower():
            print("\n  LIKELY CAUSE: Polar H10 went out of range or powered off.")


def main():
    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        print(f"\n\n  Stopped. {upload_count} uploads sent.")


if __name__ == "__main__":
    main()

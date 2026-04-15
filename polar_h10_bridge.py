"""
Polar H10 → TI Platform Bridge
================================
Run this on your Acer laptop to stream heart rate + HRV to the Mood Amplifier.

SETUP (one time only):
  pip install bleak requests

  Then just run:
    python polar_h10_bridge.py

Your Polar H10 must be:
  - Wet (lick or wet the two electrode bumps on the strap)
  - Worn snugly on your chest
  - Turned on (it auto-powers when worn)
  - NOT connected to any other app (close Polar Flow, Polar Beat, etc.)

Press Ctrl+C to stop.
"""

import asyncio
import math
import time
import json
import requests
from datetime import datetime
from collections import deque

try:
    from bleak import BleakScanner, BleakClient
except ImportError:
    print("=" * 60)
    print("  ERROR: bleak is not installed.")
    print("  Fix: open Command Prompt and run:")
    print("       pip install bleak requests")
    print("=" * 60)
    exit(1)

# ── Configuration ──────────────────────────────────────────────
REPLIT_URL   = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"
POST_INTERVAL = 5   # seconds between uploads
# ───────────────────────────────────────────────────────────────

HR_SERVICE_UUID  = "0000180d-0000-1000-8000-00805f9b34fb"
HR_CHAR_UUID     = "00002a37-0000-1000-8000-00805f9b34fb"

_rr_buffer = deque(maxlen=30)   # store last 30 RR intervals (≈30 s)
_last_hr   = 0
_packet_count = 0


def _parse_hr_measurement(data: bytearray):
    """
    Parse standard Bluetooth GATT Heart Rate Measurement characteristic.
    Returns (heart_rate, [rr_interval_ms, ...])
    """
    flags = data[0]
    hr_format = flags & 0x01         # 0 = UINT8, 1 = UINT16
    rr_present = (flags >> 4) & 0x01

    if hr_format == 0:
        hr = data[1]
        offset = 2
    else:
        hr = int.from_bytes(data[1:3], 'little')
        offset = 3

    rr_intervals = []
    if rr_present:
        while offset + 1 < len(data):
            rr_raw = int.from_bytes(data[offset:offset+2], 'little')
            rr_ms = round(rr_raw * 1000 / 1024)   # convert 1/1024 s → ms
            rr_intervals.append(rr_ms)
            offset += 2

    return hr, rr_intervals


def _compute_rmssd(rr_list):
    """Root mean square of successive RR differences."""
    if len(rr_list) < 2:
        return None
    diffs = [rr_list[i+1] - rr_list[i] for i in range(len(rr_list)-1)]
    rmssd = math.sqrt(sum(d*d for d in diffs) / len(diffs))
    return round(rmssd, 1)


def _hr_callback(sender, data: bytearray):
    global _last_hr, _packet_count
    hr, rr_intervals = _parse_hr_measurement(data)
    _last_hr = hr
    _packet_count += 1
    for rr in rr_intervals:
        if 300 < rr < 2000:   # sanity: 30–200 bpm
            _rr_buffer.append(rr)


def _post_to_replit():
    """Upload current HR + HRV snapshot to Replit."""
    rr_list = list(_rr_buffer)
    rmssd   = _compute_rmssd(rr_list)
    payload = {
        "heart_rate":   _last_hr,
        "rr_interval":  rr_list[-1] if rr_list else None,
        "rr_intervals": rr_list[-10:],
        "rmssd":        rmssd,
        "coherence":    round(min(1.0, (rmssd or 0) / 100.0), 3) if rmssd else None,
        "source":       "polar_h10_bridge",
        "device_id":    "POLAR_H10",
        "session_id":   "live_hrv_session",
        "polar_connected": True,
    }
    payload = {k: v for k, v in payload.items() if v is not None}
    try:
        r = requests.post(
            f"{REPLIT_URL}/api/polar/upload",
            json=payload, timeout=6
        )
        status = "✓" if r.status_code in (200, 201) else f"✗ {r.status_code}"
        ts = datetime.now().strftime("%H:%M:%S")
        bar_hr = "♥" * min(10, max(0, (_last_hr - 50) // 5))
        print(f"  {ts} | HR: {_last_hr:3d} bpm  {bar_hr:<10}  "
              f"RMSSD: {rmssd or '---':>6}  [{status}]")
    except Exception as e:
        print(f"  ✗  Cannot reach Replit: {e}")


async def _find_polar():
    print("🔍 Scanning for Polar H10 (10 s)...")
    devices = await BleakScanner.discover(timeout=10.0)
    for d in devices:
        if d.name and "Polar" in d.name:
            print(f"✅ Found: {d.name}  ({d.address})")
            return d.address
    return None


async def run():
    address = await _find_polar()
    if not address:
        print()
        print("❌ Polar H10 not found.")
        print("   • Wet the strap electrodes and wear it snugly")
        print("   • Close Polar Flow / Polar Beat apps if open")
        print("   • Make sure Windows Bluetooth is ON")
        print("   • Try: Windows Settings → Bluetooth → Add device → Polar H10")
        print("     (pair it once, then re-run this script)")
        return

    print(f"🔗 Connecting to {address} ...")
    async with BleakClient(address, timeout=20.0) as client:
        if not client.is_connected:
            print("❌ Connection failed — retry in a moment.")
            return

        print(f"✅ Connected to Polar H10!")
        print(f"📡 Uploading to Replit every {POST_INTERVAL}s")
        print(f"{'─'*60}")
        print(f"   Time    |  HR         |  RMSSD  | Status")
        print(f"{'─'*60}")

        await client.start_notify(HR_CHAR_UUID, _hr_callback)

        _next_post = time.time() + POST_INTERVAL
        while client.is_connected:
            await asyncio.sleep(0.5)
            if time.time() >= _next_post:
                if _last_hr > 0:
                    _post_to_replit()
                else:
                    print("  ⏳ Waiting for first HR packet...")
                _next_post = time.time() + POST_INTERVAL


def main():
    print()
    print("=" * 60)
    print("  POLAR H10 → TI PLATFORM BRIDGE")
    print("=" * 60)
    print(f"  Replit: {REPLIT_URL}")
    print(f"  Upload every {POST_INTERVAL}s")
    print()

    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        print("\n\n  Stopped. 👋")


if __name__ == "__main__":
    main()

"""
Polar H10 → TI Platform Bridge
================================
Run this on your Acer laptop. Press Ctrl+C to stop.

First-time setup (if Polar not found):
  Windows Settings → Bluetooth → Add device → search for Polar H10 → Pair
  Then re-run this script.
"""

import asyncio
import math
import sys
import time
import requests
from datetime import datetime
from collections import deque

# Windows: bleak requires SelectorEventLoop (not the default ProactorEventLoop)
if sys.platform == "win32":
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())

try:
    from bleak import BleakScanner, BleakClient
except ImportError:
    print("=" * 60)
    print("  ERROR: bleak is not installed.")
    print("  Fix — open Command Prompt and run:")
    print("       python -m pip install bleak requests")
    print("=" * 60)
    input("Press Enter to exit...")
    sys.exit(1)

# ── Configuration ──────────────────────────────────────────────
REPLIT_URL    = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"
POST_INTERVAL = 5   # seconds between uploads
# ───────────────────────────────────────────────────────────────

HR_CHAR_UUID = "00002a37-0000-1000-8000-00805f9b34fb"

_rr_buffer  = deque(maxlen=30)
_last_hr    = 0
_connected  = False


def _parse_hr(data: bytearray):
    flags = data[0]
    hr_16bit   = flags & 0x01
    rr_present = (flags >> 4) & 0x01
    hr = int.from_bytes(data[1:3], 'little') if hr_16bit else data[1]
    offset = 3 if hr_16bit else 2
    rrs = []
    if rr_present:
        while offset + 1 < len(data):
            rr_ms = round(int.from_bytes(data[offset:offset+2], 'little') * 1000 / 1024)
            if 300 < rr_ms < 2000:
                rrs.append(rr_ms)
            offset += 2
    return hr, rrs


def _rmssd(rr_list):
    if len(rr_list) < 2:
        return None
    diffs = [rr_list[i+1] - rr_list[i] for i in range(len(rr_list)-1)]
    return round(math.sqrt(sum(d*d for d in diffs) / len(diffs)), 1)


def _on_hr(sender, data: bytearray):
    global _last_hr
    hr, rrs = _parse_hr(data)
    _last_hr = hr
    _rr_buffer.extend(rrs)


def _post():
    rr_list = list(_rr_buffer)
    rv      = _rmssd(rr_list)
    payload = {
        "heart_rate":      _last_hr,
        "rr_interval":     rr_list[-1] if rr_list else None,
        "rr_intervals":    rr_list[-10:],
        "rmssd":           rv,
        "coherence":       round(min(1.0, rv / 100.0), 3) if rv else None,
        "source":          "polar_h10_bridge",
        "device_id":       "POLAR_H10",
        "session_id":      "live_hrv_session",
        "polar_connected": True,
    }
    payload = {k: v for k, v in payload.items() if v is not None}
    try:
        r = requests.post(f"{REPLIT_URL}/api/polar/upload", json=payload, timeout=6)
        ok = "✓" if r.status_code in (200, 201) else f"✗ HTTP {r.status_code}"
    except Exception as e:
        ok = f"✗ {e}"
    ts  = datetime.now().strftime("%H:%M:%S")
    bar = "♥" * min(10, max(0, (_last_hr - 50) // 5))
    print(f"  {ts} | HR: {_last_hr:3d} bpm  {bar:<10}  RMSSD: {rv or '---':>6}  [{ok}]")


async def _find_polar():
    print("🔍 Scanning for Polar H10 (15 s) — all visible BLE devices:\n")
    found = {}
    devices = await BleakScanner.discover(timeout=15.0)
    for d in devices:
        name = d.name or "(unnamed)"
        print(f"   {name:<30}  {d.address}")
        found[d.address] = name
    print()
    # Try to match Polar H10 by name
    for addr, name in found.items():
        if name and ("Polar" in name or "H10" in name):
            print(f"✅ Matched: {name} ({addr})")
            return addr
    return None


async def run():
    global _connected
    address = await _find_polar()
    if not address:
        print("❌ Polar H10 not found in the scan above.")
        print()
        print("  Fix options:")
        print("  1. Windows Settings → Bluetooth → Add device")
        print("     → search for 'Polar H10' → click Pair")
        print("     Then re-run this script.")
        print()
        print("  2. Make sure the strap is wet and on your chest.")
        print("  3. Close Polar Flow / Polar Beat — they block BLE.")
        print()
        input("Press Enter to exit...")
        return

    print(f"🔗 Connecting to {address} ...")
    try:
        async with BleakClient(address, timeout=20.0) as client:
            if not client.is_connected:
                print("❌ Connection failed. Retry in a moment.")
                return
            _connected = True
            print(f"✅ Connected to Polar H10!")
            print(f"📡 Uploading to Replit every {POST_INTERVAL}s")
            print(f"{'─'*60}")
            print(f"   Time    |  HR              |  RMSSD  | Status")
            print(f"{'─'*60}")

            await client.start_notify(HR_CHAR_UUID, _on_hr)

            _next = time.time() + POST_INTERVAL
            while client.is_connected:
                await asyncio.sleep(0.5)
                if time.time() >= _next:
                    if _last_hr > 0:
                        _post()
                    else:
                        print("  ⏳ Waiting for first HR packet — is strap wet and snug?")
                    _next = time.time() + POST_INTERVAL
    except Exception as e:
        print(f"\n❌ BLE error: {e}")
        print()
        print("  Common fixes:")
        print("  • Pair Polar H10 in Windows Bluetooth settings first")
        print("  • Close Polar Flow / Polar Beat / any Polar app")
        print("  • Try: Windows Settings → Bluetooth → remove Polar H10 → re-pair")
        input("\nPress Enter to exit...")


def main():
    print()
    print("=" * 60)
    print("  POLAR H10 → TI PLATFORM BRIDGE")
    print("=" * 60)
    print(f"  Replit: {REPLIT_URL}")
    print(f"  Upload every {POST_INTERVAL}s | Python {sys.version.split()[0]}")
    print()
    try:
        asyncio.run(run())
    except KeyboardInterrupt:
        print("\n\n  Stopped. 👋")


if __name__ == "__main__":
    main()

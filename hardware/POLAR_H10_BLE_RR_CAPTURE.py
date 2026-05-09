"""
POLAR H10 LIVE BLE GATT RR CAPTURE — T2-B Option B (Pass 12 ratified)
=====================================================================

Captures real RR-intervals (HRV-grade) directly from a Polar H10 chest
strap over BLE GATT (HRM service 0x180D, characteristic 0x2A37). Saves
to data/polar_h10/ as a session JSON with header carrying pre+post
GILE-scale PD scores.

This script targets a Brandon-local laptop / Mac with a Bluetooth
adapter present. It WILL NOT work in this Replit container (no BLE
hardware). Run locally:

    pip install bleak    # one-time
    python hardware/POLAR_H10_BLE_RR_CAPTURE.py

Pre-session prompt asks for a PD self-report (urb_755 5-item GILE
scale, see papers/T2_INSTRUMENTATION_BATCH_PASS_11_2026-05-09.md).

Polar H10 advertises the standard BLE Heart Rate Service. Per spec:
  - Service UUID:        0x180D
  - HR Measurement char: 0x2A37 (notify)
  - Flags byte indicates RR-interval present (bit 4) and 8/16-bit HR

Brandon noted as of Pass 12 only ONE BLE GATT capture session exists
in the corpus (training-session-2026-05-03 onwards mostly came from
the Polar Flow JSON export which has no RR). This script is the path
to grow that count.
"""
import argparse
import asyncio
import json
import pathlib
import struct
import sys
import time
from datetime import datetime

try:
    from bleak import BleakClient, BleakScanner
except ImportError:
    sys.exit("ERROR: bleak required.  pip install bleak")

HRM_SERVICE_UUID = "0000180d-0000-1000-8000-00805f9b34fb"
HRM_CHAR_UUID    = "00002a37-0000-1000-8000-00805f9b34fb"

OUT_DIR = pathlib.Path("data/polar_h10")


def _parse_hrm_packet(data: bytes):
    """Parse 0x2A37 HR Measurement packet → (hr_bpm, [rr_intervals_ms])."""
    flags = data[0]
    hr_16bit = bool(flags & 0x01)
    rr_present = bool(flags & 0x10)
    idx = 1
    if hr_16bit:
        hr = struct.unpack_from("<H", data, idx)[0]; idx += 2
    else:
        hr = data[idx]; idx += 1
    # Sensor contact: bits 1-2 of flags (skip)
    # Energy expended: bit 3 — if set, 2 bytes
    if flags & 0x08:
        idx += 2
    rrs = []
    if rr_present:
        while idx + 1 < len(data):
            rr_raw = struct.unpack_from("<H", data, idx)[0]
            # RR is reported in 1/1024 sec units; convert to ms
            rrs.append(rr_raw * 1000.0 / 1024.0)
            idx += 2
    return hr, rrs


async def scan_for_polar(scan_seconds=8):
    print(f"Scanning {scan_seconds}s for Polar devices...")
    devs = await BleakScanner.discover(timeout=scan_seconds)
    polar = [d for d in devs if d.name and "polar" in d.name.lower()]
    if not polar:
        sys.exit("ERROR: no Polar device found. Make sure H10 is worn (skin contact wakes it).")
    for i, d in enumerate(polar):
        print(f"  [{i}] {d.name}  {d.address}")
    if len(polar) == 1:
        return polar[0].address
    sel = input("Select device index: ").strip()
    return polar[int(sel)].address


async def capture(address, duration_s, pre_pd, notes):
    samples = []   # list of (t, hr, [rr])
    t0 = time.time()

    def cb(_, data):
        hr, rrs = _parse_hrm_packet(data)
        samples.append({"t": time.time() - t0, "hr": hr, "rr": rrs})

    print(f"Connecting to {address}...")
    async with BleakClient(address) as client:
        if not client.is_connected:
            sys.exit("ERROR: failed to connect.")
        print("Connected. Subscribing to HR Measurement notifications...")
        await client.start_notify(HRM_CHAR_UUID, cb)
        print(f"Capturing {duration_s}s. Sit still, eyes closed (per T2 protocol).")
        try:
            await asyncio.sleep(duration_s)
        finally:
            await client.stop_notify(HRM_CHAR_UUID)
    print(f"Capture done. {len(samples)} HR notifications, "
          f"{sum(len(s['rr']) for s in samples)} RR-intervals total.")

    post_pd = float(input("Post-session PD (urb_755 GILE-scale, -2 to +2): "))
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    fname = OUT_DIR / f"ble_session_{datetime.now():%Y-%m-%dT%H%M%S}.json"
    fname.write_text(json.dumps({
        "subject_id": "B",
        "instrument": "Polar H10 BLE GATT 0x2A37",
        "instrument_version": "T2-B Option B Pass 12",
        "pre_pd": pre_pd, "post_pd": post_pd, "notes": notes,
        "duration_s": duration_s, "samples": samples,
        "captured_at": datetime.now().isoformat(),
    }, indent=2))
    print(f"Saved {fname}")


def main():
    ap = argparse.ArgumentParser(description="Polar H10 BLE GATT RR capture (T2-B Option B)")
    ap.add_argument("--duration", type=int, default=480,
                    help="Capture duration in seconds (default 480 = 8 min, T2 protocol)")
    ap.add_argument("--address", type=str, default=None,
                    help="Skip scan; supply Polar BLE address directly")
    args = ap.parse_args()

    print("\n=== T2-B Option B — Polar H10 BLE GATT capture ===\n")
    pre_pd = float(input("Pre-session PD (urb_755 GILE-scale, -2 to +2): "))
    notes = input("Notes (sleep, caffeine, food, time-of-day): ")

    addr = args.address or asyncio.run(scan_for_polar())
    asyncio.run(capture(addr, args.duration, pre_pd, notes))


if __name__ == "__main__":
    main()

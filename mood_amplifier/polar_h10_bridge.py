"""
Polar H10 → Replit Bridge

Subscribes to the Polar H10 standard Heart Rate Service (UUID 0x180D),
computes a rolling RMSSD from the RR-interval stream, and posts
HR + RMSSD to the Replit /api/upload endpoint every POST_INTERVAL_SEC
seconds. Pairs with the Muse OSC bridge so the cloud sees both EEG and
HRV under correlated rows.

Run on the Acer (after pairing the H10 in Windows Bluetooth):
    python -m pip install bleak requests
    python polar_h10_bridge.py

The script auto-discovers the H10 by name (substring "Polar H10").
It does NOT need to be the only Bluetooth client — Windows can keep its
generic HRM listener running concurrently in most cases, but if scanning
fails, unpair-then-repair the strap fresh in Windows Bluetooth.
"""
import asyncio
import collections
import math
import struct
import time
import urllib.parse
import urllib.request
from bleak import BleakClient, BleakScanner

REPLIT_URL = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev:5000"
UPLOAD_PATH = "/api/upload"
POST_INTERVAL_SEC = 3
DEVICE_NAME_HINT = "Polar H10"
HR_CHAR_UUID = "00002a37-0000-1000-8000-00805f9b34fb"
SESSION_ID = f"polar_{int(time.time())}"

last_hr = [0]
rr_buffer = collections.deque(maxlen=60)  # ~last minute of RR intervals
packet_count = [0]
post_count = [0]
last_post_status = [""]


def parse_hr_packet(data: bytearray):
    """Parse standard BLE Heart Rate Measurement packet → (hr_bpm, [rr_seconds])."""
    flags = data[0]
    hr_format_uint16 = bool(flags & 0x01)
    rr_present = bool(flags & 0x10)
    idx = 1
    if hr_format_uint16:
        hr = struct.unpack_from("<H", data, idx)[0]
        idx += 2
    else:
        hr = data[idx]
        idx += 1
    rr_list = []
    if rr_present:
        while idx + 1 < len(data):
            rr_1024 = struct.unpack_from("<H", data, idx)[0]
            idx += 2
            rr_list.append(rr_1024 / 1024.0)
    return hr, rr_list


def rmssd_ms(rr_seconds):
    if len(rr_seconds) < 2:
        return 0.0
    diffs = [
        (rr_seconds[i + 1] - rr_seconds[i]) * 1000.0
        for i in range(len(rr_seconds) - 1)
    ]
    if not diffs:
        return 0.0
    mean_sq = sum(d * d for d in diffs) / len(diffs)
    return math.sqrt(mean_sq)


def hr_handler(_sender, data):
    packet_count[0] += 1
    hr, rrs = parse_hr_packet(bytearray(data))
    if hr:
        last_hr[0] = hr
    for rr in rrs:
        if 0.3 < rr < 2.0:  # plausibility guard (30–200 bpm range)
            rr_buffer.append(rr)


async def post_loop():
    while True:
        await asyncio.sleep(POST_INTERVAL_SEC)
        rmssd = rmssd_ms(list(rr_buffer))
        params = {
            "heart_rate": str(int(last_hr[0])),
            "rmssd": f"{rmssd:.2f}",
            "muse": "0",
            "polar": "1",
            "dev": "PolarH10-Acer",
            "sid": SESSION_ID,
        }
        url = REPLIT_URL + UPLOAD_PATH + "?" + urllib.parse.urlencode(params)
        try:
            req = urllib.request.Request(url, method="GET")
            with urllib.request.urlopen(req, timeout=5) as r:
                code = r.status
            post_count[0] += 1
            last_post_status[0] = f"OK {code} at {time.strftime('%H:%M:%S')}"
        except Exception as e:
            last_post_status[0] = f"FAIL: {str(e)[:60]}"


async def status_loop():
    while True:
        await asyncio.sleep(1)
        print(
            f"\rH10  HR={last_hr[0]:>3d} bpm   "
            f"RMSSD={rmssd_ms(list(rr_buffer)):>6.1f} ms   "
            f"RRwindow={len(rr_buffer):>3d}   "
            f"pkts={packet_count[0]:>5d}   posts={post_count[0]:>4d}   "
            f"last={last_post_status[0]:<40s}",
            end="",
            flush=True,
        )


async def main():
    print("Scanning for Polar H10 (10 s)...")
    devs = await BleakScanner.discover(timeout=10.0)
    target = None
    for d in devs:
        nm = (d.name or "")
        if DEVICE_NAME_HINT.lower() in nm.lower():
            target = d
            print(f"Found: {nm}  [{d.address}]")
            break
    if target is None:
        print("❌ No Polar H10 found. Pair it in Windows Bluetooth first, then retry.")
        return

    print(f"Connecting to {target.address}...")
    print(f"Session ID: {SESSION_ID}")
    print(f"Bridge target: {REPLIT_URL}")
    print()

    async with BleakClient(target.address) as client:
        await client.start_notify(HR_CHAR_UUID, hr_handler)
        await asyncio.gather(post_loop(), status_loop())


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\nstopped.")

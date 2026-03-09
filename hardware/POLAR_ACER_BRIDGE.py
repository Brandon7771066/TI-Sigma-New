#!/usr/bin/env python3
"""
Polar H10 → Replit Bridge  (run this on your Acer laptop)
==========================================================
Reads heart rate directly from Polar H10 via Bluetooth
and sends it to the Replit app every 2 seconds.

SETUP:
  pip install bleak requests

USAGE:
  python POLAR_ACER_BRIDGE.py --url https://YOUR-APP.replit.app

The Polar H10 must already be paired to Windows via Settings → Bluetooth.
"""

import asyncio
import struct
import time
import argparse
import requests

# Standard BLE Heart Rate Measurement characteristic
HR_UUID = "00002a37-0000-1000-8000-00805f9b34fb"
POLAR_NAME = "Polar H10"

latest_hr = 0


def parse_hr_packet(data: bytearray) -> int:
    flags = data[0]
    if flags & 0x01:
        return struct.unpack_from("<H", data, 1)[0]
    return data[1]


def hr_callback(sender, data):
    global latest_hr
    latest_hr = parse_hr_packet(bytearray(data))
    print(f"  HR: {latest_hr} BPM", end="\r")


def post_to_replit(url: str, hr: int):
    try:
        resp = requests.post(
            f"{url.rstrip('/')}/api/upload",
            json={"hr": hr, "polar": True, "polar_connected": True},
            timeout=4,
        )
        if resp.status_code == 200:
            print(f"  Sent {hr} BPM → Replit ✓", end="\r")
        else:
            print(f"  POST failed: {resp.status_code}", end="\r")
    except Exception as e:
        print(f"  Network error: {e}", end="\r")


async def run(replit_url: str):
    from bleak import BleakScanner, BleakClient

    print("=" * 55)
    print("  Polar H10 → Replit Bridge")
    print("=" * 55)
    print(f"  Target: {replit_url}")
    print()

    print("  Scanning for Polar H10 via Bluetooth...")
    devices = await BleakScanner.discover(timeout=10)

    polar = None
    for d in devices:
        if d.name and POLAR_NAME in d.name:
            polar = d
            print(f"  Found: {d.name}  [{d.address}]")
            break

    if not polar:
        print()
        print("  Polar H10 NOT FOUND. Troubleshooting:")
        print("  1. Make sure it's paired in Windows Settings → Bluetooth")
        print("  2. Press the button on the H10 to wake it up")
        print("  3. Try running this script again")
        return

    print(f"  Connecting...")
    async with BleakClient(polar.address) as client:
        print(f"  Connected! Streaming to Replit every 2 seconds.")
        print(f"  Press Ctrl+C to stop.\n")
        await client.start_notify(HR_UUID, hr_callback)
        while True:
            await asyncio.sleep(2)
            if latest_hr > 0:
                post_to_replit(replit_url, latest_hr)


def main():
    parser = argparse.ArgumentParser(description="Polar H10 → Replit bridge")
    parser.add_argument(
        "--url",
        required=True,
        help="Your Replit app URL, e.g. https://abc123.replit.app",
    )
    args = parser.parse_args()

    try:
        asyncio.run(run(args.url))
    except KeyboardInterrupt:
        print("\n  Stopped.")


if __name__ == "__main__":
    main()

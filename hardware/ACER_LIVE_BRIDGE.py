#!/usr/bin/env python3
"""
ACER LIVE BIOMETRIC BRIDGE
===========================
Run this on your Acer laptop while the Replit app is open.
It sends Muse + Polar data directly to the Replit server.

Setup:
  pip install requests python-osc bleak

Usage:
  py ACER_LIVE_BRIDGE.py --server https://YOUR-REPLIT-URL

Modes:
  --muse   : Mind Monitor OSC only (Muse 2 EEG)
  --polar  : Polar H10 via BLE only (heart)
  --all    : Both devices (default)
  --demo   : Demo mode — no hardware needed, sends simulated data

Mind Monitor setup:
  Settings -> OSC -> IP: YOUR ACER LAN IP (e.g., 192.168.1.x)
  Port: 5001   (not 5000 — that may be used by other apps)
"""

import argparse
import asyncio
import json
import sys
import time
import threading
import random
import math
from datetime import datetime

# ── Auto-install helper (works on Windows where bare 'pip' may not be in PATH)
import os
import subprocess

def _pip_install(pkg):
    """Try multiple pip invocations until one works."""
    for cmd in [
        [sys.executable, "-m", "pip", "install", pkg, "--quiet"],
        ["py",  "-m", "pip", "install", pkg, "--quiet"],
        ["pip", "install", pkg, "--quiet"],
        ["pip3","install", pkg, "--quiet"],
    ]:
        try:
            r = subprocess.run(cmd, capture_output=True, timeout=60)
            if r.returncode == 0:
                return True
        except Exception:
            continue
    print(f"⚠️  Could not auto-install '{pkg}'. Try manually: py -m pip install {pkg}")
    return False

# ── Try imports ─────────────────────────────────────────────────────────────
try:
    import requests
except ImportError:
    _pip_install("requests"); import requests

try:
    from pythonosc import dispatcher, osc_server
    OSC_AVAILABLE = True
except ImportError:
    _pip_install("python-osc")
    try:
        from pythonosc import dispatcher, osc_server
        OSC_AVAILABLE = True
    except Exception:
        OSC_AVAILABLE = False

try:
    from bleak import BleakClient, BleakScanner
    BLEAK_AVAILABLE = True
except ImportError:
    _pip_install("bleak")
    try:
        from bleak import BleakClient, BleakScanner
        BLEAK_AVAILABLE = True
    except Exception:
        BLEAK_AVAILABLE = False

# ── Polar H10 BLE UUID ───────────────────────────────────────────────────────
POLAR_HR_SERVICE_UUID    = "0000180d-0000-1000-8000-00805f9b34fb"
POLAR_HR_CHAR_UUID       = "00002a37-0000-1000-8000-00805f9b34fb"
POLAR_DEVICE_NAME_PREFIX = "Polar"

# ── Shared state ─────────────────────────────────────────────────────────────
latest = {
    "alpha": 0.0, "beta": 0.0, "theta": 0.0, "gamma": 0.0, "delta": 0.0,
    "hr": 0, "rmssd": 0.0, "coherence": 0.0,
    "muse_on": False, "polar_on": False,
    "muse_packets": 0, "polar_packets": 0,
}
lock = threading.Lock()


# ═══════════════════════════════════════════════════════════════════════════
# MUSE via Mind Monitor (OSC)
# ═══════════════════════════════════════════════════════════════════════════
def handle_band(band, addr, *args):
    if args:
        import numpy as np
        val = float(np.mean(args))
        with lock:
            latest[band] = val
            latest["muse_on"] = True
            latest["muse_packets"] += 1


def start_osc_listener(port=5001):
    if not OSC_AVAILABLE:
        print("⚠️  python-osc not available — Muse OSC disabled")
        return None

    disp = dispatcher.Dispatcher()
    for band in ["alpha", "beta", "theta", "gamma", "delta"]:
        disp.map(
            f"/muse/elements/{band}_absolute",
            lambda addr, *args, b=band: handle_band(b, addr, *args)
        )
    # Also map blink and jaw clench for completeness
    disp.map("/muse/elements/blink", lambda *a: None)
    disp.map("/muse/elements/jaw_clench", lambda *a: None)

    try:
        server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", port), disp)
        t = threading.Thread(target=server.serve_forever, daemon=True)
        t.start()
        print(f"🧠 OSC listener started on port {port}")
        print(f"   → In Mind Monitor: Settings → OSC → IP = this machine's LAN IP, Port = {port}")
        return server
    except OSError as e:
        print(f"❌ Could not start OSC on port {port}: {e}")
        print(f"   Try a different port with --osc-port 5002")
        return None


# ═══════════════════════════════════════════════════════════════════════════
# POLAR H10 via Bluetooth LE (bleak)
# ═══════════════════════════════════════════════════════════════════════════
def parse_hr_measurement(data: bytearray):
    """Parse BLE Heart Rate Measurement characteristic."""
    flags = data[0]
    hr_format = flags & 0x01
    contact_detected = (flags >> 1) & 0x03
    rr_present = (flags >> 4) & 0x01

    idx = 1
    if hr_format == 0:
        hr = data[idx]; idx += 1
    else:
        hr = int.from_bytes(data[idx:idx+2], 'little'); idx += 2

    rr_intervals = []
    if rr_present:
        while idx + 1 < len(data):
            rr = int.from_bytes(data[idx:idx+2], 'little') / 1024.0 * 1000  # ms
            rr_intervals.append(rr)
            idx += 2

    rmssd = 0.0
    if len(rr_intervals) >= 2:
        diffs = [abs(rr_intervals[i+1] - rr_intervals[i]) for i in range(len(rr_intervals)-1)]
        rmssd = math.sqrt(sum(d**2 for d in diffs) / len(diffs))

    coherence = min(1.0, max(0.0, 1.0 - abs(hr - 60) / 60.0))
    return hr, rmssd, coherence


def polar_hr_callback(sender, data):
    hr, rmssd, coherence = parse_hr_measurement(bytearray(data))
    with lock:
        latest["hr"] = hr
        latest["rmssd"] = rmssd
        latest["coherence"] = coherence
        latest["polar_on"] = True
        latest["polar_packets"] += 1


async def connect_polar():
    if not BLEAK_AVAILABLE:
        print("⚠️  bleak not available — Polar BLE disabled")
        return

    print("🔍 Scanning for Polar H10...")
    while True:
        try:
            devices = await BleakScanner.discover(timeout=5.0)
            polar_device = None
            for d in devices:
                if d.name and POLAR_DEVICE_NAME_PREFIX in d.name:
                    polar_device = d
                    break

            if not polar_device:
                print("⏳ Polar H10 not found. Retrying in 5s... (Make sure HR strap is on and active)")
                await asyncio.sleep(5)
                continue

            print(f"❤️  Found Polar: {polar_device.name} ({polar_device.address})")

            async with BleakClient(polar_device.address, timeout=15.0) as client:
                print(f"✅ Connected to Polar H10!")
                await client.start_notify(POLAR_HR_CHAR_UUID, polar_hr_callback)
                # Keep connected until script ends
                while client.is_connected:
                    await asyncio.sleep(1)

        except Exception as e:
            print(f"⚠️  Polar connection error: {e} — retrying in 5s")
            with lock:
                latest["polar_on"] = False
            await asyncio.sleep(5)


# ═══════════════════════════════════════════════════════════════════════════
# DEMO MODE — simulated data
# ═══════════════════════════════════════════════════════════════════════════
def simulate_data():
    """Run simulated biometric data for testing."""
    t = 0
    while True:
        t += 0.1
        with lock:
            latest["alpha"]     = 45.0 + 15.0 * math.sin(t * 0.3)
            latest["theta"]     = 30.0 + 10.0 * math.sin(t * 0.2)
            latest["beta"]      = 20.0 + 8.0  * math.sin(t * 0.5)
            latest["gamma"]     = 8.0  + 3.0  * math.sin(t * 0.7)
            latest["delta"]     = 15.0 + 5.0  * math.sin(t * 0.1)
            latest["hr"]        = int(65 + 10 * math.sin(t * 0.15))
            latest["rmssd"]     = 45.0 + 15.0 * math.sin(t * 0.25)
            latest["coherence"] = min(1.0, 0.75 + 0.2 * math.sin(t * 0.2))
            latest["muse_on"]   = True
            latest["polar_on"]  = True
        time.sleep(0.5)


# ═══════════════════════════════════════════════════════════════════════════
# UPLOAD LOOP — POST to Replit server
# ═══════════════════════════════════════════════════════════════════════════
def upload_loop(server_url: str, interval: float = 2.0):
    """POST biometric data to Replit's /api/upload endpoint every `interval` seconds."""
    endpoint = server_url.rstrip("/") + "/api/upload"
    session_id = f"acer_bridge_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    sent = 0
    failed = 0

    print(f"\n📡 Uploading to: {endpoint}")
    print("   Press Ctrl+C to stop\n")

    while True:
        try:
            with lock:
                payload = {
                    "alpha":          latest["alpha"],
                    "beta":           latest["beta"],
                    "theta":          latest["theta"],
                    "gamma":          latest["gamma"],
                    "delta":          latest["delta"],
                    "heart_rate":     latest["hr"],
                    "hr":             latest["hr"],
                    "rmssd":          latest["rmssd"],
                    "coherence":      latest["coherence"],
                    "muse_connected": latest["muse_on"],
                    "muse":           latest["muse_on"],
                    "polar_connected": latest["polar_on"],
                    "polar":          latest["polar_on"],
                    "device_id":      "ACER_BRIDGE",
                    "session_id":     session_id,
                }
                muse_pkt  = latest["muse_packets"]
                polar_pkt = latest["polar_packets"]

            r = requests.post(endpoint, json=payload, timeout=8)
            if r.status_code in (200, 201):
                sent += 1
                muse_str  = f"alpha={payload['alpha']:.1f}" if payload["muse"] else "no Muse"
                polar_str = f"HR={payload['hr']} bpm" if payload["polar"] else "no Polar"
                print(f"  ✅ #{sent} sent | 🧠 {muse_str} | ❤️  {polar_str} "
                      f"| Muse pkts={muse_pkt} Polar pkts={polar_pkt}")
            else:
                failed += 1
                print(f"  ⚠️  Server returned {r.status_code}: {r.text[:80]}")

        except requests.exceptions.ConnectionError:
            failed += 1
            print(f"  ❌ Cannot reach {endpoint} — check server URL")
        except Exception as e:
            failed += 1
            print(f"  ❌ Error: {e}")

        time.sleep(interval)


# ═══════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════
def main():
    parser = argparse.ArgumentParser(description="Acer Live Biometric Bridge → Replit")
    parser.add_argument("--server",   required=True,
                        help="Replit app URL, e.g. https://xyz.replit.dev")
    parser.add_argument("--mode",     choices=["all", "muse", "polar", "demo"],
                        default="all", help="Which devices to use")
    parser.add_argument("--osc-port", type=int, default=5001,
                        help="Local UDP port for Mind Monitor OSC (default: 5001)")
    parser.add_argument("--interval", type=float, default=2.0,
                        help="Upload interval in seconds (default: 2.0)")
    args = parser.parse_args()

    print("=" * 65)
    print("  TI SIGMA — ACER LIVE BIOMETRIC BRIDGE")
    print("=" * 65)
    print(f"  Server  : {args.server}")
    print(f"  Mode    : {args.mode}")
    print(f"  OSC Port: {args.osc_port}")
    print(f"  Interval: {args.interval}s")
    print("=" * 65 + "\n")

    threads = []

    if args.mode == "demo":
        t = threading.Thread(target=simulate_data, daemon=True)
        t.start(); threads.append(t)

    elif args.mode == "muse":
        start_osc_listener(args.osc_port)

    elif args.mode == "polar":
        if BLEAK_AVAILABLE:
            loop = asyncio.new_event_loop()
            t = threading.Thread(
                target=lambda: loop.run_until_complete(connect_polar()), daemon=True
            )
            t.start(); threads.append(t)
        else:
            print("❌ bleak not available — cannot read Polar H10 via BLE")
            sys.exit(1)

    else:  # all
        start_osc_listener(args.osc_port)
        if BLEAK_AVAILABLE:
            loop = asyncio.new_event_loop()
            t = threading.Thread(
                target=lambda: loop.run_until_complete(connect_polar()), daemon=True
            )
            t.start(); threads.append(t)
        else:
            print("⚠️  bleak unavailable — running Muse-only mode")

    # Upload loop runs in main thread
    try:
        upload_loop(args.server, args.interval)
    except KeyboardInterrupt:
        print("\n\n🛑 Bridge stopped. Goodbye!")


if __name__ == "__main__":
    main()

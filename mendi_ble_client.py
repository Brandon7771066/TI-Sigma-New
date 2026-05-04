#!/usr/bin/env python3
"""
Mendi BLE client — scaffold for Path B (BLE reverse-engineering).

THIS FILE IS A SCAFFOLD. It will not produce real Mendi data until the
GATT discovery + payload decoding work in
`papers/MENDI_BLE_REVERSE_ENGINEERING_PLAN.md` is complete (planned for
~2026-05-23 onward, AFTER the URB #826 §10.6 H10 window finishes).

Why scaffold-only right now:
- The streaming characteristic UUID is unknown until you do the
  nRF Connect for Mobile capture (Steps 1–5 in the plan).
- The payload byte format is unknown until the captures are decoded.
- This file's MENDI_NAME_PREFIX, STREAM_SVC_UUID, STREAM_CHAR_UUID, and
  decode_frame() are placeholders. They will be filled in during Phase 1
  + Phase 2 of the plan.

ARCHITECTURE:
- This client must run on a machine WITH a Bluetooth radio
  (your Mac/PC/Pi). Replit cloud has no BLE radio, so this script is
  designed to run locally and POST decoded samples to the existing
  mendi_data_bridge_api.py running on the Replit URL.
- Uses `bleak` (already in requirements).

USAGE (after captures are decoded):
    python mendi_ble_client.py \\
        --bridge-url https://<your-repl-url>:8000 \\
        --duration 600 \\
        --session-id morning-2026-05-23

USAGE (right now, scan-only — works immediately, no decode):
    python mendi_ble_client.py --scan
"""
from __future__ import annotations

import argparse
import asyncio
import datetime as _dt
import json
import sys
from typing import Optional

try:
    from bleak import BleakClient, BleakScanner
except ImportError:
    print("ERROR: 'bleak' not installed. Run: pip install bleak", file=sys.stderr)
    sys.exit(1)

try:
    import requests
except ImportError:
    requests = None

MENDI_NAME_PREFIX = "Mendi"
STREAM_SVC_UUID: Optional[str] = None
STREAM_CHAR_UUID: Optional[str] = None
CONTROL_CHAR_UUID: Optional[str] = None
CONTROL_START_PAYLOAD: Optional[bytes] = None


def decode_frame(frame: bytes) -> Optional[dict]:
    """
    Decode one BLE notification payload into {timestamp, hbo2, hbr,
    signal_quality}.

    SCAFFOLD: returns None until the byte format is known.

    Once decoded, expected return shape:
        {
          "timestamp": ISO 8601 string,
          "hbo2": float (~50-80 µmol·mm),
          "hbr":  float (~20-50 µmol·mm),
          "signal_quality": float [0.0, 1.0],
        }
    """
    return None


async def cmd_scan(timeout_s: float = 30.0) -> int:
    """List all BLE devices visible to this radio. Mendi should appear."""
    print(f"Scanning for {timeout_s:.0f} seconds — power on the Mendi headband NOW")
    print("(Make sure Mendi is NOT listed in Windows Bluetooth paired devices.)")
    print("(If it is: Settings > Bluetooth > Mendi > Remove device, then re-run.)\n")
    devices = await BleakScanner.discover(timeout=timeout_s)
    if not devices:
        print("No BLE devices found at all.")
        print("\nTroubleshooting:")
        print("  1. Is Bluetooth turned ON in Windows Settings?")
        print("  2. Is the Mendi headband powered on (blinking)?")
        print("  3. Try: right-click Command Prompt > 'Run as administrator'")
        print("  4. Close the Mendi phone app if it's open (it may hold the connection)")
        return 1

    mendi_candidates = []
    other_devices = []
    for d in devices:
        name = d.name or "(unnamed)"
        addr = d.address
        rssi = getattr(d, "rssi", None)
        line = f"  {addr}  {name:<30}  rssi={rssi}"
        if name and MENDI_NAME_PREFIX.lower() in name.lower():
            mendi_candidates.append((line, addr, name))
        elif name and any(kw in name.lower() for kw in ("mnd", "neuro", "fnirs")):
            mendi_candidates.append((line, addr, name))
        else:
            other_devices.append(line)

    print(f"\nFound {len(devices)} BLE device(s) total.\n")

    if mendi_candidates:
        print(f"=== Mendi candidates (name contains '{MENDI_NAME_PREFIX}' or similar) ===")
        for line, _, _ in mendi_candidates:
            print(line)
        print()
        print("Next step: run with --discover-gatt --address <MAC>")
        print("Example:  python mendi_ble_client.py --discover-gatt --address AA:BB:CC:DD:EE:FF")
    else:
        print(f"No device with name containing '{MENDI_NAME_PREFIX}' found.")
        print("\nAll visible devices (check if Mendi appears under a different name):")
        for line in sorted(other_devices):
            print(line)
        print(f"\n--- {len(other_devices)} device(s) listed ---")
        print("\nIf the Mendi is listed under a different name above,")
        print("copy its MAC address and run:")
        print("  python mendi_ble_client.py --discover-gatt --address <MAC>")
        print("\nIf Mendi is NOT listed at all:")
        print("  1. REMOVE Mendi from Windows Bluetooth paired devices")
        print("     (Settings > Bluetooth & devices > find Mendi > Remove)")
        print("  2. Close the Mendi phone app (it may be holding the connection)")
        print("  3. Power-cycle the Mendi headband (off, wait 5 sec, on)")
        print("  4. Right-click Command Prompt > 'Run as administrator'")
        print("  5. Re-run this scan")
    return 0


async def cmd_discover_gatt(address: str) -> int:
    """Connect and dump the GATT tree as JSON for offline analysis."""
    print(f"Connecting to {address}...")
    async with BleakClient(address) as client:
        if not client.is_connected:
            print("Connection failed.")
            return 1
        print("Connected. Discovering services...\n")
        out = {"address": address, "services": []}
        for service in client.services:
            svc_info = {
                "uuid": str(service.uuid),
                "description": service.description,
                "characteristics": [],
            }
            for char in service.characteristics:
                svc_info["characteristics"].append({
                    "uuid": str(char.uuid),
                    "properties": list(char.properties),
                    "description": char.description,
                })
            out["services"].append(svc_info)

        ts = _dt.datetime.now().strftime("%Y-%m-%dT%H-%M-%S")
        path = f"data/mendi/ble_discovery/gatt_{ts}.json"
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(out, fh, indent=2)
        print(f"Wrote GATT tree to {path}")
        print(f"Found {len(out['services'])} services, "
              f"{sum(len(s['characteristics']) for s in out['services'])} "
              "characteristics total.")
        return 0


async def cmd_stream(
    address: str, duration_s: float, bridge_url: str,
    session_id: str, dry_run: bool,
) -> int:
    """
    Stream notifications from the Mendi for `duration_s` seconds.

    SCAFFOLD: requires STREAM_CHAR_UUID + decode_frame() to be filled in.
    Until then this function only supports `--dry-run` mode which logs
    raw hex bytes for offline decoder development.
    """
    if STREAM_CHAR_UUID is None and not dry_run:
        print("ERROR: STREAM_CHAR_UUID is not set. Either:", file=sys.stderr)
        print("  - Run with --dry-run --char <uuid> to capture raw hex", file=sys.stderr)
        print("  - Edit STREAM_CHAR_UUID in this file once Phase 2 decode is done",
              file=sys.stderr)
        return 1

    print(f"Connecting to {address}...")
    async with BleakClient(address) as client:
        if not client.is_connected:
            print("Connection failed.")
            return 1

        if CONTROL_CHAR_UUID and CONTROL_START_PAYLOAD:
            await client.write_gatt_char(CONTROL_CHAR_UUID, CONTROL_START_PAYLOAD)
            print(f"Sent start command to {CONTROL_CHAR_UUID}")

        ts = _dt.datetime.now().strftime("%Y-%m-%dT%H-%M-%S")
        log_path = f"data/mendi/ble_capture/raw_{session_id}_{ts}.jsonl"
        log_fh = open(log_path, "w", encoding="utf-8")
        print(f"Logging raw frames to {log_path}")

        sample_count = {"n": 0}

        def on_notify(_handle, data: bytes):
            now = _dt.datetime.now().isoformat()
            log_fh.write(json.dumps({
                "t": now, "hex": data.hex(), "len": len(data),
            }) + "\n")
            sample_count["n"] += 1
            if dry_run:
                return
            decoded = decode_frame(data)
            if decoded is None:
                return
            decoded.setdefault("timestamp", now)
            decoded["session_id"] = session_id
            if requests is not None:
                try:
                    requests.post(
                        f"{bridge_url.rstrip('/')}/api/mendi/upload",
                        json=decoded, timeout=2.0,
                    )
                except Exception as ex:
                    print(f"  bridge POST failed: {ex}", file=sys.stderr)

        char_uuid = STREAM_CHAR_UUID or "PLACEHOLDER"
        await client.start_notify(char_uuid, on_notify)
        print(f"Subscribed to {char_uuid}. Streaming for {duration_s:.0f}s...")
        try:
            await asyncio.sleep(duration_s)
        finally:
            await client.stop_notify(char_uuid)
            log_fh.close()
        print(f"Done. {sample_count['n']} frames captured to {log_path}")
        return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=False)

    ap.add_argument("--scan", action="store_true",
                    help="scan for BLE devices and exit")
    ap.add_argument("--discover-gatt", action="store_true",
                    help="connect and dump the GATT structure")
    ap.add_argument("--stream", action="store_true",
                    help="connect and stream notifications")
    ap.add_argument("--dry-run", action="store_true",
                    help="streaming: log raw hex only, do NOT POST decoded "
                         "samples to bridge")
    ap.add_argument("--address", help="BLE MAC address of the Mendi")
    ap.add_argument("--timeout", type=float, default=30.0,
                    help="scan timeout in seconds (default 30)")
    ap.add_argument("--duration", type=float, default=120.0,
                    help="streaming duration in seconds (default 120)")
    ap.add_argument("--bridge-url",
                    default="http://localhost:8000",
                    help="URL of the mendi_data_bridge_api.py")
    ap.add_argument("--session-id",
                    default=_dt.datetime.now().strftime("session-%Y%m%d-%H%M%S"),
                    help="session id to tag uploaded samples with")
    args = ap.parse_args()

    if args.scan:
        return asyncio.run(cmd_scan(timeout_s=args.timeout))
    if args.discover_gatt:
        if not args.address:
            print("ERROR: --discover-gatt requires --address", file=sys.stderr)
            return 1
        return asyncio.run(cmd_discover_gatt(args.address))
    if args.stream:
        if not args.address:
            print("ERROR: --stream requires --address", file=sys.stderr)
            return 1
        return asyncio.run(cmd_stream(
            args.address, args.duration, args.bridge_url,
            args.session_id, args.dry_run,
        ))

    ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())

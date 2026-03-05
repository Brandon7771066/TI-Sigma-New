"""
Mind Monitor → TI Platform Bridge
===================================
Run this on your LOCAL machine (Acer laptop), NOT on Replit.

This script listens for Mind Monitor's OSC stream from your Muse 2 headband
and forwards the data to the TI Platform running on Replit.

SETUP:
  1. Install dependencies:
         pip install python-osc requests
  2. Set your Replit URL below (or set REPLIT_URL env variable)
  3. In Mind Monitor app on your phone:
         Settings → OSC Stream Host → enter your Acer's local IP
         Settings → OSC Stream Port → 5005  (or whatever LISTEN_PORT is below)
         Turn on "OSC Stream" toggle
  4. Run this script:
         python mind_monitor_bridge.py
  5. Put on your Muse 2 — data will start flowing in seconds

FINDING YOUR ACER'S LOCAL IP:
  Open Command Prompt and run: ipconfig
  Look for "IPv4 Address" under your WiFi adapter (e.g. 192.168.1.42)
  Your phone and Acer must be on the same WiFi network.
"""

import os
import sys
import time
import math
import json
import threading
import requests
from datetime import datetime
from pythonosc import dispatcher, osc_server

# ─────────────────────────────────────────────────────────────
#  CONFIGURATION — edit these two lines
# ─────────────────────────────────────────────────────────────
REPLIT_URL  = os.environ.get("REPLIT_URL", "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev")
LISTEN_PORT = int(os.environ.get("MM_PORT", "5005"))   # must match Mind Monitor settings
POST_INTERVAL = 2.0   # seconds between posts to Replit
# ─────────────────────────────────────────────────────────────

# Thread-safe data store
_lock = threading.Lock()
_data = {
    "alpha": [],   # list of per-sample means (across 4 channels)
    "beta":  [],
    "theta": [],
    "delta": [],
    "gamma": [],
    "eeg_raw": [],
    "jaw_clench": 0,
    "blink": 0,
    "horseshoe": [4, 4, 4, 4],   # 1=perfect, 4=no signal
    "is_good": [0, 0, 0, 0],
    "last_packet": None,
}

# ── OSC handlers ──────────────────────────────────────────────

def _band_handler(band_key):
    """Return a handler that appends the mean of 4 channel values."""
    def handler(address, *args):
        vals = [a for a in args if isinstance(a, (int, float)) and not math.isnan(a)]
        if vals:
            with _lock:
                _data[band_key].append(sum(vals) / len(vals))
                _data["last_packet"] = time.time()
    return handler


def _eeg_handler(address, *args):
    vals = [a for a in args if isinstance(a, (int, float)) and not math.isnan(a)]
    if vals:
        with _lock:
            _data["eeg_raw"].append(vals)
            if len(_data["eeg_raw"]) > 500:
                _data["eeg_raw"] = _data["eeg_raw"][-500:]
            _data["last_packet"] = time.time()


def _jaw_handler(address, *args):
    with _lock:
        _data["jaw_clench"] = int(args[0]) if args else 0


def _blink_handler(address, *args):
    with _lock:
        _data["blink"] = int(args[0]) if args else 0


def _horseshoe_handler(address, *args):
    with _lock:
        _data["horseshoe"] = list(args[:4]) if len(args) >= 4 else _data["horseshoe"]


def _is_good_handler(address, *args):
    with _lock:
        _data["is_good"] = list(args[:4]) if len(args) >= 4 else _data["is_good"]


def _default_handler(address, *args):
    pass   # silently ignore unmapped paths


# ── Helpers ───────────────────────────────────────────────────

def _pop_mean(key):
    """Return mean of accumulated values and clear the buffer."""
    with _lock:
        vals = _data[key]
        _data[key] = []
    return round(sum(vals) / len(vals), 6) if vals else None


def _signal_quality():
    """Return 0–1 quality score from horseshoe values (1=best, 4=worst)."""
    with _lock:
        hs = _data["horseshoe"]
    good = sum(1 for v in hs if v <= 1)
    return round(good / 4, 2)


def _format_bar(value, lo=0.0, hi=2.0, width=20):
    """Simple ASCII progress bar for a log-power value."""
    if value is None:
        return "[" + "?" * width + "]"
    frac = max(0, min(1, (value - lo) / (hi - lo)))
    filled = int(frac * width)
    return "[" + "█" * filled + "░" * (width - filled) + f"] {value:.3f}"


# ── Posting thread ─────────────────────────────────────────────

def _post_loop():
    url = REPLIT_URL.rstrip("/") + "/api/upload"
    print(f"\n▶  Posting to: {url}")
    print(f"   Every {POST_INTERVAL}s | OSC port {LISTEN_PORT}\n")
    print(f"{'─'*60}")

    consecutive_errors = 0

    while True:
        time.sleep(POST_INTERVAL)

        alpha = _pop_mean("alpha")
        beta  = _pop_mean("beta")
        theta = _pop_mean("theta")
        delta = _pop_mean("delta")
        gamma = _pop_mean("gamma")

        with _lock:
            jaw   = _data["jaw_clench"]
            blink = _data["blink"]
            last  = _data["last_packet"]
            _data["jaw_clench"] = 0
            _data["blink"]      = 0

        # Skip if no data has arrived yet
        if last is None or (time.time() - last) > 10:
            age = "never" if last is None else f"{time.time()-last:.0f}s ago"
            print(f"  ⏳  No Muse data (last packet: {age}) — waiting...")
            print(f"      Check: Muse on head? Mind Monitor streaming? Phone on same WiFi?")
            continue

        quality = _signal_quality()
        ts = datetime.now().strftime("%H:%M:%S")

        # Build payload
        payload = {
            "alpha":         alpha,
            "beta":          beta,
            "theta":         theta,
            "delta":         delta,
            "gamma":         gamma,
            "muse_connected": True,
            "muse":          True,
            "signal_quality": quality,
            "jaw_clench":    jaw,
            "blink":         blink,
            "source":        "mind_monitor_bridge",
        }
        payload = {k: v for k, v in payload.items() if v is not None}

        # Pretty console output
        print(f"\n  {ts}  |  Quality: {'▓'*int(quality*10)}{'░'*(10-int(quality*10))} {quality:.0%}")
        if alpha is not None:
            print(f"  α Alpha  {_format_bar(alpha)}")
        if beta is not None:
            print(f"  β Beta   {_format_bar(beta)}")
        if theta is not None:
            print(f"  θ Theta  {_format_bar(theta)}")
        if delta is not None:
            print(f"  δ Delta  {_format_bar(delta)}")
        if gamma is not None:
            print(f"  γ Gamma  {_format_bar(gamma)}")
        if jaw:
            print(f"  💀 JAW CLENCH detected")
        if blink:
            print(f"  👁  BLINK detected")

        # POST to Replit
        try:
            r = requests.post(url, json=payload, timeout=5)
            if r.status_code in (200, 201):
                consecutive_errors = 0
                print(f"  ✓  Sent → {r.status_code}")
            else:
                consecutive_errors += 1
                print(f"  ✗  HTTP {r.status_code}: {r.text[:80]}")
        except requests.exceptions.ConnectionError:
            consecutive_errors += 1
            print(f"  ✗  Cannot reach Replit — is the URL correct?")
            print(f"     URL: {url}")
        except requests.exceptions.Timeout:
            consecutive_errors += 1
            print(f"  ✗  Request timed out (Replit slow to respond)")
        except Exception as e:
            consecutive_errors += 1
            print(f"  ✗  Error: {e}")

        if consecutive_errors >= 5:
            print(f"\n  ⚠  {consecutive_errors} consecutive failures.")
            print(f"     Check REPLIT_URL is correct and the app is running.")
            consecutive_errors = 0


# ── Main ───────────────────────────────────────────────────────

def main():
    # Validate config
    print("\n" + "="*60)
    print("  MIND MONITOR → TI PLATFORM BRIDGE")
    print("="*60)
    print(f"\n  Replit URL : {REPLIT_URL}")
    print(f"  OSC port   : {LISTEN_PORT}  (set this in Mind Monitor settings)")
    print(f"  Post every : {POST_INTERVAL}s")
    print()
    print("  Mind Monitor setup checklist:")
    print("  ─────────────────────────────")
    print("  1. Open Mind Monitor → Settings → OSC Stream")
    print(f"    Set Host = your Acer's local WiFi IP (run ipconfig to find it)")
    print(f"    Set Port = {LISTEN_PORT}")
    print("  2. Toggle 'OSC Stream' ON")
    print("  3. Put Muse 2 on your head and connect in Mind Monitor")
    print("  4. Watch data appear below in ~3 seconds")
    print()

    # Wire up OSC dispatcher
    d = dispatcher.Dispatcher()
    d.map("/muse/elements/alpha_absolute", _band_handler("alpha"))
    d.map("/muse/elements/beta_absolute",  _band_handler("beta"))
    d.map("/muse/elements/theta_absolute", _band_handler("theta"))
    d.map("/muse/elements/delta_absolute", _band_handler("delta"))
    d.map("/muse/elements/gamma_absolute", _band_handler("gamma"))
    d.map("/muse/eeg",                     _eeg_handler)
    d.map("/muse/elements/jaw_clench",     _jaw_handler)
    d.map("/muse/elements/blink",          _blink_handler)
    d.map("/muse/elements/horseshoe",      _horseshoe_handler)
    d.map("/muse/elements/is_good",        _is_good_handler)
    d.set_default_handler(_default_handler)

    # Start posting thread (daemon — exits when main thread exits)
    poster = threading.Thread(target=_post_loop, daemon=True)
    poster.start()

    # Start OSC server (blocking)
    try:
        server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", LISTEN_PORT), d)
        print(f"  Listening for Mind Monitor on 0.0.0.0:{LISTEN_PORT} ...")
        print(f"  Press Ctrl+C to stop.\n")
        server.serve_forever()
    except OSError as e:
        if "Address already in use" in str(e):
            print(f"\n  ERROR: Port {LISTEN_PORT} is already in use.")
            print(f"  Change LISTEN_PORT in the script or run:")
            print(f"    MM_PORT=5006 python mind_monitor_bridge.py")
        else:
            print(f"\n  ERROR starting OSC server: {e}")
        sys.exit(1)
    except KeyboardInterrupt:
        print("\n\n  Stopped.")


if __name__ == "__main__":
    main()

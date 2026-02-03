#!/usr/bin/env python3
"""
Simple Muse Bridge - Real-time EEG streaming
=============================================
Receives data from Mind Monitor via OSC and forwards to webhook.

Run: py SIMPLE_MUSE_BRIDGE.py
"""

import sys
import time
from datetime import datetime

print("=" * 60)
print("SIMPLE MUSE BRIDGE - Starting...")
print("=" * 60)

try:
    import requests
except ImportError:
    print("Installing requests...")
    import os
    os.system("pip install requests")
    import requests

try:
    from pythonosc import dispatcher, osc_server
except ImportError:
    print("Installing python-osc...")
    import os
    os.system("pip install python-osc")
    from pythonosc import dispatcher, osc_server

import threading

WEBHOOK_URL = "https://webhook.site/1e18d8ff-2846-4149-a609-48cb83d5298a"
OSC_PORT = 5000

bands = {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
packet_count = 0
last_send = 0

def handle_alpha(addr, *args):
    global bands, packet_count
    if args:
        bands['alpha'] = sum(args) / len(args)
        packet_count += 1

def handle_beta(addr, *args):
    global bands
    if args:
        bands['beta'] = sum(args) / len(args)

def handle_theta(addr, *args):
    global bands
    if args:
        bands['theta'] = sum(args) / len(args)

def handle_gamma(addr, *args):
    global bands
    if args:
        bands['gamma'] = sum(args) / len(args)

def handle_delta(addr, *args):
    global bands
    if args:
        bands['delta'] = sum(args) / len(args)

def send_to_webhook():
    global last_send, packet_count
    while True:
        time.sleep(3)
        if packet_count > 0:
            now = datetime.now()
            data = {
                "timestamp": now.isoformat(),
                "type": "muse_eeg",
                "alpha": round(bands['alpha'], 4),
                "beta": round(bands['beta'], 4),
                "theta": round(bands['theta'], 4),
                "gamma": round(bands['gamma'], 4),
                "delta": round(bands['delta'], 4),
                "source": "mind_monitor",
                "device": "Muse-2"
            }
            try:
                resp = requests.post(WEBHOOK_URL, json=data, timeout=5)
                if resp.status_code in [200, 201]:
                    print(f"[{now.strftime('%H:%M:%S')}] Alpha={bands['alpha']:.2f} Beta={bands['beta']:.2f} -> SENT OK")
                elif resp.status_code == 429:
                    print(f"[{now.strftime('%H:%M:%S')}] Rate limited - waiting...")
                    time.sleep(10)
                else:
                    print(f"[{now.strftime('%H:%M:%S')}] Webhook error: {resp.status_code}")
            except Exception as e:
                print(f"Network error: {e}")
        else:
            print(f"[{datetime.now().strftime('%H:%M:%S')}] Waiting for Mind Monitor data...")

print(f"\nWebhook: {WEBHOOK_URL}")
print(f"OSC Port: {OSC_PORT}")
print("\n" + "=" * 60)
print("MIND MONITOR SETTINGS:")
print("  OSC IP Address: 127.0.0.1")
print(f"  OSC Port: {OSC_PORT}")
print("  Enable OSC Streaming: ON")
print("=" * 60)
print("\nListening for Mind Monitor data...\n")

disp = dispatcher.Dispatcher()
disp.map("/muse/elements/alpha_absolute", handle_alpha)
disp.map("/muse/elements/beta_absolute", handle_beta)
disp.map("/muse/elements/theta_absolute", handle_theta)
disp.map("/muse/elements/gamma_absolute", handle_gamma)
disp.map("/muse/elements/delta_absolute", handle_delta)

sender = threading.Thread(target=send_to_webhook, daemon=True)
sender.start()

try:
    server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", OSC_PORT), disp)
    print(f"OSC Server running on port {OSC_PORT}")
    print("Press Ctrl+C to stop\n")
    server.serve_forever()
except KeyboardInterrupt:
    print("\nStopped by user")
except Exception as e:
    print(f"\nERROR: {e}")
    print("\nTroubleshooting:")
    print("  1. Is another program using port 5000?")
    print("  2. Try changing OSC_PORT to 5001 in this script AND in Mind Monitor")
    input("\nPress Enter to exit...")

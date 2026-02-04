#!/usr/bin/env python3
"""
Muse Local Realtime - Saves EEG data locally with live display
===============================================================
No webhook needed! Data saves to CSV and displays in real-time.

Run: py MUSE_LOCAL_REALTIME.py
"""

import sys
import time
import csv
import os
from datetime import datetime

print("=" * 60)
print("MUSE LOCAL REALTIME - Starting...")
print("=" * 60)

try:
    from pythonosc import dispatcher, osc_server
except ImportError:
    print("Installing python-osc...")
    os.system("pip install python-osc")
    from pythonosc import dispatcher, osc_server

import threading

OSC_PORT = 5001  # Changed from 5000 to avoid conflicts
CSV_FILE = f"muse_data_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
SHARED_FILE = os.path.join(os.path.expanduser("~"), "muse_realtime_eeg.csv")

bands = {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
packet_count = 0
data_received = False

csv_file = open(CSV_FILE, 'w', newline='')
csv_writer = csv.writer(csv_file)
csv_writer.writerow(['timestamp', 'alpha', 'beta', 'theta', 'gamma', 'delta'])

def handle_alpha(addr, *args):
    global bands, packet_count, data_received
    if args:
        bands['alpha'] = sum(args) / len(args)
        packet_count += 1
        data_received = True

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

def save_and_display():
    global data_received
    samples = 0
    
    # Initialize shared file with header
    with open(SHARED_FILE, 'w', newline='') as sf:
        sf.write('timestamp,alpha,beta,theta,gamma,delta\n')
    print(f"Shared file for Pong: {SHARED_FILE}")
    
    while True:
        time.sleep(1)
        now = datetime.now()
        
        if data_received:
            row_data = [
                now.isoformat(),
                round(bands['alpha'], 4),
                round(bands['beta'], 4),
                round(bands['theta'], 4),
                round(bands['gamma'], 4),
                round(bands['delta'], 4)
            ]
            
            # Write to main CSV
            csv_writer.writerow(row_data)
            csv_file.flush()
            
            # Also write to shared file for Pong game
            with open(SHARED_FILE, 'w', newline='') as sf:
                sf.write('timestamp,alpha,beta,theta,gamma,delta\n')
                sf.write(','.join(str(x) for x in row_data) + '\n')
            
            samples += 1
            
            ratio = bands['alpha'] / bands['beta'] if bands['beta'] > 0 else 0
            state = "RELAXED" if ratio > 1.5 else "FOCUSED" if ratio < 0.8 else "BALANCED"
            
            print(f"[{now.strftime('%H:%M:%S')}] "
                  f"Alpha={bands['alpha']:6.2f} "
                  f"Beta={bands['beta']:6.2f} "
                  f"Theta={bands['theta']:6.2f} "
                  f"| A/B={ratio:.2f} {state} "
                  f"| {samples} saved")
        else:
            print(f"[{now.strftime('%H:%M:%S')}] Waiting for Mind Monitor data...")

print(f"\nSaving to: {CSV_FILE}")
print(f"OSC Port: {OSC_PORT}")
print("\n" + "=" * 60)
print("MIND MONITOR SETTINGS:")
print(f"  OSC IP Address: 127.0.0.1")
print(f"  OSC Port: {OSC_PORT}")
print("  Enable OSC Streaming: ON")
print("=" * 60)
print("\nFOR EEG PONG: Run EEG_PONG_LCC_TEST.py in another terminal!")
print(f"  Pong reads from: {SHARED_FILE}")
print("\nListening for Mind Monitor data...\n")

disp = dispatcher.Dispatcher()
disp.map("/muse/elements/alpha_absolute", handle_alpha)
disp.map("/muse/elements/beta_absolute", handle_beta)
disp.map("/muse/elements/theta_absolute", handle_theta)
disp.map("/muse/elements/gamma_absolute", handle_gamma)
disp.map("/muse/elements/delta_absolute", handle_delta)

saver = threading.Thread(target=save_and_display, daemon=True)
saver.start()

try:
    server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", OSC_PORT), disp)
    print(f"OSC Server running on port {OSC_PORT}")
    print("Press Ctrl+C to stop\n")
    server.serve_forever()
except KeyboardInterrupt:
    print(f"\n\nStopped! Data saved to: {CSV_FILE}")
    print(f"Total samples: {packet_count}")
    csv_file.close()
except Exception as e:
    print(f"\nERROR: {e}")
    print("\nIf port 5000 is busy, close the other script first!")
    input("\nPress Enter to exit...")
    csv_file.close()

#!/usr/bin/env python3
"""
Combined Muse 2 EEG + Polar H10 HRV Collector
==============================================
Captures both brainwaves AND heart data for complete entrainment analysis.

Run: py MUSE_POLAR_COMBINED.py

Requirements:
- python-osc (for Muse via Mind Monitor)
- bleak (for Polar H10 BLE)
"""

import sys
import time
import csv
import os
import asyncio
import threading
from datetime import datetime
from collections import deque
import numpy as np

print("=" * 70)
print("MUSE + POLAR H10 COMBINED BIOMETRIC COLLECTOR")
print("=" * 70)

try:
    from pythonosc import dispatcher, osc_server
except ImportError:
    print("Installing python-osc...")
    os.system("pip install python-osc")
    from pythonosc import dispatcher, osc_server

try:
    from bleak import BleakClient, BleakScanner
    BLEAK_AVAILABLE = True
    print("✅ Bluetooth LE (bleak) available for Polar H10")
except ImportError:
    print("⚠️ Installing bleak for Polar H10...")
    os.system("pip install bleak")
    try:
        from bleak import BleakClient, BleakScanner
        BLEAK_AVAILABLE = True
    except:
        BLEAK_AVAILABLE = False
        print("⚠️ Polar H10 unavailable - EEG only mode")

# Configuration
OSC_PORT = 5000
CSV_FILE = f"biometric_data_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"

# Polar H10 UUIDs
HEART_RATE_SERVICE_UUID = "0000180d-0000-1000-8000-00805f9b34fb"
HEART_RATE_MEASUREMENT_UUID = "00002a37-0000-1000-8000-00805f9b34fb"

# Data storage
eeg_bands = {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
hrv_data = {'hr': 0, 'rr': 0, 'coherence': 0}
rr_buffer = deque(maxlen=60)  # Last 60 RR intervals for HRV calculation

packet_count = 0
eeg_received = False
hrv_received = False
polar_connected = False
polar_device_name = "Not connected"

# CSV setup
csv_file = open(CSV_FILE, 'w', newline='')
csv_writer = csv.writer(csv_file)
csv_writer.writerow([
    'timestamp', 
    'alpha', 'beta', 'theta', 'gamma', 'delta',  # EEG
    'heart_rate', 'rr_interval', 'hrv_coherence',  # HRV
    'ab_ratio', 'state', 'heart_brain_sync'  # Derived
])

# =============================================================================
# EEG HANDLERS (Muse 2 via Mind Monitor)
# =============================================================================

def handle_alpha(addr, *args):
    global eeg_bands, packet_count, eeg_received
    if args:
        eeg_bands['alpha'] = sum(args) / len(args)
        packet_count += 1
        eeg_received = True

def handle_beta(addr, *args):
    global eeg_bands
    if args:
        eeg_bands['beta'] = sum(args) / len(args)

def handle_theta(addr, *args):
    global eeg_bands
    if args:
        eeg_bands['theta'] = sum(args) / len(args)

def handle_gamma(addr, *args):
    global eeg_bands
    if args:
        eeg_bands['gamma'] = sum(args) / len(args)

def handle_delta(addr, *args):
    global eeg_bands
    if args:
        eeg_bands['delta'] = sum(args) / len(args)

# =============================================================================
# HRV HANDLERS (Polar H10 via BLE)
# =============================================================================

def calculate_hrv_coherence(rr_intervals):
    """Calculate HRV coherence score (0-1) from RR intervals."""
    if len(rr_intervals) < 10:
        return 0.0
    
    rr_array = np.array(list(rr_intervals))
    
    # RMSSD - Root Mean Square of Successive Differences
    diffs = np.diff(rr_array)
    rmssd = np.sqrt(np.mean(diffs ** 2))
    
    # SDNN - Standard Deviation of NN intervals  
    sdnn = np.std(rr_array)
    
    # Coherence proxy: Lower RMSSD relative to SDNN = more coherent
    # Normalize to 0-1 scale
    if sdnn > 0:
        ratio = rmssd / sdnn
        coherence = max(0, min(1, 1 - (ratio - 0.5) / 1.5))
    else:
        coherence = 0.5
    
    return coherence

def hr_notification_handler(sender, data):
    """Handle heart rate notifications from Polar H10."""
    global hrv_data, rr_buffer, hrv_received
    
    # Parse heart rate data
    flags = data[0]
    hr_format_16bit = flags & 0x01
    rr_present = (flags >> 4) & 0x01
    
    if hr_format_16bit:
        heart_rate = int.from_bytes(data[1:3], byteorder='little')
        rr_start = 3
    else:
        heart_rate = data[1]
        rr_start = 2
    
    hrv_data['hr'] = heart_rate
    hrv_received = True
    
    # Extract RR intervals if present
    if rr_present and len(data) > rr_start:
        i = rr_start
        while i + 1 < len(data):
            rr = int.from_bytes(data[i:i+2], byteorder='little')
            rr_ms = rr / 1024.0 * 1000  # Convert to milliseconds
            rr_buffer.append(rr_ms)
            hrv_data['rr'] = rr_ms
            i += 2
    
    # Calculate coherence
    hrv_data['coherence'] = calculate_hrv_coherence(rr_buffer)

async def scan_and_connect_polar():
    """Scan for and connect to Polar H10."""
    global polar_connected, polar_device_name
    
    print("\n🔍 Scanning for Polar H10...")
    
    try:
        devices = await BleakScanner.discover(timeout=10.0)
        
        polar_device = None
        for d in devices:
            if d.name and "Polar" in d.name:
                polar_device = d
                polar_device_name = d.name
                print(f"✅ Found: {d.name} ({d.address})")
                break
        
        if not polar_device:
            print("⚠️ No Polar device found. Running EEG-only mode.")
            return
        
        print(f"🔗 Connecting to {polar_device.name}...")
        
        async with BleakClient(polar_device.address) as client:
            polar_connected = True
            print(f"✅ Connected to {polar_device.name}!")
            
            # Start heart rate notifications
            await client.start_notify(HEART_RATE_MEASUREMENT_UUID, hr_notification_handler)
            print("💓 Heart rate streaming started!")
            
            # Keep connection alive
            while polar_connected:
                await asyncio.sleep(1)
                
    except Exception as e:
        print(f"⚠️ Polar connection error: {e}")
        print("Running in EEG-only mode.")

def start_polar_stream():
    """Start Polar H10 in background thread."""
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    loop.run_until_complete(scan_and_connect_polar())

# =============================================================================
# DATA LOGGING & DISPLAY
# =============================================================================

def calculate_heart_brain_sync(alpha, hrv_coherence):
    """Calculate heart-brain synchronization score."""
    if hrv_coherence == 0:
        return 0.0
    
    # High alpha + high HRV coherence = strong heart-brain sync
    # Normalize alpha (typically -1 to 1 log scale)
    alpha_norm = max(0, min(1, (alpha + 1) / 2))
    
    # Combine with HRV coherence
    sync = (alpha_norm * 0.4 + hrv_coherence * 0.6)
    return sync

def save_and_display():
    global eeg_received, hrv_received
    samples = 0
    
    while True:
        time.sleep(1)
        now = datetime.now()
        
        if eeg_received or hrv_received:
            # Calculate derived metrics
            ab_ratio = eeg_bands['alpha'] / eeg_bands['beta'] if eeg_bands['beta'] != 0 else 0
            
            if ab_ratio > 1.5:
                state = "RELAXED"
            elif ab_ratio < 0.8:
                state = "FOCUSED"
            else:
                state = "BALANCED"
            
            # Heart-brain sync
            hb_sync = calculate_heart_brain_sync(eeg_bands['alpha'], hrv_data['coherence'])
            
            # Save to CSV
            csv_writer.writerow([
                now.isoformat(),
                round(eeg_bands['alpha'], 4),
                round(eeg_bands['beta'], 4),
                round(eeg_bands['theta'], 4),
                round(eeg_bands['gamma'], 4),
                round(eeg_bands['delta'], 4),
                round(hrv_data['hr'], 0),
                round(hrv_data['rr'], 1),
                round(hrv_data['coherence'], 3),
                round(ab_ratio, 2),
                state,
                round(hb_sync, 3)
            ])
            csv_file.flush()
            samples += 1
            
            # Display
            eeg_str = f"Alpha={eeg_bands['alpha']:5.2f} Beta={eeg_bands['beta']:5.2f} Theta={eeg_bands['theta']:5.2f} Gamma={eeg_bands['gamma']:5.2f}"
            
            if hrv_received and hrv_data['hr'] > 0:
                hrv_str = f"💓 HR={hrv_data['hr']:.0f} Coh={hrv_data['coherence']:.2f}"
                sync_str = f"🔗 Sync={hb_sync:.2f}"
            else:
                hrv_str = "💓 Waiting..."
                sync_str = ""
            
            # Sync indicator
            if hb_sync > 0.7:
                sync_status = "🟢 IN SYNC!"
            elif hb_sync > 0.5:
                sync_status = "🟡 SYNCING"
            elif hrv_received:
                sync_status = "🔴 LOW"
            else:
                sync_status = ""
            
            print(f"[{now.strftime('%H:%M:%S')}] {eeg_str} | {hrv_str} {sync_str} {sync_status} | {samples} saved")
        else:
            print(f"[{now.strftime('%H:%M:%S')}] Waiting for sensor data...")

# =============================================================================
# MAIN
# =============================================================================

print(f"\n📁 Saving to: {CSV_FILE}")
print(f"📡 OSC Port: {OSC_PORT}")

print("\n" + "=" * 70)
print("SETUP INSTRUCTIONS:")
print("=" * 70)
print("\n🧠 MUSE 2 (Mind Monitor):")
print("   OSC IP Address: [Your PC's local IP, e.g., 192.168.1.xxx]")
print(f"   OSC Port: {OSC_PORT}")
print("   Enable OSC Streaming: ON")
print("\n💓 POLAR H10:")
print("   Just wear the strap - we'll auto-connect via Bluetooth!")
print("=" * 70)

# Setup OSC dispatcher for Muse
disp = dispatcher.Dispatcher()
disp.map("/muse/elements/alpha_absolute", handle_alpha)
disp.map("/muse/elements/beta_absolute", handle_beta)
disp.map("/muse/elements/theta_absolute", handle_theta)
disp.map("/muse/elements/gamma_absolute", handle_gamma)
disp.map("/muse/elements/delta_absolute", handle_delta)

# Start data saver thread
saver = threading.Thread(target=save_and_display, daemon=True)
saver.start()

# Start Polar H10 in background if available
if BLEAK_AVAILABLE:
    polar_thread = threading.Thread(target=start_polar_stream, daemon=True)
    polar_thread.start()
    time.sleep(2)  # Give it time to start scanning

# Start OSC server for Muse
print("\n🎯 Listening for sensor data...\n")

try:
    server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", OSC_PORT), disp)
    print(f"✅ OSC Server running on port {OSC_PORT}")
    print("Press Ctrl+C to stop\n")
    server.serve_forever()
except KeyboardInterrupt:
    polar_connected = False
    print(f"\n\n✅ Session Complete!")
    print(f"📁 Data saved to: {CSV_FILE}")
    print(f"📊 Total samples: {packet_count}")
    csv_file.close()
except Exception as e:
    print(f"\n❌ ERROR: {e}")
    if "address already in use" in str(e).lower():
        print("Port 5000 is busy - close other scripts first!")
    csv_file.close()

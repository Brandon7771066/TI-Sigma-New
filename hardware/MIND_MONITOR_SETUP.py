#!/usr/bin/env python3
"""
Mind Monitor + Polar H10 Bridge
================================

Run this script on YOUR COMPUTER (laptop/desktop) to stream biometric data
from Mind Monitor and Polar H10 to the Replit dashboard.

STEP-BY-STEP SETUP:
===================

1. Download this file to your computer

2. Install Python dependencies:
   pip install requests python-osc bleak numpy

3. Get your Replit app URL (looks like: https://workspace-brandonemerick9.replit.app)
   Or use the dev URL shown in the Replit webview

4. Configure Mind Monitor app on your phone:
   - Open Mind Monitor settings
   - Enable OSC streaming
   - Set OSC IP to YOUR COMPUTER'S IP (find with: ipconfig or ifconfig)
   - Set OSC Port to 5000 (or your chosen port)

5. Run this script:
   python MIND_MONITOR_SETUP.py --url https://YOUR-REPLIT-URL

Usage Examples:
   python MIND_MONITOR_SETUP.py --mode mind_monitor --url https://workspace-brandonemerick9.replit.app
   python MIND_MONITOR_SETUP.py --mode polar --url https://workspace-brandonemerick9.replit.app
   python MIND_MONITOR_SETUP.py --mode all --url https://workspace-brandonemerick9.replit.app
   python MIND_MONITOR_SETUP.py --mode demo --url https://workspace-brandonemerick9.replit.app

Author: TI Framework
Date: February 2026
"""

import argparse
import json
import time
import threading
import sys
import os
from datetime import datetime
from collections import deque

try:
    import requests
    import numpy as np
except ImportError:
    print("Missing core dependencies. Install with:")
    print("pip install requests numpy")
    sys.exit(1)

SESSION_ID = f"session_{datetime.now().strftime('%Y%m%d_%H%M%S')}"


class MindMonitorBridge:
    """Receive OSC from Mind Monitor and forward to Replit"""
    
    def __init__(self, api_url, osc_port=5000):
        self.api_url = api_url
        self.osc_port = osc_port
        self.running = False
        self.latest_data = {
            'raw': {'tp9': 0, 'af7': 0, 'af8': 0, 'tp10': 0},
            'bands': {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0},
            'metrics': {'attention': 0, 'meditation': 0, 'mellow': 0, 'concentration': 0}
        }
        self.packets_received = 0
        
    def start_osc_server(self):
        """Start OSC server to receive Mind Monitor data"""
        try:
            from pythonosc import dispatcher, osc_server
            
            disp = dispatcher.Dispatcher()
            
            disp.map("/muse/eeg", self.handle_eeg)
            disp.map("/muse/elements/alpha_absolute", lambda addr, *args: self.handle_band('alpha', args))
            disp.map("/muse/elements/beta_absolute", lambda addr, *args: self.handle_band('beta', args))
            disp.map("/muse/elements/theta_absolute", lambda addr, *args: self.handle_band('theta', args))
            disp.map("/muse/elements/gamma_absolute", lambda addr, *args: self.handle_band('gamma', args))
            disp.map("/muse/elements/delta_absolute", lambda addr, *args: self.handle_band('delta', args))
            disp.map("/muse/algorithm/mellow", lambda addr, *args: self.handle_metric('mellow', args))
            disp.map("/muse/algorithm/concentration", lambda addr, *args: self.handle_metric('concentration', args))
            
            server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", self.osc_port), disp)
            print(f"OSC Server listening on port {self.osc_port}")
            return server
            
        except ImportError:
            print("python-osc not installed. Run: pip install python-osc")
            return None
    
    def handle_eeg(self, address, *args):
        if len(args) >= 4:
            self.latest_data['raw'] = {'tp9': args[0], 'af7': args[1], 'af8': args[2], 'tp10': args[3]}
            self.packets_received += 1
    
    def handle_band(self, band, args):
        if args:
            self.latest_data['bands'][band] = float(np.mean(args))
    
    def handle_metric(self, metric, args):
        if args:
            self.latest_data['metrics'][metric] = args[0]
    
    def stream(self):
        server = self.start_osc_server()
        if not server:
            return
        
        server_thread = threading.Thread(target=server.serve_forever)
        server_thread.daemon = True
        server_thread.start()
        
        self.running = True
        
        print(f"\n{'='*60}")
        print("MIND MONITOR BRIDGE ACTIVE")
        print(f"{'='*60}")
        print(f"Forwarding to: {self.api_url}/api/muse/upload")
        print(f"Session: {SESSION_ID}")
        print(f"\nIn Mind Monitor app:")
        print(f"  1. Go to Settings > OSC Stream")
        print(f"  2. Set IP to your computer's IP address")
        print(f"  3. Set Port to {self.osc_port}")
        print(f"  4. Enable OSC streaming")
        print(f"\nPress Ctrl+C to stop\n")
        
        last_upload = 0
        
        while self.running:
            try:
                time.sleep(1.0)
                
                if self.packets_received == 0:
                    print("Waiting for Mind Monitor data...")
                    continue
                
                data = {
                    "timestamp": datetime.now().isoformat(),
                    "raw": self.latest_data['raw'],
                    "bands": self.latest_data['bands'],
                    "alpha": self.latest_data['bands'].get('alpha', 0),
                    "beta": self.latest_data['bands'].get('beta', 0),
                    "theta": self.latest_data['bands'].get('theta', 0),
                    "gamma": self.latest_data['bands'].get('gamma', 0),
                    "delta": self.latest_data['bands'].get('delta', 0),
                    "session_id": SESSION_ID,
                    "source": "mind_monitor",
                    "device": "Muse-MindMonitor",
                    "muse": True,
                    "polar": False
                }
                
                try:
                    resp = requests.post(f"{self.api_url}/api/muse/upload", json=data, timeout=5)
                    alpha = self.latest_data['bands'].get('alpha', 0)
                    beta = self.latest_data['bands'].get('beta', 0)
                    
                    if resp.status_code in [200, 201]:
                        print(f"[Muse] Alpha={alpha:.2f} Beta={beta:.2f} Packets={self.packets_received}")
                    else:
                        print(f"API Error: {resp.status_code} - {resp.text[:100]}")
                except requests.exceptions.RequestException as e:
                    print(f"Network error: {e}")
                    
            except Exception as e:
                print(f"Error: {e}")
        
        server.shutdown()
    
    def stop(self):
        self.running = False


class PolarH10Bridge:
    """Connect to Polar H10 via Bluetooth and forward to Replit"""
    
    def __init__(self, api_url):
        self.api_url = api_url
        self.running = False
        self.rr_buffer = deque(maxlen=120)
        
    def find_polar_device(self):
        try:
            import asyncio
            from bleak import BleakScanner
            
            print("Scanning for Polar H10...")
            print("(Make sure you're wearing the chest strap - it needs skin contact)")
            
            async def scan():
                devices = await BleakScanner.discover(timeout=15)
                for d in devices:
                    if d.name and "Polar" in d.name:
                        print(f"Found: {d.name} ({d.address})")
                        return d.address
                return None
            
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            address = loop.run_until_complete(scan())
            
            if not address:
                print("No Polar H10 found.")
                print("Tips:")
                print("  - Wet the electrode pads on the strap")
                print("  - Put the strap on (it won't broadcast without skin contact)")
                print("  - Make sure Bluetooth is enabled")
            return address
            
        except ImportError:
            print("bleak not installed. Run: pip install bleak")
            return None
    
    def compute_hrv_metrics(self):
        if len(self.rr_buffer) < 10:
            return None
        
        rr = np.array(list(self.rr_buffer))
        diffs = np.diff(rr)
        rmssd = np.sqrt(np.mean(diffs ** 2))
        sdnn = np.std(rr)
        
        hr_values = 60000 / rr
        hr_stability = 1.0 - min(1.0, np.std(hr_values[-10:]) / 10)
        rmssd_norm = min(1.0, rmssd / 80)
        coherence = rmssd_norm * 0.5 + hr_stability * 0.5
        
        return {'rmssd': float(rmssd), 'sdnn': float(sdnn), 'coherence': float(coherence)}
    
    def stream(self):
        try:
            import asyncio
            from bleak import BleakClient
            
            address = self.find_polar_device()
            if not address:
                return
            
            HR_UUID = "00002a37-0000-1000-8000-00805f9b34fb"
            self.running = True
            
            async def run():
                async with BleakClient(address) as client:
                    print(f"\n{'='*60}")
                    print("POLAR H10 BRIDGE ACTIVE")
                    print(f"{'='*60}")
                    print(f"Connected to: {address}")
                    print(f"Forwarding to: {self.api_url}/api/polar/upload")
                    print(f"Session: {SESSION_ID}")
                    print(f"\nPress Ctrl+C to stop\n")
                    
                    def callback(sender, data):
                        flags = data[0]
                        hr_format = flags & 0x01
                        
                        if hr_format:
                            hr = int.from_bytes(data[1:3], 'little')
                            rr_offset = 3
                        else:
                            hr = data[1]
                            rr_offset = 2
                        
                        rr_present = (flags >> 4) & 0x01
                        rr_intervals = []
                        
                        if rr_present:
                            while rr_offset + 1 < len(data):
                                rr = int.from_bytes(data[rr_offset:rr_offset+2], 'little')
                                rr_intervals.append(rr)
                                self.rr_buffer.append(rr)
                                rr_offset += 2
                        
                        hrv = self.compute_hrv_metrics()
                        
                        payload = {
                            "timestamp": datetime.now().isoformat(),
                            "heart_rate": hr,
                            "hr": hr,
                            "rr_interval": rr_intervals[0] if rr_intervals else 0,
                            "rr": rr_intervals[0] if rr_intervals else 0,
                            "rmssd": hrv.get('rmssd', 0) if hrv else 0,
                            "coherence": hrv.get('coherence', 0) if hrv else 0,
                            "session_id": SESSION_ID,
                            "source": "polar_ble_direct",
                            "device": address,
                            "polar": True,
                            "muse": False
                        }
                        
                        try:
                            resp = requests.post(f"{self.api_url}/api/polar/upload", json=payload, timeout=5)
                            rmssd = hrv.get('rmssd', 0) if hrv else 0
                            coh = hrv.get('coherence', 0) if hrv else 0
                            
                            if resp.status_code in [200, 201]:
                                print(f"[Polar] HR={hr} RMSSD={rmssd:.1f} Coherence={coh:.2f}")
                            else:
                                print(f"API Error: {resp.status_code}")
                        except:
                            pass
                    
                    await client.start_notify(HR_UUID, callback)
                    
                    while self.running:
                        await asyncio.sleep(1)
                    
                    await client.stop_notify(HR_UUID)
            
            asyncio.run(run())
            
        except Exception as e:
            print(f"Polar error: {e}")
    
    def stop(self):
        self.running = False


def demo_mode(api_url):
    """Send demo data to test the connection"""
    print(f"\n{'='*60}")
    print("DEMO MODE - Testing Connection")
    print(f"{'='*60}")
    print(f"Target: {api_url}/api/upload")
    print(f"Session: {SESSION_ID}")
    print("\nSending synthetic data to verify connectivity...")
    print("Press Ctrl+C to stop\n")
    
    t = 0
    while True:
        try:
            hr = int(70 + 5 * np.sin(t/20) + np.random.normal(0, 2))
            alpha = 0.5 + 0.3 * np.sin(t/10) + np.random.normal(0, 0.05)
            
            data = {
                "timestamp": datetime.now().isoformat(),
                "hr": hr,
                "heart_rate": hr,
                "rr": int(60000 / hr),
                "alpha": alpha,
                "beta": 0.3 + np.random.normal(0, 0.03),
                "theta": 0.4 + np.random.normal(0, 0.04),
                "gamma": 0.2 + np.random.normal(0, 0.02),
                "delta": 0.3 + np.random.normal(0, 0.03),
                "rmssd": 45 + np.random.normal(0, 5),
                "coherence": 0.7 + np.random.normal(0, 0.1),
                "session_id": SESSION_ID,
                "source": "demo",
                "device": "Demo-Device",
                "muse": True,
                "polar": True
            }
            
            resp = requests.post(f"{api_url}/api/upload", json=data, timeout=5)
            
            if resp.status_code in [200, 201]:
                print(f"[Demo] HR={hr} Alpha={alpha:.2f} - OK")
            else:
                print(f"Error: {resp.status_code} - {resp.text[:100]}")
            
            t += 1
            time.sleep(1)
            
        except KeyboardInterrupt:
            print("\nDemo stopped.")
            break
        except Exception as e:
            print(f"Error: {e}")
            time.sleep(2)


def main():
    parser = argparse.ArgumentParser(
        description="Bridge Mind Monitor and Polar H10 to Replit",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python MIND_MONITOR_SETUP.py --mode demo --url https://your-app.replit.app
  python MIND_MONITOR_SETUP.py --mode mind_monitor --url https://your-app.replit.app
  python MIND_MONITOR_SETUP.py --mode polar --url https://your-app.replit.app
  python MIND_MONITOR_SETUP.py --mode all --url https://your-app.replit.app
        """
    )
    
    parser.add_argument('--mode', choices=['demo', 'mind_monitor', 'polar', 'all'], 
                        default='demo', help='Mode: demo, mind_monitor, polar, or all')
    parser.add_argument('--url', required=True, help='Your Replit app URL')
    parser.add_argument('--osc-port', type=int, default=5000, help='OSC port for Mind Monitor (default: 5000)')
    
    args = parser.parse_args()
    
    url = args.url.rstrip('/')
    
    print(f"\n{'='*60}")
    print("TI FRAMEWORK BIOMETRIC BRIDGE")
    print(f"{'='*60}")
    print(f"Mode: {args.mode}")
    print(f"Target: {url}")
    print(f"{'='*60}\n")
    
    try:
        if args.mode == 'demo':
            demo_mode(url)
            
        elif args.mode == 'mind_monitor':
            bridge = MindMonitorBridge(url, args.osc_port)
            bridge.stream()
            
        elif args.mode == 'polar':
            bridge = PolarH10Bridge(url)
            bridge.stream()
            
        elif args.mode == 'all':
            print("Starting both Mind Monitor and Polar H10 bridges...")
            
            muse_bridge = MindMonitorBridge(url, args.osc_port)
            polar_bridge = PolarH10Bridge(url)
            
            muse_thread = threading.Thread(target=muse_bridge.stream)
            polar_thread = threading.Thread(target=polar_bridge.stream)
            
            muse_thread.daemon = True
            polar_thread.daemon = True
            
            muse_thread.start()
            polar_thread.start()
            
            try:
                while True:
                    time.sleep(1)
            except KeyboardInterrupt:
                print("\nStopping...")
                muse_bridge.stop()
                polar_bridge.stop()
                
    except KeyboardInterrupt:
        print("\nStopped by user.")


if __name__ == "__main__":
    main()

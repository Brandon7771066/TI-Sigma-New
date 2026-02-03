#!/usr/bin/env python3
"""
Local Biometric Collector
=========================
Collects data from Mind Monitor and Polar H10, saves to local CSV file.
You can then upload this file to the Replit dashboard.

Usage:
  python LOCAL_BIOMETRIC_COLLECTOR.py --mode demo
  python LOCAL_BIOMETRIC_COLLECTOR.py --mode mind_monitor
  python LOCAL_BIOMETRIC_COLLECTOR.py --mode polar
  python LOCAL_BIOMETRIC_COLLECTOR.py --mode all
"""

import argparse
import csv
import os
import sys
import time
import threading
from datetime import datetime
from collections import deque

try:
    import numpy as np
except ImportError:
    print("Installing numpy...")
    os.system("pip install numpy")
    import numpy as np

SESSION_ID = f"session_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
OUTPUT_FILE = f"biometric_data_{SESSION_ID}.csv"

data_buffer = []
buffer_lock = threading.Lock()


def save_to_csv():
    """Save buffered data to CSV file"""
    global data_buffer
    with buffer_lock:
        if not data_buffer:
            return
        
        file_exists = os.path.exists(OUTPUT_FILE)
        
        with open(OUTPUT_FILE, 'a', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=[
                'timestamp', 'hr', 'rr', 'rmssd', 'coherence',
                'alpha', 'beta', 'theta', 'gamma', 'delta',
                'source', 'session_id'
            ])
            
            if not file_exists:
                writer.writeheader()
            
            for row in data_buffer:
                writer.writerow(row)
        
        count = len(data_buffer)
        data_buffer = []
        print(f"  [Saved {count} records to {OUTPUT_FILE}]")


def add_data(data):
    """Add data to buffer"""
    with buffer_lock:
        data_buffer.append(data)
    
    if len(data_buffer) >= 10:
        save_to_csv()


class MindMonitorReceiver:
    """Receive OSC from Mind Monitor"""
    
    def __init__(self, osc_port=5000):
        self.osc_port = osc_port
        self.running = False
        self.latest_data = {
            'bands': {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
        }
        self.packets_received = 0
        
    def start_osc_server(self):
        try:
            from pythonosc import dispatcher, osc_server
            
            disp = dispatcher.Dispatcher()
            disp.map("/muse/elements/alpha_absolute", lambda addr, *args: self.handle_band('alpha', args))
            disp.map("/muse/elements/beta_absolute", lambda addr, *args: self.handle_band('beta', args))
            disp.map("/muse/elements/theta_absolute", lambda addr, *args: self.handle_band('theta', args))
            disp.map("/muse/elements/gamma_absolute", lambda addr, *args: self.handle_band('gamma', args))
            disp.map("/muse/elements/delta_absolute", lambda addr, *args: self.handle_band('delta', args))
            
            server = osc_server.ThreadingOSCUDPServer(("0.0.0.0", self.osc_port), disp)
            print(f"OSC Server listening on port {self.osc_port}")
            return server
            
        except ImportError:
            print("python-osc not installed. Run: pip install python-osc")
            return None
    
    def handle_band(self, band, args):
        if args:
            self.latest_data['bands'][band] = float(np.mean(args))
            self.packets_received += 1
    
    def stream(self):
        server = self.start_osc_server()
        if not server:
            return
        
        server_thread = threading.Thread(target=server.serve_forever)
        server_thread.daemon = True
        server_thread.start()
        
        self.running = True
        
        print(f"\n{'='*60}")
        print("MIND MONITOR LOCAL COLLECTOR")
        print(f"{'='*60}")
        print(f"Saving to: {OUTPUT_FILE}")
        print(f"Session: {SESSION_ID}")
        print(f"\nIn Mind Monitor app:")
        print(f"  1. Set OSC IP to your computer's IP")
        print(f"  2. Set OSC Port to {self.osc_port}")
        print(f"  3. Enable OSC streaming")
        print(f"\nPress Ctrl+C to stop\n")
        
        while self.running:
            try:
                time.sleep(1.0)
                
                if self.packets_received == 0:
                    print("Waiting for Mind Monitor data...")
                    continue
                
                data = {
                    'timestamp': datetime.now().isoformat(),
                    'hr': 0,
                    'rr': 0,
                    'rmssd': 0,
                    'coherence': 0,
                    'alpha': self.latest_data['bands'].get('alpha', 0),
                    'beta': self.latest_data['bands'].get('beta', 0),
                    'theta': self.latest_data['bands'].get('theta', 0),
                    'gamma': self.latest_data['bands'].get('gamma', 0),
                    'delta': self.latest_data['bands'].get('delta', 0),
                    'source': 'mind_monitor',
                    'session_id': SESSION_ID
                }
                
                add_data(data)
                alpha = self.latest_data['bands'].get('alpha', 0)
                print(f"[Muse] Alpha={alpha:.2f} Packets={self.packets_received}")
                    
            except Exception as e:
                print(f"Error: {e}")
        
        server.shutdown()
        save_to_csv()
    
    def stop(self):
        self.running = False


class PolarH10Receiver:
    """Connect to Polar H10 via Bluetooth"""
    
    def __init__(self):
        self.running = False
        self.rr_buffer = deque(maxlen=120)
        
    def find_polar_device(self):
        try:
            import asyncio
            from bleak import BleakScanner
            
            print("Scanning for Polar H10...")
            print("(Make sure you're wearing the chest strap)")
            
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
                print("No Polar H10 found. Tips:")
                print("  - Wet the electrode pads")
                print("  - Put the strap on (needs skin contact)")
            return address
            
        except ImportError:
            print("bleak not installed. Run: pip install bleak")
            return None
    
    def compute_hrv(self):
        if len(self.rr_buffer) < 10:
            return None
        rr = np.array(list(self.rr_buffer))
        diffs = np.diff(rr)
        rmssd = np.sqrt(np.mean(diffs ** 2))
        hr_values = 60000 / rr
        coherence = 1.0 - min(1.0, np.std(hr_values[-10:]) / 10)
        return {'rmssd': float(rmssd), 'coherence': float(coherence)}
    
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
                    print("POLAR H10 LOCAL COLLECTOR")
                    print(f"{'='*60}")
                    print(f"Connected to: {address}")
                    print(f"Saving to: {OUTPUT_FILE}")
                    print(f"Session: {SESSION_ID}")
                    print(f"\nPress Ctrl+C to stop\n")
                    
                    def callback(sender, data_bytes):
                        flags = data_bytes[0]
                        hr_format = flags & 0x01
                        
                        if hr_format:
                            hr = int.from_bytes(data_bytes[1:3], 'little')
                            rr_offset = 3
                        else:
                            hr = data_bytes[1]
                            rr_offset = 2
                        
                        rr_present = (flags >> 4) & 0x01
                        rr_intervals = []
                        
                        if rr_present:
                            while rr_offset + 1 < len(data_bytes):
                                rr = int.from_bytes(data_bytes[rr_offset:rr_offset+2], 'little')
                                rr_intervals.append(rr)
                                self.rr_buffer.append(rr)
                                rr_offset += 2
                        
                        hrv = self.compute_hrv()
                        
                        data = {
                            'timestamp': datetime.now().isoformat(),
                            'hr': hr,
                            'rr': rr_intervals[0] if rr_intervals else 0,
                            'rmssd': hrv.get('rmssd', 0) if hrv else 0,
                            'coherence': hrv.get('coherence', 0) if hrv else 0,
                            'alpha': 0,
                            'beta': 0,
                            'theta': 0,
                            'gamma': 0,
                            'delta': 0,
                            'source': 'polar_h10',
                            'session_id': SESSION_ID
                        }
                        
                        add_data(data)
                        rmssd = hrv.get('rmssd', 0) if hrv else 0
                        print(f"[Polar] HR={hr} RMSSD={rmssd:.1f}")
                    
                    await client.start_notify(HR_UUID, callback)
                    
                    while self.running:
                        await asyncio.sleep(1)
                    
                    await client.stop_notify(HR_UUID)
            
            asyncio.run(run())
            
        except Exception as e:
            print(f"Polar error: {e}")
        finally:
            save_to_csv()
    
    def stop(self):
        self.running = False


def demo_mode():
    """Generate demo data to test the system"""
    print(f"\n{'='*60}")
    print("DEMO MODE - Generating Test Data")
    print(f"{'='*60}")
    print(f"Saving to: {OUTPUT_FILE}")
    print(f"Session: {SESSION_ID}")
    print("\nGenerating synthetic biometric data...")
    print("Press Ctrl+C to stop\n")
    
    t = 0
    while True:
        try:
            hr = int(70 + 5 * np.sin(t/20) + np.random.normal(0, 2))
            alpha = 0.5 + 0.3 * np.sin(t/10) + np.random.normal(0, 0.05)
            
            data = {
                'timestamp': datetime.now().isoformat(),
                'hr': hr,
                'rr': int(60000 / hr),
                'rmssd': 45 + np.random.normal(0, 5),
                'coherence': 0.7 + np.random.normal(0, 0.1),
                'alpha': alpha,
                'beta': 0.3 + np.random.normal(0, 0.03),
                'theta': 0.4 + np.random.normal(0, 0.04),
                'gamma': 0.2 + np.random.normal(0, 0.02),
                'delta': 0.3 + np.random.normal(0, 0.03),
                'source': 'demo',
                'session_id': SESSION_ID
            }
            
            add_data(data)
            print(f"[Demo] HR={hr} Alpha={alpha:.2f}")
            
            t += 1
            time.sleep(1)
            
        except KeyboardInterrupt:
            print("\nDemo stopped.")
            save_to_csv()
            print(f"\nData saved to: {OUTPUT_FILE}")
            print("Upload this file to the Replit dashboard!")
            break


def main():
    parser = argparse.ArgumentParser(description="Local Biometric Data Collector")
    parser.add_argument('--mode', choices=['demo', 'mind_monitor', 'polar', 'all'], 
                        default='demo', help='Collection mode')
    parser.add_argument('--osc-port', type=int, default=5000, help='OSC port for Mind Monitor')
    
    args = parser.parse_args()
    
    print(f"\n{'='*60}")
    print("LOCAL BIOMETRIC COLLECTOR")
    print(f"{'='*60}")
    print(f"Mode: {args.mode}")
    print(f"Output: {OUTPUT_FILE}")
    print(f"{'='*60}\n")
    
    try:
        if args.mode == 'demo':
            demo_mode()
            
        elif args.mode == 'mind_monitor':
            receiver = MindMonitorReceiver(args.osc_port)
            receiver.stream()
            
        elif args.mode == 'polar':
            receiver = PolarH10Receiver()
            receiver.stream()
            
        elif args.mode == 'all':
            print("Starting both Mind Monitor and Polar H10...")
            
            muse = MindMonitorReceiver(args.osc_port)
            polar = PolarH10Receiver()
            
            muse_thread = threading.Thread(target=muse.stream)
            polar_thread = threading.Thread(target=polar.stream)
            
            muse_thread.daemon = True
            polar_thread.daemon = True
            
            muse_thread.start()
            polar_thread.start()
            
            try:
                while True:
                    time.sleep(1)
            except KeyboardInterrupt:
                print("\nStopping...")
                muse.stop()
                polar.stop()
                save_to_csv()
                
    except KeyboardInterrupt:
        save_to_csv()
        print(f"\nData saved to: {OUTPUT_FILE}")


if __name__ == "__main__":
    main()

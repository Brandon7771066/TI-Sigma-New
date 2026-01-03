#!/usr/bin/env python3
"""
🧠 Local Biometric Collector for Mood Amplifier
================================================

Run this script on your LOCAL computer (laptop/desktop) to stream biometric data
from your devices to the Replit cloud dashboard.

SETUP OPTIONS:

1. MUSE EEG via Mind Monitor (RECOMMENDED - Easiest):
   - Install Mind Monitor on your phone (iOS/Android)
   - Connect Muse headband to Mind Monitor
   - In Mind Monitor settings, enable OSC streaming to your laptop's IP:5000
   - Run: python local_biometric_collector.py --mode mind_monitor

2. MUSE EEG via MuseLSL (Direct Bluetooth):
   - Install: pip install muselsl pylsl
   - Pair Muse to your laptop via Bluetooth
   - Run: muselsl stream (in another terminal)
   - Run: python local_biometric_collector.py --mode muselsl

3. POLAR H10 via Bleak (Direct Bluetooth):
   - Pair Polar H10 to your laptop via Bluetooth
   - Run: python local_biometric_collector.py --mode polar

4. ALL DEVICES (Combined):
   - Run: python local_biometric_collector.py --mode all

REQUIREMENTS:
    pip install requests python-osc numpy

OPTIONAL (for specific modes):
    pip install muselsl pylsl  # For MuseLSL mode
    pip install bleak         # For direct Polar BLE

Author: BlissGene Therapeutics
Date: November 28, 2025
"""

import argparse
import json
import time
import threading
import requests
import numpy as np
from datetime import datetime
from collections import deque

# Configuration - UPDATE THIS with your Replit app URL
# REPLIT_API_URL = "https://your-replit-app.replit.app"  # For published app
REPLIT_API_URL = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"  # Current dev URL

# Alternatively, use the local development URL if running locally
# REPLIT_API_URL = "http://localhost:8000"

SESSION_ID = f"session_{datetime.now().strftime('%Y%m%d_%H%M%S')}"


class MuseLSLCollector:
    """Collect Muse EEG data via Lab Streaming Layer (LSL)"""
    
    def __init__(self, api_url):
        self.api_url = api_url
        self.running = False
        self.sample_buffer = deque(maxlen=256)
        
    def connect(self):
        """Connect to Muse LSL stream"""
        try:
            from pylsl import StreamInlet, resolve_stream
            
            print("🔍 Looking for Muse LSL stream...")
            print("   (Make sure 'muselsl stream' is running in another terminal)")
            
            streams = resolve_stream('type', 'EEG', timeout=30)
            if not streams:
                print("❌ No Muse LSL stream found!")
                print("   Run: muselsl stream")
                return False
            
            self.inlet = StreamInlet(streams[0])
            print(f"✅ Connected to Muse LSL stream: {streams[0].name()}")
            return True
            
        except ImportError:
            print("❌ pylsl not installed. Run: pip install pylsl muselsl")
            return False
        except Exception as e:
            print(f"❌ LSL connection error: {e}")
            return False
    
    def compute_band_powers(self, samples):
        """Compute FFT band powers from EEG samples"""
        if len(samples) < 256:
            return None
        
        data = np.array(samples)
        
        # FFT for each channel, average across channels
        powers = {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
        
        for ch in range(min(4, data.shape[1])):
            channel_data = data[:, ch]
            fft = np.fft.fft(channel_data)
            freqs = np.fft.fftfreq(len(channel_data), 1/256)  # 256 Hz sample rate
            power = np.abs(fft) ** 2
            
            # Band definitions
            bands = {
                'delta': (1, 4),
                'theta': (4, 8),
                'alpha': (8, 12),
                'beta': (13, 30),
                'gamma': (30, 50)
            }
            
            for band, (low, high) in bands.items():
                idx = np.logical_and(freqs >= low, freqs <= high)
                powers[band] += np.sum(power[idx]) / len(channel_data)
        
        # Average across channels
        for band in powers:
            powers[band] /= 4
            
        return powers
    
    def stream(self):
        """Stream data to Replit API"""
        if not self.connect():
            return
        
        self.running = True
        samples_collected = 0
        batch = []
        
        print(f"\n🚀 Streaming Muse EEG to {self.api_url}/api/muse/upload")
        print(f"📊 Session ID: {SESSION_ID}")
        print("   Press Ctrl+C to stop\n")
        
        while self.running:
            try:
                sample, timestamp = self.inlet.pull_sample(timeout=1.0)
                
                if sample:
                    self.sample_buffer.append(sample[:4])  # TP9, AF7, AF8, TP10
                    samples_collected += 1
                    
                    # Every 256 samples (~1 second), compute and send
                    if samples_collected % 256 == 0:
                        powers = self.compute_band_powers(list(self.sample_buffer))
                        
                        if powers:
                            data = {
                                "timestamp": datetime.now().isoformat(),
                                "raw": {
                                    "tp9": sample[0],
                                    "af7": sample[1],
                                    "af8": sample[2],
                                    "tp10": sample[3]
                                },
                                "bands": powers,
                                "session_id": SESSION_ID,
                                "source": "muselsl",
                                "device_id": "Muse-LSL"
                            }
                            
                            try:
                                resp = requests.post(
                                    f"{self.api_url}/api/muse/upload",
                                    json=data,
                                    timeout=5
                                )
                                if resp.status_code == 201:
                                    print(f"✓ Sent: Alpha={powers['alpha']:.1f} Beta={powers['beta']:.1f}")
                                else:
                                    print(f"⚠ API error: {resp.status_code}")
                            except requests.exceptions.RequestException as e:
                                print(f"⚠ Network error: {e}")
                
            except Exception as e:
                print(f"⚠ Stream error: {e}")
                time.sleep(0.1)
    
    def stop(self):
        self.running = False


class MindMonitorCollector:
    """Collect Muse EEG data via Mind Monitor OSC"""
    
    def __init__(self, api_url, osc_port=5000):
        self.api_url = api_url
        self.osc_port = osc_port
        self.running = False
        self.latest_data = {
            'raw': {'tp9': 0, 'af7': 0, 'af8': 0, 'tp10': 0},
            'bands': {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0},
            'metrics': {'attention': 0, 'meditation': 0, 'mellow': 0, 'concentration': 0}
        }
        
    def start_osc_server(self):
        """Start OSC server to receive Mind Monitor data"""
        try:
            from pythonosc import dispatcher, osc_server
            
            disp = dispatcher.Dispatcher()
            
            # Raw EEG channels
            disp.map("/muse/eeg", self.handle_eeg)
            
            # Band powers (absolute)
            disp.map("/muse/elements/alpha_absolute", lambda addr, *args: self.handle_band('alpha', args))
            disp.map("/muse/elements/beta_absolute", lambda addr, *args: self.handle_band('beta', args))
            disp.map("/muse/elements/theta_absolute", lambda addr, *args: self.handle_band('theta', args))
            disp.map("/muse/elements/gamma_absolute", lambda addr, *args: self.handle_band('gamma', args))
            disp.map("/muse/elements/delta_absolute", lambda addr, *args: self.handle_band('delta', args))
            
            # Mellow/Concentration (Mind Monitor proprietary)
            disp.map("/muse/algorithm/mellow", lambda addr, *args: self.handle_metric('mellow', args))
            disp.map("/muse/algorithm/concentration", lambda addr, *args: self.handle_metric('concentration', args))
            
            server = osc_server.ThreadingOSCUDPServer(
                ("0.0.0.0", self.osc_port), disp
            )
            
            print(f"🎧 OSC Server listening on port {self.osc_port}")
            print(f"   Configure Mind Monitor to send OSC to YOUR_LAPTOP_IP:{self.osc_port}")
            
            return server
            
        except ImportError:
            print("❌ python-osc not installed. Run: pip install python-osc")
            return None
    
    def handle_eeg(self, address, *args):
        """Handle raw EEG data"""
        if len(args) >= 4:
            self.latest_data['raw'] = {
                'tp9': args[0], 'af7': args[1], 'af8': args[2], 'tp10': args[3]
            }
    
    def handle_band(self, band, args):
        """Handle band power data"""
        if args:
            self.latest_data['bands'][band] = np.mean(args)
    
    def handle_metric(self, metric, args):
        """Handle Mind Monitor metrics"""
        if args:
            self.latest_data['metrics'][metric] = args[0]
    
    def stream(self):
        """Stream data to Replit API"""
        server = self.start_osc_server()
        if not server:
            return
        
        # Start OSC server in background
        server_thread = threading.Thread(target=server.serve_forever)
        server_thread.daemon = True
        server_thread.start()
        
        self.running = True
        
        print(f"\n🚀 Forwarding Mind Monitor data to {self.api_url}/api/muse/upload")
        print(f"📊 Session ID: {SESSION_ID}")
        print("   Press Ctrl+C to stop\n")
        
        while self.running:
            try:
                # Send every second
                time.sleep(1.0)
                
                data = {
                    "timestamp": datetime.now().isoformat(),
                    "raw": self.latest_data['raw'],
                    "bands": self.latest_data['bands'],
                    "metrics": self.latest_data['metrics'],
                    "session_id": SESSION_ID,
                    "source": "mind_monitor",
                    "device_id": "Muse-MindMonitor"
                }
                
                try:
                    resp = requests.post(
                        f"{self.api_url}/api/muse/upload",
                        json=data,
                        timeout=5
                    )
                    if resp.status_code == 201:
                        alpha = self.latest_data['bands'].get('alpha', 0)
                        beta = self.latest_data['bands'].get('beta', 0)
                        print(f"✓ Sent: Alpha={alpha:.2f} Beta={beta:.2f}")
                    else:
                        print(f"⚠ API error: {resp.status_code}")
                except requests.exceptions.RequestException as e:
                    print(f"⚠ Network error: {e}")
                    
            except Exception as e:
                print(f"⚠ Stream error: {e}")
        
        server.shutdown()
    
    def stop(self):
        self.running = False


class PolarH10Collector:
    """Collect Polar H10 HRV data via Bluetooth LE"""
    
    def __init__(self, api_url):
        self.api_url = api_url
        self.running = False
        self.rr_buffer = deque(maxlen=120)  # 2 minutes of RR intervals
        
    def find_polar_device(self):
        """Scan for Polar H10 device"""
        try:
            import asyncio
            from bleak import BleakScanner
            
            print("🔍 Scanning for Polar H10...")
            
            async def scan():
                devices = await BleakScanner.discover(timeout=10)
                for d in devices:
                    if d.name and "Polar" in d.name:
                        print(f"✅ Found: {d.name} ({d.address})")
                        return d.address
                return None
            
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            address = loop.run_until_complete(scan())
            
            if not address:
                print("❌ No Polar H10 found. Make sure it's paired and nearby.")
            return address
            
        except ImportError:
            print("❌ bleak not installed. Run: pip install bleak")
            return None
    
    def compute_hrv_metrics(self):
        """Compute HRV metrics from RR intervals"""
        if len(self.rr_buffer) < 10:
            return None
        
        rr = np.array(list(self.rr_buffer))
        
        # RMSSD
        diffs = np.diff(rr)
        rmssd = np.sqrt(np.mean(diffs ** 2))
        
        # SDNN
        sdnn = np.std(rr)
        
        # Simple coherence estimate
        hr_values = 60000 / rr  # Convert RR to HR
        hr_stability = 1.0 - min(1.0, np.std(hr_values[-10:]) / 10)
        rmssd_norm = min(1.0, rmssd / 80)
        coherence = rmssd_norm * 0.5 + hr_stability * 0.5
        
        return {
            'rmssd': float(rmssd),
            'sdnn': float(sdnn),
            'coherence': float(coherence)
        }
    
    def stream(self):
        """Stream Polar H10 data to Replit API"""
        try:
            import asyncio
            from bleak import BleakClient
            
            address = self.find_polar_device()
            if not address:
                return
            
            # Heart Rate Measurement UUID
            HR_UUID = "00002a37-0000-1000-8000-00805f9b34fb"
            
            self.running = True
            
            async def run():
                async with BleakClient(address) as client:
                    print(f"\n🚀 Connected to Polar H10!")
                    print(f"📊 Streaming to {self.api_url}/api/polar/upload")
                    print(f"📊 Session ID: {SESSION_ID}")
                    print("   Press Ctrl+C to stop\n")
                    
                    def callback(sender, data):
                        # Parse heart rate data
                        flags = data[0]
                        hr_format = flags & 0x01
                        
                        if hr_format:
                            hr = int.from_bytes(data[1:3], 'little')
                            rr_offset = 3
                        else:
                            hr = data[1]
                            rr_offset = 2
                        
                        # Extract RR intervals if present
                        rr_present = (flags >> 4) & 0x01
                        rr_intervals = []
                        
                        if rr_present:
                            while rr_offset + 1 < len(data):
                                rr = int.from_bytes(data[rr_offset:rr_offset+2], 'little')
                                rr_intervals.append(rr)
                                self.rr_buffer.append(rr)
                                rr_offset += 2
                        
                        # Compute HRV metrics
                        hrv = self.compute_hrv_metrics()
                        
                        # Send to API
                        payload = {
                            "timestamp": datetime.now().isoformat(),
                            "heart_rate": hr,
                            "rr_interval": rr_intervals[0] if rr_intervals else None,
                            "rr_intervals": rr_intervals,
                            "hrv": hrv or {},
                            "coherence": hrv.get('coherence') if hrv else None,
                            "session_id": SESSION_ID,
                            "source": "polar_ble_direct",
                            "device_id": address
                        }
                        
                        try:
                            resp = requests.post(
                                f"{self.api_url}/api/polar/upload",
                                json=payload,
                                timeout=5
                            )
                            if resp.status_code == 201:
                                rmssd = hrv.get('rmssd', 0) if hrv else 0
                                print(f"✓ HR={hr} RMSSD={rmssd:.1f}")
                        except:
                            pass
                    
                    await client.start_notify(HR_UUID, callback)
                    
                    while self.running:
                        await asyncio.sleep(1)
                    
                    await client.stop_notify(HR_UUID)
            
            asyncio.run(run())
            
        except Exception as e:
            print(f"❌ Polar error: {e}")
    
    def stop(self):
        self.running = False


def demo_mode(api_url):
    """Send synthetic demo data to test the connection"""
    print(f"\n🧪 DEMO MODE - Sending synthetic data to {api_url}")
    print(f"📊 Session ID: {SESSION_ID}")
    print("   Press Ctrl+C to stop\n")
    
    t = 0
    while True:
        try:
            # Synthetic Muse data
            muse_data = {
                "timestamp": datetime.now().isoformat(),
                "raw": {
                    "tp9": 800 + np.random.normal(0, 50),
                    "af7": 810 + np.random.normal(0, 50),
                    "af8": 805 + np.random.normal(0, 50),
                    "tp10": 795 + np.random.normal(0, 50)
                },
                "bands": {
                    "alpha": 0.5 + 0.3 * np.sin(t/10) + np.random.normal(0, 0.05),
                    "beta": 0.3 + 0.1 * np.sin(t/8) + np.random.normal(0, 0.03),
                    "theta": 0.4 + 0.2 * np.sin(t/12) + np.random.normal(0, 0.04),
                    "gamma": 0.2 + 0.1 * np.sin(t/6) + np.random.normal(0, 0.02),
                    "delta": 0.3 + 0.1 * np.sin(t/15) + np.random.normal(0, 0.03)
                },
                "session_id": SESSION_ID,
                "source": "demo",
                "device_id": "Demo-Muse"
            }
            
            # Synthetic Polar data
            hr = int(70 + 5 * np.sin(t/20) + np.random.normal(0, 2))
            polar_data = {
                "timestamp": datetime.now().isoformat(),
                "heart_rate": hr,
                "rr_interval": int(60000 / hr + np.random.normal(0, 20)),
                "hrv": {
                    "rmssd": 45 + 10 * np.sin(t/30) + np.random.normal(0, 5),
                    "sdnn": 50 + 8 * np.sin(t/25) + np.random.normal(0, 4)
                },
                "coherence": 0.5 + 0.2 * np.sin(t/15) + np.random.normal(0, 0.05),
                "session_id": SESSION_ID,
                "source": "demo",
                "device_id": "Demo-Polar"
            }
            
            # Send to API
            try:
                resp1 = requests.post(f"{api_url}/api/muse/upload", json=muse_data, timeout=5)
                resp2 = requests.post(f"{api_url}/api/polar/upload", json=polar_data, timeout=5)
                
                if resp1.status_code == 201 and resp2.status_code == 201:
                    print(f"✓ Demo: HR={hr} Alpha={muse_data['bands']['alpha']:.2f}")
                else:
                    print(f"⚠ API: Muse={resp1.status_code} Polar={resp2.status_code}")
            except requests.exceptions.RequestException as e:
                print(f"⚠ Network error: {e}")
            
            t += 1
            time.sleep(1)
            
        except KeyboardInterrupt:
            print("\n\n👋 Demo stopped.")
            break


def main():
    parser = argparse.ArgumentParser(
        description="Local Biometric Collector for Mood Amplifier",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Test connection with demo data:
  python local_biometric_collector.py --mode demo --url https://your-app.replit.app

  # Collect Muse via Mind Monitor OSC:
  python local_biometric_collector.py --mode mind_monitor --url https://your-app.replit.app

  # Collect Muse via MuseLSL:
  python local_biometric_collector.py --mode muselsl --url https://your-app.replit.app

  # Collect Polar H10 via Bluetooth:
  python local_biometric_collector.py --mode polar --url https://your-app.replit.app
        """
    )
    
    parser.add_argument(
        '--mode', 
        choices=['demo', 'mind_monitor', 'muselsl', 'polar', 'all'],
        default='demo',
        help='Collection mode (default: demo)'
    )
    
    parser.add_argument(
        '--url',
        default=REPLIT_API_URL,
        help='Replit API URL (e.g., https://your-app.replit.app)'
    )
    
    parser.add_argument(
        '--osc-port',
        type=int,
        default=5000,
        help='OSC port for Mind Monitor (default: 5000)'
    )
    
    args = parser.parse_args()
    
    print("=" * 60)
    print("🧠 Local Biometric Collector for Mood Amplifier")
    print("=" * 60)
    print(f"\nMode: {args.mode.upper()}")
    print(f"API URL: {args.url}")
    print(f"Session: {SESSION_ID}")
    
    # Check API health
    try:
        resp = requests.get(f"{args.url}/health", timeout=5)
        if resp.status_code == 200:
            print("✅ API connection OK")
        else:
            print(f"⚠ API returned {resp.status_code}")
    except:
        print("⚠ Could not reach API - check your URL")
    
    print()
    
    try:
        if args.mode == 'demo':
            demo_mode(args.url)
            
        elif args.mode == 'mind_monitor':
            collector = MindMonitorCollector(args.url, args.osc_port)
            collector.stream()
            
        elif args.mode == 'muselsl':
            collector = MuseLSLCollector(args.url)
            collector.stream()
            
        elif args.mode == 'polar':
            collector = PolarH10Collector(args.url)
            collector.stream()
            
        elif args.mode == 'all':
            print("🔗 Starting all collectors in parallel...")
            threads = []
            
            # Muse via Mind Monitor
            mm = MindMonitorCollector(args.url, args.osc_port)
            t1 = threading.Thread(target=mm.stream)
            t1.daemon = True
            threads.append(t1)
            
            # Polar
            polar = PolarH10Collector(args.url)
            t2 = threading.Thread(target=polar.stream)
            t2.daemon = True
            threads.append(t2)
            
            for t in threads:
                t.start()
            
            # Keep main thread alive
            while True:
                time.sleep(1)
                
    except KeyboardInterrupt:
        print("\n\n👋 Collector stopped. Data saved to Replit database!")


if __name__ == "__main__":
    main()

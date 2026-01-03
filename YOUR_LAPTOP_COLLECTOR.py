#!/usr/bin/env python3
"""
🧠 MOOD AMPLIFIER - Run this on YOUR LAPTOP!
=============================================

This streams your Muse 2 EEG + Polar H10 HRV to the Replit dashboard.

SETUP:
1. Save this file to your laptop
2. Install: pip install bleak requests numpy
3. Make sure Muse 2 is on your head & Polar H10 strap is wet + on
4. Run: python YOUR_LAPTOP_COLLECTOR.py

Author: BlissGene Therapeutics
"""

import asyncio
import threading
import time
import requests
import numpy as np
from datetime import datetime
from collections import deque

# ========== CONFIGURATION ==========
# UPDATE THIS URL if needed (get from your Replit webview URL)
REPLIT_URL = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"

SESSION_ID = f"live_session_{datetime.now().strftime('%Y%m%d_%H%M%S')}"

print("=" * 60)
print("🧠 MOOD AMPLIFIER - Real-Time Biometric Streaming")
print("=" * 60)
print(f"Session: {SESSION_ID}")
print(f"Streaming to: {REPLIT_URL}")
print()


# ========== POLAR H10 COLLECTOR ==========
class PolarH10Collector:
    """Stream heart rate + HRV from Polar H10"""
    
    HR_UUID = "00002a37-0000-1000-8000-00805f9b34fb"
    
    def __init__(self):
        self.running = False
        self.latest_hr = 0
        self.rr_buffer = deque(maxlen=120)
        self.address = None
    
    async def find_device(self):
        """Scan for Polar H10"""
        from bleak import BleakScanner
        
        print("🔍 Scanning for Polar H10...")
        devices = await BleakScanner.discover(timeout=15)
        
        for device in devices:
            if device.name and "Polar" in device.name:
                print(f"✅ Found: {device.name} ({device.address})")
                return device.address
        
        print("❌ Polar H10 not found! Make sure it's paired and the strap is wet.")
        return None
    
    def compute_hrv(self):
        """Calculate RMSSD from RR intervals"""
        if len(self.rr_buffer) < 10:
            return {"rmssd": 0, "coherence": 0}
        
        rr = np.array(list(self.rr_buffer))
        diffs = np.diff(rr)
        rmssd = np.sqrt(np.mean(diffs ** 2))
        
        # Simple coherence (stability)
        hr_values = 60000 / rr
        stability = 1.0 - min(1.0, np.std(hr_values[-10:]) / 10)
        coherence = (min(1.0, rmssd / 80) * 0.5) + (stability * 0.5)
        
        return {"rmssd": float(rmssd), "coherence": float(coherence)}
    
    async def stream(self):
        """Connect and stream heart data"""
        from bleak import BleakClient
        
        self.address = await self.find_device()
        if not self.address:
            return
        
        self.running = True
        
        async with BleakClient(self.address) as client:
            print(f"\n💓 Connected to Polar H10!")
            print(f"📡 Streaming to {REPLIT_URL}/api/polar/upload")
            print("   Press Ctrl+C to stop\n")
            
            def callback(sender, data):
                flags = data[0]
                
                if flags & 0x01:
                    hr = int.from_bytes(data[1:3], 'little')
                    rr_offset = 3
                else:
                    hr = data[1]
                    rr_offset = 2
                
                self.latest_hr = hr
                
                # Extract RR intervals
                rr_intervals = []
                if len(data) > rr_offset:
                    while rr_offset + 1 < len(data):
                        rr = int.from_bytes(data[rr_offset:rr_offset+2], 'little')
                        rr_intervals.append(rr)
                        self.rr_buffer.append(rr)
                        rr_offset += 2
                
                hrv = self.compute_hrv()
                
                payload = {
                    "timestamp": datetime.now().isoformat(),
                    "heart_rate": hr,
                    "rr_interval": rr_intervals[0] if rr_intervals else None,
                    "rr_intervals": rr_intervals,
                    "hrv": hrv,
                    "coherence": hrv.get('coherence'),
                    "session_id": SESSION_ID,
                    "source": "polar_ble_live",
                    "device_id": self.address
                }
                
                try:
                    resp = requests.post(
                        f"{REPLIT_URL}/api/polar/upload",
                        json=payload,
                        timeout=5
                    )
                    rmssd = hrv.get('rmssd', 0)
                    coh = hrv.get('coherence', 0)
                    if resp.status_code == 201:
                        print(f"💓 HR={hr} bpm | RMSSD={rmssd:.1f}ms | Coherence={coh:.2f}")
                    else:
                        print(f"⚠ Upload error: {resp.status_code}")
                except Exception as e:
                    print(f"⚠ Network: {e}")
            
            await client.start_notify(self.HR_UUID, callback)
            
            while self.running:
                await asyncio.sleep(1)
            
            await client.stop_notify(self.HR_UUID)


# ========== MUSE 2 COLLECTOR ==========
class Muse2Collector:
    """Stream EEG from Muse 2"""
    
    SERVICE_UUID = "0000fe8d-0000-1000-8000-00805f9b34fb"
    EEG_TP9 = "273e0003-4c4d-454d-96be-f03bac821358"
    EEG_AF7 = "273e0004-4c4d-454d-96be-f03bac821358"
    EEG_AF8 = "273e0005-4c4d-454d-96be-f03bac821358"
    EEG_TP10 = "273e0006-4c4d-454d-96be-f03bac821358"
    
    def __init__(self):
        self.running = False
        self.address = None
        self.samples = {
            'TP9': deque(maxlen=1280),
            'AF7': deque(maxlen=1280),
            'AF8': deque(maxlen=1280),
            'TP10': deque(maxlen=1280)
        }
        self.sample_count = 0
    
    async def find_device(self):
        """Scan for Muse 2"""
        from bleak import BleakScanner
        
        print("🔍 Scanning for Muse 2...")
        devices = await BleakScanner.discover(timeout=15)
        
        for device in devices:
            if device.name and "Muse" in device.name:
                print(f"✅ Found: {device.name} ({device.address})")
                return device.address
        
        print("❌ Muse 2 not found! Make sure it's powered on and paired.")
        return None
    
    def make_handler(self, channel_name):
        """Create notification handler for EEG channel"""
        import struct
        
        def handler(sender, data):
            try:
                for i in range(0, len(data), 2):
                    if i + 1 < len(data):
                        raw = struct.unpack('>h', data[i:i+2])[0]
                        voltage = raw * 0.48828125
                        self.samples[channel_name].append(voltage)
                
                self.sample_count += len(data) // 2
            except:
                pass
        
        return handler
    
    def compute_band_powers(self):
        """Compute alpha, beta, theta, gamma, delta powers"""
        if len(self.samples['AF7']) < 256:
            return None
        
        powers = {'alpha': 0, 'beta': 0, 'theta': 0, 'gamma': 0, 'delta': 0}
        
        for channel in ['TP9', 'AF7', 'AF8', 'TP10']:
            data = np.array(list(self.samples[channel])[-256:])
            fft = np.fft.fft(data)
            freqs = np.fft.fftfreq(len(data), 1/256)
            power = np.abs(fft) ** 2
            
            bands = {
                'delta': (1, 4),
                'theta': (4, 8),
                'alpha': (8, 12),
                'beta': (13, 30),
                'gamma': (30, 50)
            }
            
            for band, (low, high) in bands.items():
                idx = np.logical_and(freqs >= low, freqs <= high)
                powers[band] += np.sum(power[idx]) / len(data)
        
        for band in powers:
            powers[band] /= 4
        
        return powers
    
    async def stream(self):
        """Connect and stream EEG data"""
        from bleak import BleakClient
        
        self.address = await self.find_device()
        if not self.address:
            return
        
        self.running = True
        
        async with BleakClient(self.address) as client:
            print(f"\n🧠 Connected to Muse 2!")
            print(f"📡 Streaming to {REPLIT_URL}/api/muse/upload")
            print("   Press Ctrl+C to stop\n")
            
            channels = [
                ('TP9', self.EEG_TP9),
                ('AF7', self.EEG_AF7),
                ('AF8', self.EEG_AF8),
                ('TP10', self.EEG_TP10)
            ]
            
            for name, uuid in channels:
                await client.start_notify(uuid, self.make_handler(name))
                print(f"   ✓ Subscribed to {name}")
            
            last_send = 0
            
            while self.running:
                await asyncio.sleep(0.1)
                
                if self.sample_count - last_send >= 256:
                    powers = self.compute_band_powers()
                    
                    if powers:
                        payload = {
                            "timestamp": datetime.now().isoformat(),
                            "raw": {
                                "tp9": list(self.samples['TP9'])[-1] if self.samples['TP9'] else 0,
                                "af7": list(self.samples['AF7'])[-1] if self.samples['AF7'] else 0,
                                "af8": list(self.samples['AF8'])[-1] if self.samples['AF8'] else 0,
                                "tp10": list(self.samples['TP10'])[-1] if self.samples['TP10'] else 0
                            },
                            "bands": powers,
                            "session_id": SESSION_ID,
                            "source": "muse_ble_live",
                            "device_id": self.address
                        }
                        
                        try:
                            resp = requests.post(
                                f"{REPLIT_URL}/api/muse/upload",
                                json=payload,
                                timeout=5
                            )
                            alpha = powers.get('alpha', 0)
                            beta = powers.get('beta', 0)
                            if resp.status_code == 201:
                                print(f"🧠 Alpha={alpha:.2f} | Beta={beta:.2f} | Theta={powers.get('theta',0):.2f}")
                            else:
                                print(f"⚠ Upload error: {resp.status_code}")
                        except Exception as e:
                            print(f"⚠ Network: {e}")
                    
                    last_send = self.sample_count
            
            for name, uuid in channels:
                await client.stop_notify(uuid)


# ========== MAIN ==========
async def run_polar():
    polar = PolarH10Collector()
    await polar.stream()

async def run_muse():
    muse = Muse2Collector()
    await muse.stream()

async def run_both():
    """Run both collectors simultaneously"""
    print("\n🚀 Starting BOTH Muse 2 + Polar H10 collectors...\n")
    
    polar = PolarH10Collector()
    muse = Muse2Collector()
    
    polar_task = asyncio.create_task(polar.stream())
    muse_task = asyncio.create_task(muse.stream())
    
    try:
        await asyncio.gather(polar_task, muse_task)
    except asyncio.CancelledError:
        polar.running = False
        muse.running = False


if __name__ == "__main__":
    import sys
    
    print("\n📋 SELECT MODE:")
    print("   1. Polar H10 only (heart rate + HRV)")
    print("   2. Muse 2 only (EEG brainwaves)")
    print("   3. BOTH devices (recommended!)")
    print()
    
    try:
        from bleak import BleakScanner
    except ImportError:
        print("❌ Missing dependency! Run:")
        print("   pip install bleak requests numpy")
        sys.exit(1)
    
    choice = input("Enter 1, 2, or 3 (default=3): ").strip() or "3"
    
    try:
        if choice == "1":
            print("\n💓 Starting Polar H10 only...")
            asyncio.run(run_polar())
        elif choice == "2":
            print("\n🧠 Starting Muse 2 only...")
            asyncio.run(run_muse())
        else:
            print("\n🔥 Starting BOTH devices...")
            asyncio.run(run_both())
    
    except KeyboardInterrupt:
        print("\n\n👋 Streaming stopped. Go check your Replit dashboard!")
    except Exception as e:
        print(f"\n❌ Error: {e}")
        print("\nTroubleshooting:")
        print("  - Make sure Muse 2 headband is powered ON")
        print("  - Make sure Polar H10 strap is WET and on your chest")
        print("  - Make sure both devices are paired to your laptop via Bluetooth")
        print("  - Try: pip install --upgrade bleak")

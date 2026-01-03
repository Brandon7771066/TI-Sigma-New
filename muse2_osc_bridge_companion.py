"""
Muse 2 OSC Bridge - Companion App
==================================

Run this script on a device with Bluetooth LE access (phone/laptop) to:
1. Connect to Muse 2 via Bluetooth
2. Forward EEG data to Streamlit app via OSC (Open Sound Control)

SETUP INSTRUCTIONS:
===================

1. Install dependencies:
   ```
   pip install bleak python-osc muselsl
   ```

2. Find your Replit app URL (e.g., https://your-app.replit.app)

3. Run this script:
   ```
   python muse2_osc_bridge_companion.py --target-ip <REPLIT_IP> --target-port 5005
   ```

4. Put on your Muse 2 headband

5. Script will auto-discover and connect, then stream to your Replit app!

ARCHITECTURE:
=============
Phone/Laptop (this script) ---OSC---> Replit Streamlit App
     |
     +--> Muse 2 (BLE connection)

Author: Brandon Emerick
Date: November 22, 2025
"""

import argparse
import asyncio
import time
from typing import Optional
from datetime import datetime

try:
    from bleak import BleakClient, BleakScanner
    from pythonosc import udp_client
    DEPS_AVAILABLE = True
except ImportError:
    print("❌ Dependencies not installed!")
    print("Install: pip install bleak python-osc")
    DEPS_AVAILABLE = False
    exit(1)


class Muse2OSCBridge:
    """
    Bridge between Muse 2 (BLE) and Streamlit app (OSC).
    """
    
    # Muse 2 Bluetooth UUIDs
    MUSE_SERVICE_UUID = "0000fe8d-0000-1000-8000-00805f9b34fb"
    EEG_TP9_UUID  = "00000273-0000-1000-8000-00805f9b34fb"
    EEG_AF7_UUID  = "00000274-0000-1000-8000-00805f9b34fb"
    EEG_AF8_UUID  = "00000275-0000-1000-8000-00805f9b34fb"
    EEG_TP10_UUID = "00000276-0000-1000-8000-00805f9b34fb"
    
    def __init__(self, target_ip: str, target_port: int = 5005):
        """
        Initialize OSC bridge.
        
        Args:
            target_ip: IP address of Replit app
            target_port: OSC port (default 5005)
        """
        self.target_ip = target_ip
        self.target_port = target_port
        self.client: Optional[BleakClient] = None
        self.osc_client = udp_client.SimpleUDPClient(target_ip, target_port)
        
        # EEG data buffers
        self.eeg_data = {
            'TP9': [],
            'AF7': [],
            'AF8': [],
            'TP10': []
        }
        
        self.packets_sent = 0
        self.start_time = datetime.now()
    
    async def discover_muse(self) -> Optional[str]:
        """
        Discover Muse 2 headband.
        
        Returns:
            MAC address of Muse 2, or None
        """
        print("🔍 Scanning for Muse 2 headband...")
        
        devices = await BleakScanner.discover(timeout=10.0)
        
        for device in devices:
            if device.name and "Muse" in device.name:
                print(f"✅ Found Muse device: {device.name} ({device.address})")
                return device.address
        
        print("❌ No Muse device found")
        return None
    
    async def connect_and_stream(self, device_address: Optional[str] = None):
        """
        Connect to Muse 2 and start streaming to OSC.
        """
        try:
            # Discover if address not provided
            if not device_address:
                device_address = await self.discover_muse()
                if not device_address:
                    print("❌ Failed to find Muse 2")
                    return
            
            # Connect
            print(f"🔗 Connecting to Muse 2: {device_address}")
            self.client = BleakClient(device_address)
            await self.client.connect(timeout=20.0)
            
            if not self.client.is_connected:
                print("❌ Connection failed")
                return
            
            print(f"✅ Connected to Muse 2!")
            print(f"📡 Forwarding EEG data to {self.target_ip}:{self.target_port}")
            
            # Start EEG notifications
            await self.client.start_notify(self.EEG_TP9_UUID, lambda s, d: self._eeg_callback('TP9', d))
            await self.client.start_notify(self.EEG_AF7_UUID, lambda s, d: self._eeg_callback('AF7', d))
            await self.client.start_notify(self.EEG_AF8_UUID, lambda s, d: self._eeg_callback('AF8', d))
            await self.client.start_notify(self.EEG_TP10_UUID, lambda s, d: self._eeg_callback('TP10', d))
            
            print("🧠 EEG streaming started!")
            
            # Keep connection alive and show stats
            while self.client.is_connected:
                await asyncio.sleep(5)
                elapsed = (datetime.now() - self.start_time).total_seconds()
                rate = self.packets_sent / elapsed if elapsed > 0 else 0
                print(f"📊 Stats: {self.packets_sent} packets sent ({rate:.1f} pkt/s)")
            
        except Exception as e:
            print(f"❌ Error: {e}")
        
        finally:
            if self.client and self.client.is_connected:
                await self.client.disconnect()
                print("👋 Disconnected from Muse 2")
    
    def _eeg_callback(self, channel: str, data: bytearray):
        """
        Callback for EEG data.
        
        Muse 2 sends EEG as 12-bit samples packed in bytes.
        """
        try:
            # Parse EEG samples (12-bit values)
            # Format: [samples_count, sample1_high, sample1_low, sample2_high, sample2_low, ...]
            if len(data) < 3:
                return
            
            # Number of samples in this packet
            num_samples = data[0]
            
            samples = []
            for i in range(num_samples):
                # 12-bit sample split across 2 bytes
                idx = 1 + (i * 2)
                if idx + 1 < len(data):
                    # Combine high and low bytes
                    high = data[idx]
                    low = data[idx + 1]
                    value = (high << 8) | low
                    
                    # Convert to signed value (12-bit)
                    if value > 2047:
                        value -= 4096
                    
                    samples.append(float(value))
            
            # Send to Replit app via OSC
            for sample in samples:
                osc_address = f"/muse/eeg/{channel}"
                self.osc_client.send_message(osc_address, sample)
                self.packets_sent += 1
            
            # Buffer locally
            self.eeg_data[channel].extend(samples)
            
            # Keep buffer size manageable
            if len(self.eeg_data[channel]) > 10000:
                self.eeg_data[channel] = self.eeg_data[channel][-10000:]
            
        except Exception as e:
            print(f"❌ Error parsing EEG data: {e}")


def main():
    parser = argparse.ArgumentParser(
        description="Muse 2 OSC Bridge - Forward EEG data to Replit app"
    )
    parser.add_argument(
        "--target-ip",
        required=True,
        help="IP address of Replit Streamlit app"
    )
    parser.add_argument(
        "--target-port",
        type=int,
        default=5005,
        help="OSC port (default: 5005)"
    )
    parser.add_argument(
        "--device-address",
        default=None,
        help="Muse 2 MAC address (auto-discover if not provided)"
    )
    
    args = parser.parse_args()
    
    print("=" * 60)
    print("  Muse 2 OSC Bridge - Companion App")
    print("=" * 60)
    print(f"Target: {args.target_ip}:{args.target_port}")
    print()
    
    # Create bridge
    bridge = Muse2OSCBridge(args.target_ip, args.target_port)
    
    # Run async connection
    try:
        asyncio.run(bridge.connect_and_stream(args.device_address))
    except KeyboardInterrupt:
        print("\n👋 Shutting down...")


if __name__ == "__main__":
    if not DEPS_AVAILABLE:
        exit(1)
    main()

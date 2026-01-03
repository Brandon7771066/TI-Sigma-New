"""
Muse 2 EEG Headband Integration via Bluetooth LE
=================================================

Real-time EEG data streaming from Muse 2 headband using bleak (BLE library).

Features:
- Automatic device discovery and connection
- Real-time 4-channel EEG streaming (TP9, AF7, AF8, TP10)
- Battery monitoring
- Connection status tracking
- Data buffering for authentication

Author: Brandon Emerick
Date: November 21, 2025
Framework: Transcendent Intelligence (TI)
"""

import asyncio
from bleak import BleakClient, BleakScanner
import numpy as np
from typing import Dict, List, Optional, Callable
from datetime import datetime
import struct
from collections import deque

# Muse 2 BLE UUIDs (official Muse SDK)
MUSE_SERVICE_UUID = "0000fe8d-0000-1000-8000-00805f9b34fb"

# EEG Channel UUIDs
EEG_TP9_UUID = "273e0003-4c4d-454d-96be-f03bac821358"  # Left temporal
EEG_AF7_UUID = "273e0004-4c4d-454d-96be-f03bac821358"  # Left frontal
EEG_AF8_UUID = "273e0005-4c4d-454d-96be-f03bac821358"  # Right frontal
EEG_TP10_UUID = "273e0006-4c4d-454d-96be-f03bac821358"  # Right temporal

# Other UUIDs
BATTERY_UUID = "00002a19-0000-1000-8000-00805f9b34fb"
GYROSCOPE_UUID = "273e0009-4c4d-454d-96be-f03bac821358"
ACCELEROMETER_UUID = "273e000a-4c4d-454d-96be-f03bac821358"


class Muse2Device:
    """
    Muse 2 EEG Headband Interface
    
    Connects to Muse 2 via Bluetooth LE and streams real-time EEG data.
    """
    
    def __init__(self, device_address: Optional[str] = None):
        """
        Initialize Muse 2 device connection
        
        Args:
            device_address: MAC address of Muse 2 (None for auto-discovery)
        """
        self.device_address = device_address
        self.client: Optional[BleakClient] = None
        self.is_connected = False
        self.is_streaming = False
        
        # EEG data buffers (256 Hz sampling rate)
        self.eeg_buffers: Dict[str, deque] = {
            'TP9': deque(maxlen=5120),  # 20 seconds of data
            'AF7': deque(maxlen=5120),
            'AF8': deque(maxlen=5120),
            'TP10': deque(maxlen=5120)
        }
        
        # Metadata
        self.battery_level: Optional[int] = None
        self.connection_time: Optional[datetime] = None
        self.last_data_time: Optional[datetime] = None
        
        # Callback for real-time data
        self.data_callback: Optional[Callable] = None
    
    async def discover_muse2(self, timeout: float = 10.0) -> Optional[str]:
        """
        Discover Muse 2 headband via Bluetooth LE
        
        Args:
            timeout: Discovery timeout in seconds
        
        Returns:
            Device address if found, None otherwise
        """
        print("🔍 Scanning for Muse 2 headband...")
        
        devices = await BleakScanner.discover(timeout=timeout)
        
        for device in devices:
            # Muse 2 devices have "Muse" in their name
            if device.name and "Muse" in device.name:
                print(f"✅ Found Muse 2: {device.name} ({device.address})")
                return device.address
        
        print("❌ No Muse 2 devices found")
        return None
    
    async def connect(self) -> bool:
        """
        Connect to Muse 2 device
        
        Returns:
            True if connected successfully
        """
        try:
            # Auto-discover if no address provided
            if not self.device_address:
                self.device_address = await self.discover_muse2()
                if not self.device_address:
                    return False
            
            # Connect to device
            print(f"🔗 Connecting to Muse 2 at {self.device_address}...")
            self.client = BleakClient(self.device_address)
            await self.client.connect()
            
            self.is_connected = True
            self.connection_time = datetime.now()
            
            print("✅ Connected to Muse 2!")
            
            # Read battery level
            await self._read_battery()
            
            return True
            
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            self.is_connected = False
            return False
    
    async def disconnect(self):
        """Disconnect from Muse 2"""
        if self.client and self.is_connected:
            await self.stop_streaming()
            await self.client.disconnect()
            self.is_connected = False
            print("🔌 Disconnected from Muse 2")
    
    async def _read_battery(self):
        """Read battery level from Muse 2"""
        try:
            battery_data = await self.client.read_gatt_char(BATTERY_UUID)
            self.battery_level = int.from_bytes(battery_data, 'little')
            print(f"🔋 Battery: {self.battery_level}%")
        except Exception as e:
            print(f"⚠️ Could not read battery: {e}")
    
    def _eeg_notification_handler(self, channel_name: str):
        """
        Create notification handler for EEG channel
        
        Args:
            channel_name: Channel name (TP9, AF7, AF8, TP10)
        
        Returns:
            Notification handler function
        """
        def handler(sender, data: bytearray):
            """Handle incoming EEG data"""
            # Muse 2 sends 12 samples per packet (256 Hz / ~21.3 packets/sec)
            # Each sample is 2 bytes (12-bit resolution, big-endian)
            try:
                samples = []
                for i in range(0, len(data), 2):
                    if i + 1 < len(data):
                        # Convert 12-bit big-endian to voltage
                        raw_value = struct.unpack('>h', data[i:i+2])[0]
                        # Scale to microvolts (Muse 2 specific scaling)
                        voltage = raw_value * 0.48828125
                        samples.append(voltage)
                
                # Add to buffer
                self.eeg_buffers[channel_name].extend(samples)
                self.last_data_time = datetime.now()
                
                # Call callback if registered
                if self.data_callback:
                    self.data_callback(channel_name, samples)
                    
            except Exception as e:
                print(f"❌ Error parsing EEG data from {channel_name}: {e}")
        
        return handler
    
    async def start_streaming(self, callback: Optional[Callable] = None):
        """
        Start streaming EEG data from all channels
        
        Args:
            callback: Optional callback function(channel_name, samples)
        """
        if not self.is_connected or not self.client:
            print("❌ Not connected to Muse 2")
            return False
        
        try:
            self.data_callback = callback
            
            # Subscribe to all EEG channels
            channels = [
                ('TP9', EEG_TP9_UUID),
                ('AF7', EEG_AF7_UUID),
                ('AF8', EEG_AF8_UUID),
                ('TP10', EEG_TP10_UUID)
            ]
            
            for channel_name, uuid in channels:
                handler = self._eeg_notification_handler(channel_name)
                await self.client.start_notify(uuid, handler)
                print(f"✅ Streaming {channel_name}")
            
            self.is_streaming = True
            print("🧠 EEG streaming started!")
            return True
            
        except Exception as e:
            print(f"❌ Failed to start streaming: {e}")
            return False
    
    async def stop_streaming(self):
        """Stop streaming EEG data"""
        if not self.is_streaming or not self.client:
            return
        
        try:
            # Unsubscribe from all channels
            channels_uuids = [EEG_TP9_UUID, EEG_AF7_UUID, EEG_AF8_UUID, EEG_TP10_UUID]
            for uuid in channels_uuids:
                await self.client.stop_notify(uuid)
            
            self.is_streaming = False
            print("⏹️ EEG streaming stopped")
            
        except Exception as e:
            print(f"⚠️ Error stopping streaming: {e}")
    
    def get_latest_data(self, duration_seconds: float = 5.0) -> Dict[str, np.ndarray]:
        """
        Get latest EEG data from all channels
        
        Args:
            duration_seconds: Duration of data to retrieve
        
        Returns:
            Dict of channel_name -> numpy array of voltages
        """
        sample_rate = 256  # Hz
        num_samples = int(duration_seconds * sample_rate)
        
        eeg_data = {}
        for channel_name, buffer in self.eeg_buffers.items():
            # Get last N samples
            samples = list(buffer)[-num_samples:]
            eeg_data[channel_name] = np.array(samples)
        
        return eeg_data
    
    def get_status(self) -> Dict[str, any]:
        """Get current device status"""
        return {
            'is_connected': self.is_connected,
            'is_streaming': self.is_streaming,
            'battery_level': self.battery_level,
            'connection_time': self.connection_time,
            'last_data_time': self.last_data_time,
            'buffer_sizes': {
                name: len(buffer) 
                for name, buffer in self.eeg_buffers.items()
            }
        }


# Synchronous wrapper for Streamlit
class Muse2Manager:
    """
    Synchronous manager for Muse 2 integration with Streamlit
    
    Handles async/await complexity behind the scenes
    """
    
    def __init__(self):
        self.device: Optional[Muse2Device] = None
        self.loop: Optional[asyncio.AbstractEventLoop] = None
    
    def connect(self, device_address: Optional[str] = None) -> bool:
        """Connect to Muse 2 (synchronous)"""
        self.device = Muse2Device(device_address)
        
        # Run async connect in new event loop
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        success = loop.run_until_complete(self.device.connect())
        
        if success:
            # Start streaming
            loop.run_until_complete(self.device.start_streaming())
        
        self.loop = loop
        return success
    
    def disconnect(self):
        """Disconnect from Muse 2"""
        if self.device and self.loop:
            self.loop.run_until_complete(self.device.disconnect())
            self.loop.close()
    
    def get_eeg_data(self, duration_seconds: float = 5.0) -> Dict[str, np.ndarray]:
        """Get latest EEG data"""
        if not self.device:
            raise RuntimeError("Not connected to Muse 2")
        return self.device.get_latest_data(duration_seconds)
    
    def get_status(self) -> Dict[str, any]:
        """Get device status"""
        if not self.device:
            return {'is_connected': False}
        return self.device.get_status()


# Example usage
if __name__ == "__main__":
    async def main():
        # Create Muse 2 device
        muse = Muse2Device()
        
        # Connect
        connected = await muse.connect()
        if not connected:
            print("Failed to connect")
            return
        
        # Start streaming
        await muse.start_streaming()
        
        # Stream for 10 seconds
        print("📊 Collecting EEG data for 10 seconds...")
        await asyncio.sleep(10)
        
        # Get data
        eeg_data = muse.get_latest_data(duration_seconds=5.0)
        
        print("\n📈 EEG Data Summary:")
        for channel, data in eeg_data.items():
            print(f"  {channel}: {len(data)} samples, mean={np.mean(data):.2f}µV, std={np.std(data):.2f}µV")
        
        # Stop and disconnect
        await muse.stop_streaming()
        await muse.disconnect()
        
        print("\n✅ Muse 2 integration test complete!")
    
    # Run test
    asyncio.run(main())

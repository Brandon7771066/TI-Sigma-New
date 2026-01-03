"""
🧠 fNIRS Manager - Mendi Headband Integration
Real-time prefrontal cortex blood oxygenation monitoring via BLE

Integrates with TI Framework for:
- GILE alignment tracking
- Δτ_i (temporal dissonance) measurement
- Network access signature detection
- Consciousness field coherence

Author: Brandon Emerick
Date: November 22, 2025
Framework: Transcendent Intelligence (TI)
"""

import asyncio
import numpy as np
from typing import Optional, Dict, List, Callable
from datetime import datetime
from dataclasses import dataclass
import threading

try:
    from bleak import BleakScanner, BleakClient
    BLEAK_AVAILABLE = True
except ImportError:
    BLEAK_AVAILABLE = False
    print("⚠️ bleak not available - fNIRS will run in DEMO mode")


@dataclass
class fNIRSSnapshot:
    """Single fNIRS measurement snapshot"""
    timestamp: datetime
    hbo2: float  # Oxygenated hemoglobin (μM)
    hbr: float   # Deoxygenated hemoglobin (μM)
    total_hb: float  # Total hemoglobin
    oxygenation_percent: float  # % oxygenation (0-100)
    activation_level: float  # Activation vs baseline (-3 to +3)
    coherence: float  # Inter-hemisphere coherence (0-1)
    gile_alignment: float  # GILE-based alignment score (-2.5 to +2.5)
    delta_tau_i: float  # Temporal dissonance (0 = perfect coherence)
    

class MendifNIRSManager:
    """
    Manages Mendi fNIRS headband connection and data processing
    
    Features:
    - BLE connectivity with auto-reconnect
    - Real-time HbO2/HbR monitoring
    - Baseline correction
    - GILE alignment calculation
    - Δτ_i (temporal dissonance) tracking
    - Network access signature detection
    """
    
    # Mendi BLE UUIDs (to be determined from reverse engineering or Mendi support)
    # These are placeholder UUIDs - actual values need verification
    DEVICE_NAME_PREFIX = "Mendi"
    DATA_SERVICE_UUID = "6e400001-b5a3-f393-e0a9-e50e24dcca9e"
    DATA_CHARACTERISTIC_UUID = "6e400002-b5a3-f393-e0a9-e50e24dcca9e"
    BATTERY_CHARACTERISTIC_UUID = "00002a19-0000-1000-8000-00805f9b34fb"
    
    def __init__(self, demo_mode: bool = True):
        """
        Initialize fNIRS manager
        
        Args:
            demo_mode: If True, generates synthetic data instead of real BLE
        """
        self.demo_mode = demo_mode or not BLEAK_AVAILABLE
        self.connected = False
        self.device_address = None
        self.client = None
        self.battery_level = 0
        
        # Data buffers
        self.hbo2_buffer = []
        self.hbr_buffer = []
        self.timestamps = []
        
        # Baseline values (set during calibration)
        self.baseline_hbo2 = 0.0
        self.baseline_hbr = 0.0
        self.baseline_calibrated = False
        
        # Session tracking
        self.session_active = False
        self.session_start = None
        
        # Demo data generation
        self.demo_time = 0.0
        
    async def scan_devices(self) -> List[str]:
        """Scan for Mendi devices"""
        if self.demo_mode:
            return ["DEMO-Mendi-A1B2C3"]
        
        devices = await BleakScanner.discover()
        mendi_devices = []
        
        for device in devices:
            if device.name and self.DEVICE_NAME_PREFIX.lower() in device.name.lower():
                mendi_devices.append(f"{device.name} ({device.address})")
        
        return mendi_devices
    
    async def connect(self, address: Optional[str] = None) -> bool:
        """
        Connect to Mendi device
        
        Args:
            address: BLE device address (None = auto-discover)
            
        Returns:
            True if connection successful
        """
        if self.demo_mode:
            self.connected = True
            self.battery_level = 87
            return True
        
        try:
            # Auto-discover if no address provided
            if address is None:
                devices = await BleakScanner.discover()
                for device in devices:
                    if device.name and self.DEVICE_NAME_PREFIX.lower() in device.name.lower():
                        address = device.address
                        break
                
                if address is None:
                    print("❌ No Mendi device found")
                    return False
            
            # Connect to device
            self.client = BleakClient(address)
            await self.client.connect()
            
            if self.client.is_connected:
                self.connected = True
                self.device_address = address
                
                # Read battery level
                try:
                    battery_data = await self.client.read_gatt_char(self.BATTERY_CHARACTERISTIC_UUID)
                    self.battery_level = int(battery_data[0])
                except Exception as e:
                    print(f"⚠️ Could not read battery: {e}")
                    self.battery_level = 0
                
                # Start notifications for fNIRS data
                await self.client.start_notify(
                    self.DATA_CHARACTERISTIC_UUID,
                    self._data_callback
                )
                
                print(f"✅ Connected to Mendi at {address}")
                return True
            
            return False
            
        except Exception as e:
            print(f"❌ Connection failed: {e}")
            self.connected = False
            return False
    
    async def disconnect(self):
        """Disconnect from Mendi device"""
        if self.demo_mode:
            self.connected = False
            return
        
        if self.client and self.client.is_connected:
            await self.client.disconnect()
            self.connected = False
            print("🔌 Disconnected from Mendi")
    
    def _data_callback(self, sender, data: bytearray):
        """
        Callback for incoming fNIRS data
        
        Data format (to be determined from Mendi protocol):
        - Typically: timestamp, HbO2, HbR values
        """
        try:
            # Parse data (placeholder - actual format TBD)
            # Expected: [timestamp_ms, hbo2_value, hbr_value]
            if len(data) >= 12:  # Assuming 3 floats (4 bytes each)
                timestamp = int.from_bytes(data[0:4], 'little')
                hbo2 = float(int.from_bytes(data[4:8], 'little')) / 1000.0
                hbr = float(int.from_bytes(data[8:12], 'little')) / 1000.0
                
                self._process_sample(hbo2, hbr)
        except Exception as e:
            print(f"⚠️ Error parsing fNIRS data: {e}")
    
    def _process_sample(self, hbo2: float, hbr: float):
        """Process a single fNIRS sample"""
        self.hbo2_buffer.append(hbo2)
        self.hbr_buffer.append(hbr)
        self.timestamps.append(datetime.now())
        
        # Keep only last 300 samples (5 minutes at 1 Hz)
        max_samples = 300
        if len(self.hbo2_buffer) > max_samples:
            self.hbo2_buffer = self.hbo2_buffer[-max_samples:]
            self.hbr_buffer = self.hbr_buffer[-max_samples:]
            self.timestamps = self.timestamps[-max_samples:]
    
    def calibrate_baseline(self, duration_seconds: int = 30):
        """
        Calibrate baseline from current readings
        
        Args:
            duration_seconds: How long to collect baseline data
        """
        if len(self.hbo2_buffer) < 10:
            print("⚠️ Not enough data for calibration")
            return False
        
        # Use last N samples for baseline
        n_samples = min(duration_seconds, len(self.hbo2_buffer))
        
        self.baseline_hbo2 = np.mean(self.hbo2_buffer[-n_samples:])
        self.baseline_hbr = np.mean(self.hbr_buffer[-n_samples:])
        self.baseline_calibrated = True
        
        print(f"✅ Baseline calibrated: HbO2={self.baseline_hbo2:.2f}, HbR={self.baseline_hbr:.2f}")
        return True
    
    def get_current_snapshot(self) -> Optional[fNIRSSnapshot]:
        """
        Get current fNIRS state snapshot
        
        Returns:
            fNIRSSnapshot object or None if not connected
        """
        if not self.connected:
            return None
        
        # Demo mode: generate synthetic data
        if self.demo_mode:
            self.demo_time += 0.1
            
            # Synthetic oscillation with upward trend (simulating training effect)
            base_hbo2 = 45.0 + 3.0 * np.sin(self.demo_time * 0.5) + 0.1 * self.demo_time
            base_hbr = 25.0 - 1.5 * np.sin(self.demo_time * 0.5)
            
            # Add noise
            hbo2 = base_hbo2 + np.random.normal(0, 0.5)
            hbr = base_hbr + np.random.normal(0, 0.3)
            
            # Calculate metrics
            total_hb = hbo2 + hbr
            oxygenation_percent = (hbo2 / total_hb) * 100 if total_hb > 0 else 50.0
            
            # Activation level (vs baseline)
            if not self.baseline_calibrated:
                self.baseline_hbo2 = 45.0
                self.baseline_hbr = 25.0
                self.baseline_calibrated = True
            
            activation_level = (hbo2 - self.baseline_hbo2) / 10.0  # Normalize to -3 to +3
            
            # Coherence (simulated)
            coherence = 0.65 + 0.2 * np.sin(self.demo_time * 0.3)
            coherence = max(0.0, min(1.0, coherence))
            
            # GILE alignment (high oxygenation = high GILE)
            gile_alignment = (oxygenation_percent - 60.0) / 20.0  # Map 60-80% to -1 to +1
            gile_alignment = max(-2.5, min(2.5, gile_alignment))
            
            # Δτ_i (temporal dissonance - low when coherent)
            delta_tau_i = (1.0 - coherence) * 2.0  # 0 = perfect coherence, 2 = max dissonance
            
            return fNIRSSnapshot(
                timestamp=datetime.now(),
                hbo2=hbo2,
                hbr=hbr,
                total_hb=total_hb,
                oxygenation_percent=oxygenation_percent,
                activation_level=activation_level,
                coherence=coherence,
                gile_alignment=gile_alignment,
                delta_tau_i=delta_tau_i
            )
        
        # Real mode: process actual data
        if len(self.hbo2_buffer) < 1:
            return None
        
        current_hbo2 = self.hbo2_buffer[-1]
        current_hbr = self.hbr_buffer[-1]
        
        total_hb = current_hbo2 + current_hbr
        oxygenation_percent = (current_hbo2 / total_hb) * 100 if total_hb > 0 else 50.0
        
        # Activation level
        if self.baseline_calibrated:
            activation_level = (current_hbo2 - self.baseline_hbo2) / 10.0
        else:
            activation_level = 0.0
        
        # Coherence (calculate from recent variance)
        if len(self.hbo2_buffer) >= 10:
            recent_std = np.std(self.hbo2_buffer[-10:])
            coherence = max(0.0, min(1.0, 1.0 - (recent_std / 10.0)))
        else:
            coherence = 0.5
        
        # GILE alignment
        gile_alignment = (oxygenation_percent - 60.0) / 20.0
        gile_alignment = max(-2.5, min(2.5, gile_alignment))
        
        # Δτ_i
        delta_tau_i = (1.0 - coherence) * 2.0
        
        return fNIRSSnapshot(
            timestamp=datetime.now(),
            hbo2=current_hbo2,
            hbr=current_hbr,
            total_hb=total_hb,
            oxygenation_percent=oxygenation_percent,
            activation_level=activation_level,
            coherence=coherence,
            gile_alignment=gile_alignment,
            delta_tau_i=delta_tau_i
        )
    
    def get_signal_quality(self) -> float:
        """
        Calculate signal quality (0-100%)
        
        Based on:
        - Connection status
        - Data freshness
        - Signal variance
        """
        if not self.connected:
            return 0.0
        
        if self.demo_mode:
            return 92.0  # High quality in demo mode
        
        if len(self.hbo2_buffer) < 5:
            return 30.0  # Low quality with insufficient data
        
        # Check data freshness
        if self.timestamps:
            last_update = (datetime.now() - self.timestamps[-1]).total_seconds()
            if last_update > 5.0:  # No data for 5+ seconds
                return 20.0
        
        # Signal variance check (too much = noisy, too little = frozen)
        recent_std = np.std(self.hbo2_buffer[-10:])
        if recent_std < 0.1:
            quality = 40.0  # Frozen signal
        elif recent_std > 10.0:
            quality = 50.0  # Too noisy
        else:
            quality = 85.0  # Good signal
        
        return quality


# Singleton instance
_fnirs_manager = None

def get_fnirs_manager(demo_mode: bool = True) -> MendifNIRSManager:
    """Get singleton fNIRS manager instance"""
    global _fnirs_manager
    if _fnirs_manager is None:
        _fnirs_manager = MendifNIRSManager(demo_mode=demo_mode)
    return _fnirs_manager

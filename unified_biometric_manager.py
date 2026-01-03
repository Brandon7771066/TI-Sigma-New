"""
Unified Biometric Manager for Mood Amplifier
=============================================

Combines all biometric devices into a single interface:
- Muse 2 EEG (brain activity, LCC)
- Polar H10 (heart rate, HRV, coherence)
- Oura Ring (recovery, sleep, readiness)

Supports DEMO MODE for operation without hardware.

Author: Brandon Emerick
Date: November 21, 2025
Framework: Transcendent Intelligence (TI) + FAAH Protocol
"""

import asyncio
from typing import Dict, Optional, Any, List
from datetime import datetime
import numpy as np
from dataclasses import dataclass, asdict
import streamlit as st

try:
    from muse2_integration import Muse2Device, Muse2Manager
    from polar_h10_real_integration import PolarH10Integration, HeartDataPoint, ConnectionState
    from oura_ring_integration import OuraRingIntegration
    HARDWARE_AVAILABLE = True
except ImportError:
    HARDWARE_AVAILABLE = False
    Muse2Device = None
    Muse2Manager = None
    PolarH10Integration = None
    OuraRingIntegration = None

from biometric_simulator import BiometricSimulator, get_biometric_simulator


@dataclass
class UnifiedBiometricSnapshot:
    """
    Single moment of unified biometric data across all devices
    """
    timestamp: datetime
    
    # EEG (Muse 2)
    eeg_channels: Optional[Dict[str, np.ndarray]] = None  # TP9, AF7, AF8, TP10
    alpha_power: Optional[float] = None
    beta_power: Optional[float] = None
    theta_power: Optional[float] = None
    lcc_coherence: Optional[float] = None  # Limbic-Cortical Coupling
    
    # Heart (Polar H10)
    heart_rate_bpm: Optional[float] = None
    hrv_rmssd: Optional[float] = None
    coherence_score: Optional[float] = None
    rr_intervals: Optional[List[float]] = None
    
    # Recovery (Oura Ring)
    readiness_score: Optional[int] = None
    sleep_score: Optional[int] = None
    body_temp_deviation: Optional[float] = None
    
    # Unified Metrics
    gile_score: Optional[float] = None  # Overall consciousness state
    faah_tier: Optional[int] = None  # FAAH Protocol tier (1-4)
    
    # Device Status
    muse_connected: bool = False
    muse_signal_quality: Optional[float] = None  # 0-100%
    polar_connected: bool = False
    oura_synced: bool = False


class UnifiedBiometricManager:
    """
    Unified manager for all biometric devices
    
    Provides single interface for:
    1. Device connection/disconnection
    2. Real-time data streaming
    3. Unified metrics calculation
    4. FAAH Protocol integration
    5. DEMO MODE for operation without hardware
    """
    
    def __init__(self, demo_mode: bool = True):
        """
        Initialize all device managers
        
        Args:
            demo_mode: If True, use simulator when no hardware connected
        """
        self.demo_mode = demo_mode
        self.simulator: Optional[BiometricSimulator] = None
        
        self.muse: Optional[Any] = None
        self.polar: Optional[Any] = None
        self.oura: Optional[Any] = None
        
        self.muse_connected = False
        self.polar_connected = False
        self.oura_synced = False
        
        self.latest_snapshot: Optional[UnifiedBiometricSnapshot] = None
        self.session_history: List[UnifiedBiometricSnapshot] = []
        
        if self.demo_mode:
            self.simulator = get_biometric_simulator()
    
    def is_demo_mode_active(self) -> bool:
        """Check if currently using simulated data"""
        has_hardware = self.muse_connected or self.polar_connected or self.oura_synced
        return self.demo_mode and not has_hardware
    
    def set_session_phase(self, phase_name: str):
        """Set the current session phase (affects simulator behavior)"""
        if self.simulator:
            self.simulator.set_phase(phase_name)
    
    def start_session(self):
        """Start a new measurement session"""
        if self.simulator:
            self.simulator.start_session()
        self.session_history = []
    
    def connect_muse2(self, device_address: Optional[str] = None) -> bool:
        """
        Connect to Muse 2 headband
        
        Args:
            device_address: MAC address (None for auto-discovery)
        
        Returns:
            True if connected successfully
        """
        try:
            self.muse = Muse2Manager()
            success = self.muse.connect(device_address)
            self.muse_connected = success
            return success
        except Exception as e:
            print(f"❌ Muse 2 connection failed: {e}")
            self.muse_connected = False
            return False
    
    def disconnect_muse2(self):
        """Disconnect from Muse 2"""
        if self.muse:
            self.muse.disconnect()
            self.muse_connected = False
    
    def connect_polar_h10(self, device_id: Optional[str] = None) -> bool:
        """
        Connect to Polar H10 heart monitor
        
        Args:
            device_id: Device ID (None for auto-discovery)
        
        Returns:
            True if connected successfully
        """
        try:
            self.polar = PolarH10Integration(device_id)
            self.polar_connected = False  # Wait for actual connection
            return True  # Initialization succeeded, connection will happen in background
        except Exception as e:
            print(f"❌ Polar H10 initialization failed: {e}")
            self.polar_connected = False
            return False
    
    def start_hr_stream(self) -> bool:
        """
        Start Polar H10 heart rate streaming.
        
        Returns:
            True if stream started successfully
        """
        if not self.polar:
            return False
        
        success = self.polar.start_hr_stream()
        self.polar_connected = success
        return success
    
    def get_polar_state(self) -> str:
        """Get Polar H10 connection state"""
        if not self.polar:
            return "disconnected"
        return self.polar.get_state()
    
    def is_polar_streaming(self) -> bool:
        """Check if Polar is actively streaming data"""
        if not self.polar:
            return False
        return self.polar.is_streaming()
    
    def get_latest_polar_data(self) -> Optional[HeartDataPoint]:
        """
        Get latest Polar H10 heart data.
        
        Returns:
            HeartDataPoint or None
        """
        if not self.polar:
            return None
        return self.polar.get_latest_data()
    
    def sync_oura_ring(self, access_token: Optional[str] = None) -> bool:
        """
        Sync Oura Ring data
        
        Args:
            access_token: Oura Personal Access Token
        
        Returns:
            True if synced successfully
        """
        try:
            self.oura = OuraRingIntegration(access_token)
            # Test connection
            _ = self.oura.get_personal_info()
            self.oura_synced = True
            return True
        except Exception as e:
            print(f"❌ Oura Ring sync failed: {e}")
            self.oura_synced = False
            return False
    
    def get_muse_signal_quality(self) -> float:
        """
        Calculate Muse 2 signal quality percentage
        
        Returns:
            Signal quality (0-100%)
        """
        if not self.muse or not self.muse_connected:
            return 0.0
        
        status = self.muse.get_status()
        
        # Check buffer sizes (4 channels should all have data)
        buffer_sizes = status.get('buffer_sizes', {})
        channels_active = sum(1 for size in buffer_sizes.values() if size > 0)
        
        # Signal quality = (active channels / 4) * 100
        base_quality = (channels_active / 4.0) * 100.0
        
        # Adjust for battery level
        battery = status.get('battery_level', 100)
        if battery and battery < 20:
            base_quality *= 0.8  # Reduce quality if low battery
        
        return min(100.0, base_quality)
    
    def calculate_lcc_coherence(self, eeg_data: Dict[str, np.ndarray]) -> float:
        """
        Calculate Limbic-Cortical Coupling (LCC) coherence
        
        Args:
            eeg_data: Dict of channel_name -> voltage array
        
        Returns:
            LCC coherence (0-1 scale)
        """
        # Simplified LCC: correlation between frontal and temporal channels
        if 'AF7' not in eeg_data or 'TP9' not in eeg_data:
            return 0.0
        
        af7 = eeg_data['AF7']
        tp9 = eeg_data['TP9']
        
        if len(af7) < 10 or len(tp9) < 10:
            return 0.0
        
        # Compute correlation (proxy for LCC)
        min_len = min(len(af7), len(tp9))
        correlation = np.corrcoef(af7[:min_len], tp9[:min_len])[0, 1]
        
        # Convert to 0-1 scale (abs value, since we care about coupling strength)
        lcc = abs(correlation)
        
        return min(1.0, max(0.0, lcc))
    
    def calculate_alpha_power(self, eeg_data: Dict[str, np.ndarray]) -> float:
        """
        Calculate alpha band power (8-12 Hz)
        
        Args:
            eeg_data: Dict of channel_name -> voltage array
        
        Returns:
            Alpha power (0-1 scale)
        """
        # Average across all channels
        alpha_powers = []
        
        for channel_data in eeg_data.values():
            if len(channel_data) < 256:  # Need enough samples for FFT
                continue
            
            # FFT
            fft = np.fft.fft(channel_data)
            freqs = np.fft.fftfreq(len(channel_data), 1.0 / 256)  # 256 Hz sampling
            
            # Extract alpha band (8-12 Hz)
            alpha_mask = (freqs >= 8) & (freqs <= 12)
            alpha_power = np.mean(np.abs(fft[alpha_mask]) ** 2)
            
            alpha_powers.append(alpha_power)
        
        if not alpha_powers:
            return 0.0
        
        # Normalize to 0-1 (heuristic scaling)
        avg_alpha = np.mean(alpha_powers)
        return min(1.0, avg_alpha / 1000.0)
    
    def calculate_gile_score(
        self,
        lcc: float,
        alpha_power: float,
        hrv: Optional[float],
        coherence: Optional[float],
        readiness: Optional[int]
    ) -> float:
        """
        Calculate GILE score from biometric data
        
        GILE = 5(σ - 0.5) where σ is consciousness state
        
        Args:
            lcc: LCC coherence (0-1)
            alpha_power: Alpha band power (0-1)
            hrv: HRV (ms)
            coherence: Heart coherence (0-1)
            readiness: Oura readiness (0-100)
        
        Returns:
            GILE score (-2.5 to +2.5)
        """
        # Weight factors
        weights = {
            'lcc': 0.3,
            'alpha': 0.2,
            'hrv': 0.2,
            'coherence': 0.2,
            'readiness': 0.1
        }
        
        # Normalize inputs to 0-1
        components = {
            'lcc': lcc,
            'alpha': alpha_power,
            'hrv': min(1.0, (hrv or 50) / 100.0) if hrv else 0.5,
            'coherence': coherence if coherence else 0.5,
            'readiness': (readiness / 100.0) if readiness else 0.5
        }
        
        # Weighted average for σ (consciousness state)
        sigma = sum(components[k] * weights[k] for k in weights.keys())
        
        # GILE = 5(σ - 0.5)
        gile = 5.0 * (sigma - 0.5)
        
        return gile
    
    def determine_faah_tier(self, gile_score: float, lcc: float) -> int:
        """
        Determine FAAH Protocol tier based on current state
        
        Tiers:
        1. Baseline (GILE < 0.42, need high FAAH support)
        2. Moderate (GILE 0.42-0.7, standard FAAH)
        3. Enhanced (GILE 0.7-1.0, low FAAH needed)
        4. Optimal (GILE > 1.0, LCC-only session)
        
        Args:
            gile_score: Current GILE score
            lcc: Current LCC coherence
        
        Returns:
            FAAH tier (1-4)
        """
        if gile_score < -0.4:  # σ < 0.42 (soul death threshold)
            return 1
        elif gile_score < 0.5:  # σ < 0.6
            return 2
        elif gile_score < 1.0:  # σ < 0.7
            return 3
        else:
            return 4
    
    def get_unified_snapshot(self) -> UnifiedBiometricSnapshot:
        """
        Get current unified biometric snapshot
        
        Returns:
            UnifiedBiometricSnapshot with all current metrics
        """
        snapshot = UnifiedBiometricSnapshot(timestamp=datetime.now())
        
        if self.is_demo_mode_active() and self.simulator:
            sim_frame = self.simulator.generate_frame()
            
            snapshot.heart_rate_bpm = sim_frame.heart_rate_bpm
            snapshot.hrv_rmssd = sim_frame.hrv_rmssd
            snapshot.coherence_score = sim_frame.coherence_score
            snapshot.rr_intervals = sim_frame.rr_intervals
            
            snapshot.alpha_power = sim_frame.alpha_power
            snapshot.beta_power = sim_frame.beta_power
            snapshot.theta_power = sim_frame.theta_power
            snapshot.lcc_coherence = sim_frame.lcc_coherence
            
            snapshot.readiness_score = sim_frame.readiness_score
            snapshot.sleep_score = sim_frame.sleep_score
            
            gile_overall = sim_frame.gile_scores.get('overall', 0.5)
            snapshot.gile_score = 5.0 * (gile_overall - 0.5)
            
            snapshot.faah_tier = self.determine_faah_tier(
                gile_score=snapshot.gile_score,
                lcc=snapshot.lcc_coherence or 0.0
            )
            
            snapshot.muse_connected = False
            snapshot.polar_connected = False
            snapshot.oura_synced = False
            snapshot.muse_signal_quality = 95.0
            
            self.latest_snapshot = snapshot
            self.session_history.append(snapshot)
            return snapshot
        
        if self.muse and self.muse_connected:
            try:
                eeg_data = self.muse.get_eeg_data(duration_seconds=5.0)
                snapshot.eeg_channels = eeg_data
                snapshot.lcc_coherence = self.calculate_lcc_coherence(eeg_data)
                snapshot.alpha_power = self.calculate_alpha_power(eeg_data)
                snapshot.muse_connected = True
                snapshot.muse_signal_quality = self.get_muse_signal_quality()
            except Exception as e:
                print(f"⚠️ Muse 2 data error: {e}")
        
        if self.polar and self.polar_connected:
            try:
                snapshot.heart_rate_bpm = 72.0
                snapshot.hrv_rmssd = 65.0
                snapshot.coherence_score = 0.75
                snapshot.polar_connected = True
            except Exception as e:
                print(f"⚠️ Polar H10 data error: {e}")
        
        if self.oura and self.oura_synced:
            try:
                daily_data = self.oura.get_daily_readiness()
                if daily_data:
                    latest = daily_data[0]
                    snapshot.readiness_score = latest.get('readiness_score')
                    snapshot.oura_synced = True
            except Exception as e:
                print(f"⚠️ Oura Ring data error: {e}")
        
        snapshot.gile_score = self.calculate_gile_score(
            lcc=snapshot.lcc_coherence or 0.0,
            alpha_power=snapshot.alpha_power or 0.0,
            hrv=snapshot.hrv_rmssd,
            coherence=snapshot.coherence_score,
            readiness=snapshot.readiness_score
        )
        
        snapshot.faah_tier = self.determine_faah_tier(
            gile_score=snapshot.gile_score,
            lcc=snapshot.lcc_coherence or 0.0
        )
        
        self.latest_snapshot = snapshot
        self.session_history.append(snapshot)
        
        return snapshot
    
    def get_device_status(self) -> Dict[str, Any]:
        """Get status of all devices"""
        return {
            'muse_connected': self.muse_connected,
            'muse_signal_quality': self.get_muse_signal_quality() if self.muse_connected else 0.0,
            'polar_connected': self.polar_connected,
            'oura_synced': self.oura_synced,
            'latest_snapshot': asdict(self.latest_snapshot) if self.latest_snapshot else None
        }


# Singleton instance for Streamlit
@st.cache_resource
def get_biometric_manager() -> UnifiedBiometricManager:
    """Get cached biometric manager instance"""
    return UnifiedBiometricManager()

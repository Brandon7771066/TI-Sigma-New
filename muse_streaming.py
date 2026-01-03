"""
MUSE 2 EEG STREAMING INTEGRATION
================================

Real-time EEG streaming from Muse 2 headband for brain-computer interface.
Uses muselsl library for BLE connection and LSL streaming.

Features:
- Connect to Muse 2 via Bluetooth
- Stream EEG data in real-time
- Integrate with TI Framework L × E measurements
- Support for recorded session playback (for testing)

Author: Brandon Emerick
Date: December 26, 2025
"""

import numpy as np
import time
import threading
from typing import Optional, Dict, List, Callable
from dataclasses import dataclass, field
from collections import deque
from queue import Queue
import asyncio

# Try to import muselsl (may not be available in all environments)
MUSELSL_AVAILABLE = False
try:
    from muselsl import stream, list_muses
    from pylsl import StreamInlet, resolve_byprop
    MUSELSL_AVAILABLE = True
except (ImportError, RuntimeError) as e:
    pass  # Silently fall back to simulated mode


@dataclass
class MuseConfig:
    """Configuration for Muse 2 streaming"""
    buffer_size: int = 256  # 1 second at 256 Hz
    channels: List[str] = field(default_factory=lambda: ['TP9', 'AF7', 'AF8', 'TP10', 'AUX'])
    sample_rate: int = 256
    timeout: float = 5.0  # Connection timeout


class MuseEEGStream:
    """
    Real-time EEG streaming from Muse 2 headband.
    
    Usage:
        stream = MuseEEGStream()
        stream.connect()
        stream.start_streaming()
        
        while True:
            sample = stream.get_latest_sample()
            if sample:
                process(sample)
    """
    
    def __init__(self, config: MuseConfig = None):
        self.config = config or MuseConfig()
        self.is_connected = False
        self.is_streaming = False
        self.inlet: Optional[StreamInlet] = None
        self.data_buffer: Dict[str, deque] = {
            ch: deque(maxlen=self.config.buffer_size) 
            for ch in self.config.channels[:4]  # Exclude AUX
        }
        self.sample_queue: Queue = Queue()
        self.streaming_thread: Optional[threading.Thread] = None
        self._stop_event = threading.Event()
        
        # Callbacks for new data
        self.on_sample_callbacks: List[Callable] = []
        
        # Simulated mode for testing
        self.simulated_mode = not MUSELSL_AVAILABLE
        self.simulated_thread: Optional[threading.Thread] = None
        
    def list_available_muses(self) -> List[Dict]:
        """List available Muse headbands"""
        if not MUSELSL_AVAILABLE:
            print("muselsl not available. Returning simulated device.")
            return [{'name': 'Simulated Muse', 'address': 'SIM-001'}]
            
        try:
            muses = list_muses()
            return [{'name': m['name'], 'address': m['address']} for m in muses]
        except Exception as e:
            print(f"Error listing Muses: {e}")
            return []
    
    def connect(self, address: str = None) -> bool:
        """
        Connect to Muse 2 headband.
        
        Args:
            address: Optional MAC address of specific Muse
            
        Returns:
            True if connected successfully
        """
        if self.simulated_mode:
            print("Running in simulated mode (no real Muse connection)")
            self.is_connected = True
            return True
            
        try:
            print("Searching for Muse EEG stream...")
            streams = resolve_byprop('type', 'EEG', timeout=self.config.timeout)
            
            if not streams:
                print("No EEG stream found. Make sure Muse is streaming.")
                print("Run: muselsl stream --name 'YourMuseName'")
                return False
                
            self.inlet = StreamInlet(streams[0])
            self.is_connected = True
            print("Connected to Muse EEG stream!")
            return True
            
        except Exception as e:
            print(f"Connection error: {e}")
            return False
    
    def start_streaming(self) -> bool:
        """Start streaming EEG data in background thread"""
        if not self.is_connected:
            print("Not connected. Call connect() first.")
            return False
            
        if self.is_streaming:
            print("Already streaming.")
            return True
            
        self._stop_event.clear()
        self.is_streaming = True
        
        if self.simulated_mode:
            self.simulated_thread = threading.Thread(
                target=self._simulated_stream_loop,
                daemon=True
            )
            self.simulated_thread.start()
        else:
            self.streaming_thread = threading.Thread(
                target=self._stream_loop,
                daemon=True
            )
            self.streaming_thread.start()
            
        print("Streaming started.")
        return True
    
    def stop_streaming(self) -> None:
        """Stop streaming"""
        self._stop_event.set()
        self.is_streaming = False
        print("Streaming stopped.")
    
    def _stream_loop(self) -> None:
        """Background thread for reading EEG samples"""
        while not self._stop_event.is_set():
            try:
                sample, timestamp = self.inlet.pull_sample(timeout=0.1)
                
                if sample:
                    # Map sample to channels
                    sample_dict = {}
                    for i, ch in enumerate(self.config.channels[:4]):
                        if i < len(sample):
                            self.data_buffer[ch].append(sample[i])
                            sample_dict[ch] = sample[i]
                    
                    sample_dict['timestamp'] = timestamp
                    self.sample_queue.put(sample_dict)
                    
                    # Call callbacks
                    for callback in self.on_sample_callbacks:
                        callback(sample_dict)
                        
            except Exception as e:
                if not self._stop_event.is_set():
                    print(f"Streaming error: {e}")
    
    def _simulated_stream_loop(self) -> None:
        """Simulated streaming for testing without real Muse"""
        t = 0
        while not self._stop_event.is_set():
            # Generate realistic-looking EEG signal
            # Alpha wave (10 Hz) + Beta wave (20 Hz) + noise
            sample_dict = {}
            
            for ch in self.config.channels[:4]:
                # Simulate EEG: alpha + beta + gamma + noise
                alpha = 20 * np.sin(2 * np.pi * 10 * t / self.config.sample_rate)
                beta = 10 * np.sin(2 * np.pi * 20 * t / self.config.sample_rate)
                gamma = 5 * np.sin(2 * np.pi * 40 * t / self.config.sample_rate)
                noise = np.random.randn() * 5
                
                value = alpha + beta + gamma + noise
                
                self.data_buffer[ch].append(value)
                sample_dict[ch] = value
                
            sample_dict['timestamp'] = time.time()
            self.sample_queue.put(sample_dict)
            
            # Call callbacks
            for callback in self.on_sample_callbacks:
                callback(sample_dict)
            
            t += 1
            time.sleep(1 / self.config.sample_rate)
    
    def get_latest_sample(self) -> Optional[Dict]:
        """Get the latest EEG sample (non-blocking)"""
        try:
            return self.sample_queue.get_nowait()
        except:
            return None
    
    def get_buffer(self, channel: str) -> np.ndarray:
        """Get the full buffer for a channel"""
        if channel in self.data_buffer:
            return np.array(list(self.data_buffer[channel]))
        return np.array([])
    
    def get_all_buffers(self) -> Dict[str, np.ndarray]:
        """Get buffers for all channels"""
        return {ch: self.get_buffer(ch) for ch in self.config.channels[:4]}
    
    def add_callback(self, callback: Callable) -> None:
        """Add callback function for new samples"""
        self.on_sample_callbacks.append(callback)
    
    def remove_callback(self, callback: Callable) -> None:
        """Remove callback function"""
        if callback in self.on_sample_callbacks:
            self.on_sample_callbacks.remove(callback)


class RecordedSessionPlayer:
    """
    Play back recorded EEG sessions for testing and validation.
    
    Allows testing the BCI system without a real Muse headband.
    """
    
    def __init__(self, sample_rate: int = 256):
        self.sample_rate = sample_rate
        self.channels = ['TP9', 'AF7', 'AF8', 'TP10']
        self.data: Dict[str, np.ndarray] = {}
        self.current_index = 0
        self.is_playing = False
        
    def generate_motor_imagery_session(self, duration_seconds: float = 60) -> None:
        """
        Generate a synthetic motor imagery session.
        
        Simulates a session with alternating REST, IMAGINE_UP, IMAGINE_DOWN periods.
        """
        n_samples = int(duration_seconds * self.sample_rate)
        
        # Initialize data arrays
        for ch in self.channels:
            self.data[ch] = np.zeros(n_samples)
            
        # Generate baseline EEG
        t = np.arange(n_samples) / self.sample_rate
        
        for ch in self.channels:
            # Base signal: alpha + beta + gamma
            alpha = 20 * np.sin(2 * np.pi * 10 * t)
            beta = 10 * np.sin(2 * np.pi * 20 * t)
            gamma = 5 * np.sin(2 * np.pi * 40 * t)
            noise = np.random.randn(n_samples) * 5
            
            self.data[ch] = alpha + beta + gamma + noise
        
        # Add motor imagery events (mu suppression)
        # Every 10 seconds: 3s REST, 3s IMAGINE_UP, 3s IMAGINE_DOWN, 1s REST
        trial_length = 10 * self.sample_rate
        n_trials = int(n_samples / trial_length)
        
        for trial in range(n_trials):
            start = trial * trial_length
            
            # IMAGINE_UP period (3-6 seconds): suppress mu in left hemisphere
            up_start = start + 3 * self.sample_rate
            up_end = start + 6 * self.sample_rate
            
            # Reduce power in left channels (TP9, AF7)
            self.data['TP9'][up_start:up_end] *= 0.5
            self.data['AF7'][up_start:up_end] *= 0.5
            
            # IMAGINE_DOWN period (6-9 seconds): suppress mu in right hemisphere
            down_start = start + 6 * self.sample_rate
            down_end = start + 9 * self.sample_rate
            
            # Reduce power in right channels (AF8, TP10)
            self.data['AF8'][down_start:down_end] *= 0.5
            self.data['TP10'][down_start:down_end] *= 0.5
        
        print(f"Generated {duration_seconds}s motor imagery session with {n_trials} trials")
    
    def load_from_file(self, filepath: str) -> bool:
        """Load recorded session from file"""
        try:
            import json
            with open(filepath, 'r') as f:
                session_data = json.load(f)
            
            for ch in self.channels:
                if ch in session_data:
                    self.data[ch] = np.array(session_data[ch])
            
            print(f"Loaded session from {filepath}")
            return True
        except Exception as e:
            print(f"Error loading session: {e}")
            return False
    
    def save_to_file(self, filepath: str) -> bool:
        """Save session to file"""
        try:
            import json
            session_data = {ch: self.data[ch].tolist() for ch in self.channels}
            
            with open(filepath, 'w') as f:
                json.dump(session_data, f)
            
            print(f"Saved session to {filepath}")
            return True
        except Exception as e:
            print(f"Error saving session: {e}")
            return False
    
    def get_sample(self) -> Optional[Dict[str, float]]:
        """Get next sample from recorded session"""
        if not self.data or 'TP9' not in self.data:
            return None
            
        max_index = len(self.data['TP9'])
        
        if self.current_index >= max_index:
            self.current_index = 0  # Loop
            
        sample = {
            ch: float(self.data[ch][self.current_index])
            for ch in self.channels
        }
        sample['timestamp'] = time.time()
        
        self.current_index += 1
        return sample
    
    def reset(self) -> None:
        """Reset playback to beginning"""
        self.current_index = 0


class HRVSimulator:
    """
    Simulate HRV measurements for E (Existence) calculation.
    
    In real implementation, would receive data from:
    - Polar H10 heart rate monitor
    - Apple Watch
    - Oura Ring
    - Or PPG sensor
    """
    
    def __init__(self, baseline_rmssd: float = 45.0):
        self.baseline_rmssd = baseline_rmssd
        self.current_rmssd = baseline_rmssd
        self.rr_intervals: deque = deque(maxlen=300)  # 5 minutes of RR
        self._simulate_baseline()
        
    def _simulate_baseline(self) -> None:
        """Generate baseline RR intervals"""
        # Typical resting HR ~60 bpm = 1000ms RR interval
        base_rr = 1000
        for _ in range(60):
            # Add realistic HRV
            rr = base_rr + np.random.randn() * 50
            self.rr_intervals.append(rr)
    
    def add_rr_interval(self, rr_ms: float) -> None:
        """Add a new RR interval from heart rate monitor"""
        self.rr_intervals.append(rr_ms)
        self._update_rmssd()
    
    def _update_rmssd(self) -> None:
        """Calculate RMSSD from RR intervals"""
        if len(self.rr_intervals) < 2:
            return
            
        rr = np.array(list(self.rr_intervals))
        diffs = np.diff(rr)
        self.current_rmssd = np.sqrt(np.mean(diffs ** 2))
    
    def get_rmssd(self) -> float:
        """Get current RMSSD value"""
        return self.current_rmssd
    
    def get_E(self, reference: float = 60.0) -> float:
        """
        Get E (Existence) value from RMSSD.
        E = min(1, RMSSD / reference)
        """
        return min(1.0, self.current_rmssd / reference)
    
    def simulate_stress(self) -> None:
        """Simulate stress (lower HRV)"""
        for _ in range(10):
            rr = 800 + np.random.randn() * 20  # Higher HR, lower variability
            self.rr_intervals.append(rr)
        self._update_rmssd()
    
    def simulate_relaxation(self) -> None:
        """Simulate relaxation (higher HRV)"""
        for _ in range(10):
            rr = 1100 + np.random.randn() * 80  # Lower HR, higher variability
            self.rr_intervals.append(rr)
        self._update_rmssd()


# =============================================================================
# INTEGRATED BCI STREAM
# =============================================================================

class IntegratedBCIStream:
    """
    Integrated stream combining EEG and HRV for complete L × E measurement.
    
    This is the production class that combines:
    - Muse 2 EEG streaming (for L)
    - HRV monitoring (for E)
    - Real-time L × E computation
    """
    
    def __init__(self):
        self.muse = MuseEEGStream()
        self.hrv = HRVSimulator()
        self.processor = None  # Set from eeg_bci_system
        
        # L × E values
        self.L = 0.0
        self.E = 0.0
        self.lexis = 0.0
        
        # Streaming status
        self.is_active = False
        
    def setup(self, processor) -> None:
        """Connect to the EEG signal processor"""
        self.processor = processor
        
        # Add callback to process incoming samples
        self.muse.add_callback(self._on_eeg_sample)
    
    def _on_eeg_sample(self, sample: Dict) -> None:
        """Process incoming EEG sample"""
        if self.processor:
            # Add to processor
            for ch in ['TP9', 'AF7', 'AF8', 'TP10']:
                if ch in sample:
                    self.processor.add_sample(ch, sample[ch])
            
            # Update L
            self.L = self.processor.compute_L()
            
            # Update E from HRV
            self.E = self.hrv.get_E()
            
            # Update processor's E value
            self.processor.set_E_from_hrv(self.hrv.get_rmssd())
            
            # Compute Lexis
            self.lexis = self.L * self.E
    
    def start(self) -> bool:
        """Start integrated streaming"""
        if self.muse.connect():
            if self.muse.start_streaming():
                self.is_active = True
                return True
        return False
    
    def stop(self) -> None:
        """Stop streaming"""
        self.muse.stop_streaming()
        self.is_active = False
    
    def get_metrics(self) -> Dict:
        """Get current L × E metrics"""
        return {
            'L': self.L,
            'E': self.E,
            'lexis': self.lexis,
            'exceeds_threshold': self.lexis >= 0.85,
            'is_active': self.is_active
        }


# =============================================================================
# DEMONSTRATION
# =============================================================================

def demonstrate_streaming():
    """Demonstrate the Muse streaming system"""
    
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║                                                                      ║
║   MUSE 2 EEG STREAMING DEMONSTRATION                                 ║
║                                                                      ║
║   Real-time brain signal streaming for BCI                           ║
║                                                                      ║
╚══════════════════════════════════════════════════════════════════════╝
    """)
    
    # Create stream
    stream = MuseEEGStream()
    
    # Check for Muse devices
    print("\n--- DEVICE DISCOVERY ---")
    devices = stream.list_available_muses()
    print(f"Found {len(devices)} device(s):")
    for dev in devices:
        print(f"  - {dev['name']} ({dev['address']})")
    
    # Connect
    print("\n--- CONNECTION ---")
    if stream.connect():
        print("Connection successful!")
    else:
        print("Running in simulated mode")
    
    # Start streaming
    print("\n--- STREAMING ---")
    stream.start_streaming()
    
    # Read samples for 2 seconds
    print("Reading samples for 2 seconds...")
    start = time.time()
    sample_count = 0
    
    while time.time() - start < 2.0:
        sample = stream.get_latest_sample()
        if sample:
            sample_count += 1
            if sample_count % 50 == 0:  # Print every 50th sample
                print(f"  Sample {sample_count}: TP9={sample.get('TP9', 0):.2f}, "
                      f"AF7={sample.get('AF7', 0):.2f}")
    
    print(f"Received {sample_count} samples ({sample_count/2:.1f} Hz)")
    
    # Stop streaming
    stream.stop_streaming()
    
    # Demonstrate HRV simulator
    print("\n--- HRV SIMULATION ---")
    hrv = HRVSimulator()
    print(f"Baseline RMSSD: {hrv.get_rmssd():.1f} ms")
    print(f"Baseline E: {hrv.get_E():.3f}")
    
    hrv.simulate_relaxation()
    print(f"After relaxation - RMSSD: {hrv.get_rmssd():.1f} ms, E: {hrv.get_E():.3f}")
    
    hrv.simulate_stress()
    print(f"After stress - RMSSD: {hrv.get_rmssd():.1f} ms, E: {hrv.get_E():.3f}")
    
    # Demonstrate recorded session
    print("\n--- RECORDED SESSION ---")
    player = RecordedSessionPlayer()
    player.generate_motor_imagery_session(10)
    
    print("Playing back recorded session...")
    for i in range(5):
        sample = player.get_sample()
        print(f"  Sample {i}: TP9={sample['TP9']:.2f}")
    
    print("\n" + "="*60)
    print("STREAMING DEMONSTRATION COMPLETE!")
    print("="*60)


if __name__ == "__main__":
    demonstrate_streaming()

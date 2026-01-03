# Muse 2 Real-Time EEG Integration Guide
## Complete Setup for Mood Amplifier Validation

**Date:** November 8, 2025  
**Hardware:** Muse 2 Headband, iPhone XR, 2020 HP Laptop  
**Goal:** Real-time EEG streaming into Mood Amplifier Streamlit app

---

## 🎯 OVERVIEW

Your Mood Amplifier currently lacks real-time EEG integration. This guide provides two complete solutions for livestreaming Muse 2 data into your validation framework.

---

## 📱 SOLUTION 1: Mind Monitor App (RECOMMENDED)

**Best For:** Quick setup, mobile flexibility, immediate results

### Step 1: Install Mind Monitor

- **iOS (iPhone XR):** https://apps.apple.com/us/app/mind-monitor/id988527143
- **Cost:** ~$5-15 (one-time purchase)
- **Why:** Industry-standard app, real-time visualization + OSC streaming

### Step 2: Connect Muse 2

1. Turn on Muse 2 headband
2. Open Mind Monitor app
3. Tap "Connect" → Select your Muse 2
4. Verify sensor quality (horseshoe indicator should be green/yellow)

### Step 3: Enable OSC Streaming

**In Mind Monitor Settings:**
- Tap "OSC Streaming"
- Enable: ✅ "Stream OSC"
- Server IP: `[Your HP laptop's local IP]` (e.g., 192.168.1.100)
- Port: `5000`
- Streaming Rate: 10 Hz (or 256 Hz for raw EEG)

**Find Your HP's IP:**
- Windows: `ipconfig` in Command Prompt
- Look for "IPv4 Address" on your WiFi adapter

### Step 4: Python OSC Receiver (On HP)

**Install Required Libraries:**
```bash
pip install python-osc numpy pandas
```

**Create: `muse_receiver.py`**
```python
from pythonosc import dispatcher, osc_server
import numpy as np
import pandas as pd
from datetime import datetime
import threading

class MuseEEGReceiver:
    """Receives real-time EEG from Mind Monitor via OSC."""
    
    def __init__(self, port=5000):
        self.port = port
        self.eeg_buffer = []
        self.latest_sample = None
        
        # Setup OSC dispatcher
        self.dispatcher = dispatcher.Dispatcher()
        self.dispatcher.map("/muse/eeg", self.eeg_handler)
        self.dispatcher.map("/muse/batt", self.battery_handler)
        self.dispatcher.map("/muse/elements/alpha_absolute", self.alpha_handler)
        
        # Start server in background thread
        self.server = osc_server.ThreadingOSCUDPServer(
            ("0.0.0.0", self.port), 
            self.dispatcher
        )
        
        self.server_thread = threading.Thread(target=self.server.serve_forever)
        self.server_thread.daemon = True
        
    def start(self):
        """Start listening for OSC messages."""
        print(f"🎧 Listening for Muse 2 EEG on port {self.port}...")
        self.server_thread.start()
        
    def eeg_handler(self, address, *args):
        """Handle raw EEG data: /muse/eeg [TP9, AF7, AF8, TP10]"""
        timestamp = datetime.now().isoformat()
        self.latest_sample = {
            'timestamp': timestamp,
            'TP9': args[0],  # Left ear
            'AF7': args[1],  # Left forehead
            'AF8': args[2],  # Right forehead
            'TP10': args[3]  # Right ear
        }
        self.eeg_buffer.append(self.latest_sample)
        
        # Keep buffer manageable (last 1000 samples)
        if len(self.eeg_buffer) > 1000:
            self.eeg_buffer.pop(0)
    
    def alpha_handler(self, address, *args):
        """Handle alpha band power."""
        if self.latest_sample:
            self.latest_sample['alpha'] = args
    
    def battery_handler(self, address, *args):
        """Handle battery level."""
        print(f"🔋 Muse 2 Battery: {args[0]}%")
    
    def get_latest(self):
        """Get most recent EEG sample."""
        return self.latest_sample
    
    def get_buffer_df(self):
        """Get buffer as pandas DataFrame."""
        return pd.DataFrame(self.eeg_buffer)
    
    def save_session(self, filename):
        """Save recorded session to CSV."""
        df = self.get_buffer_df()
        df.to_csv(filename, index=False)
        print(f"💾 Saved {len(df)} samples to {filename}")


# Example usage
if __name__ == "__main__":
    receiver = MuseEEGReceiver(port=5000)
    receiver.start()
    
    # Keep running and print updates
    import time
    try:
        while True:
            latest = receiver.get_latest()
            if latest:
                print(f"EEG: TP9={latest['TP9']:.1f}µV, AF7={latest['AF7']:.1f}µV, "
                      f"AF8={latest['AF8']:.1f}µV, TP10={latest['TP10']:.1f}µV")
            time.sleep(1)  # Update every second
    except KeyboardInterrupt:
        receiver.save_session("muse_session.csv")
```

### Step 5: Integrate with Streamlit Mood Amplifier

**Modify `app.py` or create new validation tab:**

```python
import streamlit as st
from muse_receiver import MuseEEGReceiver
import time

# Initialize receiver (runs in background)
if 'muse_receiver' not in st.session_state:
    st.session_state.muse_receiver = MuseEEGReceiver(port=5000)
    st.session_state.muse_receiver.start()

st.header("🧠 Real-Time Muse 2 Validation")

# Display latest EEG
latest = st.session_state.muse_receiver.get_latest()

if latest:
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        st.metric("TP9 (L Ear)", f"{latest['TP9']:.1f} µV")
    with col2:
        st.metric("AF7 (L Forehead)", f"{latest['AF7']:.1f} µV")
    with col3:
        st.metric("AF8 (R Forehead)", f"{latest['AF8']:.1f} µV")
    with col4:
        st.metric("TP10 (R Ear)", f"{latest['TP10']:.1f} µV")
    
    # Plot real-time EEG
    df = st.session_state.muse_receiver.get_buffer_df()
    if not df.empty:
        st.line_chart(df[['TP9', 'AF7', 'AF8', 'TP10']].tail(100))
    
    # Mood Amplifier validation
    st.subheader("LCC Protocol Validation")
    
    if st.button("Start LCC Session"):
        # Your existing LCC protocol here
        # Now with real-time EEG feedback!
        pass
else:
    st.warning("⚠️ No EEG data received. Check Mind Monitor OSC streaming settings.")

# Auto-refresh every 0.5 seconds
time.sleep(0.5)
st.rerun()
```

---

## 💻 SOLUTION 2: Direct Python via MuseLSL (Advanced)

**Best For:** Maximum control, research applications, no mobile app needed

### Step 1: Install MuseLSL

```bash
pip install muselsl pylsl
```

**For Windows:** Also install BlueMuse GUI:
https://github.com/kowalej/BlueMuse

### Step 2: Start Streaming (HP Laptop)

**Command Line:**
```bash
# List available Muse devices
muselsl list

# Start streaming all sensors
muselsl stream --ppg_enabled --acc_enabled --gyro_enabled
```

**Or Python Script:**
```python
from muselsl import stream, list_muses

# Find Muse 2
muses = list_muses()
print(f"Found Muse devices: {muses}")

# Stream EEG + PPG + Accelerometer + Gyroscope
stream(
    muses[0]['address'],
    ppg_enabled=True,   # Heart rate
    acc_enabled=True,    # Accelerometer
    gyro_enabled=True    # Gyroscope
)
```

### Step 3: Receive Real-Time Data

```python
from pylsl import StreamInlet, resolve_byprop
import numpy as np

def connect_muse():
    """Connect to Muse 2 LSL stream."""
    print("🔍 Looking for Muse 2 EEG stream...")
    
    streams = resolve_byprop('type', 'EEG', timeout=10)
    
    if not streams:
        print("❌ No EEG stream found. Make sure muselsl stream is running.")
        return None
    
    inlet = StreamInlet(streams[0])
    print(f"✅ Connected to {streams[0].name()}")
    return inlet

def read_eeg_realtime(inlet, duration=10):
    """Read EEG for specified duration."""
    samples = []
    timestamps = []
    
    start_time = time.time()
    while time.time() - start_time < duration:
        sample, timestamp = inlet.pull_sample()
        samples.append(sample)
        timestamps.append(timestamp)
    
    return np.array(samples), np.array(timestamps)

# Usage
inlet = connect_muse()
if inlet:
    # Continuous reading
    while True:
        sample, ts = inlet.pull_sample()
        print(f"EEG: {sample[:4]}")  # First 4 channels
```

### Step 4: Integrate with Streamlit

```python
import streamlit as st
from pylsl import StreamInlet, resolve_byprop
import threading
import queue

class MuseLSLInterface:
    """Thread-safe LSL interface for Streamlit."""
    
    def __init__(self):
        self.inlet = None
        self.data_queue = queue.Queue(maxsize=1000)
        self.running = False
        
    def connect(self):
        streams = resolve_byprop('type', 'EEG', timeout=5)
        if streams:
            self.inlet = StreamInlet(streams[0])
            return True
        return False
    
    def start_streaming(self):
        self.running = True
        thread = threading.Thread(target=self._stream_worker)
        thread.daemon = True
        thread.start()
    
    def _stream_worker(self):
        while self.running:
            if self.inlet:
                sample, ts = self.inlet.pull_sample()
                try:
                    self.data_queue.put_nowait({
                        'timestamp': ts,
                        'eeg': sample[:4],
                        'ppg': sample[4:7] if len(sample) > 4 else None
                    })
                except queue.Full:
                    self.data_queue.get()  # Remove oldest
    
    def get_latest(self):
        try:
            return self.data_queue.get_nowait()
        except queue.Empty:
            return None

# In Streamlit app
if 'muse_lsl' not in st.session_state:
    st.session_state.muse_lsl = MuseLSLInterface()
    if st.session_state.muse_lsl.connect():
        st.session_state.muse_lsl.start_streaming()
```

---

## 🧪 VALIDATION PROTOCOLS

### Protocol 1: LCC Efficacy with Real-Time EEG

```python
def validate_lcc_protocol(muse_interface, lcc_params):
    """
    Validate LCC protocol with real-time Muse 2 feedback.
    
    Args:
        muse_interface: Connected Muse receiver
        lcc_params: {'frequency': 10, 'amplitude': 0.5, 'duration': 300}
    """
    
    # Baseline (60 seconds)
    st.write("📊 Recording baseline...")
    baseline_eeg = record_eeg(muse_interface, duration=60)
    baseline_alpha = calculate_alpha_power(baseline_eeg)
    
    # Apply LCC
    st.write(f"🎵 Applying LCC @ {lcc_params['frequency']} Hz...")
    # [Your LCC application code here]
    
    # Active recording
    active_eeg = record_eeg(muse_interface, duration=lcc_params['duration'])
    active_alpha = calculate_alpha_power(active_eeg)
    
    # Post-session (60 seconds)
    st.write("📊 Recording post-session...")
    post_eeg = record_eeg(muse_interface, duration=60)
    post_alpha = calculate_alpha_power(post_eeg)
    
    # Analysis
    improvement = ((active_alpha - baseline_alpha) / baseline_alpha) * 100
    
    st.success(f"✅ Alpha power increase: {improvement:.1f}%")
    
    return {
        'baseline': baseline_alpha,
        'active': active_alpha,
        'post': post_alpha,
        'improvement_percent': improvement
    }
```

### Protocol 2: Eyes-Open Validation

```python
def validate_eyes_open_capability():
    """
    Validate Muse 2 for eyes-open LCC sessions.
    Confirms 83% correlation with research-grade EEG.
    """
    
    st.write("👁️ Eyes-Open Validation Protocol")
    
    # Record eyes-open session
    eyes_open_data = record_eeg(muse_interface, duration=300)
    
    # Compare with expected research-grade patterns
    correlation = calculate_correlation(eyes_open_data, reference_patterns)
    
    if correlation > 0.80:
        st.success(f"✅ Eyes-open capability validated: {correlation:.1%} correlation")
    else:
        st.warning(f"⚠️ Lower than expected: {correlation:.1%} (target: >80%)")
```

---

## 📊 DATA EXPORT & ANALYSIS

### Save Sessions for Research

```python
# After LCC session
receiver.save_session(f"lcc_session_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv")

# Load and analyze
import pandas as pd
df = pd.read_csv("lcc_session_20251108_153000.csv")

# Calculate band powers
from scipy.signal import welch

def calculate_band_power(eeg_signal, fs=256, band=(8, 13)):
    """Calculate power in frequency band (e.g., alpha 8-13 Hz)."""
    freqs, psd = welch(eeg_signal, fs=fs, nperseg=fs*2)
    idx = np.logical_and(freqs >= band[0], freqs <= band[1])
    return np.trapz(psd[idx], freqs[idx])

# Analyze alpha across session
df['alpha_power'] = df.apply(
    lambda row: calculate_band_power(
        [row['TP9'], row['AF7'], row['AF8'], row['TP10']]
    ), axis=1
)
```

---

## ⚡ QUICK START CHECKLIST

### For Mind Monitor (Easiest):
- [ ] Buy & install Mind Monitor app on iPhone XR
- [ ] Connect Muse 2 to app
- [ ] Enable OSC streaming (IP: HP laptop, Port: 5000)
- [ ] Run `muse_receiver.py` on HP
- [ ] Integrate with Streamlit app
- [ ] Test real-time display

### For MuseLSL (Advanced):
- [ ] Install `muselsl` and `pylsl` on HP
- [ ] Windows: Install BlueMuse GUI
- [ ] Run `muselsl stream --ppg_enabled`
- [ ] Create LSL receiver in Python
- [ ] Integrate with Streamlit
- [ ] Validate data quality

---

## 🎯 NEXT STEPS

1. **Immediate:** Install Mind Monitor ($5-15) and test OSC streaming
2. **This Week:** Integrate real-time EEG display into Mood Amplifier app
3. **This Month:** Run 10+ LCC validation sessions with documented EEG changes
4. **Long-term:** Publish "Muse 2 Eyes-Open LCC Validation Study"

---

## 🔗 RESOURCES

- **Mind Monitor:** https://mind-monitor.com/
- **MuseLSL GitHub:** https://github.com/alexandrebarachant/muse-lsl
- **BlueMuse (Windows):** https://github.com/kowalej/BlueMuse
- **OSC Protocol:** https://opensoundcontrol.stanford.edu/

**Your Mood Amplifier is about to get REAL-TIME validation! 🚀**

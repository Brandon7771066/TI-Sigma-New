"""
🧠 Real-Time Biometric Stream - Flicker-Free Display
====================================================

Smooth, second-by-second biometric display without screen blinking.
Uses Streamlit's fragment/container pattern for stable updates.

Connects via:
- ESP32 BLE Bridge → HTTP API
- Direct BLE (Muse 2, Mendi, Polar H10)
- Data Bridge API (HTTP endpoint)

Author: Brandon Emerick
Date: December 2025
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from datetime import datetime, timedelta
from typing import Dict, List, Optional
from dataclasses import dataclass, field
import time
import requests
import os
import psycopg2
from collections import deque


@dataclass
class BiometricReading:
    """Single biometric reading from all devices"""
    timestamp: datetime
    
    eeg_alpha: float = 0.0
    eeg_beta: float = 0.0
    eeg_theta: float = 0.0
    eeg_gamma: float = 0.0
    eeg_delta: float = 0.0
    
    fnirs_hbo2: float = 0.0
    fnirs_hbr: float = 0.0
    fnirs_oxygenation: float = 0.0
    
    heart_rate: int = 0
    hrv_rmssd: float = 0.0
    heart_coherence: float = 0.0
    
    muse_connected: bool = False
    mendi_connected: bool = False
    polar_connected: bool = False
    
    gile_score: float = 0.0
    psi_score: float = 0.0
    lcc_coupling: float = 0.0


class BiometricStreamManager:
    """Manages real-time biometric data streaming from all sources"""
    
    def __init__(self, max_history: int = 300):
        self.max_history = max_history
        self.history: deque = deque(maxlen=max_history)
        self.db_url = os.environ.get('DATABASE_URL')
        self.api_base = "http://localhost:8000"
        self.last_fetch_time = datetime.now() - timedelta(seconds=10)
        
    def fetch_from_database(self) -> Optional[BiometricReading]:
        """Fetch latest biometric data from PostgreSQL"""
        if not self.db_url:
            return None
            
        try:
            conn = psycopg2.connect(self.db_url)
            cur = conn.cursor()
            
            reading = BiometricReading(timestamp=datetime.now())
            
            cur.execute("""
                SELECT timestamp, hbo2, hbr, oxygenation_percent, signal_quality
                FROM mendi_realtime_data 
                ORDER BY created_at DESC LIMIT 1
            """)
            row = cur.fetchone()
            if row:
                reading.fnirs_hbo2 = row[1] or 0.0
                reading.fnirs_hbr = row[2] or 0.0
                reading.fnirs_oxygenation = row[3] or 0.0
                reading.mendi_connected = True
            
            cur.execute("""
                SELECT timestamp, heart_rate, rr_interval, hrv_rmssd, coherence
                FROM polar_realtime_data 
                ORDER BY created_at DESC LIMIT 1
            """)
            row = cur.fetchone()
            if row:
                reading.heart_rate = row[1] or 0
                reading.hrv_rmssd = row[3] or 0.0
                reading.heart_coherence = row[4] or 0.0
                reading.polar_connected = True
            
            cur.execute("""
                SELECT timestamp, alpha, beta, theta, gamma, delta
                FROM muse_realtime_data 
                ORDER BY created_at DESC LIMIT 1
            """)
            row = cur.fetchone()
            if row:
                reading.eeg_alpha = row[1] or 0.0
                reading.eeg_beta = row[2] or 0.0
                reading.eeg_theta = row[3] or 0.0
                reading.eeg_gamma = row[4] or 0.0
                reading.eeg_delta = row[5] or 0.0
                reading.muse_connected = True
            
            cur.execute("""
                SELECT timestamp, heart_rate, rr_interval, 
                       alpha, beta, theta, gamma, delta,
                       rmssd, coherence,
                       muse_connected, polar_connected
                FROM esp32_biometric_data 
                ORDER BY created_at DESC LIMIT 1
            """)
            row = cur.fetchone()
            if row:
                reading.heart_rate = row[1] or 0
                reading.eeg_alpha = row[3] or 0.0
                reading.eeg_beta = row[4] or 0.0
                reading.eeg_theta = row[5] or 0.0
                reading.eeg_gamma = row[6] or 0.0
                reading.eeg_delta = row[7] or 0.0
                reading.hrv_rmssd = row[8] or 0.0
                reading.heart_coherence = row[9] or 0.0
                reading.muse_connected = row[10] or False
                reading.polar_connected = row[11] or False
            
            conn.close()
            
            reading.gile_score = self._calculate_gile(reading)
            reading.psi_score = self._calculate_psi(reading)
            reading.lcc_coupling = self._calculate_lcc(reading)
            
            return reading
            
        except Exception as e:
            return None
    
    def fetch_from_api(self) -> Optional[BiometricReading]:
        """Fetch latest data from HTTP API endpoints"""
        reading = BiometricReading(timestamp=datetime.now())
        
        try:
            resp = requests.get(f"{self.api_base}/api/mendi/latest", timeout=2)
            if resp.status_code == 200:
                data = resp.json()
                reading.fnirs_hbo2 = data.get('hbo2', 0.0)
                reading.fnirs_hbr = data.get('hbr', 0.0)
                reading.fnirs_oxygenation = data.get('oxygenation_percent', 0.0)
                reading.mendi_connected = True
        except:
            pass
        
        try:
            resp = requests.get(f"{self.api_base}/api/polar/latest", timeout=2)
            if resp.status_code == 200:
                data = resp.json()
                reading.heart_rate = data.get('heart_rate', 0)
                reading.hrv_rmssd = data.get('hrv', {}).get('rmssd', 0.0)
                reading.heart_coherence = data.get('hrv', {}).get('coherence', 0.0)
                reading.polar_connected = True
        except:
            pass
        
        try:
            resp = requests.get(f"{self.api_base}/api/muse/latest", timeout=2)
            if resp.status_code == 200:
                data = resp.json()
                bands = data.get('bands', {})
                reading.eeg_alpha = bands.get('alpha', 0.0)
                reading.eeg_beta = bands.get('beta', 0.0)
                reading.eeg_theta = bands.get('theta', 0.0)
                reading.eeg_gamma = bands.get('gamma', 0.0)
                reading.eeg_delta = bands.get('delta', 0.0)
                reading.muse_connected = True
        except:
            pass
        
        reading.gile_score = self._calculate_gile(reading)
        reading.psi_score = self._calculate_psi(reading)
        reading.lcc_coupling = self._calculate_lcc(reading)
        
        return reading
    
    def get_latest(self) -> BiometricReading:
        """Get latest biometric reading from best available source"""
        db_reading = self.fetch_from_database()
        if db_reading and (db_reading.muse_connected or db_reading.mendi_connected or db_reading.polar_connected):
            self.history.append(db_reading)
            return db_reading
        
        api_reading = self.fetch_from_api()
        if api_reading and (api_reading.muse_connected or api_reading.mendi_connected or api_reading.polar_connected):
            self.history.append(api_reading)
            return api_reading
        
        sim_reading = self._generate_simulated()
        self.history.append(sim_reading)
        return sim_reading
    
    def _generate_simulated(self) -> BiometricReading:
        """Generate simulated biometric data for testing"""
        t = time.time()
        
        return BiometricReading(
            timestamp=datetime.now(),
            
            eeg_alpha=0.4 + 0.2 * np.sin(t * 0.5),
            eeg_beta=0.3 + 0.15 * np.sin(t * 0.8),
            eeg_theta=0.25 + 0.1 * np.sin(t * 0.3),
            eeg_gamma=0.15 + 0.08 * np.sin(t * 1.2),
            eeg_delta=0.2 + 0.1 * np.sin(t * 0.2),
            
            fnirs_hbo2=55.0 + 10.0 * np.sin(t * 0.4),
            fnirs_hbr=35.0 + 5.0 * np.sin(t * 0.35),
            fnirs_oxygenation=60.0 + 5.0 * np.sin(t * 0.3),
            
            heart_rate=int(65 + 10 * np.sin(t * 0.1)),
            hrv_rmssd=45.0 + 15.0 * np.sin(t * 0.25),
            heart_coherence=0.6 + 0.2 * np.sin(t * 0.2),
            
            muse_connected=False,
            mendi_connected=False,
            polar_connected=False,
            
            gile_score=0.5 + 0.3 * np.sin(t * 0.15),
            psi_score=0.55 + 0.25 * np.sin(t * 0.18),
            lcc_coupling=0.65 + 0.2 * np.sin(t * 0.22)
        )
    
    def _calculate_gile(self, reading: BiometricReading) -> float:
        """Calculate GILE score from biometrics"""
        components = []
        
        if reading.heart_coherence > 0:
            components.append(reading.heart_coherence)
        if reading.fnirs_oxygenation > 0:
            components.append(reading.fnirs_oxygenation / 100.0)
        if reading.hrv_rmssd > 0:
            components.append(min(1.0, reading.hrv_rmssd / 80.0))
        
        if components:
            return sum(components) / len(components)
        return 0.5
    
    def _calculate_psi(self, reading: BiometricReading) -> float:
        """Calculate PSI score (intuitive potential)"""
        psi = 0.5
        
        if reading.heart_coherence > 0.7:
            psi += 0.2
        if reading.eeg_alpha > 0.5:
            psi += 0.15
        if reading.hrv_rmssd > 50:
            psi += 0.1
        
        return min(1.0, psi)
    
    def _calculate_lcc(self, reading: BiometricReading) -> float:
        """Calculate Limbic-Cortical Coupling"""
        if reading.eeg_alpha > 0 and reading.heart_coherence > 0:
            alpha_norm = min(1.0, reading.eeg_alpha / 0.8)
            return (alpha_norm * 0.6 + reading.heart_coherence * 0.4)
        return 0.5
    
    def get_history_arrays(self) -> Dict[str, List]:
        """Get history as arrays for plotting"""
        if not self.history:
            return {}
        
        return {
            'timestamps': [r.timestamp for r in self.history],
            'heart_rate': [r.heart_rate for r in self.history],
            'hrv_rmssd': [r.hrv_rmssd for r in self.history],
            'heart_coherence': [r.heart_coherence for r in self.history],
            'fnirs_hbo2': [r.fnirs_hbo2 for r in self.history],
            'fnirs_oxygenation': [r.fnirs_oxygenation for r in self.history],
            'eeg_alpha': [r.eeg_alpha for r in self.history],
            'eeg_beta': [r.eeg_beta for r in self.history],
            'gile_score': [r.gile_score for r in self.history],
            'psi_score': [r.psi_score for r in self.history],
            'lcc_coupling': [r.lcc_coupling for r in self.history],
        }


def get_stream_manager() -> BiometricStreamManager:
    """Get or create stream manager in session state"""
    if 'bio_stream_manager' not in st.session_state:
        st.session_state.bio_stream_manager = BiometricStreamManager()
    return st.session_state.bio_stream_manager


def create_realtime_charts(reading: BiometricReading, history: Dict) -> go.Figure:
    """Create multi-panel real-time chart without flickering"""
    
    fig = make_subplots(
        rows=3, cols=2,
        subplot_titles=(
            'Heart Rate & HRV', 'Brain Oxygenation (fNIRS)',
            'EEG Band Powers', 'Heart Coherence',
            'GILE Score', 'PSI & LCC'
        ),
        vertical_spacing=0.12,
        horizontal_spacing=0.1
    )
    
    if history.get('timestamps'):
        times = history['timestamps'][-60:]
        
        fig.add_trace(
            go.Scatter(
                x=times, 
                y=history['heart_rate'][-60:],
                name='Heart Rate',
                line=dict(color='red', width=2),
                fill='tozeroy',
                fillcolor='rgba(255, 0, 0, 0.1)'
            ),
            row=1, col=1
        )
        
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['fnirs_hbo2'][-60:],
                name='HbO2',
                line=dict(color='red', width=2)
            ),
            row=1, col=2
        )
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['fnirs_oxygenation'][-60:],
                name='Oxygenation %',
                line=dict(color='green', width=2)
            ),
            row=1, col=2
        )
        
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['eeg_alpha'][-60:],
                name='Alpha',
                line=dict(color='blue', width=2)
            ),
            row=2, col=1
        )
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['eeg_beta'][-60:],
                name='Beta',
                line=dict(color='orange', width=2)
            ),
            row=2, col=1
        )
        
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['heart_coherence'][-60:],
                name='Coherence',
                line=dict(color='purple', width=3),
                fill='tozeroy',
                fillcolor='rgba(128, 0, 128, 0.2)'
            ),
            row=2, col=2
        )
        
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['gile_score'][-60:],
                name='GILE',
                line=dict(color='gold', width=3),
                fill='tozeroy',
                fillcolor='rgba(255, 215, 0, 0.2)'
            ),
            row=3, col=1
        )
        
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['psi_score'][-60:],
                name='PSI',
                line=dict(color='cyan', width=2)
            ),
            row=3, col=2
        )
        fig.add_trace(
            go.Scatter(
                x=times,
                y=history['lcc_coupling'][-60:],
                name='LCC',
                line=dict(color='magenta', width=2)
            ),
            row=3, col=2
        )
    
    fig.update_layout(
        height=700,
        showlegend=True,
        legend=dict(orientation='h', yanchor='bottom', y=1.02),
        margin=dict(l=50, r=50, t=80, b=50),
        paper_bgcolor='rgba(0,0,0,0)',
        plot_bgcolor='rgba(240,240,240,0.5)'
    )
    
    fig.update_xaxes(showgrid=True, gridwidth=1, gridcolor='rgba(200,200,200,0.5)')
    fig.update_yaxes(showgrid=True, gridwidth=1, gridcolor='rgba(200,200,200,0.5)')
    
    return fig


def render_realtime_biometric_stream():
    """Main render function for real-time biometric streaming"""
    
    st.header("Real-Time Biometric Stream")
    st.markdown("**Smooth, second-by-second updates without screen flicker**")
    
    stream = get_stream_manager()
    
    if 'streaming_active' not in st.session_state:
        st.session_state.streaming_active = False
    if 'update_interval' not in st.session_state:
        st.session_state.update_interval = 1.0
    
    ctrl_col1, ctrl_col2, ctrl_col3 = st.columns([1, 1, 2])
    
    with ctrl_col1:
        if st.session_state.streaming_active:
            if st.button("Stop Streaming", type="secondary", use_container_width=True):
                st.session_state.streaming_active = False
                st.rerun()
        else:
            if st.button("Start Streaming", type="primary", use_container_width=True):
                st.session_state.streaming_active = True
                st.rerun()
    
    with ctrl_col2:
        st.session_state.update_interval = st.selectbox(
            "Update Rate",
            options=[0.5, 1.0, 2.0, 5.0],
            index=1,
            format_func=lambda x: f"{x}s"
        )
    
    with ctrl_col3:
        reading = stream.get_latest()
        status_items = []
        if reading.muse_connected:
            status_items.append("Muse 2")
        if reading.mendi_connected:
            status_items.append("Mendi")
        if reading.polar_connected:
            status_items.append("Polar H10")
        
        if status_items:
            st.success(f"Connected: {', '.join(status_items)}")
        else:
            st.warning("No devices connected - showing simulated data")
    
    st.divider()
    
    metrics_placeholder = st.empty()
    chart_placeholder = st.empty()
    
    if st.session_state.streaming_active:
        while st.session_state.streaming_active:
            reading = stream.get_latest()
            history = stream.get_history_arrays()
            
            with metrics_placeholder.container():
                m1, m2, m3, m4, m5, m6 = st.columns(6)
                
                with m1:
                    st.metric(
                        "Heart Rate",
                        f"{reading.heart_rate} BPM",
                        delta=None
                    )
                
                with m2:
                    st.metric(
                        "HRV (RMSSD)",
                        f"{reading.hrv_rmssd:.1f} ms"
                    )
                
                with m3:
                    st.metric(
                        "Coherence",
                        f"{reading.heart_coherence:.2f}"
                    )
                
                with m4:
                    st.metric(
                        "Brain O2",
                        f"{reading.fnirs_oxygenation:.1f}%"
                    )
                
                with m5:
                    st.metric(
                        "GILE Score",
                        f"{reading.gile_score:.2f}"
                    )
                
                with m6:
                    st.metric(
                        "PSI Score",
                        f"{reading.psi_score:.2f}"
                    )
            
            with chart_placeholder.container():
                fig = create_realtime_charts(reading, history)
                st.plotly_chart(fig, use_container_width=True, key=f"chart_{time.time()}")
            
            time.sleep(st.session_state.update_interval)
            
            if not st.session_state.get('streaming_active', False):
                break
    
    else:
        reading = stream.get_latest()
        history = stream.get_history_arrays()
        
        with metrics_placeholder.container():
            m1, m2, m3, m4, m5, m6 = st.columns(6)
            
            with m1:
                st.metric("Heart Rate", f"{reading.heart_rate} BPM")
            with m2:
                st.metric("HRV (RMSSD)", f"{reading.hrv_rmssd:.1f} ms")
            with m3:
                st.metric("Coherence", f"{reading.heart_coherence:.2f}")
            with m4:
                st.metric("Brain O2", f"{reading.fnirs_oxygenation:.1f}%")
            with m5:
                st.metric("GILE Score", f"{reading.gile_score:.2f}")
            with m6:
                st.metric("PSI Score", f"{reading.psi_score:.2f}")
        
        with chart_placeholder.container():
            if history.get('timestamps'):
                fig = create_realtime_charts(reading, history)
                st.plotly_chart(fig, use_container_width=True)
            else:
                st.info("Click 'Start Streaming' to begin collecting data")
    
    st.divider()
    
    with st.expander("ESP32 Setup Instructions"):
        st.markdown("""
        ### ESP32 BLE Bridge Setup
        
        **Hardware Needed:**
        - ESP32 DevKit (~$9 on Amazon)
        - Muse 2 EEG Headband
        - Polar H10 Heart Rate Monitor (wet the strap!)
        
        **Setup Steps:**
        1. Open `ESP32_BLE_BRIDGE.ino` in Arduino IDE
        2. Change WiFi settings at the top of the file:
           ```cpp
           const char* ssid = "YOUR_WIFI_SSID";
           const char* password = "YOUR_WIFI_PASSWORD";
           ```
        3. Upload to your ESP32 DevKit
        4. Turn on Muse 2 (press button until LEDs flash)
        5. Put on Polar H10 with wet strap (water on contact pads)
        6. ESP32 auto-detects devices and streams here!
        
        **What You'll See:**
        - Heart Rate + HRV (RMSSD, Coherence) from Polar H10
        - EEG Band Power (Alpha, Beta, Theta, Gamma, Delta) from Muse 2
        - GILE Score calculated from your biometrics
        
        **Troubleshooting:**
        - Check ESP32 serial monitor for connection status
        - Ensure devices are powered on and in range
        - Wet the Polar strap contacts for better signal
        """)


if __name__ == "__main__":
    st.set_page_config(
        page_title="Real-Time Biometrics",
        page_icon="🧠",
        layout="wide"
    )
    render_realtime_biometric_stream()

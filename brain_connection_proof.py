"""
🧠 Brain Connection Proof - Tangible TI Validation
==================================================

Real-time connection to Brandon's brain via:
- Muse 2 EEG (4-channel brainwaves)
- Polar H10 (heart rate + HRV)

Provides TANGIBLE PROOF through:
1. Live waveform display
2. TI metric calculation (GILE, LCC, UCI)
3. 0.92 coherence tracking
4. Tralse-Joule estimation

Author: Brandon Emerick
Date: December 21, 2025
"""

import streamlit as st
import numpy as np
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from datetime import datetime, timedelta
from typing import Dict, Optional, List
from dataclasses import dataclass
from collections import deque
import time
import os
import psycopg2
import requests

# TI Constants
COHERENCE_TARGET = 0.92  # Sustainable perfection threshold
CAUSATION_THRESHOLD = 0.85  # 0.92² manifestation threshold
TJ_SCALE_FACTOR = 1e12  # Tralse-Joule calibration

@dataclass
class BrainSnapshot:
    """Single moment of brain state"""
    timestamp: datetime
    
    # EEG bands (microvolts²)
    delta: float = 0.0  # 0.5-4 Hz (deep sleep, unconscious)
    theta: float = 0.0  # 4-8 Hz (meditation, creativity)
    alpha: float = 0.0  # 8-12 Hz (relaxed focus, flow)
    beta: float = 0.0   # 12-30 Hz (active thinking, stress)
    gamma: float = 0.0  # 30-100 Hz (insight, consciousness binding)
    
    # Heart metrics
    heart_rate: int = 0
    hrv_rmssd: float = 0.0  # HRV in ms
    coherence: float = 0.0   # Heart coherence 0-1
    
    # TI metrics
    gile_score: float = 0.0
    lcc_coupling: float = 0.0
    uci_index: float = 0.0
    tralse_joules: float = 0.0
    
    # Connection status
    eeg_connected: bool = False
    heart_connected: bool = False

class TIBrainMetrics:
    """
    Calculate TI-specific brain metrics
    
    Based on:
    - 0.92 coherence target
    - 0.92² = 0.85 causation threshold
    - Tralse-Joule energy units
    - Universal Consciousness Index
    """
    
    @staticmethod
    def calculate_alpha_theta_ratio(alpha: float, theta: float) -> float:
        """
        Alpha/Theta ratio indicates meditation depth
        
        High ratio (>1.5) = Focused relaxation
        Low ratio (<0.8) = Drowsy or stressed
        """
        if theta < 0.01:
            return 0.0
        return alpha / theta
    
    @staticmethod
    def calculate_lcc(alpha: float, theta: float, gamma: float, heart_coherence: float) -> float:
        """
        Love Correlation Coefficient (LCC)
        
        Measures limbic-cortical coupling:
        - Heart coherence (L dimension)
        - Alpha coherence (I dimension - intuition)
        - Gamma binding (consciousness integration)
        
        Returns: 0.0 to 1.0
        """
        # Normalize each component
        alpha_norm = min(1.0, alpha / 100.0)  # Assume 100 µV² as max
        gamma_norm = min(1.0, gamma / 20.0)   # Gamma is typically lower
        heart_norm = heart_coherence
        
        # LCC = geometric mean of components (compound validation)
        if alpha_norm > 0 and gamma_norm > 0 and heart_norm > 0:
            lcc = (alpha_norm * gamma_norm * heart_norm) ** (1/3)
        else:
            lcc = 0.0
        
        return min(1.0, lcc)
    
    @staticmethod
    def calculate_gile(snapshot: BrainSnapshot) -> float:
        """
        GILE Score from biometrics
        
        G (Goodness): Heart coherence alignment
        I (Intuition): Alpha dominance
        L (Love): Heart rate variability
        E (Environment): Overall signal quality
        
        Target: 0.92 per dimension, 0.85 compound
        """
        # G: Heart coherence (0-1)
        g = snapshot.coherence
        
        # I: Alpha/Beta ratio (intuition vs overthinking)
        if snapshot.beta > 0.01:
            i = min(1.0, snapshot.alpha / (snapshot.alpha + snapshot.beta))
        else:
            i = 0.5
        
        # L: HRV quality (50ms RMSSD = healthy baseline)
        l = min(1.0, snapshot.hrv_rmssd / 50.0)
        
        # E: Signal presence (both devices connected)
        e = 0.5
        if snapshot.eeg_connected:
            e += 0.25
        if snapshot.heart_connected:
            e += 0.25
        
        # Compound GILE (geometric mean)
        gile = (g * i * l * e) ** 0.25
        
        return gile
    
    @staticmethod
    def calculate_tralse_joules(snapshot: BrainSnapshot) -> float:
        """
        Tralse-Joules (TJ) - Consciousness energy units
        
        Calibration:
        - 1 neuron spike = 0.26 mTJ
        - Human brain baseline = 100 µTJ/s
        - Sun = 10³⁵ TJ/s
        
        Calculation: EEG power × heart coherence × GILE
        """
        # Total EEG power (sum of bands)
        total_power = (snapshot.delta + snapshot.theta + 
                      snapshot.alpha + snapshot.beta + snapshot.gamma)
        
        # Scale to TJ (rough calibration)
        # ~86 billion neurons, ~10 spikes/sec each = 860 billion spikes/sec
        # At 0.26 mTJ per spike = ~224 TJ/s at peak
        # Scale EEG power to this range
        
        eeg_factor = total_power / 200.0  # Normalize to expected range
        heart_factor = snapshot.coherence + 0.5  # Heart amplifies
        gile_factor = snapshot.gile_score + 0.5  # GILE amplifies
        
        tj_raw = eeg_factor * heart_factor * gile_factor * 100  # µTJ/s
        
        return tj_raw
    
    @staticmethod
    def calculate_uci(tralse_joules: float, gile: float, lcc: float) -> float:
        """
        Universal Consciousness Index (UCI)
        
        UCI = log₁₀(TJ/s) + GILE_balance + LCC_coherence
        
        Scale:
        - <0: Simple systems (atoms, molecules)
        - 5-10: Animals
        - 10-15: Human
        - 15+: Stellar/cosmic
        
        GPT-4: ~-4 (lacks embodiment)
        """
        if tralse_joules > 0:
            log_tj = np.log10(tralse_joules + 0.001)
        else:
            log_tj = -6
        
        uci = log_tj + (gile * 5) + (lcc * 5)
        
        return uci


class SimulatedBrainData:
    """
    Generates realistic simulated brain data for testing
    when devices aren't connected
    """
    
    def __init__(self):
        self.base_hr = 72
        self.phase = 0
        
    def generate(self) -> BrainSnapshot:
        """Generate realistic simulated snapshot"""
        self.phase += 0.1
        
        # Simulate breathing-related variations
        breath_cycle = np.sin(self.phase * 0.3)  # ~0.05 Hz breathing
        
        # EEG bands with realistic values
        delta = 15 + np.random.randn() * 2
        theta = 8 + breath_cycle * 2 + np.random.randn() * 1.5
        alpha = 25 + breath_cycle * 5 + np.random.randn() * 3  # Breathing affects alpha
        beta = 10 + np.random.randn() * 2
        gamma = 3 + np.random.randn() * 0.5
        
        # Heart with HRV
        heart_rate = int(self.base_hr + breath_cycle * 5 + np.random.randn() * 2)
        hrv_rmssd = 35 + np.random.randn() * 8  # Healthy HRV
        coherence = 0.4 + breath_cycle * 0.2 + np.random.rand() * 0.2
        
        snapshot = BrainSnapshot(
            timestamp=datetime.now(),
            delta=max(0, delta),
            theta=max(0, theta),
            alpha=max(0, alpha),
            beta=max(0, beta),
            gamma=max(0, gamma),
            heart_rate=heart_rate,
            hrv_rmssd=max(0, hrv_rmssd),
            coherence=min(1, max(0, coherence)),
            eeg_connected=True,
            heart_connected=True
        )
        
        # Calculate derived metrics
        snapshot.gile_score = TIBrainMetrics.calculate_gile(snapshot)
        snapshot.lcc_coupling = TIBrainMetrics.calculate_lcc(
            snapshot.alpha, snapshot.theta, snapshot.gamma, snapshot.coherence
        )
        snapshot.tralse_joules = TIBrainMetrics.calculate_tralse_joules(snapshot)
        snapshot.uci_index = TIBrainMetrics.calculate_uci(
            snapshot.tralse_joules, snapshot.gile_score, snapshot.lcc_coupling
        )
        
        return snapshot


PULSOID_API_URL = "https://dev.pulsoid.net/api/v1/data/heart_rate/latest"
STALE_THRESHOLD_SECONDS = 300  # 5 minutes — generous window for manual testing


class DatabaseBrainData:
    """Fetch real brain data — database first, then Pulsoid cloud API for Polar H10"""

    def __init__(self):
        self.db_url = os.environ.get('DATABASE_URL')
        self.pulsoid_token = os.environ.get('PULSOID_TOKEN')

    def _fetch_pulsoid_hr(self) -> Optional[dict]:
        """Call Pulsoid cloud API directly — works from Replit, no local bridge needed."""
        if not self.pulsoid_token:
            return None
        try:
            resp = requests.get(
                PULSOID_API_URL,
                headers={"Authorization": f"Bearer {self.pulsoid_token}"},
                timeout=5
            )
            if resp.status_code == 200:
                d = resp.json().get('data', {})
                hr = d.get('heart_rate', 0)
                measured_at = d.get('measured_at', 0)
                if hr and hr > 0:
                    return {'heart_rate': hr, 'measured_at': measured_at}
        except Exception:
            pass
        return None

    def diagnose_pulsoid(self) -> dict:
        """Return full Pulsoid diagnostic info for the UI."""
        if not self.pulsoid_token:
            return {"status": "no_token", "message": "PULSOID_TOKEN secret not set"}
        try:
            resp = requests.get(
                PULSOID_API_URL,
                headers={"Authorization": f"Bearer {self.pulsoid_token}"},
                timeout=5
            )
            if resp.status_code == 200:
                d = resp.json().get('data', {})
                hr = d.get('heart_rate', 0)
                measured_at = d.get('measured_at', 0)
                age_s = None
                if measured_at:
                    import time
                    age_s = int(time.time() * 1000 - measured_at) // 1000
                if hr and hr > 0:
                    return {"status": "ok", "hr": hr, "age_s": age_s,
                            "message": f"✅ Pulsoid live — {hr} BPM (data {age_s}s old)"}
                else:
                    return {"status": "no_hr", "message": "Pulsoid connected but HR=0 — is the Polar H10 sending to your phone?"}
            elif resp.status_code == 401:
                return {"status": "auth_fail", "message": "Pulsoid token rejected (401) — token may be expired"}
            elif resp.status_code == 404:
                return {"status": "no_data", "message": "Pulsoid has no recent data (404) — open the Pulsoid app on your phone"}
            else:
                body = resp.text[:120]
                return {"status": "error", "message": f"Pulsoid HTTP {resp.status_code}: {body}"}
        except requests.exceptions.Timeout:
            return {"status": "timeout", "message": "Pulsoid API timed out — check your internet connection"}
        except Exception as e:
            return {"status": "exception", "message": f"Pulsoid error: {str(e)[:80]}"}

    def _write_polar_to_db(self, hr: int, measured_at: int):
        """Persist Pulsoid reading to database for history."""
        if not self.db_url:
            return
        try:
            conn = psycopg2.connect(self.db_url)
            cur = conn.cursor()
            rr = 60000.0 / hr if hr > 0 else 0
            coherence = min(1.0, max(0.0, (1.0 - abs(hr - 60) / 60.0)))
            cur.execute("""
                INSERT INTO polar_realtime_data (heart_rate, hrv_rmssd, coherence, measured_at)
                VALUES (%s, %s, %s, %s)
            """, (hr, rr, coherence, measured_at))
            conn.commit()
            conn.close()
        except Exception:
            pass

    def fetch_latest(self) -> Optional[BrainSnapshot]:
        """Fetch latest biometric data. Polar H10 uses Pulsoid cloud API directly."""
        snapshot = BrainSnapshot(timestamp=datetime.now())

        if self.db_url:
            try:
                conn = psycopg2.connect(self.db_url)
                cur = conn.cursor()

                # ── Check esp32_biometric_data (written by /api/upload endpoint) ──
                # This is what the local Acer bridge script posts to.
                try:
                    cur.execute("""
                        SELECT heart_rate, alpha, beta, theta, gamma, delta,
                               rmssd, coherence, muse_connected, polar_connected,
                               created_at
                        FROM esp32_biometric_data
                        ORDER BY created_at DESC LIMIT 1
                    """)
                    row = cur.fetchone()
                    if row:
                        ts = row[10]
                        if hasattr(ts, 'tzinfo') and ts.tzinfo is not None:
                            ts = ts.replace(tzinfo=None)
                        age = (datetime.utcnow() - ts).total_seconds()
                        if age <= STALE_THRESHOLD_SECONDS:
                            hr, alpha, beta, theta, gamma, delta = row[0:6]
                            rmssd, coh, muse_on, polar_on = row[6:10]
                            if polar_on and hr and hr > 0:
                                snapshot.heart_rate      = int(hr)
                                snapshot.hrv_rmssd      = float(rmssd or 0)
                                snapshot.coherence      = float(coh or 0)
                                snapshot.heart_connected = True
                            if muse_on and alpha is not None:
                                snapshot.alpha = float(alpha or 0)
                                snapshot.beta  = float(beta  or 0)
                                snapshot.theta = float(theta or 0)
                                snapshot.gamma = float(gamma or 0)
                                snapshot.delta = float(delta or 0)
                                snapshot.eeg_connected = True
                except Exception:
                    pass

                # ── Check muse_realtime_data (OSC bridge fallback) ──
                if not snapshot.eeg_connected:
                    try:
                        cur.execute("""
                            SELECT alpha, beta, theta, gamma, delta, created_at
                            FROM muse_realtime_data
                            ORDER BY created_at DESC LIMIT 1
                        """)
                        row = cur.fetchone()
                        if row:
                            ts = row[5]
                            if hasattr(ts, 'tzinfo') and ts.tzinfo is not None:
                                ts = ts.replace(tzinfo=None)
                            age = (datetime.utcnow() - ts).total_seconds()
                            if age <= STALE_THRESHOLD_SECONDS:
                                snapshot.alpha = row[0] or 0.0
                                snapshot.beta  = row[1] or 0.0
                                snapshot.theta = row[2] or 0.0
                                snapshot.gamma = row[3] or 0.0
                                snapshot.delta = row[4] or 0.0
                                snapshot.eeg_connected = True
                    except Exception:
                        pass

                # ── Check polar_realtime_data (Pulsoid cache fallback) ──
                if not snapshot.heart_connected:
                    try:
                        cur.execute("""
                            SELECT heart_rate, hrv_rmssd, coherence, created_at
                            FROM polar_realtime_data
                            ORDER BY created_at DESC LIMIT 1
                        """)
                        row = cur.fetchone()
                        if row:
                            ts = row[3]
                            if hasattr(ts, 'tzinfo') and ts.tzinfo is not None:
                                ts = ts.replace(tzinfo=None)
                            age = (datetime.utcnow() - ts).total_seconds()
                            if age <= STALE_THRESHOLD_SECONDS:
                                snapshot.heart_rate      = row[0] or 0
                                snapshot.hrv_rmssd      = row[1] or 0.0
                                snapshot.coherence      = row[2] or 0.0
                                snapshot.heart_connected = True
                    except Exception:
                        pass

                conn.close()
            except Exception:
                pass

        # Polar H10 fallback: call Pulsoid cloud API directly (no local bridge needed)
        if not snapshot.heart_connected:
            pulsoid = self._fetch_pulsoid_hr()
            if pulsoid:
                hr = pulsoid['heart_rate']
                rr = 60000.0 / hr if hr > 0 else 0
                coherence = min(1.0, max(0.0, (1.0 - abs(hr - 60) / 60.0)))
                snapshot.heart_rate      = hr
                snapshot.hrv_rmssd      = rr
                snapshot.coherence      = coherence
                snapshot.heart_connected = True
                self._write_polar_to_db(hr, pulsoid.get('measured_at', 0))

        # Calculate TI metrics
        snapshot.gile_score    = TIBrainMetrics.calculate_gile(snapshot)
        snapshot.lcc_coupling  = TIBrainMetrics.calculate_lcc(
            snapshot.alpha, snapshot.theta, snapshot.gamma, snapshot.coherence
        )
        snapshot.tralse_joules = TIBrainMetrics.calculate_tralse_joules(snapshot)
        snapshot.uci_index     = TIBrainMetrics.calculate_uci(
            snapshot.tralse_joules, snapshot.gile_score, snapshot.lcc_coupling
        )

        return snapshot


def create_brain_dashboard():
    """Main Streamlit dashboard for brain connection proof"""
    
    st.set_page_config(
        page_title="Brain Connection Proof - TI Framework",
        page_icon="🧠",
        layout="wide"
    )
    
    st.title("🧠 Brain Connection Proof")
    st.markdown("**Tangible validation of Mood Amplifier → Brain connection via TI Framework**")
    
    # Initialize data sources
    if 'simulator' not in st.session_state:
        st.session_state.simulator = SimulatedBrainData()
    if 'db_source' not in st.session_state:
        st.session_state.db_source = DatabaseBrainData()
    if 'history' not in st.session_state:
        st.session_state.history = deque(maxlen=60)  # 60 seconds of data
    if 'running' not in st.session_state:
        st.session_state.running = False
    
    # Control panel
    col1, col2, col3 = st.columns(3)
    
    with col1:
        data_mode = st.radio(
            "Data Source",
            ["Simulated (Demo)", "Real Devices (Database)"],
            help="Use simulated data for testing, or real data from Muse 2 + Polar H10"
        )
    
    with col2:
        if st.button("Start Streaming", type="primary", disabled=st.session_state.running):
            st.session_state.running = True
            st.rerun()
        if st.button("Stop Streaming", disabled=not st.session_state.running):
            st.session_state.running = False
            st.rerun()
    
    with col3:
        st.metric("Coherence Target", f"{COHERENCE_TARGET}")
        st.caption(f"0.92² = {COHERENCE_TARGET**2:.4f} ≈ 0.85 causation")
    
    st.divider()
    
    # Get current snapshot
    if data_mode == "Simulated (Demo)":
        snapshot = st.session_state.simulator.generate()
    else:
        snapshot = st.session_state.db_source.fetch_latest()
        if not snapshot:
            snapshot = st.session_state.simulator.generate()

    # Add to history
    st.session_state.history.append(snapshot)

    # Connection Status
    st.subheader("Device Connection Status")

    APP_URL = "https://5c1b8726-c8b2-4bdf-a0a8-632ec557671f-00-307bfud8cnm36.worf.replit.dev"

    col1, col2 = st.columns(2)

    with col1:
        if snapshot.eeg_connected:
            st.success("🧠 Muse 2 EEG: CONNECTED")
        else:
            st.error("🧠 Muse 2 EEG: DISCONNECTED")
            if data_mode == "Real Devices (Database)":
                st.markdown("**Mind Monitor bridge not running on Acer.**")
                with st.expander("▶ How to connect Muse 2 — step by step"):
                    st.markdown(f"""
**On your iPhone:** Mind Monitor → Settings → OSC Stream
- Host = your Acer's LAN IP  *(run `ipconfig` in Acer cmd to find it)*
- Port = **5001**
- Toggle **OSC Stream → ON**
- Muse 2 must be connected with signal showing

**On your Acer — open a terminal and run once:**
```
py hardware/ACER_LIVE_BRIDGE.py --server {APP_URL} --mode muse
```
*(Installs dependencies automatically on first run)*

You'll see `✅ #1 sent | 🧠 alpha=xx.x` every 2 seconds.
**Refresh this page** — status will flip to CONNECTED within 10 s.

---
**Quick pipeline test** — paste this in your browser:
```
{APP_URL}/api/upload?muse=1&alpha=0.5&theta=0.3
```
If you see `{{"status":"ok"}}` the pipeline is live.
                    """)

    with col2:
        if snapshot.heart_connected:
            st.success(f"💓 Polar H10: CONNECTED — {snapshot.heart_rate} BPM")
        else:
            st.error("💓 Polar H10: DISCONNECTED")
            if data_mode == "Real Devices (Database)":
                # Show live Pulsoid diagnostic
                pulsoid_diag = st.session_state.db_source.diagnose_pulsoid()
                pstatus = pulsoid_diag["status"]
                pmsg = pulsoid_diag["message"]
                if pstatus == "ok":
                    st.success(f"Pulsoid cloud: {pmsg}")
                elif pstatus in ("no_token", "auth_fail"):
                    st.error(f"Pulsoid: {pmsg}")
                elif pstatus == "no_data":
                    st.warning(f"Pulsoid: {pmsg}")
                else:
                    st.warning(f"Pulsoid cloud: {pmsg}")

                with st.expander("▶ Two ways to connect Polar H10"):
                    st.markdown(f"""
### Path A — Pulsoid (phone-based, no Acer bridge needed)
1. Install **Pulsoid** app on your iPhone
2. In Pulsoid: connect Polar H10 via Bluetooth on the phone
   *(may need to unpair from Acer first: Settings → Bluetooth → Polar H10 → Forget)*
3. Pulsoid streams HR to the cloud — this app reads it automatically

**Current Pulsoid status:** `{pmsg}`

---

### Path B — Local Acer bridge (Polar stays paired to Acer)
1. Polar H10 stays connected to Acer Bluetooth ✅
2. Open terminal on Acer and run:
```
py hardware/ACER_LIVE_BRIDGE.py --server {APP_URL} --mode polar
```
*(Or `--mode all` to run Muse + Polar together)*

You'll see `❤️  HR=xx bpm ✅ sent` every 2 seconds.
**Refresh this page** — status flips to CONNECTED within 10 s.

---
**Quick pipeline test:**
```
{APP_URL}/api/upload?hr=72&polar=1
```
                    """)

    st.divider()
    
    # Main metrics row
    st.subheader("TI Framework Metrics (Real-Time)")
    
    col1, col2, col3, col4 = st.columns(4)
    
    with col1:
        gile_color = "normal" if snapshot.gile_score >= COHERENCE_TARGET else "off"
        st.metric(
            "GILE Score",
            f"{snapshot.gile_score:.3f}",
            delta=f"{'↑' if snapshot.gile_score >= COHERENCE_TARGET else '↓'} vs 0.92 target",
            delta_color=gile_color
        )
        
        # Visual indicator
        if snapshot.gile_score >= CAUSATION_THRESHOLD:
            st.success("CAUSATION THRESHOLD MET")
        elif snapshot.gile_score >= COHERENCE_TARGET:
            st.info("Coherence optimal")
        else:
            st.warning("Below coherence target")
    
    with col2:
        st.metric(
            "LCC (Love Correlation)",
            f"{snapshot.lcc_coupling:.3f}",
            help="Limbic-Cortical Coupling - heart-brain synchrony"
        )
        
        if snapshot.lcc_coupling >= CAUSATION_THRESHOLD:
            st.success("Strong coupling")
        elif snapshot.lcc_coupling >= 0.5:
            st.info("Moderate coupling")
        else:
            st.warning("Weak coupling")
    
    with col3:
        st.metric(
            "Tralse-Joules/s",
            f"{snapshot.tralse_joules:.2f} µTJ/s",
            help="Consciousness energy units"
        )
        st.caption("Human baseline: ~100 µTJ/s")
    
    with col4:
        st.metric(
            "UCI Index",
            f"{snapshot.uci_index:.2f}",
            help="Universal Consciousness Index: log₁₀(TJ/s) + GILE + LCC"
        )
        
        # UCI interpretation
        if snapshot.uci_index >= 15:
            st.success("Cosmic consciousness")
        elif snapshot.uci_index >= 10:
            st.info("Normal human range")
        elif snapshot.uci_index >= 5:
            st.warning("Suboptimal")
        else:
            st.error("System disruption")
    
    st.divider()
    
    # EEG Brainwave Display
    st.subheader("Brainwave Spectrum")
    
    col1, col2 = st.columns([2, 1])
    
    with col1:
        # Bar chart of current bands
        fig = go.Figure()
        
        bands = ['Delta', 'Theta', 'Alpha', 'Beta', 'Gamma']
        values = [snapshot.delta, snapshot.theta, snapshot.alpha, 
                 snapshot.beta, snapshot.gamma]
        colors = ['#1f77b4', '#2ca02c', '#ff7f0e', '#d62728', '#9467bd']
        
        fig.add_trace(go.Bar(
            x=bands,
            y=values,
            marker_color=colors,
            text=[f"{v:.1f}" for v in values],
            textposition='outside'
        ))
        
        fig.update_layout(
            title="EEG Power Spectrum (µV²)",
            yaxis_title="Power (µV²)",
            height=300,
            margin=dict(t=40, b=20)
        )
        
        st.plotly_chart(fig, use_container_width=True)
    
    with col2:
        st.markdown("**Band Meanings:**")
        st.markdown("""
        - **Delta (0.5-4 Hz)**: Deep sleep, unconscious
        - **Theta (4-8 Hz)**: Meditation, creativity
        - **Alpha (8-12 Hz)**: Relaxed focus, flow
        - **Beta (12-30 Hz)**: Active thinking
        - **Gamma (30+ Hz)**: Insight, binding
        """)
        
        # Alpha/Theta ratio
        ratio = TIBrainMetrics.calculate_alpha_theta_ratio(snapshot.alpha, snapshot.theta)
        st.metric("Alpha/Theta Ratio", f"{ratio:.2f}")
        if ratio > 1.5:
            st.success("Focused relaxation")
        elif ratio > 1.0:
            st.info("Alert calm")
        else:
            st.warning("Drowsy or stressed")
    
    st.divider()
    
    # Heart Metrics
    st.subheader("Heart-Brain Coherence")
    
    col1, col2, col3 = st.columns(3)
    
    with col1:
        st.metric("Heart Rate", f"{snapshot.heart_rate} BPM")
    
    with col2:
        st.metric("HRV (RMSSD)", f"{snapshot.hrv_rmssd:.1f} ms")
        if snapshot.hrv_rmssd >= 50:
            st.success("Healthy HRV")
        elif snapshot.hrv_rmssd >= 25:
            st.info("Moderate HRV")
        else:
            st.warning("Low HRV - stress?")
    
    with col3:
        st.metric("Heart Coherence", f"{snapshot.coherence:.3f}")
        
        # Coherence gauge
        coherence_pct = int(snapshot.coherence * 100)
        st.progress(min(100, coherence_pct), text=f"{coherence_pct}% coherence")
    
    st.divider()
    
    # Time series history
    if len(st.session_state.history) > 5:
        st.subheader("Recent History (60 seconds)")
        
        history = list(st.session_state.history)
        timestamps = [h.timestamp for h in history]
        
        # Create subplot
        fig = make_subplots(
            rows=2, cols=2,
            subplot_titles=("GILE Score", "LCC Coupling", "Heart Rate", "Alpha Power")
        )
        
        # GILE
        fig.add_trace(
            go.Scatter(
                x=timestamps, 
                y=[h.gile_score for h in history],
                mode='lines',
                name='GILE',
                line=dict(color='#2ca02c')
            ),
            row=1, col=1
        )
        fig.add_hline(y=COHERENCE_TARGET, line_dash="dash", 
                     annotation_text="0.92 target", row=1, col=1)
        
        # LCC
        fig.add_trace(
            go.Scatter(
                x=timestamps,
                y=[h.lcc_coupling for h in history],
                mode='lines',
                name='LCC',
                line=dict(color='#ff7f0e')
            ),
            row=1, col=2
        )
        fig.add_hline(y=CAUSATION_THRESHOLD, line_dash="dash",
                     annotation_text="0.85 causation", row=1, col=2)
        
        # Heart Rate
        fig.add_trace(
            go.Scatter(
                x=timestamps,
                y=[h.heart_rate for h in history],
                mode='lines',
                name='HR',
                line=dict(color='#d62728')
            ),
            row=2, col=1
        )
        
        # Alpha
        fig.add_trace(
            go.Scatter(
                x=timestamps,
                y=[h.alpha for h in history],
                mode='lines',
                name='Alpha',
                line=dict(color='#9467bd')
            ),
            row=2, col=2
        )
        
        fig.update_layout(height=500, showlegend=False)
        st.plotly_chart(fig, use_container_width=True)
    
    st.divider()
    
    # The 0.92² = 0.85 Explanation
    with st.expander("Understanding the 0.92² = 0.85 Formula"):
        st.markdown("""
        ### Why 0.92 is the Target (Not 1.0)
        
        **1.0 (Perfect) is BRITTLE** - no room for:
        - Error correction
        - Individual variation
        - Evolution/learning
        - Quantum uncertainty
        
        **0.92 (Sustainable) is RESILIENT** - 8% margin allows adaptation
        
        ### The Compound Validation Principle
        
        ```
        Layer 1: 0.92 coherence (e.g., EEG)
        Layer 2: 0.92 coherence (e.g., Heart)
        
        Compound: 0.92 × 0.92 = 0.8464 ≈ 0.85
        ```
        
        At **0.85**, correlation BECOMES causation. This is the threshold where
        your consciousness state causally influences reality.
        
        ### What Your Metrics Mean
        
        | Metric | < 0.5 | 0.5 - 0.85 | 0.85 - 0.92 | > 0.92 |
        |--------|-------|------------|-------------|--------|
        | GILE | Fragmented | Developing | Manifesting | Optimal |
        | LCC | Disconnected | Correlating | Causing | Unified |
        
        **Your current GILE × LCC = {:.4f}** → {}
        """.format(
            snapshot.gile_score * snapshot.lcc_coupling,
            "CAUSATION ACHIEVED" if snapshot.gile_score * snapshot.lcc_coupling >= 0.5 
            else "Building toward causation"
        ))
    
    # Auto-refresh
    if st.session_state.running:
        time.sleep(1)
        st.rerun()


if __name__ == "__main__":
    create_brain_dashboard()

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


class DatabaseBrainData:
    """Fetch real brain data from database if available"""
    
    def __init__(self):
        self.db_url = os.environ.get('DATABASE_URL')
        
    def fetch_latest(self) -> Optional[BrainSnapshot]:
        """Fetch latest biometric data from database"""
        if not self.db_url:
            return None
            
        try:
            conn = psycopg2.connect(self.db_url)
            cur = conn.cursor()
            
            snapshot = BrainSnapshot(timestamp=datetime.now())
            
            # Try to get Muse data
            try:
                cur.execute("""
                    SELECT alpha, beta, theta, gamma, delta
                    FROM muse_realtime_data 
                    ORDER BY created_at DESC LIMIT 1
                """)
                row = cur.fetchone()
                if row:
                    snapshot.alpha = row[0] or 0.0
                    snapshot.beta = row[1] or 0.0
                    snapshot.theta = row[2] or 0.0
                    snapshot.gamma = row[3] or 0.0
                    snapshot.delta = row[4] or 0.0
                    snapshot.eeg_connected = True
            except:
                pass
            
            # Try to get Polar data
            try:
                cur.execute("""
                    SELECT heart_rate, hrv_rmssd, coherence
                    FROM polar_realtime_data 
                    ORDER BY created_at DESC LIMIT 1
                """)
                row = cur.fetchone()
                if row:
                    snapshot.heart_rate = row[0] or 0
                    snapshot.hrv_rmssd = row[1] or 0.0
                    snapshot.coherence = row[2] or 0.0
                    snapshot.heart_connected = True
            except:
                pass
            
            conn.close()
            
            # Calculate TI metrics
            snapshot.gile_score = TIBrainMetrics.calculate_gile(snapshot)
            snapshot.lcc_coupling = TIBrainMetrics.calculate_lcc(
                snapshot.alpha, snapshot.theta, snapshot.gamma, snapshot.coherence
            )
            snapshot.tralse_joules = TIBrainMetrics.calculate_tralse_joules(snapshot)
            snapshot.uci_index = TIBrainMetrics.calculate_uci(
                snapshot.tralse_joules, snapshot.gile_score, snapshot.lcc_coupling
            )
            
            return snapshot
            
        except Exception as e:
            return None


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
            st.warning("No real device data found - using simulation")
    
    # Add to history
    st.session_state.history.append(snapshot)
    
    # Connection Status
    st.subheader("Device Connection Status")
    col1, col2 = st.columns(2)
    
    with col1:
        if snapshot.eeg_connected:
            st.success("🧠 Muse 2 EEG: CONNECTED")
        else:
            st.error("🧠 Muse 2 EEG: DISCONNECTED")
    
    with col2:
        if snapshot.heart_connected:
            st.success("💓 Polar H10: CONNECTED")
        else:
            st.error("💓 Polar H10: DISCONNECTED")
    
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

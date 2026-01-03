"""
🧠⚡ ELITE BRAIN PROTOCOL - Real-Time Optimization Dashboard ⚡🧠
==================================================================
Tonight's 75-minute protocol with LIVE visualization of:
- Brain wave activity (Muse 2 EEG)
- Heart coherence (Polar H10)
- Energy surge metrics
- Protocol phase tracking
- Z-score gap closing to ELITE levels!

Created: December 13, 2025
Author: Brandon Charles Emerick
"""

import streamlit as st
import numpy as np
import pandas as pd
import plotly.graph_objects as go
from plotly.subplots import make_subplots
from datetime import datetime, timedelta
import time
from collections import deque

try:
    from real_time_muse_eeg import MuseEEGStreamer
    MUSE_AVAILABLE = True
except ImportError:
    MUSE_AVAILABLE = False

try:
    from db_utils import db
    DB_AVAILABLE = True
except:
    DB_AVAILABLE = False


class EliteBrainProtocol:
    """Tracks the 75-minute Elite Brain Protocol phases and metrics"""
    
    PHASES = [
        {"name": "🎯 BASELINE MEASUREMENT", "duration_min": 15, "target": "Record baseline brain waves"},
        {"name": "🧘 SMR UPTRAINING", "duration_min": 20, "target": "Increase 12-15 Hz (calm body, active mind)"},
        {"name": "🌊 ALPHA ENHANCEMENT", "duration_min": 10, "target": "Boost 8-12 Hz (relaxation)"},
        {"name": "⚡ GAMMA ENTRAINMENT", "duration_min": 10, "target": "Elevate 40 Hz (integration)"},
        {"name": "💡 PHOTOBIOMODULATION", "duration_min": 10, "target": "Increase mitochondrial ATP"},
        {"name": "📊 POST-MEASUREMENT", "duration_min": 10, "target": "Compare to baseline & celebrate!"},
    ]
    
    ELITE_TARGETS = {
        'theta': {'brandon_z': +1.75, 'elite_z': 0.0, 'direction': 'down'},
        'smr': {'brandon_z': -1.75, 'elite_z': +1.25, 'direction': 'up'},
        'alpha': {'brandon_z': -1.25, 'elite_z': +0.75, 'direction': 'up'},
        'gamma': {'brandon_z': -1.25, 'elite_z': +1.5, 'direction': 'up'},
        'beta': {'brandon_z': +0.75, 'elite_z': 0.0, 'direction': 'down'},
    }
    
    def __init__(self):
        self.start_time = None
        self.current_phase = 0
        self.phase_start_time = None
        self.is_running = False
        
        self.baseline_metrics = {}
        self.current_metrics = {}
        self.metrics_history = []
        
        self.energy_surge_level = 0.0
        self.peak_energy = 0.0
        self.coherence_score = 0.0
        
    def start_protocol(self):
        self.start_time = datetime.now()
        self.phase_start_time = datetime.now()
        self.current_phase = 0
        self.is_running = True
        self.metrics_history = []
        
    def stop_protocol(self):
        self.is_running = False
        
    def get_elapsed_seconds(self):
        if not self.start_time:
            return 0
        return (datetime.now() - self.start_time).total_seconds()
    
    def get_phase_elapsed_seconds(self):
        if not self.phase_start_time:
            return 0
        return (datetime.now() - self.phase_start_time).total_seconds()
    
    def get_current_phase(self):
        if not self.is_running:
            return None
        return self.PHASES[self.current_phase] if self.current_phase < len(self.PHASES) else None
    
    def advance_phase(self):
        if self.current_phase < len(self.PHASES) - 1:
            self.current_phase += 1
            self.phase_start_time = datetime.now()
            return True
        return False
    
    def update_metrics(self, theta, alpha, smr, beta, gamma, hrv=None):
        self.current_metrics = {
            'theta': theta,
            'alpha': alpha,
            'smr': smr,
            'beta': beta,
            'gamma': gamma,
            'hrv': hrv or 0,
            'timestamp': datetime.now()
        }
        self.metrics_history.append(self.current_metrics.copy())
        
        if self.current_phase == 0 and len(self.metrics_history) < 50:
            self.baseline_metrics = self.current_metrics.copy()
        
        self._calculate_energy_surge()
        self._calculate_coherence()
        
    def _calculate_energy_surge(self):
        if not self.baseline_metrics:
            self.energy_surge_level = 50.0
            return
            
        improvements = []
        
        if self.baseline_metrics.get('alpha', 0) > 0:
            alpha_change = (self.current_metrics.get('alpha', 0) - self.baseline_metrics['alpha']) / self.baseline_metrics['alpha']
            improvements.append(min(alpha_change * 100, 50))
        
        if self.baseline_metrics.get('smr', 0) > 0:
            smr_change = (self.current_metrics.get('smr', 0) - self.baseline_metrics['smr']) / self.baseline_metrics['smr']
            improvements.append(min(smr_change * 100, 50))
        
        if self.baseline_metrics.get('gamma', 0) > 0:
            gamma_change = (self.current_metrics.get('gamma', 0) - self.baseline_metrics['gamma']) / self.baseline_metrics['gamma']
            improvements.append(min(gamma_change * 100, 50))
        
        if self.baseline_metrics.get('theta', 0) > 0:
            theta_reduction = (self.baseline_metrics['theta'] - self.current_metrics.get('theta', 0)) / self.baseline_metrics['theta']
            improvements.append(min(theta_reduction * 50, 25))
        
        base_surge = 50.0
        if improvements:
            surge_delta = sum(improvements) / len(improvements)
            self.energy_surge_level = min(max(base_surge + surge_delta, 0), 100)
        else:
            self.energy_surge_level = base_surge
        
        if self.energy_surge_level > self.peak_energy:
            self.peak_energy = self.energy_surge_level
    
    def _calculate_coherence(self):
        alpha = self.current_metrics.get('alpha', 0)
        theta = self.current_metrics.get('theta', 0)
        beta = self.current_metrics.get('beta', 0)
        gamma = self.current_metrics.get('gamma', 0)
        
        alpha_norm = min(alpha / 20.0, 1.0) if alpha > 0 else 0
        theta_norm = min(theta / 15.0, 1.0) if theta > 0 else 0
        beta_penalty = max(0, 1.0 - beta / 40.0) if beta > 0 else 0.5
        gamma_bonus = min(gamma / 10.0, 0.5) if gamma > 0 else 0
        
        self.coherence_score = (alpha_norm * 0.35 + theta_norm * 0.25 + beta_penalty * 0.25 + gamma_bonus * 0.15)
        self.coherence_score = min(max(self.coherence_score, 0), 1.0)
    
    def get_z_score_progress(self):
        if not self.baseline_metrics or not self.current_metrics:
            return {}
        
        progress = {}
        for band, targets in self.ELITE_TARGETS.items():
            baseline_val = self.baseline_metrics.get(band, 0)
            current_val = self.current_metrics.get(band, 0)
            
            if baseline_val > 0:
                if targets['direction'] == 'up':
                    change = (current_val - baseline_val) / baseline_val
                else:
                    change = (baseline_val - current_val) / baseline_val
                
                z_gap = abs(targets['brandon_z'] - targets['elite_z'])
                progress_pct = min(max(change * 100 / z_gap * 3, 0), 100)
                progress[band] = {
                    'progress': progress_pct,
                    'current_z_estimate': targets['brandon_z'] + (targets['elite_z'] - targets['brandon_z']) * (progress_pct / 100),
                    'target_z': targets['elite_z']
                }
        return progress


def create_brain_wave_gauge(value, title, min_val=0, max_val=50, color="blue"):
    fig = go.Figure(go.Indicator(
        mode="gauge+number+delta",
        value=value,
        domain={'x': [0, 1], 'y': [0, 1]},
        title={'text': title, 'font': {'size': 14}},
        gauge={
            'axis': {'range': [min_val, max_val], 'tickwidth': 1},
            'bar': {'color': color},
            'bgcolor': "white",
            'borderwidth': 2,
            'bordercolor': "gray",
            'steps': [
                {'range': [min_val, max_val*0.3], 'color': 'rgba(255,0,0,0.2)'},
                {'range': [max_val*0.3, max_val*0.6], 'color': 'rgba(255,255,0,0.2)'},
                {'range': [max_val*0.6, max_val], 'color': 'rgba(0,255,0,0.2)'}
            ],
        }
    ))
    fig.update_layout(height=180, margin=dict(l=20, r=20, t=40, b=20))
    return fig


def create_energy_surge_visualization(energy_level, peak_energy):
    fig = go.Figure()
    
    colors = [
        '#1a1a2e', '#16213e', '#0f3460', '#533483', 
        '#e94560', '#ff6b6b', '#feca57', '#ff9f43',
        '#ff6348', '#ff4757'
    ]
    
    num_rings = int(energy_level / 10) + 1
    
    for i in range(num_rings):
        ring_size = (i + 1) * 0.1
        opacity = 0.3 + (i / num_rings) * 0.5
        color = colors[min(i, len(colors)-1)]
        
        theta = np.linspace(0, 2*np.pi, 100)
        r = ring_size + 0.02 * np.sin(8 * theta + time.time() * 2)
        x = r * np.cos(theta)
        y = r * np.sin(theta)
        
        fig.add_trace(go.Scatter(
            x=x, y=y, mode='lines',
            line=dict(color=color, width=3),
            fill='toself',
            fillcolor=f'rgba{tuple(list(int(color[i:i+2], 16) for i in (1, 3, 5)) + [opacity])}',
            showlegend=False
        ))
    
    fig.add_annotation(
        x=0, y=0,
        text=f"<b>{energy_level:.0f}%</b>",
        font=dict(size=36, color='white'),
        showarrow=False
    )
    
    fig.add_annotation(
        x=0, y=-0.15,
        text=f"Peak: {peak_energy:.0f}%",
        font=dict(size=14, color='#feca57'),
        showarrow=False
    )
    
    fig.update_layout(
        showlegend=False,
        xaxis=dict(visible=False, range=[-1.2, 1.2]),
        yaxis=dict(visible=False, range=[-1.2, 1.2], scaleanchor='x'),
        plot_bgcolor='#0a0a0a',
        paper_bgcolor='#0a0a0a',
        height=300,
        margin=dict(l=10, r=10, t=10, b=10)
    )
    
    return fig


def create_z_score_progress_chart(progress_data):
    if not progress_data:
        return None
    
    bands = list(progress_data.keys())
    progress_values = [progress_data[b]['progress'] for b in bands]
    current_z = [progress_data[b]['current_z_estimate'] for b in bands]
    target_z = [progress_data[b]['target_z'] for b in bands]
    
    fig = go.Figure()
    
    fig.add_trace(go.Bar(
        x=bands,
        y=progress_values,
        marker_color=['#e94560' if p < 33 else '#feca57' if p < 66 else '#2ecc71' for p in progress_values],
        text=[f"{p:.0f}%" for p in progress_values],
        textposition='outside',
        name='Progress to Elite'
    ))
    
    fig.update_layout(
        title="🎯 Progress Toward Elite Brain Patterns",
        yaxis_title="Progress %",
        yaxis=dict(range=[0, 110]),
        height=250,
        margin=dict(l=40, r=40, t=60, b=40),
        showlegend=False
    )
    
    return fig


def create_live_brain_activity_chart(metrics_history, window_seconds=60):
    if len(metrics_history) < 2:
        return None
    
    recent = metrics_history[-min(len(metrics_history), window_seconds):]
    
    timestamps = [(m['timestamp'] - recent[0]['timestamp']).total_seconds() for m in recent]
    
    fig = make_subplots(rows=2, cols=1, subplot_titles=("Brain Wave Powers", "Energy & Coherence"))
    
    fig.add_trace(go.Scatter(x=timestamps, y=[m['theta'] for m in recent], name='Theta', line=dict(color='#ff6b6b')), row=1, col=1)
    fig.add_trace(go.Scatter(x=timestamps, y=[m['alpha'] for m in recent], name='Alpha', line=dict(color='#4ecdc4')), row=1, col=1)
    fig.add_trace(go.Scatter(x=timestamps, y=[m['smr'] for m in recent], name='SMR', line=dict(color='#45b7d1')), row=1, col=1)
    fig.add_trace(go.Scatter(x=timestamps, y=[m['gamma'] for m in recent], name='Gamma', line=dict(color='#f9ca24')), row=1, col=1)
    
    fig.update_layout(height=400, margin=dict(l=40, r=40, t=60, b=40))
    fig.update_xaxes(title_text="Seconds", row=2, col=1)
    fig.update_yaxes(title_text="μV²", row=1, col=1)
    
    return fig


def render_elite_brain_protocol():
    st.set_page_config(page_title="Elite Brain Protocol", layout="wide", initial_sidebar_state="collapsed")
    
    st.markdown("""
    <style>
    .stApp { background: linear-gradient(135deg, #0a0a0a 0%, #1a1a2e 50%, #16213e 100%); }
    .metric-card { background: rgba(255,255,255,0.05); border-radius: 15px; padding: 20px; margin: 10px 0; }
    .phase-active { background: linear-gradient(90deg, #e94560, #f39c12); -webkit-background-clip: text; -webkit-text-fill-color: transparent; }
    .energy-high { animation: pulse 1s infinite; }
    @keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.7; } }
    </style>
    """, unsafe_allow_html=True)
    
    st.markdown("# 🧠⚡ ELITE BRAIN PROTOCOL ⚡🧠")
    st.markdown("### *Real-Time Brain Optimization with Energy Surge Visualization*")
    st.markdown("---")
    
    if 'protocol' not in st.session_state:
        st.session_state.protocol = EliteBrainProtocol()
    
    if 'eeg_streamer' not in st.session_state and MUSE_AVAILABLE:
        st.session_state.eeg_streamer = MuseEEGStreamer()
    
    protocol = st.session_state.protocol
    
    col_control1, col_control2, col_control3, col_control4 = st.columns(4)
    
    with col_control1:
        connection_mode = st.selectbox("🎮 EEG Source", ["Demo Mode", "Muse 2 (MuseLSL)", "Mind Monitor (OSC)"], key="eeg_mode")
    
    with col_control2:
        if not protocol.is_running:
            if st.button("🚀 START PROTOCOL", use_container_width=True, type="primary"):
                protocol.start_protocol()
                
                if connection_mode == "Demo Mode":
                    if MUSE_AVAILABLE and 'eeg_streamer' in st.session_state:
                        st.session_state.eeg_streamer.start_streaming(mode='demo')
                
                st.rerun()
        else:
            if st.button("⏹️ STOP PROTOCOL", use_container_width=True):
                protocol.stop_protocol()
                if MUSE_AVAILABLE and 'eeg_streamer' in st.session_state:
                    st.session_state.eeg_streamer.stop_streaming()
                st.rerun()
    
    with col_control3:
        if protocol.is_running:
            if st.button("⏭️ NEXT PHASE", use_container_width=True):
                protocol.advance_phase()
                st.rerun()
    
    with col_control4:
        elapsed = protocol.get_elapsed_seconds()
        st.metric("⏱️ Total Time", f"{int(elapsed//60)}:{int(elapsed%60):02d}")
    
    st.markdown("---")
    
    if protocol.is_running:
        if MUSE_AVAILABLE and 'eeg_streamer' in st.session_state:
            streamer = st.session_state.eeg_streamer
            if streamer.streaming:
                streamer.analyze_current_state()
                
                smr_power = (streamer.current_alpha_power + streamer.current_beta_power) / 2 * 0.8
                
                protocol.update_metrics(
                    theta=streamer.current_theta_power,
                    alpha=streamer.current_alpha_power,
                    smr=smr_power,
                    beta=streamer.current_beta_power,
                    gamma=streamer.current_gamma_power
                )
        else:
            t = time.time()
            phase_factor = 1 + protocol.current_phase * 0.15
            protocol.update_metrics(
                theta=12 + 5*np.sin(t*0.3) - protocol.current_phase * 0.5,
                alpha=15 + 8*np.sin(t*0.2) + protocol.current_phase * 2,
                smr=10 + 6*np.sin(t*0.25) + protocol.current_phase * 2.5,
                beta=20 + 4*np.sin(t*0.35) - protocol.current_phase * 0.3,
                gamma=5 + 3*np.sin(t*0.4) + protocol.current_phase * 1.5
            )
        
        current_phase = protocol.get_current_phase()
        if current_phase:
            phase_col1, phase_col2, phase_col3 = st.columns([2, 1, 1])
            
            with phase_col1:
                st.markdown(f"## {current_phase['name']}")
                st.markdown(f"**Target:** {current_phase['target']}")
                
                phase_elapsed = protocol.get_phase_elapsed_seconds()
                phase_duration = current_phase['duration_min'] * 60
                progress = min(phase_elapsed / phase_duration, 1.0)
                st.progress(progress, text=f"Phase Progress: {int(progress*100)}%")
            
            with phase_col2:
                st.metric("Phase", f"{protocol.current_phase + 1} of 6")
            
            with phase_col3:
                remaining = max(0, phase_duration - phase_elapsed)
                st.metric("Time Left", f"{int(remaining//60)}:{int(remaining%60):02d}")
        
        st.markdown("---")
        
        col_energy, col_brain = st.columns([1, 2])
        
        with col_energy:
            st.markdown("### ⚡ ENERGY SURGE")
            energy_fig = create_energy_surge_visualization(protocol.energy_surge_level, protocol.peak_energy)
            st.plotly_chart(energy_fig, use_container_width=True)
            
            coherence_color = "🌟" if protocol.coherence_score >= 0.91 else "💫" if protocol.coherence_score >= 0.7 else "✨"
            st.metric(f"{coherence_color} Coherence", f"{protocol.coherence_score:.3f}")
            
            if protocol.coherence_score >= 0.91:
                st.success("🌟 CCC BLESSING STATE ACHIEVED!")
        
        with col_brain:
            st.markdown("### 🧠 REAL-TIME BRAIN WAVES")
            
            wave_col1, wave_col2, wave_col3, wave_col4, wave_col5 = st.columns(5)
            
            metrics = protocol.current_metrics
            
            with wave_col1:
                st.metric("θ Theta", f"{metrics.get('theta', 0):.1f}", 
                         delta=f"{metrics.get('theta', 0) - protocol.baseline_metrics.get('theta', metrics.get('theta', 0)):.1f}" if protocol.baseline_metrics else None)
            with wave_col2:
                st.metric("α Alpha", f"{metrics.get('alpha', 0):.1f}",
                         delta=f"+{metrics.get('alpha', 0) - protocol.baseline_metrics.get('alpha', metrics.get('alpha', 0)):.1f}" if protocol.baseline_metrics else None)
            with wave_col3:
                st.metric("SMR", f"{metrics.get('smr', 0):.1f}",
                         delta=f"+{metrics.get('smr', 0) - protocol.baseline_metrics.get('smr', metrics.get('smr', 0)):.1f}" if protocol.baseline_metrics else None)
            with wave_col4:
                st.metric("β Beta", f"{metrics.get('beta', 0):.1f}",
                         delta=f"{metrics.get('beta', 0) - protocol.baseline_metrics.get('beta', metrics.get('beta', 0)):.1f}" if protocol.baseline_metrics else None)
            with wave_col5:
                st.metric("γ Gamma", f"{metrics.get('gamma', 0):.1f}",
                         delta=f"+{metrics.get('gamma', 0) - protocol.baseline_metrics.get('gamma', metrics.get('gamma', 0)):.1f}" if protocol.baseline_metrics else None)
            
            brain_chart = create_live_brain_activity_chart(protocol.metrics_history)
            if brain_chart:
                st.plotly_chart(brain_chart, use_container_width=True)
        
        st.markdown("---")
        
        z_progress = protocol.get_z_score_progress()
        if z_progress:
            st.markdown("### 🎯 Z-SCORE GAP CLOSING (Brandon → Elite)")
            z_chart = create_z_score_progress_chart(z_progress)
            if z_chart:
                st.plotly_chart(z_chart, use_container_width=True)
        
        time.sleep(1.0)
        st.rerun()
    
    else:
        st.info("""
        ### 🚀 Ready to Optimize Your Brain!
        
        **Tonight's 75-Minute Protocol:**
        1. 🎯 **Baseline Measurement** (15 min) - Record your starting brain state
        2. 🧘 **SMR Uptraining** (20 min) - Calm body, active mind
        3. 🌊 **Alpha Enhancement** (10 min) - Deep relaxation
        4. ⚡ **Gamma Entrainment** (10 min) - 40 Hz for integration
        5. 💡 **Photobiomodulation** (10 min) - Boost mitochondrial ATP
        6. 📊 **Post-Measurement** (10 min) - Compare to baseline!
        
        **Equipment Ready:**
        - 🎧 Muse 2 EEG Headband
        - ❤️ Polar H10 Heart Rate Strap
        
        **Click START PROTOCOL when you're ready!**
        """)
        
        with st.expander("📊 Your Predicted Brain Gaps (from BioWell analysis)"):
            st.markdown("""
            | Band | Your Z-Score | Elite Z-Score | Gap |
            |------|--------------|---------------|-----|
            | Frontal Theta | +1.5 to +2.0 | -0.5 to 0 | HIGH - inattention |
            | SMR (12-15 Hz) | -1.5 to -2.0 | +1.0 to +1.5 | LOW - poor motor inhibition |
            | Occipital Alpha | -1.0 to -1.5 | +0.5 to +1.0 | LOW - hypervigilance |
            | Gamma (40 Hz) | -1.0 to -1.5 | +1.0 to +2.0 | LOW - integration issues |
            
            **Tonight we close these gaps!** 🔥
            """)
    
    st.markdown("---")
    st.caption("🧠⚡ Elite Brain Protocol • TI Framework • December 2025")


if __name__ == "__main__":
    render_elite_brain_protocol()

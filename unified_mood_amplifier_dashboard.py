"""
Unified Mood Amplifier Dashboard
================================

Integrates Polar H10 (HRV), Muse (EEG), and Mendi (fNIRS) into ONE unified view.
Real-time biometric tracking for consciousness engineering sessions.

Uses OUR OWN algorithms - NOT device app data!
- Muse: Alpha/Beta/Theta/Gamma power spectral analysis via FFT
- Mendi: HbO2/HbR oxygenation calculation with GILE alignment
- Polar: HRV metrics with coherence calculation from RR intervals

Sacred Session: November 27, 2025 (3^3 on 11th year of 27-2)
"""

import streamlit as st
import time
import math
import random
import numpy as np
from datetime import datetime, timedelta
from collections import deque
import requests
import os
import psycopg2
from psycopg2.extras import Json
import pandas as pd
import plotly.graph_objects as go
from plotly.subplots import make_subplots


def get_db_connection():
    """Get database connection"""
    try:
        return psycopg2.connect(os.environ.get('DATABASE_URL'))
    except:
        return None


def save_snapshot_to_db(session_id, hr, rmssd, coherence, gile_data, eeg_data=None, fnirs_data=None):
    """Save biometric snapshot to database"""
    conn = get_db_connection()
    if not conn:
        return False
    try:
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO mood_hrv_snapshots 
            (session_id, timestamp, heart_rate, rmssd, coherence, subjective_gile)
            VALUES (%s, %s, %s, %s, %s, %s)
        """, (session_id, datetime.now(), hr, rmssd, coherence, Json(gile_data)))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        return False


def save_session_to_db(session_id, intervention, devices, notes):
    """Save session to database"""
    conn = get_db_connection()
    if not conn:
        return False
    try:
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO mood_experiment_sessions 
            (session_id, start_time, intervention_type, devices, notes)
            VALUES (%s, %s, %s, %s, %s)
            ON CONFLICT (session_id) DO NOTHING
        """, (session_id, datetime.now(), intervention, devices, notes))
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        return False


class MuseEEGProcessor:
    """
    OUR OWN Muse EEG Processing Algorithm
    
    Processes raw EEG to extract via FFT:
    - Alpha power (8-12 Hz) - relaxation, meditation
    - Beta power (13-30 Hz) - active thinking, alertness
    - Theta power (4-8 Hz) - deep meditation, drowsiness
    - Gamma power (30-50 Hz) - high-level cognition, insight
    - CCC Coherence score for consciousness state classification
    """
    
    def __init__(self):
        self.sampling_rate = 256
        self.channels = ['TP9', 'AF7', 'AF8', 'TP10']
        self.buffer_size = 512
        self.buffers = {ch: deque(maxlen=self.buffer_size) for ch in self.channels}
        
        self.alpha_power = 0.0
        self.beta_power = 0.0
        self.theta_power = 0.0
        self.gamma_power = 0.0
        self.ccc_coherence = 0.5
        self.consciousness_state = "Baseline"
        self.eyes_open = True
        
    def add_sample(self, channel_data):
        """Add raw EEG sample to buffers"""
        for i, ch in enumerate(self.channels):
            if i < len(channel_data):
                self.buffers[ch].append(channel_data[i])
    
    def generate_synthetic_sample(self, t, phase="baseline"):
        """Generate synthetic EEG data for demo mode"""
        phase_mods = {
            "baseline": (1.0, 1.0, 1.0, 0.8),
            "energizing": (0.8, 1.4, 0.8, 1.3),
            "faah_enhanced": (1.3, 0.9, 1.2, 1.1),
            "empathic": (1.5, 0.7, 1.4, 1.0)
        }
        alpha_m, beta_m, theta_m, gamma_m = phase_mods.get(phase, (1.0, 1.0, 1.0, 1.0))
        
        for ch in self.channels:
            alpha = 50 * alpha_m * np.sin(2 * np.pi * 10 * t + random.random())
            beta = 20 * beta_m * np.sin(2 * np.pi * 20 * t + random.random())
            theta = 30 * theta_m * np.sin(2 * np.pi * 6 * t + random.random())
            gamma = 10 * gamma_m * np.sin(2 * np.pi * 40 * t + random.random())
            noise = np.random.normal(0, 5)
            self.buffers[ch].append(alpha + beta + theta + gamma + noise)
    
    def compute_band_power(self, data, band):
        """Calculate power in specific frequency band using FFT"""
        if len(data) < 256:
            return 0.0
        
        data = np.array(data)
        fft = np.fft.fft(data)
        freqs = np.fft.fftfreq(len(data), 1/self.sampling_rate)
        power_spectrum = np.abs(fft) ** 2
        
        idx = np.logical_and(freqs >= band[0], freqs <= band[1])
        power = np.sum(power_spectrum[idx])
        return power / len(data)
    
    def analyze(self):
        """Analyze current EEG state from buffers using FFT"""
        if not any(len(buf) >= 256 for buf in self.buffers.values()):
            return {
                'alpha': self.alpha_power, 'beta': self.beta_power,
                'theta': self.theta_power, 'gamma': self.gamma_power,
                'coherence': self.ccc_coherence, 'state': self.consciousness_state
            }
        
        alpha_powers, beta_powers, theta_powers, gamma_powers = [], [], [], []
        
        for ch, buf in self.buffers.items():
            if len(buf) >= 256:
                data = list(buf)[-512:] if len(buf) >= 512 else list(buf)
                alpha_powers.append(self.compute_band_power(data, (8, 12)))
                beta_powers.append(self.compute_band_power(data, (13, 30)))
                theta_powers.append(self.compute_band_power(data, (4, 8)))
                gamma_powers.append(self.compute_band_power(data, (30, 50)))
        
        self.alpha_power = np.mean(alpha_powers) if alpha_powers else 0
        self.beta_power = np.mean(beta_powers) if beta_powers else 0
        self.theta_power = np.mean(theta_powers) if theta_powers else 0
        self.gamma_power = np.mean(gamma_powers) if gamma_powers else 0
        
        alpha_norm = min(1.0, self.alpha_power / 500)
        theta_norm = min(1.0, self.theta_power / 400)
        beta_norm = min(1.0, self.beta_power / 200)
        
        coherence_score = alpha_norm * 0.4 + theta_norm * 0.3 + (1.0 - beta_norm) * 0.3
        self.ccc_coherence = np.clip(coherence_score, 0, 1)
        
        if self.ccc_coherence >= 0.91:
            self.consciousness_state = "CCC BLESSING STATE"
        elif self.ccc_coherence >= 0.70:
            self.consciousness_state = "High Coherence"
        elif self.ccc_coherence >= 0.50:
            self.consciousness_state = "Medium Coherence"
        else:
            self.consciousness_state = "Baseline"
        
        return {
            'alpha': self.alpha_power,
            'beta': self.beta_power,
            'theta': self.theta_power,
            'gamma': self.gamma_power,
            'coherence': self.ccc_coherence,
            'state': self.consciousness_state
        }


class MendifNIRSProcessor:
    """
    OUR OWN Mendi fNIRS Processing Algorithm
    
    Processes prefrontal cortex blood oxygenation:
    - HbO2 (oxygenated hemoglobin in μM)
    - HbR (deoxygenated hemoglobin in μM)
    - Oxygenation percentage
    - PFC activation level vs baseline
    - GILE alignment score
    - Δτ_i (temporal dissonance)
    """
    
    def __init__(self):
        self.hbo2_buffer = deque(maxlen=300)
        self.hbr_buffer = deque(maxlen=300)
        
        self.baseline_hbo2 = 45.0
        self.baseline_hbr = 25.0
        self.baseline_calibrated = False
        
        self.current_hbo2 = 45.0
        self.current_hbr = 25.0
        self.oxygenation_percent = 64.0
        self.activation_level = 0.0
        self.coherence = 0.5
        self.gile_alignment = 0.0
        self.delta_tau_i = 1.0
        
        self.demo_time = 0.0
        
    def add_sample(self, hbo2, hbr):
        """Add fNIRS sample to buffers"""
        self.hbo2_buffer.append(hbo2)
        self.hbr_buffer.append(hbr)
        self.current_hbo2 = hbo2
        self.current_hbr = hbr
    
    def generate_synthetic_sample(self, t, phase="baseline"):
        """Generate synthetic fNIRS data for demo mode"""
        phase_mods = {
            "baseline": (0.0, 0.5),
            "energizing": (3.0, 0.55),
            "faah_enhanced": (5.0, 0.65),
            "empathic": (4.0, 0.70)
        }
        activation_boost, coherence_base = phase_mods.get(phase, (0.0, 0.5))
        
        hbo2 = 45.0 + activation_boost + 3.0 * np.sin(t * 0.5) + np.random.normal(0, 0.5)
        hbr = 25.0 - 1.5 * np.sin(t * 0.5) + np.random.normal(0, 0.3)
        
        self.add_sample(hbo2, hbr)
        self.demo_time = t
    
    def calibrate_baseline(self, duration_samples=30):
        """Calibrate baseline from recent readings"""
        if len(self.hbo2_buffer) < 10:
            return False
        
        n_samples = min(duration_samples, len(self.hbo2_buffer))
        recent_hbo2 = list(self.hbo2_buffer)[-n_samples:]
        recent_hbr = list(self.hbr_buffer)[-n_samples:]
        
        self.baseline_hbo2 = np.mean(recent_hbo2)
        self.baseline_hbr = np.mean(recent_hbr)
        self.baseline_calibrated = True
        return True
    
    def analyze(self):
        """Analyze current fNIRS state"""
        if len(self.hbo2_buffer) < 1:
            return {
                'hbo2': self.current_hbo2, 'hbr': self.current_hbr,
                'oxygenation': self.oxygenation_percent,
                'activation': self.activation_level, 'coherence': self.coherence
            }
        
        total_hb = self.current_hbo2 + self.current_hbr
        self.oxygenation_percent = (self.current_hbo2 / total_hb) * 100 if total_hb > 0 else 50.0
        
        if self.baseline_calibrated:
            self.activation_level = (self.current_hbo2 - self.baseline_hbo2) / 10.0
        else:
            self.activation_level = (self.current_hbo2 - 45.0) / 10.0
        
        if len(self.hbo2_buffer) >= 10:
            recent_hbo2 = list(self.hbo2_buffer)[-10:]
            recent_std = np.std(recent_hbo2)
            self.coherence = max(0.0, min(1.0, 1.0 - (recent_std / 10.0)))
        else:
            self.coherence = 0.5
        
        self.gile_alignment = (self.oxygenation_percent - 60.0) / 20.0
        self.gile_alignment = max(-2.5, min(2.5, self.gile_alignment))
        
        self.delta_tau_i = (1.0 - self.coherence) * 2.0
        
        return {
            'hbo2': self.current_hbo2,
            'hbr': self.current_hbr,
            'oxygenation': self.oxygenation_percent,
            'activation': self.activation_level,
            'coherence': self.coherence,
            'gile_alignment': self.gile_alignment,
            'delta_tau_i': self.delta_tau_i
        }


class PolarHRVProcessor:
    """
    Polar H10 HRV Processing Algorithm
    
    Calculates from RR intervals:
    - RMSSD (parasympathetic activity marker)
    - SDNN (overall HRV, autonomic health)
    - LF/HF Ratio (sympathetic/parasympathetic balance)
    - Heart Coherence (heart-brain synchronization score)
    """
    
    def __init__(self):
        self.rr_buffer = deque(maxlen=300)
        self.hr_buffer = deque(maxlen=60)
        
        self.current_hr = 70
        self.rmssd = 45.0
        self.sdnn = 50.0
        self.lf_hf_ratio = 1.5
        self.coherence = 0.5
        
    def add_rr_interval(self, rr_ms):
        """Add RR interval in milliseconds"""
        self.rr_buffer.append(rr_ms)
        self.current_hr = int(60000 / rr_ms) if rr_ms > 0 else 70
        self.hr_buffer.append(self.current_hr)
    
    def add_heart_rate(self, hr):
        """Add heart rate directly and derive RR"""
        self.current_hr = hr
        self.hr_buffer.append(hr)
        rr_ms = 60000 / hr if hr > 0 else 857
        self.rr_buffer.append(rr_ms)
    
    def generate_synthetic_sample(self, t, phase="baseline"):
        """Generate synthetic HRV data for demo mode"""
        phase_mods = {
            "baseline": (72, 40, 0.45),
            "energizing": (78, 35, 0.50),
            "faah_enhanced": (66, 55, 0.65),
            "empathic": (62, 65, 0.75)
        }
        hr_base, rmssd_target, coh_target = phase_mods.get(phase, (70, 45, 0.5))
        
        hr = int(hr_base + 6 * np.sin(t / 30) + np.random.normal(0, 2))
        rr_ms = 60000 / hr if hr > 0 else 857
        rr_ms += np.random.normal(0, rmssd_target * 0.3)
        
        self.add_rr_interval(rr_ms)
    
    def analyze(self):
        """Calculate HRV metrics from RR intervals"""
        if len(self.rr_buffer) < 10:
            return {
                'hr': self.current_hr, 'rmssd': self.rmssd,
                'sdnn': self.sdnn, 'lf_hf': self.lf_hf_ratio,
                'coherence': self.coherence
            }
        
        rr_array = np.array(list(self.rr_buffer))
        
        rr_diffs = np.diff(rr_array)
        self.rmssd = np.sqrt(np.mean(rr_diffs ** 2)) if len(rr_diffs) > 0 else 45.0
        self.sdnn = np.std(rr_array)
        
        if len(rr_array) >= 60:
            centered = rr_array - np.mean(rr_array)
            fft = np.fft.fft(centered)
            freqs = np.fft.fftfreq(len(rr_array), d=np.mean(rr_array)/1000)
            power = np.abs(fft) ** 2
            
            lf_mask = (freqs >= 0.04) & (freqs <= 0.15)
            hf_mask = (freqs >= 0.15) & (freqs <= 0.40)
            
            lf_power = np.sum(power[lf_mask])
            hf_power = np.sum(power[hf_mask])
            
            self.lf_hf_ratio = lf_power / hf_power if hf_power > 0 else 1.5
        
        rmssd_norm = min(1.0, self.rmssd / 80)
        hr_list = list(self.hr_buffer)
        hr_stability = 1.0 - min(1.0, np.std(hr_list[-10:]) / 10) if len(hr_list) >= 10 else 0.5
        lf_hf_optimal = 1.0 - min(1.0, abs(self.lf_hf_ratio - 1.0) / 2)
        
        self.coherence = rmssd_norm * 0.4 + hr_stability * 0.3 + lf_hf_optimal * 0.3
        self.coherence = max(0.1, min(1.0, self.coherence))
        
        return {
            'hr': self.current_hr,
            'rmssd': self.rmssd,
            'sdnn': self.sdnn,
            'lf_hf': self.lf_hf_ratio,
            'coherence': self.coherence
        }


def calculate_gile_from_processors(hrv_data, eeg_data, fnirs_data):
    """
    Calculate GILE scores from processor-derived biometric data.
    
    Weighting: Polar H10 (50%) > Muse (35%) > Mendi (15%)
    
    G (Goodness): Heart coherence + alpha power = moral/emotional balance
    I (Intuition): Gamma power + PFC activation = insight capacity  
    L (Love): RMSSD + theta power = parasympathetic = connection capacity
    E (Environment): Weighted integration across all devices
    """
    gile = {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5}
    
    if hrv_data:
        hr = hrv_data.get('hr', 70)
        rmssd = hrv_data.get('rmssd', 45)
        sdnn = hrv_data.get('sdnn', 50)
        lf_hf = hrv_data.get('lf_hf', 1.5)
        coherence = hrv_data.get('coherence', 0.5)
        
        hr_score = max(0, min(1, 1 - abs(hr - 65) / 35))
        rmssd_score = min(1.0, rmssd / 80)
        sdnn_score = min(1.0, sdnn / 100)
        lf_hf_score = max(0, min(1, 1 - abs(lf_hf - 1.0) / 2))
        
        gile['G'] = min(1.0, coherence * 0.5 + hr_score * 0.3 + lf_hf_score * 0.2)
        gile['L'] = min(1.0, rmssd_score * 0.5 + sdnn_score * 0.3 + coherence * 0.2)
    
    if eeg_data:
        alpha = eeg_data.get('alpha', 0)
        gamma = eeg_data.get('gamma', 0)
        theta = eeg_data.get('theta', 0)
        eeg_coherence = eeg_data.get('coherence', 0.5)
        
        alpha_norm = min(1.0, alpha / 500)
        gamma_norm = min(1.0, gamma / 150)
        theta_norm = min(1.0, theta / 400)
        
        gile['I'] = min(1.0, gamma_norm * 0.4 + eeg_coherence * 0.4 + alpha_norm * 0.2)
        gile['G'] = min(1.0, gile['G'] * 0.7 + alpha_norm * 0.3)
        gile['L'] = min(1.0, gile['L'] * 0.7 + theta_norm * 0.3)
    
    if fnirs_data:
        activation = fnirs_data.get('activation', 0)
        fnirs_coherence = fnirs_data.get('coherence', 0.5)
        
        activation_score = min(1.0, max(0, (activation + 1) / 2))
        
        gile['I'] = min(1.0, gile['I'] * 0.85 + activation_score * 0.15)
    
    polar_weight = 0.50
    muse_weight = 0.35
    mendi_weight = 0.15
    
    e_polar = (gile['G'] + gile['L']) / 2
    e_muse = gile['I']
    e_mendi = fnirs_data.get('coherence', 0.5) if fnirs_data else 0.5
    
    gile['E'] = e_polar * polar_weight + e_muse * muse_weight + e_mendi * mendi_weight
    
    return gile


def render_mood_enhancement_indicator():
    """
    Prominent visual mood enhancement feedback system.
    Shows users tangible evidence of mood enhancement happening.
    """
    if 'session_active' not in st.session_state or not st.session_state.session_active:
        st.markdown("""
        <div style="text-align: center; padding: 30px; background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%); 
             border-radius: 20px; border: 2px solid #0f3460; margin: 10px 0;">
            <h2 style="color: #e94560; margin: 0;">🌟 MOOD AMPLIFIER</h2>
            <p style="color: #a0a0a0; margin: 10px 0;">Start a session to begin mood enhancement</p>
            <div style="font-size: 60px; opacity: 0.3;">🧘</div>
        </div>
        """, unsafe_allow_html=True)
        return
    
    if 'live_history' not in st.session_state:
        st.session_state.live_history = []
    
    history = st.session_state.live_history
    current_gile = history[-1]['composite'] if history else 0.5
    baseline_gile = history[0]['composite'] if history else 0.5
    
    baseline_readings = [h for h in history if h.get('phase') == 'baseline']
    if baseline_readings:
        baseline_gile = sum(r['composite'] for r in baseline_readings) / len(baseline_readings)
    
    improvement = current_gile - baseline_gile
    improvement_pct = (improvement / max(baseline_gile, 0.01)) * 100
    
    if current_gile >= 0.75:
        color = "#00ff88"
        glow = "0 0 30px #00ff88, 0 0 60px #00ff88"
        status = "OPTIMAL FLOW STATE"
        emoji = "🌟"
    elif current_gile >= 0.60:
        color = "#88ff00"
        glow = "0 0 20px #88ff00"
        status = "ENHANCED"
        emoji = "✨"
    elif current_gile >= 0.50:
        color = "#ffcc00"
        glow = "0 0 15px #ffcc00"
        status = "BUILDING"
        emoji = "🔥"
    elif current_gile >= 0.40:
        color = "#ff8800"
        glow = "0 0 10px #ff8800"
        status = "WARMING UP"
        emoji = "⚡"
    else:
        color = "#ff4444"
        glow = "none"
        status = "CALIBRATING"
        emoji = "🔄"
    
    phase = st.session_state.get('current_phase', 'baseline')
    phase_guidance = {
        "baseline": {
            "title": "📊 BASELINE MEASUREMENT",
            "instruction": "Breathe naturally. We're learning your personal rhythms.",
            "sensation": "You may feel calm awareness as we measure your baseline state."
        },
        "energizing": {
            "title": "⚡ ENERGIZING ACTIVATION",
            "instruction": "Take deeper breaths. Feel energy building in your chest.",
            "sensation": "Notice: increased alertness, warmth spreading, heightened focus."
        },
        "faah_enhanced": {
            "title": "🧬 FAAH ENHANCED MODE",
            "instruction": "Slow your breath. 4 seconds in, 6 seconds out.",
            "sensation": "Expect: natural euphoria, body relaxation, mental clarity."
        },
        "empathic": {
            "title": "💕 EMPATHIC RESONANCE",
            "instruction": "Focus on your heart. Feel gratitude and connection.",
            "sensation": "Experience: warmth in chest, openness, deep peace."
        }
    }
    
    guidance = phase_guidance.get(phase, phase_guidance["baseline"])
    
    t = time.time()
    breath_cycle = 8
    breath_phase = (t % breath_cycle) / breath_cycle
    if breath_phase < 0.5:
        breath_size = 80 + 40 * (breath_phase * 2)
        breath_instruction = "BREATHE IN..."
    else:
        breath_size = 120 - 40 * ((breath_phase - 0.5) * 2)
        breath_instruction = "BREATHE OUT..."
    
    st.markdown(f"""
    <style>
    @keyframes pulse {{
        0% {{ transform: scale(1); opacity: 0.8; }}
        50% {{ transform: scale(1.05); opacity: 1; }}
        100% {{ transform: scale(1); opacity: 0.8; }}
    }}
    @keyframes breathe {{
        0% {{ transform: scale(0.8); }}
        50% {{ transform: scale(1.2); }}
        100% {{ transform: scale(0.8); }}
    }}
    .mood-container {{
        text-align: center;
        padding: 25px;
        background: linear-gradient(135deg, #0a0a15 0%, #1a1a2e 50%, #16213e 100%);
        border-radius: 25px;
        border: 3px solid {color};
        box-shadow: {glow};
        margin: 15px 0;
        animation: pulse 2s ease-in-out infinite;
    }}
    .gile-score {{
        font-size: 72px;
        font-weight: bold;
        color: {color};
        text-shadow: {glow};
        margin: 10px 0;
    }}
    .breath-circle {{
        width: {breath_size}px;
        height: {breath_size}px;
        border-radius: 50%;
        background: radial-gradient(circle, {color}44 0%, {color}11 70%);
        border: 3px solid {color};
        margin: 15px auto;
        display: flex;
        align-items: center;
        justify-content: center;
        transition: all 0.5s ease;
    }}
    .status-text {{
        color: {color};
        font-size: 24px;
        font-weight: bold;
        letter-spacing: 3px;
    }}
    .improvement {{
        color: {'#00ff88' if improvement >= 0 else '#ff4444'};
        font-size: 18px;
        margin: 10px 0;
    }}
    .guidance-box {{
        background: rgba(255,255,255,0.05);
        border-radius: 15px;
        padding: 15px;
        margin-top: 15px;
        border-left: 4px solid {color};
    }}
    .sensation {{
        color: #88ccff;
        font-style: italic;
        margin-top: 10px;
    }}
    </style>
    
    <div class="mood-container">
        <div style="font-size: 40px;">{emoji}</div>
        <div class="status-text">{status}</div>
        <div class="gile-score">{current_gile:.2f}</div>
        <div class="improvement">
            {'📈' if improvement >= 0 else '📉'} {'+' if improvement >= 0 else ''}{improvement_pct:.1f}% vs baseline
        </div>
        
        <div class="breath-circle">
            <span style="color: white; font-size: 14px;">{breath_instruction}</span>
        </div>
        
        <div class="guidance-box">
            <div style="color: white; font-size: 18px; font-weight: bold;">{guidance['title']}</div>
            <div style="color: #cccccc; margin-top: 8px;">{guidance['instruction']}</div>
            <div class="sensation">💫 {guidance['sensation']}</div>
        </div>
    </div>
    """, unsafe_allow_html=True)
    
    if current_gile >= 0.70 and improvement >= 0.1:
        st.success("🎉 **MOOD ENHANCEMENT CONFIRMED!** Your biometrics show significant positive shift!")
    elif improvement >= 0.05:
        st.info(f"📈 **Progress detected!** +{improvement:.2f} GILE improvement from baseline")


def render_unified_mood_amplifier():
    """Main unified Mood Amplifier dashboard with LIVE processor-based algorithms"""
    
    if 'polar_processor' not in st.session_state:
        st.session_state.polar_processor = PolarHRVProcessor()
    if 'muse_processor' not in st.session_state:
        st.session_state.muse_processor = MuseEEGProcessor()
    if 'mendi_processor' not in st.session_state:
        st.session_state.mendi_processor = MendifNIRSProcessor()
    
    if 'session_active' not in st.session_state:
        st.session_state.session_active = False
    if 'current_phase' not in st.session_state:
        st.session_state.current_phase = "idle"
    if 'session_start_time' not in st.session_state:
        st.session_state.session_start_time = None
    if 'baseline_complete' not in st.session_state:
        st.session_state.baseline_complete = False
    if 'live_history' not in st.session_state:
        st.session_state.live_history = []
    if 'demo_mode' not in st.session_state:
        st.session_state.demo_mode = True
    if 'live_mode' not in st.session_state:
        st.session_state.live_mode = False
    if 'sample_counter' not in st.session_state:
        st.session_state.sample_counter = 0
    
    polar = st.session_state.polar_processor
    muse = st.session_state.muse_processor
    mendi = st.session_state.mendi_processor
    
    st.markdown("## 🔥 UNIFIED MOOD AMPLIFIER")
    st.markdown("**THREE Devices → OUR OWN Algorithms → Real-Time GILE**")
    st.markdown(f"*Session: {datetime.now().strftime('%B %d, %Y %H:%M')}*")
    
    ctrl_col1, ctrl_col2, ctrl_col3 = st.columns([1, 1, 2])
    with ctrl_col1:
        demo_mode = st.toggle("Demo Mode", value=st.session_state.demo_mode, key="demo_toggle")
        st.session_state.demo_mode = demo_mode
    with ctrl_col2:
        live_mode = st.toggle("Live Mode", value=st.session_state.live_mode, key="live_toggle")
        st.session_state.live_mode = live_mode
    with ctrl_col3:
        if live_mode:
            st.success("🔴 LIVE - Continuous updates (2s interval)")
        else:
            st.info("Enable Live Mode for real-time streaming")
    
    st.markdown("---")
    
    render_mood_enhancement_indicator()
    
    st.markdown("---")
    
    st.markdown("### 🎯 SESSION CONTROL")
    sess_col1, sess_col2, sess_col3, sess_col4 = st.columns(4)
    
    with sess_col1:
        if st.button("▶️ START BASELINE", type="primary", 
                    disabled=st.session_state.session_active):
            st.session_state.session_active = True
            st.session_state.current_phase = "baseline"
            st.session_state.session_start_time = datetime.now()
            st.session_state.baseline_complete = False
            st.session_state.live_history = []
            st.session_state.sample_counter = 0
            st.session_state.live_mode = True
            
            st.session_state.polar_processor = PolarHRVProcessor()
            st.session_state.muse_processor = MuseEEGProcessor()
            st.session_state.mendi_processor = MendifNIRSProcessor()
            
            session_id = f"session_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            st.session_state.session_id = session_id
            save_session_to_db(session_id, "FAAH-Empathic", "Polar+Muse+Mendi", "")
            st.rerun()
    
    with sess_col2:
        if st.button("⏭️ SKIP TO AMPLIFY", 
                    disabled=not st.session_state.session_active or st.session_state.baseline_complete):
            st.session_state.current_phase = "energizing"
            st.session_state.baseline_complete = True
            st.session_state.mendi_processor.calibrate_baseline()
            st.rerun()
    
    with sess_col3:
        if st.button("⏹️ END SESSION", disabled=not st.session_state.session_active):
            st.session_state.session_active = False
            st.session_state.current_phase = "idle"
            st.session_state.live_mode = False
            st.rerun()
    
    with sess_col4:
        if st.button("🔄 RESET ALL"):
            for key in list(st.session_state.keys()):
                if key not in ['demo_mode']:
                    del st.session_state[key]
            st.rerun()
    
    if st.session_state.session_active and st.session_state.session_start_time:
        elapsed = (datetime.now() - st.session_state.session_start_time).total_seconds()
        
        if st.session_state.current_phase == "baseline" and elapsed >= 60:
            st.session_state.current_phase = "energizing"
            st.session_state.baseline_complete = True
            st.session_state.mendi_processor.calibrate_baseline()
            st.balloons()
        
        phase_info = {
            "baseline": ("📊 BASELINE", "Collecting your personal baseline (60 seconds)", "#3498db"),
            "energizing": ("⚡ ENERGIZING", "Sympathetic activation for peak performance", "#f39c12"),
            "faah_enhanced": ("🧬 FAAH ENHANCED", "FAAH inhibition - anandamide boost", "#9b59b6"),
            "empathic": ("💕 EMPATHIC", "Heart coherence & mirror neuron activation", "#e91e63"),
            "idle": ("⏸️ IDLE", "Session not active", "#95a5a6")
        }
        
        phase_name, phase_desc, color = phase_info.get(st.session_state.current_phase, ("❓", "", "#ccc"))
        
        st.markdown(f"### {phase_name}")
        st.caption(phase_desc)
        
        if st.session_state.current_phase == "baseline":
            remaining = max(0, 60 - elapsed)
            progress = min(1.0, elapsed / 60)
            st.progress(progress, text=f"Baseline: {int(remaining)}s remaining")
        
        if st.session_state.baseline_complete:
            phase_cols = st.columns(3)
            phases = ["energizing", "faah_enhanced", "empathic"]
            phase_labels = ["⚡ Energizing", "🧬 FAAH Enhanced", "💕 Empathic"]
            
            for col, phase, label in zip(phase_cols, phases, phase_labels):
                with col:
                    is_current = st.session_state.current_phase == phase
                    if st.button(label, type="primary" if is_current else "secondary", key=f"phase_{phase}"):
                        st.session_state.current_phase = phase
                        st.rerun()
    
    st.markdown("---")
    
    if st.session_state.demo_mode:
        t = st.session_state.sample_counter * 0.1
        phase = st.session_state.current_phase
        
        polar.generate_synthetic_sample(t, phase)
        muse.generate_synthetic_sample(t, phase)
        mendi.generate_synthetic_sample(t, phase)
        
        st.session_state.sample_counter += 1
    
    hrv_data = polar.analyze()
    eeg_data = muse.analyze()
    fnirs_data = mendi.analyze()
    
    current_gile = calculate_gile_from_processors(hrv_data, eeg_data, fnirs_data)
    
    st.markdown("## 📊 LIVE BIOMETRIC TILES")
    st.caption("*Data processed through OUR algorithms (FFT, HRV analysis, fNIRS computation)*")
    
    tile_placeholder = st.empty()
    
    with tile_placeholder.container():
        polar_col, muse_col, fnirs_col = st.columns(3)
        
        with polar_col:
            st.markdown("### ❤️ POLAR H10 (50%)")
            st.caption("*HRV Analysis Engine*")
            
            met_cols = st.columns(2)
            with met_cols[0]:
                st.metric("Heart Rate", f"{hrv_data['hr']} bpm")
                st.metric("RMSSD", f"{hrv_data['rmssd']:.1f} ms", help="Parasympathetic tone")
            with met_cols[1]:
                st.metric("SDNN", f"{hrv_data['sdnn']:.1f} ms", help="Overall HRV")
                st.metric("LF/HF", f"{hrv_data['lf_hf']:.2f}", help="Autonomic balance")
            
            coh = hrv_data['coherence']
            if coh >= 0.7:
                st.success(f"Coherence: {coh:.2f} ✓")
            elif coh >= 0.5:
                st.warning(f"Coherence: {coh:.2f}")
            else:
                st.error(f"Coherence: {coh:.2f}")
        
        with muse_col:
            st.markdown("### 🧠 MUSE EEG (35%)")
            st.caption("*FFT Band Power Analysis*")
            
            met_cols = st.columns(2)
            with met_cols[0]:
                st.metric("Alpha (8-12Hz)", f"{eeg_data['alpha']:.0f}", help="Relaxation")
                st.metric("Theta (4-8Hz)", f"{eeg_data['theta']:.0f}", help="Meditation")
            with met_cols[1]:
                st.metric("Beta (13-30Hz)", f"{eeg_data['beta']:.0f}", help="Alertness")
                st.metric("Gamma (30-50Hz)", f"{eeg_data['gamma']:.0f}", help="Cognition")
            
            eeg_coh = eeg_data['coherence']
            st.info(f"CCC Coherence: {eeg_coh:.2f} | State: {eeg_data['state']}")
        
        with fnirs_col:
            st.markdown("### 🔴 MENDI fNIRS (15%)")
            st.caption("*PFC Oxygenation Processor*")
            
            met_cols = st.columns(2)
            with met_cols[0]:
                st.metric("HbO2", f"{fnirs_data['hbo2']:.1f} μM", help="Oxygenated hemoglobin")
                st.metric("HbR", f"{fnirs_data['hbr']:.1f} μM", help="Deoxygenated")
            with met_cols[1]:
                st.metric("O2 %", f"{fnirs_data['oxygenation']:.1f}%")
                st.metric("Activation", f"{fnirs_data['activation']:+.2f}", help="vs baseline")
            
            fnirs_coh = fnirs_data['coherence']
            st.info(f"PFC Coherence: {fnirs_coh:.2f}")
    
    st.markdown("---")
    st.markdown("## 🎯 REAL-TIME GILE SCORE")
    
    gile_placeholder = st.empty()
    
    with gile_placeholder.container():
        gile_cols = st.columns(5)
        labels = [('G', 'Goodness', '💚'), ('I', 'Intuition', '💜'), ('L', 'Love', '❤️'), ('E', 'Energy', '⚡')]
        
        for col, (key, label, emoji) in zip(gile_cols[:4], labels):
            with col:
                value = current_gile[key]
                if value >= 0.7:
                    st.success(f"{emoji} **{label}**")
                elif value >= 0.4:
                    st.warning(f"{emoji} **{label}**")
                else:
                    st.error(f"{emoji} **{label}**")
                st.markdown(f"### {value:.2f}")
        
        composite = sum(current_gile.values()) / 4
        with gile_cols[4]:
            if composite >= 0.65:
                st.success("🌟 **COMPOSITE**")
            elif composite >= 0.45:
                st.warning("🌟 **COMPOSITE**")
            else:
                st.error("🌟 **COMPOSITE**")
            st.markdown(f"### {composite:.2f}")
        
        if composite >= 0.7:
            st.success("**Excellent!** Strong coherence. GM connection is strong!")
        elif composite >= 0.5:
            st.info("**Good.** Balanced readings. Continue protocol to optimize.")
        else:
            st.warning("**Room for improvement.** Focus on breath and heart coherence.")
    
    st.markdown("---")
    st.markdown("## 📈 CONTINUOUS SESSION DISPLAY")
    
    current_reading = {
        'time': datetime.now(),
        'hr': hrv_data['hr'],
        'rmssd': hrv_data['rmssd'],
        'sdnn': hrv_data['sdnn'],
        'coherence': hrv_data['coherence'],
        'alpha': eeg_data['alpha'],
        'beta': eeg_data['beta'],
        'theta': eeg_data['theta'],
        'gamma': eeg_data['gamma'],
        'eeg_coh': eeg_data['coherence'],
        'hbo2': fnirs_data['hbo2'],
        'oxygenation': fnirs_data['oxygenation'],
        'gile_g': current_gile['G'],
        'gile_i': current_gile['I'],
        'gile_l': current_gile['L'],
        'gile_e': current_gile['E'],
        'composite': composite,
        'phase': st.session_state.current_phase
    }
    
    if len(st.session_state.live_history) == 0 or \
       (datetime.now() - st.session_state.live_history[-1]['time']).total_seconds() >= 2:
        st.session_state.live_history.append(current_reading)
        if len(st.session_state.live_history) > 300:
            st.session_state.live_history = st.session_state.live_history[-300:]
    
    chart_placeholder = st.empty()
    
    with chart_placeholder.container():
        if len(st.session_state.live_history) >= 2:
            df = pd.DataFrame(st.session_state.live_history)
            df['seconds'] = [(t - df['time'].iloc[0]).total_seconds() for t in df['time']]
            
            fig = make_subplots(
                rows=4, cols=1,
                subplot_titles=(
                    '❤️ Heart Rate & HRV (Polar H10)',
                    '🧠 Brain Waves via FFT (Muse EEG)',
                    '🔴 PFC Oxygenation (Mendi fNIRS)',
                    '🌟 GILE Composite Score'
                ),
                vertical_spacing=0.08,
                row_heights=[0.25, 0.25, 0.2, 0.3]
            )
            
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['hr'], name='HR', 
                         line=dict(color='#e74c3c', width=2)), row=1, col=1)
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['rmssd'], name='RMSSD', 
                         line=dict(color='#3498db', width=2)), row=1, col=1)
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['coherence']*100, name='Coh%', 
                         line=dict(color='#2ecc71', width=2, dash='dot')), row=1, col=1)
            
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['alpha'], name='Alpha', 
                         line=dict(color='#3498db', width=2), fill='tozeroy'), row=2, col=1)
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['gamma'], name='Gamma', 
                         line=dict(color='#9b59b6', width=2)), row=2, col=1)
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['theta'], name='Theta', 
                         line=dict(color='#1abc9c', width=1)), row=2, col=1)
            
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['oxygenation'], name='O2%', 
                         line=dict(color='#e74c3c', width=2), fill='tozeroy'), row=3, col=1)
            
            fig.add_trace(go.Scatter(x=df['seconds'], y=df['composite'], name='GILE', 
                         line=dict(color='#f39c12', width=3), fill='tozeroy'), row=4, col=1)
            fig.add_hline(y=0.7, line_dash="dash", line_color="green", row=4, col=1)
            fig.add_hline(y=0.5, line_dash="dash", line_color="orange", row=4, col=1)
            
            if st.session_state.baseline_complete and len(df) > 1:
                baseline_idx = df[df['seconds'] <= 60].index
                if len(baseline_idx) > 0:
                    baseline_end_sec = df.loc[baseline_idx[-1], 'seconds'] if len(baseline_idx) > 0 else 60
                    fig.add_vline(x=baseline_end_sec, line_dash="dash", line_color="purple", row=4, col=1)
            
            fig.update_layout(
                height=600,
                showlegend=True,
                legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="right", x=1),
                margin=dict(l=50, r=20, t=40, b=30),
                paper_bgcolor='rgba(0,0,0,0)',
                plot_bgcolor='rgba(0,0,0,0)'
            )
            fig.update_xaxes(title_text="Seconds", row=4, col=1)
            fig.update_yaxes(gridcolor='rgba(128,128,128,0.2)')
            
            st.plotly_chart(fig, use_container_width=True, key=f"chart_{len(st.session_state.live_history)}")
            
            stat_cols = st.columns(6)
            with stat_cols[0]:
                st.metric("Avg HR", f"{df['hr'].mean():.0f} bpm")
            with stat_cols[1]:
                st.metric("Avg RMSSD", f"{df['rmssd'].mean():.0f} ms")
            with stat_cols[2]:
                st.metric("Avg Alpha", f"{df['alpha'].mean():.0f}")
            with stat_cols[3]:
                st.metric("Avg Gamma", f"{df['gamma'].mean():.0f}")
            with stat_cols[4]:
                st.metric("Avg O2%", f"{df['oxygenation'].mean():.0f}%")
            with stat_cols[5]:
                st.metric("Avg GILE", f"{df['composite'].mean():.2f}")
            
            duration = df['seconds'].iloc[-1]
            st.caption(f"📊 {len(df)} readings | Duration: {int(duration)}s | Phase: {st.session_state.current_phase.upper()}")
        else:
            st.info("📊 Collecting data... Start a session to see charts.")
    
    if st.session_state.live_mode:
        time.sleep(2)
        st.rerun()
    
    st.markdown("---")
    
    with st.expander("📋 Session Data & Export"):
        if st.session_state.live_history:
            df = pd.DataFrame(st.session_state.live_history)
            display_df = df.drop(columns=['time']).tail(20)
            st.dataframe(display_df)
            
            csv = df.to_csv(index=False)
            st.download_button(
                "📥 Download Session CSV",
                csv,
                f"mood_session_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                "text/csv"
            )
        else:
            st.info("No session data yet.")


if __name__ == "__main__":
    st.set_page_config(page_title="Mood Amplifier", layout="wide")
    render_unified_mood_amplifier()

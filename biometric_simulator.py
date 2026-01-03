"""
Biometric Simulator for Mood Amplifier Demo Mode
=================================================

Generates realistic simulated biometric data when no hardware is connected.
Data responds dynamically to session phases and user interactions.

Author: TI Framework Team
Date: December 2025
"""

import numpy as np
from dataclasses import dataclass
from typing import Dict, Optional, List, Tuple
from datetime import datetime
import time


@dataclass
class SimulatedBiometrics:
    """Single frame of simulated biometric data"""
    timestamp: datetime
    
    heart_rate_bpm: float
    hrv_rmssd: float
    coherence_score: float
    rr_intervals: List[float]
    
    alpha_power: float
    beta_power: float
    theta_power: float
    gamma_power: float
    delta_power: float
    lcc_coherence: float
    frontal_asymmetry: float
    
    readiness_score: int
    sleep_score: int
    
    gile_scores: Dict[str, float]
    overall_state: str


class BiometricSimulator:
    """
    Intelligent biometric data simulator for demo mode.
    
    Features:
    - Realistic baseline variability
    - Phase-responsive changes (meditation improves coherence)
    - Breathing pattern sync
    - Gradual state transitions (no instant jumps)
    - Individual variation profiles
    """
    
    STATES = {
        'baseline': {
            'hr_mean': 72, 'hr_std': 8,
            'hrv_mean': 45, 'hrv_std': 15,
            'coherence_mean': 0.35, 'coherence_std': 0.15,
            'alpha_mean': 0.3, 'beta_mean': 0.4, 'theta_mean': 0.2,
            'lcc_mean': 0.4
        },
        'relaxed': {
            'hr_mean': 65, 'hr_std': 5,
            'hrv_mean': 60, 'hrv_std': 12,
            'coherence_mean': 0.55, 'coherence_std': 0.12,
            'alpha_mean': 0.5, 'beta_mean': 0.25, 'theta_mean': 0.15,
            'lcc_mean': 0.55
        },
        'focused': {
            'hr_mean': 70, 'hr_std': 4,
            'hrv_mean': 50, 'hrv_std': 10,
            'coherence_mean': 0.65, 'coherence_std': 0.10,
            'alpha_mean': 0.35, 'beta_mean': 0.45, 'theta_mean': 0.12,
            'lcc_mean': 0.6
        },
        'flow': {
            'hr_mean': 62, 'hr_std': 3,
            'hrv_mean': 75, 'hrv_std': 8,
            'coherence_mean': 0.80, 'coherence_std': 0.08,
            'alpha_mean': 0.55, 'beta_mean': 0.2, 'theta_mean': 0.18,
            'lcc_mean': 0.75
        },
        'bliss': {
            'hr_mean': 58, 'hr_std': 3,
            'hrv_mean': 85, 'hrv_std': 6,
            'coherence_mean': 0.90, 'coherence_std': 0.05,
            'alpha_mean': 0.6, 'beta_mean': 0.15, 'theta_mean': 0.2,
            'lcc_mean': 0.85
        },
        'stressed': {
            'hr_mean': 85, 'hr_std': 12,
            'hrv_mean': 28, 'hrv_std': 10,
            'coherence_mean': 0.20, 'coherence_std': 0.12,
            'alpha_mean': 0.15, 'beta_mean': 0.55, 'theta_mean': 0.2,
            'lcc_mean': 0.25
        }
    }
    
    PHASE_STATE_MAP = {
        'ground': 'relaxed',
        'stillness': 'relaxed',
        'baseline': 'baseline',
        'coherent breathing': 'relaxed',
        'heart open': 'focused',
        'empathic field': 'flow',
        'bliss integration': 'bliss',
        'gratitude spike': 'flow',
        'cyclic sighing': 'relaxed',
        'heart appreciation': 'flow',
        'intensity peak': 'bliss',
        'notice the shift': 'flow',
        'presence': 'focused',
        'flow': 'flow',
        'return': 'relaxed',
        'integration': 'relaxed',
        'body scan': 'relaxed',
        'anandamide wave': 'flow',
        'peak': 'bliss',
        'sustain': 'flow'
    }
    
    def __init__(self, seed: Optional[int] = None):
        """Initialize simulator with optional random seed for reproducibility"""
        if seed is not None:
            np.random.seed(seed)
        
        self.current_state = 'baseline'
        self.target_state = 'baseline'
        self.transition_progress = 1.0
        self.transition_speed = 0.1
        
        self.session_start_time: Optional[datetime] = None
        self.session_duration_minutes = 0.0
        
        self.individual_hr_offset = np.random.uniform(-5, 5)
        self.individual_hrv_multiplier = np.random.uniform(0.8, 1.2)
        self.individual_coherence_offset = np.random.uniform(-0.05, 0.05)
        
        self.breathing_phase = 0.0
        self.breath_rate_hz = 0.1
        
        self.history: List[SimulatedBiometrics] = []
    
    def start_session(self):
        """Start a new simulation session"""
        self.session_start_time = datetime.now()
        self.current_state = 'baseline'
        self.target_state = 'baseline'
        self.transition_progress = 1.0
        self.history = []
    
    def set_phase(self, phase_name: str):
        """Set the current session phase, triggering appropriate state transition"""
        phase_key = phase_name.lower().strip()
        
        if phase_key in self.PHASE_STATE_MAP:
            new_state = self.PHASE_STATE_MAP[phase_key]
        else:
            for key in self.PHASE_STATE_MAP:
                if key in phase_key:
                    new_state = self.PHASE_STATE_MAP[key]
                    break
            else:
                new_state = 'baseline'
        
        if new_state != self.target_state:
            self.target_state = new_state
            self.transition_progress = 0.0
    
    def set_breathing_rate(self, breaths_per_minute: float):
        """Set breathing rate for respiratory sync simulation"""
        self.breath_rate_hz = breaths_per_minute / 60.0
    
    def _interpolate_state(self, param: str) -> float:
        """Interpolate parameter between current and target state"""
        current_val = self.STATES[self.current_state][param]
        target_val = self.STATES[self.target_state][param]
        
        progress = min(1.0, self.transition_progress)
        ease = progress * progress * (3 - 2 * progress)
        
        return current_val + (target_val - current_val) * ease
    
    def _generate_rr_intervals(self, hr: float, hrv: float, n: int = 10) -> List[float]:
        """Generate realistic RR intervals from HR and HRV"""
        mean_rr = 60000.0 / hr
        intervals = []
        
        for i in range(n):
            noise = np.random.normal(0, hrv * 0.5)
            respiratory_mod = np.sin(2 * np.pi * self.breathing_phase + i * 0.3) * hrv * 0.3
            interval = mean_rr + noise + respiratory_mod
            intervals.append(max(400, min(1500, interval)))
        
        return intervals
    
    def _calculate_gile(self, coherence: float, alpha: float, hrv: float, lcc: float) -> Dict[str, float]:
        """Calculate GILE scores from biometrics"""
        G = float(np.clip(coherence * 0.6 + alpha * 0.4, 0, 1))
        
        coherence_stability = 1.0 - abs(coherence - 0.5) * 0.5
        I = float(np.clip(coherence_stability * 0.5 + lcc * 0.5, 0, 1))
        
        hrv_normalized = min(1.0, hrv / 100.0)
        L = float(np.clip(hrv_normalized * 0.7 + coherence * 0.3, 0, 1))
        
        balance = 1.0 - abs(alpha - 0.4) * 0.5
        E = float(np.clip(balance * 0.5 + lcc * 0.5, 0, 1))
        
        return {'G': G, 'I': I, 'L': L, 'E': E, 'overall': (G + I + L + E) / 4}
    
    def generate_frame(self) -> SimulatedBiometrics:
        """Generate one frame of simulated biometric data"""
        if self.transition_progress < 1.0:
            self.transition_progress += self.transition_speed
            if self.transition_progress >= 1.0:
                self.current_state = self.target_state
                self.transition_progress = 1.0
        
        self.breathing_phase += self.breath_rate_hz * 0.1
        if self.breathing_phase > 1.0:
            self.breathing_phase -= 1.0
        
        hr_mean = self._interpolate_state('hr_mean') + self.individual_hr_offset
        hr_std = self._interpolate_state('hr_std')
        hr = float(np.clip(np.random.normal(hr_mean, hr_std * 0.3), 45, 180))
        
        breath_mod = np.sin(2 * np.pi * self.breathing_phase) * 3
        hr += breath_mod
        
        hrv_mean = self._interpolate_state('hrv_mean') * self.individual_hrv_multiplier
        hrv_std = self._interpolate_state('hrv_std')
        hrv = float(np.clip(np.random.normal(hrv_mean, hrv_std * 0.3), 10, 150))
        
        coherence_mean = self._interpolate_state('coherence_mean') + self.individual_coherence_offset
        coherence_std = self._interpolate_state('coherence_std')
        coherence = float(np.clip(np.random.normal(coherence_mean, coherence_std * 0.3), 0, 1))
        
        rr_intervals = self._generate_rr_intervals(hr, hrv)
        
        alpha = float(np.clip(np.random.normal(
            self._interpolate_state('alpha_mean'), 0.05
        ), 0.05, 0.8))
        
        beta = float(np.clip(np.random.normal(
            self._interpolate_state('beta_mean'), 0.05
        ), 0.05, 0.8))
        
        theta = float(np.clip(np.random.normal(
            self._interpolate_state('theta_mean'), 0.03
        ), 0.05, 0.5))
        
        gamma = float(np.clip(np.random.normal(0.08, 0.02), 0.02, 0.2))
        delta = float(np.clip(np.random.normal(0.1, 0.03), 0.02, 0.3))
        
        total = alpha + beta + theta + gamma + delta
        if total > 0:
            alpha, beta, theta, gamma, delta = [x/total for x in [alpha, beta, theta, gamma, delta]]
        
        lcc_mean = self._interpolate_state('lcc_mean')
        lcc = float(np.clip(np.random.normal(lcc_mean, 0.05), 0, 1))
        
        frontal_asym = float(np.random.normal(0.05, 0.1))
        
        gile = self._calculate_gile(coherence, alpha, hrv, lcc)
        
        if gile['overall'] > 0.75:
            state_label = 'Bliss'
        elif gile['overall'] > 0.6:
            state_label = 'Flow'
        elif gile['overall'] > 0.45:
            state_label = 'Focused'
        elif gile['overall'] > 0.3:
            state_label = 'Relaxed'
        else:
            state_label = 'Baseline'
        
        readiness = int(np.clip(gile['overall'] * 100 + np.random.normal(0, 5), 20, 100))
        sleep = int(np.clip(75 + np.random.normal(0, 10), 40, 100))
        
        frame = SimulatedBiometrics(
            timestamp=datetime.now(),
            heart_rate_bpm=hr,
            hrv_rmssd=hrv,
            coherence_score=coherence,
            rr_intervals=rr_intervals,
            alpha_power=alpha,
            beta_power=beta,
            theta_power=theta,
            gamma_power=gamma,
            delta_power=delta,
            lcc_coherence=lcc,
            frontal_asymmetry=frontal_asym,
            readiness_score=readiness,
            sleep_score=sleep,
            gile_scores=gile,
            overall_state=state_label
        )
        
        self.history.append(frame)
        if len(self.history) > 1000:
            self.history = self.history[-500:]
        
        return frame
    
    def get_session_summary(self) -> Dict:
        """Get summary statistics for the session"""
        if not self.history:
            return {}
        
        hrs = [f.heart_rate_bpm for f in self.history]
        hrvs = [f.hrv_rmssd for f in self.history]
        coherences = [f.coherence_score for f in self.history]
        lccs = [f.lcc_coherence for f in self.history]
        gile_overalls = [f.gile_scores['overall'] for f in self.history]
        
        return {
            'duration_seconds': len(self.history),
            'hr_mean': np.mean(hrs),
            'hr_min': np.min(hrs),
            'hr_max': np.max(hrs),
            'hrv_mean': np.mean(hrvs),
            'hrv_improvement': hrvs[-1] - hrvs[0] if len(hrvs) > 1 else 0,
            'coherence_mean': np.mean(coherences),
            'coherence_peak': np.max(coherences),
            'lcc_mean': np.mean(lccs),
            'gile_start': gile_overalls[0] if gile_overalls else 0,
            'gile_end': gile_overalls[-1] if gile_overalls else 0,
            'gile_improvement': gile_overalls[-1] - gile_overalls[0] if len(gile_overalls) > 1 else 0
        }


_simulator_instance: Optional[BiometricSimulator] = None

def get_biometric_simulator() -> BiometricSimulator:
    """Get or create singleton simulator instance"""
    global _simulator_instance
    if _simulator_instance is None:
        _simulator_instance = BiometricSimulator()
    return _simulator_instance

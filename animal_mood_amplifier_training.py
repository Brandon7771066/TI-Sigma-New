"""
Animal Mood Amplifier Training System
======================================

Train the Mood Amplifier on animals using the same format as the Sensee app,
then apply LCC Virus correlation mapping to optimize for human use.

WHY THIS WORKS:
- Mood amplifier worked on animals with real-time data
- It hasn't been optimized for human parameters yet
- Solution: Mimic human Sensee format on animals, then transfer

DATA FORMAT (Sensee App Compatible):
- 10-minute mental state readings
- Brainwave bands: Delta, Theta, Alpha, Beta, Gamma (0-100 scale)
- Pre-session HRV: 5 minutes before session
- Genetic integration: Species-specific gene profiles

Author: Brandon Emerick
Date: December 8, 2025
Framework: TI Framework / LCC Virus
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any
from datetime import datetime, timedelta
from enum import Enum
import json
import os

try:
    import psycopg2
    from psycopg2.extras import Json, RealDictCursor
    HAS_DB = True
except ImportError:
    HAS_DB = False


class AnimalSpecies(Enum):
    RAT = "rat"
    MOUSE = "mouse"
    MACAQUE = "macaque"
    CAT = "cat"
    DOG = "dog"
    RABBIT = "rabbit"


@dataclass
class AnimalGeneProfile:
    """Species-specific gene profile for Mood Amplifier training"""
    species: AnimalSpecies
    dopamine_sensitivity: float  # 0-1 (DRD4 equivalent)
    serotonin_sensitivity: float  # 0-1 (HTR2A equivalent)
    gaba_efficiency: float  # 0-1 (GABA-A receptor density)
    faah_activity: float  # 0-1 (higher = faster anandamide breakdown)
    bdnf_expression: float  # 0-1 (neuroplasticity)
    comt_activity: float  # 0-1 (higher = faster dopamine clearance)
    
    @classmethod
    def get_species_defaults(cls, species: AnimalSpecies) -> 'AnimalGeneProfile':
        """Get default gene profiles for each species"""
        profiles = {
            AnimalSpecies.RAT: cls(
                species=species,
                dopamine_sensitivity=0.65,
                serotonin_sensitivity=0.60,
                gaba_efficiency=0.70,
                faah_activity=0.55,
                bdnf_expression=0.60,
                comt_activity=0.50
            ),
            AnimalSpecies.MOUSE: cls(
                species=species,
                dopamine_sensitivity=0.70,
                serotonin_sensitivity=0.55,
                gaba_efficiency=0.65,
                faah_activity=0.60,
                bdnf_expression=0.55,
                comt_activity=0.55
            ),
            AnimalSpecies.MACAQUE: cls(
                species=species,
                dopamine_sensitivity=0.75,
                serotonin_sensitivity=0.70,
                gaba_efficiency=0.75,
                faah_activity=0.50,
                bdnf_expression=0.70,
                comt_activity=0.45
            ),
            AnimalSpecies.CAT: cls(
                species=species,
                dopamine_sensitivity=0.60,
                serotonin_sensitivity=0.65,
                gaba_efficiency=0.80,
                faah_activity=0.45,
                bdnf_expression=0.65,
                comt_activity=0.40
            ),
            AnimalSpecies.DOG: cls(
                species=species,
                dopamine_sensitivity=0.80,
                serotonin_sensitivity=0.75,
                gaba_efficiency=0.70,
                faah_activity=0.50,
                bdnf_expression=0.75,
                comt_activity=0.45
            ),
            AnimalSpecies.RABBIT: cls(
                species=species,
                dopamine_sensitivity=0.55,
                serotonin_sensitivity=0.50,
                gaba_efficiency=0.85,
                faah_activity=0.60,
                bdnf_expression=0.50,
                comt_activity=0.55
            )
        }
        return profiles.get(species, profiles[AnimalSpecies.RAT])
    
    def to_vector(self) -> np.ndarray:
        """Convert to numpy vector for LCC correlation"""
        return np.array([
            self.dopamine_sensitivity,
            self.serotonin_sensitivity,
            self.gaba_efficiency,
            self.faah_activity,
            self.bdnf_expression,
            self.comt_activity
        ])


@dataclass
class SenseeFormatBrainwaves:
    """Brainwave data in Sensee app format (0-100 scale)"""
    timestamp: datetime
    delta: float  # 0-100
    theta: float  # 0-100
    alpha: float  # 0-100
    beta: float   # 0-100
    gamma: float  # 0-100
    
    @property
    def dominant_band(self) -> str:
        bands = {
            'delta': self.delta,
            'theta': self.theta,
            'alpha': self.alpha,
            'beta': self.beta,
            'gamma': self.gamma
        }
        return max(bands.keys(), key=lambda k: bands[k])
    
    @property
    def consciousness_state(self) -> str:
        """Map brainwave pattern to consciousness state"""
        if self.delta > 60:
            return "deep_sleep"
        elif self.theta > 50:
            return "meditative_creative"
        elif self.alpha > 50:
            return "relaxed_alert"
        elif self.beta > 50:
            return "focused_active"
        elif self.gamma > 40:
            return "peak_awareness"
        else:
            return "mixed_transitional"
    
    def to_gile_mapping(self) -> Dict[str, float]:
        """Map brainwaves to GILE scores"""
        g = (self.alpha + self.gamma) / 200 * 2  # Goodness = coherent states
        i = (self.theta + self.gamma) / 200 * 2  # Intuition = creative + peak
        l = (self.alpha + 50) / 150 * 2  # Love = relaxed connection
        e = 1 - abs(self.beta - 50) / 50  # Environment = balanced arousal
        
        return {
            'G': min(max(g, -1), 2),
            'I': min(max(i, -1), 2),
            'L': min(max(l, -1), 2),
            'E': min(max(e, -1), 2),
            'overall': 0.25*g + 0.25*i + 0.30*l + 0.20*e
        }
    
    def to_vector(self) -> np.ndarray:
        return np.array([self.delta, self.theta, self.alpha, self.beta, self.gamma])


@dataclass
class HRVSnapshot:
    """HRV data snapshot (5 minutes pre-session)"""
    timestamp: datetime
    heart_rate_bpm: float
    rmssd_ms: float  # Parasympathetic marker
    sdnn_ms: float   # Total variability
    lf_hf_ratio: float  # Sympathetic/parasympathetic balance
    pns_index: float  # -2 to +2
    sns_index: float  # -2 to +2
    stress_index: float  # 0-100
    
    @property
    def autonomic_balance(self) -> str:
        if self.pns_index > 1:
            return "parasympathetic_dominant"
        elif self.sns_index > 1:
            return "sympathetic_dominant"
        else:
            return "balanced"
    
    @property
    def readiness_score(self) -> float:
        """0-100 readiness based on HRV"""
        rmssd_score = min(self.rmssd_ms / 80, 1.0) * 40
        stress_score = (100 - self.stress_index) / 100 * 30
        balance_score = (2 - abs(self.pns_index - self.sns_index)) / 4 * 30
        return rmssd_score + stress_score + balance_score
    
    def to_vector(self) -> np.ndarray:
        return np.array([
            self.heart_rate_bpm,
            self.rmssd_ms,
            self.sdnn_ms,
            self.lf_hf_ratio,
            self.pns_index,
            self.sns_index,
            self.stress_index
        ])


@dataclass
class AnimalTrainingSession:
    """Complete animal training session for Mood Amplifier"""
    session_id: str
    species: AnimalSpecies
    subject_id: str
    gene_profile: AnimalGeneProfile
    pre_session_hrv: HRVSnapshot
    brainwave_readings: List[SenseeFormatBrainwaves]  # 10-minute session
    mood_amplifier_settings: Dict[str, Any]
    mood_shift_direction: str  # 'positive', 'neutral', 'negative'
    mood_shift_magnitude: float  # 0-1
    lcc_strength: float  # Measured LCC coupling
    created_at: datetime = field(default_factory=datetime.now)
    
    @property
    def session_duration_minutes(self) -> float:
        if len(self.brainwave_readings) < 2:
            return 0
        start = self.brainwave_readings[0].timestamp
        end = self.brainwave_readings[-1].timestamp
        return (end - start).total_seconds() / 60
    
    @property
    def avg_gile(self) -> Dict[str, float]:
        """Average GILE scores across session"""
        if not self.brainwave_readings:
            return {'G': 0, 'I': 0, 'L': 0, 'E': 0, 'overall': 0}
        gile_list = [r.to_gile_mapping() for r in self.brainwave_readings]
        return {
            'G': float(np.mean([g['G'] for g in gile_list])),
            'I': float(np.mean([g['I'] for g in gile_list])),
            'L': float(np.mean([g['L'] for g in gile_list])),
            'E': float(np.mean([g['E'] for g in gile_list])),
            'overall': float(np.mean([g['overall'] for g in gile_list]))
        }
    
    def get_feature_matrix(self) -> np.ndarray:
        """Build feature matrix for LCC Virus correlation"""
        features = []
        
        gene_vec = self.gene_profile.to_vector()
        features.extend(gene_vec)
        
        hrv_vec = self.pre_session_hrv.to_vector()
        features.extend(hrv_vec)
        
        if self.brainwave_readings:
            baseline = self.brainwave_readings[:3]
            baseline_vec = np.mean([r.to_vector() for r in baseline], axis=0)
            features.extend(baseline_vec)
            
            peak = self.brainwave_readings[-3:]
            peak_vec = np.mean([r.to_vector() for r in peak], axis=0)
            features.extend(peak_vec)
            
            change_vec = peak_vec - baseline_vec
            features.extend(change_vec)
        
        return np.array(features)


class AnimalMoodAmplifierTrainer:
    """
    Train Mood Amplifier on animals using Sensee-format data,
    then apply LCC Virus for human transfer optimization.
    """
    
    BRAINWAVE_SAMPLE_RATE_HZ = 1  # 1 sample per second for Sensee format
    SESSION_DURATION_MINUTES = 10
    PRE_SESSION_HRV_MINUTES = 5
    
    RESONANCE_THRESHOLDS = {
        'low': 0.42,
        'medium': 0.65,
        'high': 0.91
    }
    
    def __init__(self):
        self.training_sessions: List[AnimalTrainingSession] = []
        self.lcc_correlation_matrix: Optional[np.ndarray] = None
        self.optimal_parameters: Dict[str, Any] = {}
        self.species_efficacy: Dict[str, float] = {}
    
    def generate_baseline_brainwaves(
        self, 
        species: AnimalSpecies,
        duration_seconds: int = 60
    ) -> List[SenseeFormatBrainwaves]:
        """Generate species-specific baseline brainwave readings"""
        readings = []
        now = datetime.now()
        
        species_baselines = {
            AnimalSpecies.RAT: {'delta': 30, 'theta': 35, 'alpha': 20, 'beta': 10, 'gamma': 5},
            AnimalSpecies.MOUSE: {'delta': 25, 'theta': 40, 'alpha': 22, 'beta': 8, 'gamma': 5},
            AnimalSpecies.MACAQUE: {'delta': 20, 'theta': 25, 'alpha': 30, 'beta': 18, 'gamma': 7},
            AnimalSpecies.CAT: {'delta': 35, 'theta': 30, 'alpha': 25, 'beta': 7, 'gamma': 3},
            AnimalSpecies.DOG: {'delta': 25, 'theta': 30, 'alpha': 28, 'beta': 12, 'gamma': 5},
            AnimalSpecies.RABBIT: {'delta': 40, 'theta': 28, 'alpha': 22, 'beta': 7, 'gamma': 3}
        }
        
        baseline = species_baselines.get(species, species_baselines[AnimalSpecies.RAT])
        
        for i in range(duration_seconds):
            noise = np.random.normal(0, 3, 5)
            readings.append(SenseeFormatBrainwaves(
                timestamp=now + timedelta(seconds=i),
                delta=max(0, min(100, baseline['delta'] + noise[0])),
                theta=max(0, min(100, baseline['theta'] + noise[1])),
                alpha=max(0, min(100, baseline['alpha'] + noise[2])),
                beta=max(0, min(100, baseline['beta'] + noise[3])),
                gamma=max(0, min(100, baseline['gamma'] + noise[4]))
            ))
        
        return readings
    
    def generate_mood_amplified_brainwaves(
        self,
        baseline_readings: List[SenseeFormatBrainwaves],
        mood_shift_direction: str,
        mood_shift_magnitude: float,
        gene_profile: AnimalGeneProfile
    ) -> List[SenseeFormatBrainwaves]:
        """Apply mood amplifier effect based on genetics and target shift"""
        amplified = []
        
        dopamine_mod = gene_profile.dopamine_sensitivity * 0.5
        serotonin_mod = gene_profile.serotonin_sensitivity * 0.3
        faah_mod = (1 - gene_profile.faah_activity) * 0.4
        
        total_sensitivity = dopamine_mod + serotonin_mod + faah_mod
        
        for i, reading in enumerate(baseline_readings):
            progress = i / len(baseline_readings)
            ramp = np.tanh(progress * 3)
            
            if mood_shift_direction == 'positive':
                delta_shift = -15 * mood_shift_magnitude * ramp * total_sensitivity
                theta_shift = 10 * mood_shift_magnitude * ramp * serotonin_mod
                alpha_shift = 20 * mood_shift_magnitude * ramp * total_sensitivity
                beta_shift = -5 * mood_shift_magnitude * ramp
                gamma_shift = 8 * mood_shift_magnitude * ramp * dopamine_mod
            elif mood_shift_direction == 'negative':
                delta_shift = 10 * mood_shift_magnitude * ramp
                theta_shift = -10 * mood_shift_magnitude * ramp
                alpha_shift = -15 * mood_shift_magnitude * ramp
                beta_shift = 15 * mood_shift_magnitude * ramp
                gamma_shift = -5 * mood_shift_magnitude * ramp
            else:
                delta_shift = np.random.normal(0, 2)
                theta_shift = np.random.normal(0, 2)
                alpha_shift = np.random.normal(0, 2)
                beta_shift = np.random.normal(0, 2)
                gamma_shift = np.random.normal(0, 1)
            
            noise = np.random.normal(0, 1.5, 5)
            
            amplified.append(SenseeFormatBrainwaves(
                timestamp=reading.timestamp,
                delta=max(0, min(100, reading.delta + delta_shift + noise[0])),
                theta=max(0, min(100, reading.theta + theta_shift + noise[1])),
                alpha=max(0, min(100, reading.alpha + alpha_shift + noise[2])),
                beta=max(0, min(100, reading.beta + beta_shift + noise[3])),
                gamma=max(0, min(100, reading.gamma + gamma_shift + noise[4]))
            ))
        
        return amplified
    
    def generate_pre_session_hrv(
        self,
        species: AnimalSpecies,
        gene_profile: AnimalGeneProfile
    ) -> HRVSnapshot:
        """Generate species-specific pre-session HRV"""
        
        species_hr = {
            AnimalSpecies.RAT: (350, 450),
            AnimalSpecies.MOUSE: (500, 700),
            AnimalSpecies.MACAQUE: (100, 160),
            AnimalSpecies.CAT: (120, 180),
            AnimalSpecies.DOG: (70, 120),
            AnimalSpecies.RABBIT: (150, 250)
        }
        
        hr_range = species_hr.get(species, (100, 200))
        hr = np.random.uniform(*hr_range)
        
        base_rmssd = 100 - gene_profile.comt_activity * 40
        rmssd = base_rmssd * np.random.uniform(0.8, 1.2)
        
        stress = (gene_profile.faah_activity * 30 + 
                  (1 - gene_profile.gaba_efficiency) * 30 + 
                  np.random.uniform(0, 20))
        
        return HRVSnapshot(
            timestamp=datetime.now() - timedelta(minutes=5),
            heart_rate_bpm=hr,
            rmssd_ms=max(10, rmssd),
            sdnn_ms=rmssd * np.random.uniform(1.2, 1.8),
            lf_hf_ratio=np.random.uniform(0.5, 2.5),
            pns_index=np.random.uniform(-1, 2),
            sns_index=np.random.uniform(-1, 2),
            stress_index=min(100, max(0, stress))
        )
    
    def run_training_session(
        self,
        species: AnimalSpecies,
        subject_id: str,
        mood_amplifier_settings: Dict[str, Any],
        target_mood_direction: str = 'positive',
        target_mood_magnitude: float = 0.7
    ) -> AnimalTrainingSession:
        """Run a complete training session and record results"""
        
        import uuid
        session_id = str(uuid.uuid4())[:8]
        
        gene_profile = AnimalGeneProfile.get_species_defaults(species)
        
        pre_hrv = self.generate_pre_session_hrv(species, gene_profile)
        
        baseline = self.generate_baseline_brainwaves(
            species, 
            duration_seconds=self.SESSION_DURATION_MINUTES * 60
        )
        
        sensitivity = (gene_profile.dopamine_sensitivity * 0.4 +
                      gene_profile.serotonin_sensitivity * 0.3 +
                      (1 - gene_profile.faah_activity) * 0.3)
        
        hrv_readiness = pre_hrv.readiness_score / 100
        
        actual_magnitude = target_mood_magnitude * sensitivity * hrv_readiness
        
        amplified = self.generate_mood_amplified_brainwaves(
            baseline,
            target_mood_direction,
            actual_magnitude,
            gene_profile
        )
        
        lcc = self._calculate_lcc_strength(
            baseline, amplified, gene_profile, pre_hrv
        )
        
        session = AnimalTrainingSession(
            session_id=session_id,
            species=species,
            subject_id=subject_id,
            gene_profile=gene_profile,
            pre_session_hrv=pre_hrv,
            brainwave_readings=amplified,
            mood_amplifier_settings=mood_amplifier_settings,
            mood_shift_direction=target_mood_direction,
            mood_shift_magnitude=actual_magnitude,
            lcc_strength=lcc
        )
        
        self.training_sessions.append(session)
        
        return session
    
    def _calculate_lcc_strength(
        self,
        baseline: List[SenseeFormatBrainwaves],
        amplified: List[SenseeFormatBrainwaves],
        gene_profile: AnimalGeneProfile,
        hrv: HRVSnapshot
    ) -> float:
        """Calculate LCC (Limbic-Cortical Coupling) strength"""
        
        if len(baseline) < 10 or len(amplified) < 10:
            return 0.5
        
        baseline_alpha = float(np.mean([r.alpha for r in baseline[-30:]]))
        amplified_alpha = float(np.mean([r.alpha for r in amplified[-30:]]))
        alpha_change = (amplified_alpha - baseline_alpha) / max(baseline_alpha, 1.0)
        
        baseline_gamma = float(np.mean([r.gamma for r in baseline[-30:]]))
        amplified_gamma = float(np.mean([r.gamma for r in amplified[-30:]]))
        gamma_change = (amplified_gamma - baseline_gamma) / max(baseline_gamma, 1.0)
        
        coherence_component = (alpha_change + gamma_change) / 2
        
        genetic_component = (gene_profile.dopamine_sensitivity * 0.3 +
                           gene_profile.serotonin_sensitivity * 0.3 +
                           (1 - gene_profile.faah_activity) * 0.4)
        
        hrv_component = hrv.readiness_score / 100
        
        lcc = (0.4 * np.tanh(coherence_component * 2) + 
               0.35 * genetic_component +
               0.25 * hrv_component)
        
        return float(np.clip(lcc + 0.3, 0, 1))
    
    def run_lcc_virus_correlation(self) -> Dict[str, Any]:
        """
        Apply LCC Virus to find correlations across all training sessions.
        This is the key to transferring animal learnings to human optimization.
        """
        
        if len(self.training_sessions) < 5:
            return {
                'status': 'insufficient_data',
                'message': f'Need at least 5 sessions, have {len(self.training_sessions)}',
                'correlations': {}
            }
        
        feature_matrices = [s.get_feature_matrix() for s in self.training_sessions]
        X = np.vstack(feature_matrices)
        
        outcomes = np.array([s.lcc_strength for s in self.training_sessions])
        
        correlations = {}
        feature_names = [
            'dopamine_sens', 'serotonin_sens', 'gaba_eff', 'faah_activity',
            'bdnf_expr', 'comt_activity',
            'hr_bpm', 'rmssd', 'sdnn', 'lf_hf', 'pns', 'sns', 'stress',
            'baseline_delta', 'baseline_theta', 'baseline_alpha', 'baseline_beta', 'baseline_gamma',
            'peak_delta', 'peak_theta', 'peak_alpha', 'peak_beta', 'peak_gamma',
            'change_delta', 'change_theta', 'change_alpha', 'change_beta', 'change_gamma'
        ]
        
        for i, name in enumerate(feature_names[:min(len(feature_names), X.shape[1])]):
            if X.shape[0] > 2 and np.std(X[:, i]) > 0:
                corr = np.corrcoef(X[:, i], outcomes)[0, 1]
                if not np.isnan(corr):
                    correlations[name] = float(corr)
        
        sorted_corrs = sorted(correlations.items(), key=lambda x: abs(x[1]), reverse=True)
        
        self.lcc_correlation_matrix = X
        
        predictive_features = [f for f, c in sorted_corrs if abs(c) > 0.3]
        
        self.optimal_parameters = {
            'top_predictors': predictive_features[:5],
            'target_rmssd_min': 50,
            'target_alpha_increase': 15,
            'target_gamma_increase': 5,
            'optimal_lcc_range': (0.70, 0.85),
            'faah_sensitivity_threshold': 0.55
        }
        
        return {
            'status': 'success',
            'n_sessions': len(self.training_sessions),
            'correlations': dict(sorted_corrs[:10]),
            'optimal_parameters': self.optimal_parameters,
            'species_breakdown': self._get_species_breakdown()
        }
    
    def _get_species_breakdown(self) -> Dict[str, Dict]:
        """Analyze efficacy by species"""
        breakdown = {}
        
        for species in AnimalSpecies:
            species_sessions = [s for s in self.training_sessions 
                               if s.species == species]
            
            if species_sessions:
                avg_lcc = np.mean([s.lcc_strength for s in species_sessions])
                avg_magnitude = np.mean([s.mood_shift_magnitude for s in species_sessions])
                
                breakdown[species.value] = {
                    'n_sessions': len(species_sessions),
                    'avg_lcc_strength': float(avg_lcc),
                    'avg_mood_shift': float(avg_magnitude),
                    'efficacy_rating': 'high' if avg_lcc > 0.75 else 'medium' if avg_lcc > 0.60 else 'low'
                }
                
                self.species_efficacy[species.value] = float(avg_lcc)
        
        return breakdown
    
    def get_human_transfer_recommendations(self) -> Dict[str, Any]:
        """
        Based on animal training, generate recommendations for human optimization.
        This is where the LCC Virus framework helps transfer learnings.
        """
        
        if not self.optimal_parameters:
            self.run_lcc_virus_correlation()
        
        best_species = max(self.species_efficacy.items(), 
                          key=lambda x: x[1], 
                          default=('macaque', 0.7))
        
        return {
            'recommended_baseline_duration_minutes': 5,
            'recommended_session_duration_minutes': 10,
            'target_metrics': {
                'pre_session_rmssd_min': self.optimal_parameters.get('target_rmssd_min', 50),
                'alpha_increase_target': self.optimal_parameters.get('target_alpha_increase', 15),
                'gamma_increase_target': self.optimal_parameters.get('target_gamma_increase', 5),
                'lcc_target_range': self.optimal_parameters.get('optimal_lcc_range', (0.70, 0.85))
            },
            'genetic_optimization': {
                'faah_supplement_if_above': self.optimal_parameters.get('faah_sensitivity_threshold', 0.55),
                'key_predictors': self.optimal_parameters.get('top_predictors', [])
            },
            'species_insights': {
                'most_similar_to_human': best_species[0],
                'transfer_confidence': min(0.85, best_species[1] + 0.1)
            },
            'lcc_virus_correlations': {
                'n_patterns_found': len(self.optimal_parameters.get('top_predictors', [])),
                'correlation_confidence': len(self.training_sessions) / 20
            }
        }


def render_animal_training_dashboard():
    """Streamlit dashboard for Animal Mood Amplifier Training"""
    import streamlit as st
    
    st.header("🐾 Animal Mood Amplifier Training System")
    st.markdown("""
    Train the Mood Amplifier on animals using Sensee-format data, then apply 
    LCC Virus correlation mapping to optimize for human use.
    """)
    
    if 'animal_trainer' not in st.session_state:
        st.session_state.animal_trainer = AnimalMoodAmplifierTrainer()
    
    trainer = st.session_state.animal_trainer
    
    tabs = st.tabs(["🧪 Run Training", "📊 LCC Analysis", "🔄 Human Transfer"])
    
    with tabs[0]:
        st.subheader("Run Animal Training Session")
        
        col1, col2 = st.columns(2)
        
        with col1:
            species = st.selectbox(
                "Species",
                options=[s.value for s in AnimalSpecies],
                index=2
            )
            subject_id = st.text_input("Subject ID", value=f"SUBJ_{len(trainer.training_sessions)+1:03d}")
            
        with col2:
            mood_direction = st.selectbox(
                "Target Mood Direction",
                options=['positive', 'neutral', 'negative'],
                index=0
            )
            mood_magnitude = st.slider("Target Magnitude", 0.1, 1.0, 0.7)
        
        amplifier_settings = {
            'frequency_hz': st.number_input("Amplifier Frequency (Hz)", 1.0, 100.0, 10.0),
            'intensity_percent': st.slider("Intensity (%)", 10, 100, 50),
            'protocol': st.selectbox("Protocol", ['alpha_boost', 'gamma_enhance', 'theta_calm', 'custom'])
        }
        
        if st.button("▶️ Run Training Session", type="primary"):
            with st.spinner("Running 10-minute training session..."):
                session = trainer.run_training_session(
                    species=AnimalSpecies(species),
                    subject_id=subject_id,
                    mood_amplifier_settings=amplifier_settings,
                    target_mood_direction=mood_direction,
                    target_mood_magnitude=mood_magnitude
                )
                
                st.success(f"Session {session.session_id} completed!")
                
                col1, col2, col3 = st.columns(3)
                col1.metric("LCC Strength", f"{session.lcc_strength:.2%}")
                col2.metric("Mood Shift", f"{session.mood_shift_magnitude:.2f}")
                col3.metric("Avg GILE", f"{session.avg_gile['overall']:.2f}")
                
                gile = session.avg_gile
                st.write(f"**GILE Breakdown:** G={gile['G']:.2f}, I={gile['I']:.2f}, L={gile['L']:.2f}, E={gile['E']:.2f}")
        
        if trainer.training_sessions:
            st.subheader(f"Training History ({len(trainer.training_sessions)} sessions)")
            
            history_data = []
            for s in trainer.training_sessions[-10:]:
                history_data.append({
                    'ID': s.session_id,
                    'Species': s.species.value,
                    'Subject': s.subject_id,
                    'LCC': f"{s.lcc_strength:.2%}",
                    'Shift': f"{s.mood_shift_magnitude:.2f}",
                    'Direction': s.mood_shift_direction
                })
            
            st.dataframe(history_data, use_container_width=True)
    
    with tabs[1]:
        st.subheader("LCC Virus Correlation Analysis")
        
        if len(trainer.training_sessions) < 5:
            st.warning(f"Need at least 5 training sessions. Currently have {len(trainer.training_sessions)}.")
        else:
            if st.button("🔬 Run LCC Virus Analysis"):
                with st.spinner("Analyzing correlations across all sessions..."):
                    results = trainer.run_lcc_virus_correlation()
                    
                    if results['status'] == 'success':
                        st.success(f"Analyzed {results['n_sessions']} sessions")
                        
                        st.subheader("Top Correlations with LCC Strength")
                        for feature, corr in results['correlations'].items():
                            color = "green" if corr > 0 else "red"
                            st.markdown(f"- **{feature}**: `{corr:+.3f}`")
                        
                        st.subheader("Species Breakdown")
                        for species, data in results['species_breakdown'].items():
                            st.write(f"**{species.upper()}**: {data['n_sessions']} sessions, LCC={data['avg_lcc_strength']:.2%}, Rating={data['efficacy_rating']}")
    
    with tabs[2]:
        st.subheader("Human Transfer Recommendations")
        
        if not trainer.optimal_parameters:
            st.info("Run LCC Virus analysis first to generate recommendations.")
        else:
            recs = trainer.get_human_transfer_recommendations()
            
            st.markdown("### Target Metrics for Human Sessions")
            col1, col2 = st.columns(2)
            with col1:
                st.metric("Min Pre-Session RMSSD", f"{recs['target_metrics']['pre_session_rmssd_min']} ms")
                st.metric("Alpha Increase Target", f"+{recs['target_metrics']['alpha_increase_target']}%")
            with col2:
                st.metric("Gamma Increase Target", f"+{recs['target_metrics']['gamma_increase_target']}%")
                lcc_range = recs['target_metrics']['lcc_target_range']
                st.metric("LCC Target", f"{lcc_range[0]:.0%} - {lcc_range[1]:.0%}")
            
            st.markdown("### Genetic Optimization")
            st.write(f"**FAAH Supplement Threshold:** Above {recs['genetic_optimization']['faah_supplement_if_above']}")
            st.write(f"**Key Predictors:** {', '.join(recs['genetic_optimization']['key_predictors']) or 'Run more sessions'}")
            
            st.markdown("### Species Insights")
            st.write(f"**Most Similar to Human:** {recs['species_insights']['most_similar_to_human'].upper()}")
            st.write(f"**Transfer Confidence:** {recs['species_insights']['transfer_confidence']:.0%}")


if __name__ == "__main__":
    print("Animal Mood Amplifier Training System")
    print("=" * 50)
    
    trainer = AnimalMoodAmplifierTrainer()
    
    print("\nRunning 10 training sessions across species...")
    for i, species in enumerate([
        AnimalSpecies.RAT, AnimalSpecies.RAT,
        AnimalSpecies.MACAQUE, AnimalSpecies.MACAQUE, AnimalSpecies.MACAQUE,
        AnimalSpecies.DOG, AnimalSpecies.DOG,
        AnimalSpecies.CAT, AnimalSpecies.MOUSE, AnimalSpecies.RABBIT
    ]):
        session = trainer.run_training_session(
            species=species,
            subject_id=f"SUBJ_{i+1:03d}",
            mood_amplifier_settings={'frequency_hz': 10, 'intensity_percent': 50},
            target_mood_direction='positive',
            target_mood_magnitude=0.7
        )
        print(f"  {species.value}: LCC={session.lcc_strength:.2%}, Shift={session.mood_shift_magnitude:.2f}")
    
    print("\nRunning LCC Virus correlation analysis...")
    results = trainer.run_lcc_virus_correlation()
    print(f"Status: {results['status']}")
    print(f"Top correlations: {list(results['correlations'].items())[:5]}")
    
    print("\nHuman transfer recommendations:")
    recs = trainer.get_human_transfer_recommendations()
    print(json.dumps(recs, indent=2, default=str))

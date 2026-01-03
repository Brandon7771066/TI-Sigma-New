"""
Animal Testing Simulation Module

Simulates observational safety and efficacy testing on animal subjects.
Generates realistic EEG data, analyzes mood shifts, tests for side effects,
and explores physical mechanisms including quantum entanglement comparisons.
"""

import numpy as np
from scipy import signal, stats
from scipy.fft import fft, fftfreq
from typing import Dict, List, Tuple, Optional
import warnings
warnings.filterwarnings('ignore')


class AnimalSubject:
    """Represents a single animal subject in the study"""
    
    def __init__(self, subject_id: int, species: str = "rat", baseline_mood: str = "neutral"):
        self.subject_id = subject_id
        self.species = species
        self.baseline_mood = baseline_mood
        self.baseline_eeg = None
        self.post_intervention_eeg = None
        self.baseline_fnirs = None  # NEW: fNIRS baseline data
        self.post_intervention_fnirs = None  # NEW: fNIRS post-intervention
        self.behavioral_observations = []
        
    def __repr__(self):
        return f"Subject {self.subject_id} ({self.species}, baseline: {self.baseline_mood})"


class EEGGenerator:
    """Generates realistic EEG signals for animal subjects"""
    
    def __init__(self, sampling_rate: int = 250):
        self.sampling_rate = sampling_rate
        
    def generate_baseline_eeg(
        self, 
        duration_seconds: float,
        mood_state: str = "neutral",
        n_channels: int = 16
    ) -> np.ndarray:
        """
        Generate baseline EEG with mood-specific characteristics
        
        Args:
            duration_seconds: Length of recording in seconds
            mood_state: One of 'stressed', 'neutral', 'positive'
            n_channels: Number of EEG channels
            
        Returns:
            EEG data of shape (n_channels, n_samples)
        """
        n_samples = int(duration_seconds * self.sampling_rate)
        eeg = np.zeros((n_channels, n_samples))
        
        # Frequency bands (in Hz)
        delta = (0.5, 4)    # Deep sleep, stress
        theta = (4, 8)      # Drowsiness, emotion
        alpha = (8, 13)     # Relaxed wakefulness
        beta = (13, 30)     # Active thinking, anxiety
        gamma = (30, 50)    # High-level processing
        
        # Mood-specific power distributions
        if mood_state == "stressed":
            power_dist = {
                'delta': 0.3, 'theta': 0.25, 'alpha': 0.15, 'beta': 0.25, 'gamma': 0.05
            }
        elif mood_state == "positive":
            power_dist = {
                'delta': 0.15, 'theta': 0.2, 'alpha': 0.35, 'beta': 0.2, 'gamma': 0.1
            }
        else:  # neutral
            power_dist = {
                'delta': 0.2, 'theta': 0.25, 'alpha': 0.25, 'beta': 0.2, 'gamma': 0.1
            }
        
        # Generate signal for each channel
        for ch in range(n_channels):
            # Add band-specific components
            for band, (low, high) in [
                ('delta', delta), ('theta', theta), ('alpha', alpha),
                ('beta', beta), ('gamma', gamma)
            ]:
                # Random frequency within band
                freq = np.random.uniform(low, high)
                # Phase
                phase = np.random.uniform(0, 2*np.pi)
                # Amplitude based on power distribution
                amplitude = np.sqrt(power_dist[band]) * np.random.uniform(5, 15)
                
                # Generate wave
                t = np.arange(n_samples) / self.sampling_rate
                eeg[ch] += amplitude * np.sin(2 * np.pi * freq * t + phase)
            
            # Add pink noise (1/f noise - characteristic of neural signals)
            pink_noise = self._generate_pink_noise(n_samples)
            eeg[ch] += pink_noise * 2
            
            # Add channel-specific offset
            eeg[ch] += np.random.uniform(-5, 5)
        
        return eeg
    
    def _generate_pink_noise(self, n_samples: int) -> np.ndarray:
        """Generate pink (1/f) noise"""
        # Generate white noise
        white = np.random.randn(n_samples)
        
        # FFT
        fft_white = fft(white)
        freqs = fftfreq(n_samples, 1/self.sampling_rate)
        
        # Apply 1/f filter (avoid division by zero)
        freqs_abs = np.abs(freqs)
        freqs_abs[freqs_abs < 1] = 1
        pink_filter = 1 / np.sqrt(freqs_abs)
        
        # Apply filter and inverse FFT
        fft_pink = fft_white * pink_filter
        pink = np.fft.ifft(fft_pink).real
        
        # Normalize
        pink = pink / np.std(pink)
        
        return pink
    
    def apply_mood_shift(
        self,
        baseline_eeg: np.ndarray,
        shift_direction: str,
        shift_magnitude: float
    ) -> np.ndarray:
        """
        Apply mood amplifier effects to baseline EEG
        
        Args:
            baseline_eeg: Original EEG data
            shift_direction: 'positive', 'negative', or 'neutral'
            shift_magnitude: How strong the effect (0.0 to 1.0)
            
        Returns:
            Modified EEG data
        """
        n_channels, n_samples = baseline_eeg.shape
        modified_eeg = baseline_eeg.copy()
        
        if shift_direction == 'positive':
            # Increase alpha (relaxation), decrease beta (anxiety)
            for ch in range(n_channels):
                # Bandpass filter for alpha
                sos_alpha = signal.butter(4, [8, 13], 'bandpass', fs=self.sampling_rate, output='sos')
                alpha_component = signal.sosfilt(sos_alpha, baseline_eeg[ch])
                
                # Bandpass filter for beta
                sos_beta = signal.butter(4, [13, 30], 'bandpass', fs=self.sampling_rate, output='sos')
                beta_component = signal.sosfilt(sos_beta, baseline_eeg[ch])
                
                # Amplify alpha, reduce beta
                modified_eeg[ch] += alpha_component * shift_magnitude * 0.3
                modified_eeg[ch] -= beta_component * shift_magnitude * 0.2
                
        elif shift_direction == 'negative':
            # Increase beta (stress), decrease alpha
            for ch in range(n_channels):
                sos_alpha = signal.butter(4, [8, 13], 'bandpass', fs=self.sampling_rate, output='sos')
                alpha_component = signal.sosfilt(sos_alpha, baseline_eeg[ch])
                
                sos_beta = signal.butter(4, [13, 30], 'bandpass', fs=self.sampling_rate, output='sos')
                beta_component = signal.sosfilt(sos_beta, baseline_eeg[ch])
                
                modified_eeg[ch] -= alpha_component * shift_magnitude * 0.2
                modified_eeg[ch] += beta_component * shift_magnitude * 0.3
        
        return modified_eeg


class fNIRSGenerator:
    """Generates realistic fNIRS signals (HbO2, HbR, oxygenation) for animal subjects"""
    
    def __init__(self, sampling_rate: int = 10):
        """fNIRS typically sampled at 10 Hz"""
        self.sampling_rate = sampling_rate
        
    def generate_baseline_fnirs(
        self,
        duration_seconds: float,
        mood_state: str = "neutral",
        species: str = "rat"
    ) -> Dict:
        """
        Generate baseline fNIRS data (HbO2, HbR, oxygenation)
        
        Args:
            duration_seconds: Length of recording in seconds
            mood_state: One of 'stressed', 'neutral', 'positive'
            species: Animal species (affects baseline values)
            
        Returns:
            Dictionary with HbO2, HbR, oxygenation time series
        """
        n_samples = int(duration_seconds * self.sampling_rate)
        
        # Species-specific baseline parameters (μM concentrations)
        species_params = {
            'rat': {'hbo2_base': 45, 'hbr_base': 25},
            'mouse': {'hbo2_base': 42, 'hbr_base': 23},
            'guinea pig': {'hbo2_base': 47, 'hbr_base': 26},
            'macaque': {'hbo2_base': 50, 'hbr_base': 28},  # Primate baseline
            'marmoset': {'hbo2_base': 48, 'hbr_base': 27}  # Primate baseline
        }
        
        params = species_params.get(species, species_params['rat'])
        
        # Mood-specific modulation
        if mood_state == "stressed":
            hbo2_mean = params['hbo2_base'] - 5  # Reduced oxygenation under stress
            hbr_mean = params['hbr_base'] + 3   # Increased deoxygenation
            variability = 1.3  # Higher variability under stress
        elif mood_state == "positive":
            hbo2_mean = params['hbo2_base'] + 3  # Increased oxygenation when positive
            hbr_mean = params['hbr_base'] - 2   # Decreased deoxygenation
            variability = 0.8  # Lower variability when relaxed
        else:  # neutral
            hbo2_mean = params['hbo2_base']
            hbr_mean = params['hbr_base']
            variability = 1.0
        
        # Generate physiological oscillations
        t = np.arange(n_samples) / self.sampling_rate
        
        # CORRECTED: Physiologically accurate frequency ranges
        # Cardiac oscillation (Hz -> BPM = Hz * 60)
        if species in ['macaque', 'marmoset']:
            cardiac_freq = np.random.uniform(1.0, 1.5)  # Hz (60-90 BPM for primates)
        elif species == 'mouse':
            cardiac_freq = np.random.uniform(8, 12)  # Hz (480-720 BPM for mice)
        elif species == 'rat':
            cardiac_freq = np.random.uniform(6, 8)  # Hz (360-480 BPM for rats)
        else:  # guinea pig and others
            cardiac_freq = np.random.uniform(5, 7)  # Hz (300-420 BPM)
        
        # Respiratory oscillation (CORRECTED frequencies)
        if species in ['macaque', 'marmoset']:
            resp_freq = np.random.uniform(0.2, 0.4)  # Hz (12-24 breaths/min for primates)
        else:  # rodents
            resp_freq = np.random.uniform(1.0, 3.0)  # Hz (60-180 breaths/min for rodents)
        
        # Very slow vasomotion (~0.01-0.1 Hz)
        vaso_freq = np.random.uniform(0.01, 0.1)
        
        # CRITICAL FIX: Generate oscillations with SHARED PHASES for anti-correlation
        cardiac_phase = np.random.uniform(0, 2*np.pi)
        resp_phase = np.random.uniform(0, 2*np.pi)
        vaso_phase = np.random.uniform(0, 2*np.pi)
        
        # Base oscillation (same for both HbO2 and HbR, but with opposite signs)
        cardiac_osc = np.sin(2 * np.pi * cardiac_freq * t + cardiac_phase)
        resp_osc = np.sin(2 * np.pi * resp_freq * t + resp_phase)
        vaso_osc = np.sin(2 * np.pi * vaso_freq * t + vaso_phase)
        
        # Generate HbO2 signal (oxygenated hemoglobin increases with activity)
        hbo2 = hbo2_mean + \
               1.5 * cardiac_osc + \
               0.8 * resp_osc + \
               0.5 * vaso_osc + \
               np.random.normal(0, variability, n_samples)
        
        # Generate HbR signal (ENFORCED anti-correlation via same phases, opposite signs)
        # HbR decreases when HbO2 increases (opposite relationship)
        hbr = hbr_mean - \
              0.8 * cardiac_osc - \
              0.5 * resp_osc - \
              0.3 * vaso_osc + \
              np.random.normal(0, variability * 0.7, n_samples)
        
        # Ensure physiologically plausible values
        hbo2 = np.clip(hbo2, 20, 80)
        hbr = np.clip(hbr, 10, 50)
        
        # Calculate oxygenation percentage
        oxygenation = (hbo2 / (hbo2 + hbr)) * 100
        
        return {
            'hbo2': hbo2,
            'hbr': hbr,
            'oxygenation': oxygenation,
            'timestamps': t
        }
    
    def apply_mood_shift_fnirs(
        self,
        baseline_fnirs: Dict,
        shift_direction: str,
        shift_magnitude: float
    ) -> Dict:
        """
        Apply mood amplifier effects to baseline fNIRS
        
        Args:
            baseline_fnirs: Original fNIRS data
            shift_direction: 'positive', 'negative', or 'neutral'
            shift_magnitude: How strong the effect (0.0 to 1.0)
            
        Returns:
            Modified fNIRS data
        """
        modified_fnirs = {
            'hbo2': baseline_fnirs['hbo2'].copy(),
            'hbr': baseline_fnirs['hbr'].copy(),
            'timestamps': baseline_fnirs['timestamps'].copy()
        }
        
        if shift_direction == 'positive':
            # Positive mood: Increase HbO2 (better oxygenation), decrease HbR
            modified_fnirs['hbo2'] += shift_magnitude * np.random.uniform(3, 7, len(modified_fnirs['hbo2']))
            modified_fnirs['hbr'] -= shift_magnitude * np.random.uniform(1, 3, len(modified_fnirs['hbr']))
            
        elif shift_direction == 'negative':
            # Negative mood: Decrease HbO2, increase HbR (stress response)
            modified_fnirs['hbo2'] -= shift_magnitude * np.random.uniform(2, 5, len(modified_fnirs['hbo2']))
            modified_fnirs['hbr'] += shift_magnitude * np.random.uniform(1, 4, len(modified_fnirs['hbr']))
        
        # Ensure physiological bounds
        modified_fnirs['hbo2'] = np.clip(modified_fnirs['hbo2'], 20, 80)
        modified_fnirs['hbr'] = np.clip(modified_fnirs['hbr'], 10, 50)
        
        # Recalculate oxygenation
        modified_fnirs['oxygenation'] = (
            modified_fnirs['hbo2'] / (modified_fnirs['hbo2'] + modified_fnirs['hbr'])
        ) * 100
        
        return modified_fnirs


class fNIRSEEGComparator:
    """Compares fNIRS and EEG modalities to validate consistent mood shift detection"""
    
    @staticmethod
    def compare_modalities(
        baseline_fnirs: Dict,
        post_fnirs: Dict,
        baseline_eeg: np.ndarray,
        post_eeg: np.ndarray
    ) -> Dict:
        """
        Compare fNIRS and EEG to check if both modalities detect the same mood shift
        
        Returns:
            Dictionary with comparison metrics and agreement score
        """
        # FNIRS mood direction from oxygenation change
        baseline_oxy = np.mean(baseline_fnirs['oxygenation'])
        post_oxy = np.mean(post_fnirs['oxygenation'])
        fnirs_oxy_change = post_oxy - baseline_oxy
        
        # fNIRS HbO2/HbR ratio change (another indicator)
        baseline_hbo2_mean = np.mean(baseline_fnirs['hbo2'])
        post_hbo2_mean = np.mean(post_fnirs['hbo2'])
        fnirs_hbo2_change = post_hbo2_mean - baseline_hbo2_mean
        
        # EEG mood direction from alpha/beta ratio
        from scipy import signal as sp_signal
        sampling_rate = 250
        
        def compute_alpha_beta_ratio(eeg):
            """Compute alpha/beta power ratio across channels"""
            ratios = []
            for ch in range(eeg.shape[0]):
                freqs, psd = sp_signal.welch(eeg[ch], fs=sampling_rate, nperseg=min(256, eeg.shape[1]//4))
                alpha_power = np.mean(psd[(freqs >= 8) & (freqs <= 13)])
                beta_power = np.mean(psd[(freqs >= 13) & (freqs <= 30)])
                ratios.append(alpha_power / (beta_power + 1e-10))
            return np.mean(ratios)
        
        baseline_ab_ratio = compute_alpha_beta_ratio(baseline_eeg)
        post_ab_ratio = compute_alpha_beta_ratio(post_eeg)
        eeg_ab_change = post_ab_ratio - baseline_ab_ratio
        
        # Determine mood shift direction from each modality
        # fNIRS: Positive shift -> increased oxygenation
        if fnirs_oxy_change > 2:
            fnirs_direction = 'positive'
        elif fnirs_oxy_change < -2:
            fnirs_direction = 'negative'
        else:
            fnirs_direction = 'neutral'
        
        # EEG: Positive shift -> increased alpha/beta ratio
        if eeg_ab_change > 0.1:
            eeg_direction = 'positive'
        elif eeg_ab_change < -0.1:
            eeg_direction = 'negative'
        else:
            eeg_direction = 'neutral'
        
        # Check agreement
        modalities_agree = (fnirs_direction == eeg_direction)
        
        # Correlation between fNIRS oxygenation and EEG alpha power
        # (Both should increase with positive mood)
        oxy_timeseries = post_fnirs['oxygenation'] - baseline_oxy
        
        # Resample EEG alpha to match fNIRS sampling rate (10 Hz)
        # Simple approach: compute alpha envelope
        alpha_envelope = []
        for ch in range(post_eeg.shape[0]):
            sos_alpha = sp_signal.butter(4, [8, 13], 'bandpass', fs=sampling_rate, output='sos')
            alpha_signal = sp_signal.sosfilt(sos_alpha, post_eeg[ch])
            # Envelope via Hilbert transform
            analytic = sp_signal.hilbert(alpha_signal)
            envelope = np.abs(analytic)
            alpha_envelope.append(envelope)
        
        avg_alpha_envelope = np.mean(alpha_envelope, axis=0)
        
        # Downsample to fNIRS rate
        from scipy.interpolate import interp1d
        eeg_time = np.linspace(0, len(avg_alpha_envelope)/sampling_rate, len(avg_alpha_envelope))
        fnirs_time = baseline_fnirs['timestamps']
        
        if len(fnirs_time) > 2 and len(eeg_time) > 2:
            interp_func = interp1d(eeg_time, avg_alpha_envelope, kind='linear', fill_value='extrapolate')
            alpha_resampled = interp_func(fnirs_time)
            
            # Compute correlation
            if len(alpha_resampled) == len(oxy_timeseries):
                correlation = np.corrcoef(oxy_timeseries, alpha_resampled)[0, 1]
            else:
                correlation = 0.0
        else:
            correlation = 0.0
        
        return {
            'fnirs_oxygenation_change_percent': fnirs_oxy_change,
            'fnirs_hbo2_change_uM': fnirs_hbo2_change,
            'fnirs_detected_direction': fnirs_direction,
            'eeg_alpha_beta_ratio_change': eeg_ab_change,
            'eeg_detected_direction': eeg_direction,
            'modalities_agree': modalities_agree,
            'fnirs_eeg_correlation': correlation,
            'agreement_strength': 'high' if (modalities_agree and abs(correlation) > 0.5) else 'low'
        }


class SafetyAnalyzer:
    """Analyzes EEG data for signs of brain damage or negative side effects"""
    
    @staticmethod
    def detect_abnormalities(eeg: np.ndarray, sampling_rate: int = 250) -> Dict:
        """
        Detect abnormal patterns that might indicate brain damage
        
        Returns:
            Dictionary with safety metrics
        """
        n_channels, n_samples = eeg.shape
        
        # 1. Seizure-like activity (excessive high-frequency synchronization)
        seizure_score = 0
        for ch in range(n_channels):
            # High-pass filter for high frequencies
            sos = signal.butter(4, 30, 'highpass', fs=sampling_rate, output='sos')
            high_freq = signal.sosfilt(sos, eeg[ch])
            
            # Check for excessive power
            if np.std(high_freq) > 15:  # Abnormally high
                seizure_score += 1
        
        seizure_risk = (seizure_score / n_channels) * 100
        
        # 2. Abnormal amplitude (cell death indicator)
        mean_amplitude = np.mean(np.abs(eeg))
        amplitude_normal = 5 <= mean_amplitude <= 50
        
        # 3. Loss of frequency diversity (flattening)
        freq_diversity_scores = []
        for ch in range(n_channels):
            # Compute power spectrum
            freqs, psd = signal.welch(eeg[ch], fs=sampling_rate, nperseg=min(256, n_samples//4))
            
            # Shannon entropy of power distribution
            psd_norm = psd / np.sum(psd)
            entropy = -np.sum(psd_norm * np.log(psd_norm + 1e-10))
            freq_diversity_scores.append(entropy)
        
        mean_diversity = np.mean(freq_diversity_scores)
        diversity_healthy = mean_diversity > 2.0  # Threshold for healthy diversity
        
        # 4. Hemispheric asymmetry (extreme imbalance can indicate damage)
        if n_channels >= 8:
            left_channels = eeg[:n_channels//2, :]
            right_channels = eeg[n_channels//2:, :]
            
            left_power = np.mean(np.var(left_channels, axis=1))
            right_power = np.mean(np.var(right_channels, axis=1))
            
            asymmetry_ratio = abs(left_power - right_power) / (left_power + right_power + 1e-10)
            asymmetry_normal = asymmetry_ratio < 0.4  # Less than 40% difference
        else:
            asymmetry_normal = True
            asymmetry_ratio = 0
        
        # Overall safety score
        safety_indicators = [
            seizure_risk < 10,  # Less than 10% channels showing seizure-like activity
            amplitude_normal,
            diversity_healthy,
            asymmetry_normal
        ]
        
        safety_score = sum(safety_indicators) / len(safety_indicators) * 100
        
        return {
            'safety_score': safety_score,
            'seizure_risk_percent': seizure_risk,
            'amplitude_normal': amplitude_normal,
            'mean_amplitude': mean_amplitude,
            'frequency_diversity_healthy': diversity_healthy,
            'mean_diversity': mean_diversity,
            'hemispheric_asymmetry_normal': asymmetry_normal,
            'asymmetry_ratio': asymmetry_ratio,
            'overall_safe': safety_score >= 75
        }
    
    @staticmethod
    def behavioral_assessment(subject: AnimalSubject) -> Dict:
        """
        Simulate behavioral observation scoring
        
        Returns:
            Behavioral safety metrics
        """
        # Simulate observations
        behaviors = {
            'motor_coordination': np.random.uniform(0.85, 1.0),  # High = normal
            'grooming_behavior': np.random.uniform(0.8, 1.0),
            'social_interaction': np.random.uniform(0.75, 1.0),
            'feeding_behavior': np.random.uniform(0.85, 1.0),
            'exploratory_activity': np.random.uniform(0.7, 1.0),
            'aggression_level': np.random.uniform(0.0, 0.15),  # Low = normal
            'stereotyped_behavior': np.random.uniform(0.0, 0.1),  # Low = normal
        }
        
        # Overall behavioral score
        positive_indicators = [
            behaviors['motor_coordination'],
            behaviors['grooming_behavior'],
            behaviors['social_interaction'],
            behaviors['feeding_behavior'],
            behaviors['exploratory_activity']
        ]
        
        negative_indicators = [
            1 - behaviors['aggression_level'],
            1 - behaviors['stereotyped_behavior']
        ]
        
        behavioral_score = np.mean(positive_indicators + negative_indicators) * 100
        
        return {
            'behavioral_score': behavioral_score,
            'behaviors': behaviors,
            'no_adverse_behaviors': behavioral_score >= 80
        }


class MoodShiftAnalyzer:
    """Analyzes magnitude and direction of mood shifts from EEG data"""
    
    @staticmethod
    def compute_mood_metrics(eeg: np.ndarray, sampling_rate: int = 250) -> Dict:
        """
        Compute mood-related metrics from EEG
        
        Returns:
            Valence and arousal estimates
        """
        n_channels, n_samples = eeg.shape
        
        # Frontal alpha asymmetry (valence indicator)
        # Left > Right alpha = positive mood
        # Right > Left alpha = negative mood
        
        if n_channels >= 4:
            # Assume first half = left, second half = right
            left_frontal = eeg[:n_channels//4, :]
            right_frontal = eeg[n_channels//4:n_channels//2, :]
            
            # Compute alpha power
            left_alpha = []
            right_alpha = []
            
            for ch in range(left_frontal.shape[0]):
                sos = signal.butter(4, [8, 13], 'bandpass', fs=sampling_rate, output='sos')
                left_filt = signal.sosfilt(sos, left_frontal[ch])
                right_filt = signal.sosfilt(sos, right_frontal[ch])
                
                left_alpha.append(np.var(left_filt))
                right_alpha.append(np.var(right_filt))
            
            left_power = np.mean(left_alpha)
            right_power = np.mean(right_alpha)
            
            # Asymmetry score: negative = more left (positive mood)
            asymmetry = (right_power - left_power) / (right_power + left_power + 1e-10)
            
            # Convert to valence scale (-1 to +1)
            valence = -asymmetry  # Flip sign so positive = positive mood
        else:
            valence = 0
        
        # Arousal from beta power
        beta_powers = []
        for ch in range(n_channels):
            sos = signal.butter(4, [13, 30], 'bandpass', fs=sampling_rate, output='sos')
            beta_filt = signal.sosfilt(sos, eeg[ch])
            beta_powers.append(np.var(beta_filt))
        
        mean_beta = np.mean(beta_powers)
        # Normalize arousal to -1 to +1 range (0 = low arousal)
        arousal = np.tanh((mean_beta - 50) / 50)
        
        return {
            'valence': valence,
            'arousal': arousal,
            'alpha_asymmetry': asymmetry if n_channels >= 4 else 0,
            'beta_power': mean_beta
        }
    
    @staticmethod
    def analyze_mood_shift(
        baseline_metrics: Dict,
        post_metrics: Dict
    ) -> Dict:
        """
        Analyze the change in mood between baseline and post-intervention
        
        Returns:
            Shift analysis including magnitude and direction
        """
        valence_shift = post_metrics['valence'] - baseline_metrics['valence']
        arousal_shift = post_metrics['arousal'] - baseline_metrics['arousal']
        
        # Overall shift magnitude
        shift_magnitude = np.sqrt(valence_shift**2 + arousal_shift**2)
        
        # Direction classification
        if abs(valence_shift) < 0.1 and abs(arousal_shift) < 0.1:
            direction = 'no_change'
            strength = 'none'
        else:
            if valence_shift > 0:
                direction = 'positive' if arousal_shift > 0 else 'calm_positive'
            else:
                direction = 'negative' if arousal_shift > 0 else 'calm_negative'
            
            # Strength classification
            if shift_magnitude < 0.2:
                strength = 'weak'
            elif shift_magnitude < 0.5:
                strength = 'moderate'
            else:
                strength = 'strong'
        
        return {
            'valence_shift': valence_shift,
            'arousal_shift': arousal_shift,
            'shift_magnitude': shift_magnitude,
            'direction': direction,
            'strength': strength,
            'baseline': baseline_metrics,
            'post_intervention': post_metrics
        }


class QuantumEntanglementComparator:
    """
    Compares coupling mechanisms to quantum entanglement
    Analyzes mathematical and behavioral similarities
    """
    
    @staticmethod
    def compute_coupling_strength(eeg1: np.ndarray, eeg2: np.ndarray) -> float:
        """
        Compute coupling strength between two EEG signals
        Uses cross-correlation as measure of coupling
        """
        # Average across channels
        sig1 = np.mean(eeg1, axis=0)
        sig2 = np.mean(eeg2, axis=0)
        
        # Normalize
        sig1 = (sig1 - np.mean(sig1)) / (np.std(sig1) + 1e-10)
        sig2 = (sig2 - np.mean(sig2)) / (np.std(sig2) + 1e-10)
        
        # Cross-correlation
        correlation = np.correlate(sig1, sig2, mode='valid')[0] / len(sig1)
        
        return abs(correlation)
    
    @staticmethod
    def quantum_entanglement_similarity_analysis() -> Dict:
        """
        Analyze mathematical and behavioral similarities to quantum entanglement
        
        Returns:
            Detailed comparison metrics
        """
        
        analysis = {
            'mathematical_similarities': {
                'non_local_correlation': {
                    'description': 'Both show correlations that persist beyond classical expectations',
                    'quantum': 'Bell inequality violations (correlation > classical limit)',
                    'neural_coupling': 'Phase synchronization across spatially separated brain regions',
                    'similarity_score': 0.7,  # Moderate similarity
                    'notes': 'Neural coupling is constrained by physical connectivity, unlike quantum entanglement'
                },
                'state_superposition': {
                    'description': 'Multiple states coexisting before measurement/observation',
                    'quantum': 'Superposition of basis states until measurement collapses wavefunction',
                    'neural_coupling': 'Multiple neural patterns coexist in different frequency bands',
                    'similarity_score': 0.5,  # Weak similarity
                    'notes': 'Neural states are classical mixtures, not quantum superpositions'
                },
                'information_transfer': {
                    'description': 'How information propagates between coupled entities',
                    'quantum': 'Instantaneous correlation changes (no signal propagation)',
                    'neural_coupling': 'Information transfer via synaptic transmission (~1-10 ms delays)',
                    'similarity_score': 0.2,  # Very different
                    'notes': 'Neural coupling obeys causality and signal propagation limits'
                },
                'measurement_effects': {
                    'description': 'Impact of observation on the system',
                    'quantum': 'Measurement collapses superposition, fundamentally altering system',
                    'neural_coupling': 'EEG measurement may influence brain state (observer effect)',
                    'similarity_score': 0.6,  # Moderate similarity
                    'notes': 'Both show observer effects, but neural effects are less fundamental'
                }
            },
            'behavioral_similarities': {
                'correlation_persistence': {
                    'description': 'Correlations maintained over time',
                    'quantum': 'Entanglement persists until decoherence',
                    'neural_coupling': 'Phase locking can persist for seconds to minutes',
                    'similarity_score': 0.8,  # High similarity
                },
                'distance_independence': {
                    'description': 'Effect of spatial separation',
                    'quantum': 'Correlation strength independent of distance',
                    'neural_coupling': 'Coupling strength decreases with anatomical distance',
                    'similarity_score': 0.3,  # Low similarity
                },
                'threshold_behavior': {
                    'description': 'Presence of critical thresholds',
                    'quantum': 'Quantum phase transitions at critical points',
                    'neural_coupling': 'Synchronization transitions at critical coupling strengths',
                    'similarity_score': 0.75,  # High similarity
                }
            },
            'key_differences': [
                'Quantum entanglement is fundamentally non-local; neural coupling requires physical connections',
                'Quantum states are discrete (quantized); neural states are continuous',
                'Quantum entanglement violates Bell inequalities; neural coupling does not',
                'Decoherence destroys quantum effects at brain temperatures; neural effects are robust',
                'Quantum entanglement cannot transmit classical information; neural coupling clearly does'
            ],
            'overall_similarity_score': 0.52,  # Moderate overall similarity
            'conclusion': 'Neural coupling shares some mathematical formalism with quantum entanglement (correlation functions, phase relationships) but operates via classical mechanisms. The similarities are analogical rather than fundamental.'
        }
        
        return analysis
    
    @staticmethod
    def analyze_coupling_mechanism(coupling_strength: float) -> Dict:
        """
        Hypothesize the physical mechanism of coupling based on strength
        """
        
        mechanisms = []
        
        if coupling_strength < 0.3:
            mechanisms.append({
                'name': 'Weak Synaptic Modulation',
                'description': 'Diffuse neurotransmitter effects with minimal synchronization',
                'probability': 0.7,
                'physical_basis': 'Volume transmission of neuromodulators (serotonin, dopamine)'
            })
        
        if 0.3 <= coupling_strength < 0.6:
            mechanisms.append({
                'name': 'Network Resonance',
                'description': 'Oscillatory networks finding common resonant frequencies',
                'probability': 0.8,
                'physical_basis': 'PING (Pyramidal-Interneuron Network Gamma) and similar rhythms'
            })
            mechanisms.append({
                'name': 'Thalamocortical Synchronization',
                'description': 'Thalamus acting as pacemaker to synchronize cortical regions',
                'probability': 0.6,
                'physical_basis': 'Thalamic relay neurons and reticular nucleus interactions'
            })
        
        if 0.6 <= coupling_strength < 0.85:
            mechanisms.append({
                'name': 'Strong Phase Locking',
                'description': 'Neural populations locking to common phase across regions',
                'probability': 0.9,
                'physical_basis': 'Long-range synchronization via white matter tracts'
            })
            mechanisms.append({
                'name': 'Cross-Frequency Coupling',
                'description': 'Nested oscillations coupling different frequency bands',
                'probability': 0.7,
                'physical_basis': 'Phase-amplitude coupling (PAC) mechanisms'
            })
        
        if coupling_strength >= 0.85:
            mechanisms.append({
                'name': 'Hypersynchronization',
                'description': 'Excessive synchronization approaching pathological levels',
                'probability': 0.8,
                'physical_basis': 'Similar to pre-ictal states; may indicate over-coupling',
                'warning': 'This level of coupling may be unstable or indicate seizure risk'
            })
        
        return {
            'coupling_strength': coupling_strength,
            'regime': 'weak' if coupling_strength < 0.3 else
                     'moderate' if coupling_strength < 0.6 else
                     'strong' if coupling_strength < 0.85 else
                     'hypersynchronized',
            'proposed_mechanisms': mechanisms,
            'confidence': 0.6 if len(mechanisms) > 0 else 0.3
        }


class BrainAlterationHypothesizer:
    """
    Generates hypotheses about how the brain is altered by coupling
    Based on EEG patterns and coupling strength
    """
    
    @staticmethod
    def generate_hypotheses(
        mood_shift: Dict,
        safety_metrics: Dict,
        coupling_strength: float
    ) -> Dict:
        """
        Generate evidence-based hypotheses about brain alterations
        """
        
        hypotheses = {
            'structural_changes': [],
            'functional_changes': [],
            'neurochemical_changes': [],
            'risk_assessment': {},
            'reversibility': {}
        }
        
        # Analyze mood shift direction and magnitude
        shift_direction = mood_shift['direction']
        shift_strength = mood_shift['strength']
        
        # Functional changes (always present with mood shift)
        if shift_strength != 'none':
            hypotheses['functional_changes'].append({
                'hypothesis': 'Altered Prefrontal-Limbic Connectivity',
                'evidence': f"{shift_strength.capitalize()} {shift_direction} mood shift detected",
                'mechanism': 'Changes in functional connectivity between PFC and amygdala/hippocampus',
                'timeframe': 'Acute (minutes to hours)',
                'reversibility': 'Likely reversible'
            })
            
            hypotheses['functional_changes'].append({
                'hypothesis': 'Modified Oscillatory Patterns',
                'evidence': f"Valence shift: {mood_shift['valence_shift']:.3f}, Arousal shift: {mood_shift['arousal_shift']:.3f}",
                'mechanism': 'Altered balance of alpha/beta rhythms affecting mood regulation',
                'timeframe': 'Immediate (seconds to minutes)',
                'reversibility': 'Highly reversible'
            })
        
        # Neurochemical changes
        if shift_direction in ['positive', 'calm_positive']:
            hypotheses['neurochemical_changes'].append({
                'hypothesis': 'Increased Serotonergic/Dopaminergic Tone',
                'evidence': 'Positive valence shift observed',
                'mechanism': 'Enhanced monoamine neurotransmitter release or receptor sensitivity',
                'supporting_data': 'Increased alpha power (relaxation), reduced beta (anxiety)',
                'reversibility': 'Reversible over hours to days'
            })
        elif shift_direction in ['negative', 'calm_negative']:
            hypotheses['neurochemical_changes'].append({
                'hypothesis': 'Altered Stress Response Axis',
                'evidence': 'Negative valence shift observed',
                'mechanism': 'Potential HPA axis activation or altered cortisol regulation',
                'supporting_data': 'Increased beta power (stress/anxiety)',
                'reversibility': 'Reversible, but may require longer recovery'
            })
        
        # Structural changes (only with very strong coupling or safety concerns)
        if coupling_strength > 0.85 or not safety_metrics.get('overall_safe', True):
            hypotheses['structural_changes'].append({
                'hypothesis': 'Risk of Synaptic Remodeling',
                'evidence': f"High coupling strength ({coupling_strength:.2f}) or safety concerns detected",
                'mechanism': 'Excessive neural activity may trigger LTP/LTD and synaptic plasticity',
                'risk_level': 'Moderate',
                'timeframe': 'Chronic (days to weeks)',
                'reversibility': 'Potentially irreversible if prolonged'
            })
        
        if safety_metrics.get('seizure_risk_percent', 0) > 10:
            hypotheses['structural_changes'].append({
                'hypothesis': 'Potential Excitotoxicity Risk',
                'evidence': f"Seizure-like activity in {safety_metrics['seizure_risk_percent']:.1f}% of channels",
                'mechanism': 'Excessive glutamate release leading to calcium overload',
                'risk_level': 'High',
                'reversibility': 'May cause permanent neuronal damage'
            })
        
        # Overall risk assessment
        if safety_metrics.get('overall_safe', True) and shift_strength in ['weak', 'moderate']:
            hypotheses['risk_assessment'] = {
                'overall_risk': 'Low',
                'recommendation': 'Intervention appears safe at current parameters',
                'monitoring': 'Continue observation for delayed effects'
            }
        elif safety_metrics.get('overall_safe', True) and shift_strength == 'strong':
            hypotheses['risk_assessment'] = {
                'overall_risk': 'Moderate',
                'recommendation': 'Strong effects observed; monitor for tolerance or adaptation',
                'monitoring': 'Assess long-term stability and reversibility'
            }
        else:
            hypotheses['risk_assessment'] = {
                'overall_risk': 'High',
                'recommendation': 'Safety concerns detected; consider reducing intervention strength',
                'monitoring': 'Immediate assessment required; check for adverse effects'
            }
        
        # Reversibility analysis
        if shift_strength == 'none':
            hypotheses['reversibility'] = {
                'predicted_recovery_time': 'N/A (no effect detected)',
                'confidence': 'High'
            }
        elif shift_strength == 'weak':
            hypotheses['reversibility'] = {
                'predicted_recovery_time': '15-30 minutes',
                'confidence': 'High',
                'mechanism': 'Natural homeostatic regulation restores baseline'
            }
        elif shift_strength == 'moderate':
            hypotheses['reversibility'] = {
                'predicted_recovery_time': '1-4 hours',
                'confidence': 'Moderate',
                'mechanism': 'Neurochemical normalization and network rebalancing'
            }
        else:  # strong
            hypotheses['reversibility'] = {
                'predicted_recovery_time': '4-24 hours',
                'confidence': 'Moderate to Low',
                'mechanism': 'May require active homeostatic compensation; potential for lasting changes',
                'note': 'Recovery time may increase with repeated exposure'
            }
        
        return hypotheses


class AnimalStudySimulator:
    """Main simulator for complete animal testing protocol"""
    
    def __init__(self, n_subjects: int = 30, species: str = "rat"):
        self.n_subjects = n_subjects
        self.species = species
        self.subjects = []
        self.eeg_generator = EEGGenerator()
        self.fnirs_generator = fNIRSGenerator()  # NEW: Add fNIRS support
        self.fnirs_eeg_comparator = fNIRSEEGComparator()  # NEW: Compare modalities
        self.safety_analyzer = SafetyAnalyzer()
        self.mood_analyzer = MoodShiftAnalyzer()
        self.quantum_comparator = QuantumEntanglementComparator()
        self.hypothesis_generator = BrainAlterationHypothesizer()
    
    def run_study(
        self,
        intervention_duration_minutes: int = 3,
        recording_duration_minutes: int = 2
    ) -> Dict:
        """
        Run complete animal study with specified parameters
        
        Args:
            intervention_duration_minutes: How long the mood amplifier is applied
            recording_duration_minutes: How long to record EEG after intervention
            
        Returns:
            Complete study results
        """
        
        print(f"\n{'='*60}")
        print(f"ANIMAL STUDY SIMULATION")
        print(f"{'='*60}")
        print(f"Subjects: {self.n_subjects} {self.species}s")
        print(f"Intervention Duration: {intervention_duration_minutes} minutes")
        print(f"Recording Duration: {recording_duration_minutes} minutes")
        print(f"{'='*60}\n")
        
        results = {
            'study_parameters': {
                'n_subjects': self.n_subjects,
                'species': self.species,
                'intervention_duration_min': intervention_duration_minutes,
                'recording_duration_min': recording_duration_minutes
            },
            'individual_results': [],
            'group_statistics': {},
            'safety_summary': {},
            'quantum_analysis': {},
            'brain_alteration_hypotheses': {}
        }
        
        # Generate baseline moods for subjects
        baseline_moods = np.random.choice(['stressed', 'neutral', 'positive'], 
                                         size=self.n_subjects,
                                         p=[0.3, 0.5, 0.2])
        
        # Run study for each subject
        for i in range(self.n_subjects):
            subject = AnimalSubject(
                subject_id=i+1,
                species=self.species,
                baseline_mood=baseline_moods[i]
            )
            
            # Generate baseline EEG
            baseline_eeg = self.eeg_generator.generate_baseline_eeg(
                duration_seconds=60,  # 1 minute baseline
                mood_state=baseline_moods[i]
            )
            subject.baseline_eeg = baseline_eeg
            
            # NEW: Generate baseline fNIRS (parallel modality)
            baseline_fnirs = self.fnirs_generator.generate_baseline_fnirs(
                duration_seconds=60,  # 1 minute baseline (same as EEG)
                mood_state=baseline_moods[i],
                species=self.species
            )
            subject.baseline_fnirs = baseline_fnirs
            
            # Compute baseline mood metrics
            baseline_metrics = self.mood_analyzer.compute_mood_metrics(baseline_eeg)
            
            # Apply intervention (simulate mood shift)
            # Most subjects show positive shift, some neutral, rare negative
            shift_probs = [0.75, 0.20, 0.05]  # positive, neutral, negative
            shift_direction = np.random.choice(['positive', 'neutral', 'negative'], p=shift_probs)
            
            # Shift magnitude depends on baseline and intervention duration
            base_magnitude = 0.3 + (intervention_duration_minutes / 10)
            magnitude_variation = np.random.uniform(0.8, 1.2)
            shift_magnitude = base_magnitude * magnitude_variation
            
            # Generate post-intervention EEG
            post_eeg = self.eeg_generator.apply_mood_shift(
                baseline_eeg,
                shift_direction,
                shift_magnitude
            )
            subject.post_intervention_eeg = post_eeg
            
            # NEW: Apply same mood shift to fNIRS (parallel modality)
            post_fnirs = self.fnirs_generator.apply_mood_shift_fnirs(
                baseline_fnirs,
                shift_direction,
                shift_magnitude
            )
            subject.post_intervention_fnirs = post_fnirs
            
            # Compute post-intervention metrics
            post_metrics = self.mood_analyzer.compute_mood_metrics(post_eeg)
            
            # Analyze mood shift
            mood_shift = self.mood_analyzer.analyze_mood_shift(
                baseline_metrics, post_metrics
            )
            
            # Safety analysis
            safety_metrics = self.safety_analyzer.detect_abnormalities(post_eeg)
            behavioral_metrics = self.safety_analyzer.behavioral_assessment(subject)
            
            # NEW: fNIRS-EEG comparison to validate modality agreement
            fnirs_eeg_comparison = self.fnirs_eeg_comparator.compare_modalities(
                baseline_fnirs,
                post_fnirs,
                baseline_eeg,
                post_eeg
            )
            
            # Coupling analysis (simulate coupling between two random subjects)
            if len(results['individual_results']) > 0:
                prev_subject_eeg = results['individual_results'][-1]['post_eeg']
                coupling = self.quantum_comparator.compute_coupling_strength(
                    post_eeg, prev_subject_eeg
                )
            else:
                coupling = np.random.uniform(0.3, 0.8)
            
            # Store individual results
            results['individual_results'].append({
                'subject_id': subject.subject_id,
                'baseline_mood': subject.baseline_mood,
                'mood_shift': mood_shift,
                'safety_metrics': safety_metrics,
                'behavioral_metrics': behavioral_metrics,
                'coupling_strength': coupling,
                'baseline_eeg': baseline_eeg,
                'post_eeg': post_eeg,
                # NEW: fNIRS data and comparison results
                'baseline_fnirs': baseline_fnirs,
                'post_fnirs': post_fnirs,
                'fnirs_eeg_comparison': fnirs_eeg_comparison
            })
            
            self.subjects.append(subject)
        
        # Compute group statistics
        results['group_statistics'] = self._compute_group_statistics(results['individual_results'])
        
        # Safety summary
        results['safety_summary'] = self._generate_safety_summary(results['individual_results'])
        
        # Quantum entanglement analysis
        results['quantum_analysis'] = self.quantum_comparator.quantum_entanglement_similarity_analysis()
        
        # Average coupling mechanism
        avg_coupling = np.mean([r['coupling_strength'] for r in results['individual_results']])
        results['coupling_mechanism'] = self.quantum_comparator.analyze_coupling_mechanism(avg_coupling)
        
        # Brain alteration hypotheses
        typical_shift = results['individual_results'][self.n_subjects//2]['mood_shift']  # Median subject
        typical_safety = results['individual_results'][self.n_subjects//2]['safety_metrics']
        
        results['brain_alteration_hypotheses'] = self.hypothesis_generator.generate_hypotheses(
            typical_shift, typical_safety, avg_coupling
        )
        
        return results
    
    def _compute_group_statistics(self, individual_results: List[Dict]) -> Dict:
        """Compute aggregate statistics across all subjects"""
        
        # Mood shift statistics
        valence_shifts = [r['mood_shift']['valence_shift'] for r in individual_results]
        arousal_shifts = [r['mood_shift']['arousal_shift'] for r in individual_results]
        shift_magnitudes = [r['mood_shift']['shift_magnitude'] for r in individual_results]
        
        # Direction counts
        directions = [r['mood_shift']['direction'] for r in individual_results]
        direction_counts = {}
        for d in set(directions):
            direction_counts[d] = directions.count(d)
        
        # Strength counts
        strengths = [r['mood_shift']['strength'] for r in individual_results]
        strength_counts = {}
        for s in set(strengths):
            strength_counts[s] = strengths.count(s)
        
        # Safety statistics
        safety_scores = [r['safety_metrics']['safety_score'] for r in individual_results]
        seizure_risks = [r['safety_metrics']['seizure_risk_percent'] for r in individual_results]
        
        # Behavioral statistics
        behavioral_scores = [r['behavioral_metrics']['behavioral_score'] for r in individual_results]
        
        # Coupling statistics
        coupling_strengths = [r['coupling_strength'] for r in individual_results]
        
        # NEW: fNIRS-EEG comparison statistics (cohort-level aggregation)
        fnirs_eeg_comparisons = [r['fnirs_eeg_comparison'] for r in individual_results]
        modality_agreements = [c['modalities_agree'] for c in fnirs_eeg_comparisons]
        correlations = [c['fnirs_eeg_correlation'] for c in fnirs_eeg_comparisons]
        agreement_strengths = [c['agreement_strength'] for c in fnirs_eeg_comparisons]
        
        # Statistical rigor: Confidence intervals and hypothesis tests
        n_agreement = len(modality_agreements)
        
        # Count valid (finite) correlations separately
        valid_correlations = [c for c in correlations if np.isfinite(c)]
        n_correlation = len(valid_correlations)
        
        # Guard against empty or tiny samples
        if n_agreement == 0:
            # No data available - return "inference unavailable" block
            p_agree = 0.0
            ci_low_agreement = 0.0
            ci_high_agreement = 0.0
            binom_p = 1.0
            mean_corr = 0.0
            ci_low_corr = 0.0
            ci_high_corr = 0.0
            t_corr = 0.0
            p_corr = 1.0
            inference_available = False
        elif n_agreement >= 10 and n_correlation >= 8:
            # Sufficient sample for reliable statistical inference
            inference_available = True
            p_agree = sum(modality_agreements) / n_agreement  # agreement rate
            
            # Wilson score binomial confidence interval for agreement rate (95% CI)
            z = 1.96  # 95% confidence
            denominator = 1 + z**2/n_agreement
            centre_adjusted_p = (p_agree + z**2/(2*n_agreement)) / denominator
            adjusted_std = np.sqrt((p_agree*(1-p_agree)/n_agreement + z**2/(4*n_agreement**2)) / denominator)
            ci_low_agreement = max(0, centre_adjusted_p - z*adjusted_std)
            ci_high_agreement = min(1, centre_adjusted_p + z*adjusted_std)
            
            # Binomial test: does agreement exceed chance (50%)?
            from scipy.stats import binomtest
            binom_result = binomtest(sum(modality_agreements), n_agreement, 0.5, alternative='greater')
            binom_p = binom_result.pvalue
            
            # Fisher z-transform for correlation confidence interval (use valid correlations only)
            mean_corr = np.mean(valid_correlations)
            if abs(mean_corr) < 0.999:  # avoid division by zero
                fisher_z = 0.5 * np.log((1 + mean_corr) / (1 - mean_corr))
                se_fisher = 1 / np.sqrt(n_correlation - 3)
                z_low = fisher_z - z * se_fisher
                z_high = fisher_z + z * se_fisher
                ci_low_corr = (np.exp(2*z_low) - 1) / (np.exp(2*z_low) + 1)
                ci_high_corr = (np.exp(2*z_high) - 1) / (np.exp(2*z_high) + 1)
            else:
                ci_low_corr = mean_corr
                ci_high_corr = mean_corr
            
            # One-sample t-test: is correlation significantly different from zero?
            t_corr, p_corr = stats.ttest_1samp(valid_correlations, 0)
        else:
            # Sample size too small for reliable CIs - mark inference unavailable
            inference_available = False
            p_agree = sum(modality_agreements) / n_agreement if n_agreement > 0 else 0.0
            ci_low_agreement = 0.0
            ci_high_agreement = 1.0
            binom_p = 1.0  # Cannot reject null
            mean_corr = np.mean(valid_correlations) if len(valid_correlations) > 0 else 0.0
            ci_low_corr = -1.0
            ci_high_corr = 1.0
            t_corr = 0.0
            p_corr = 1.0
        
        # Statistical tests
        # Test if valence shift is significantly positive
        t_stat, p_value = stats.ttest_1samp(valence_shifts, 0)
        
        return {
            'mood_shifts': {
                'mean_valence_shift': np.mean(valence_shifts),
                'std_valence_shift': np.std(valence_shifts),
                'mean_arousal_shift': np.mean(arousal_shifts),
                'std_arousal_shift': np.std(arousal_shifts),
                'mean_magnitude': np.mean(shift_magnitudes),
                'direction_distribution': direction_counts,
                'strength_distribution': strength_counts,
                'statistical_significance': {
                    't_statistic': t_stat,
                    'p_value': p_value,
                    'significantly_positive': p_value < 0.05 and t_stat > 0
                }
            },
            'safety': {
                'mean_safety_score': np.mean(safety_scores),
                'std_safety_score': np.std(safety_scores),
                'mean_seizure_risk': np.mean(seizure_risks),
                'subjects_with_safe_scores': sum(1 for s in safety_scores if s >= 75),
                'percent_safe': (sum(1 for s in safety_scores if s >= 75) / len(safety_scores)) * 100
            },
            'behavioral': {
                'mean_behavioral_score': np.mean(behavioral_scores),
                'std_behavioral_score': np.std(behavioral_scores),
                'subjects_with_normal_behavior': sum(1 for b in behavioral_scores if b >= 80),
                'percent_normal': (sum(1 for b in behavioral_scores if b >= 80) / len(behavioral_scores)) * 100
            },
            'coupling': {
                'mean_coupling_strength': np.mean(coupling_strengths),
                'std_coupling_strength': np.std(coupling_strengths),
                'min_coupling': np.min(coupling_strengths),
                'max_coupling': np.max(coupling_strengths),
                'in_target_range_0.6_0.85': sum(1 for c in coupling_strengths if 0.6 <= c <= 0.85),
                'percent_in_target_range': (sum(1 for c in coupling_strengths if 0.6 <= c <= 0.85) / len(coupling_strengths)) * 100
            },
            # NEW: fNIRS-EEG Cross-Modality Validation Statistics (with statistical rigor)
            'fnirs_eeg_validation': {
                # Descriptive statistics
                'modality_agreement_rate_percent': p_agree * 100,
                'subjects_with_agreement': sum(modality_agreements),
                'subjects_without_agreement': len(modality_agreements) - sum(modality_agreements),
                'mean_temporal_correlation': mean_corr,
                'std_temporal_correlation': np.std(correlations),
                'min_correlation': np.min(correlations),
                'max_correlation': np.max(correlations),
                'high_agreement_strength_count': sum(1 for s in agreement_strengths if s == 'high'),
                'low_agreement_strength_count': sum(1 for s in agreement_strengths if s == 'low'),
                'percent_high_agreement': (sum(1 for s in agreement_strengths if s == 'high') / len(agreement_strengths)) * 100,
                
                # Sample sizes and inference availability
                'sample_size_agreement': n_agreement,
                'sample_size_correlation': n_correlation,
                'statistical_inference_available': inference_available,
                
                # Statistical inference for agreement rate
                'agreement_95ci_low': ci_low_agreement,
                'agreement_95ci_high': ci_high_agreement,
                'agreement_exceeds_chance_p_value': binom_p,
                'agreement_significantly_above_chance': binom_p < 0.05 and inference_available,
                
                # Statistical inference for correlation
                'correlation_95ci_low': ci_low_corr,
                'correlation_95ci_high': ci_high_corr,
                'correlation_t_statistic': t_corr,
                'correlation_significantly_nonzero_p_value': p_corr,
                'correlation_significantly_positive': p_corr < 0.05 and t_corr > 0,
                
                # Data-driven interpretation (CI-based, only if inference available)
                'validation_strength': 'strong' if (inference_available and ci_low_agreement > 0.6 and ci_low_corr > 0.3) else 'moderate' if (inference_available and ci_low_agreement > 0.5) else 'insufficient_data' if not inference_available else 'weak',
                'interpretation': f'Cross-modal validation: {ci_low_agreement*100:.1f}%-{ci_high_agreement*100:.1f}% agreement (95% CI), correlation {ci_low_corr:.2f}-{ci_high_corr:.2f}' if inference_available else f'Insufficient sample size (n_agreement={n_agreement}, n_correlation={n_correlation}). Minimum required: 10 agreement, 8 correlation samples.'
            }
        }
    
    def _generate_safety_summary(self, individual_results: List[Dict]) -> Dict:
        """Generate comprehensive safety summary"""
        
        total_subjects = len(individual_results)
        
        # Count safety issues
        subjects_with_seizure_risk = sum(1 for r in individual_results 
                                         if r['safety_metrics']['seizure_risk_percent'] > 10)
        subjects_with_abnormal_amplitude = sum(1 for r in individual_results 
                                               if not r['safety_metrics']['amplitude_normal'])
        subjects_with_poor_diversity = sum(1 for r in individual_results 
                                          if not r['safety_metrics']['frequency_diversity_healthy'])
        subjects_with_asymmetry = sum(1 for r in individual_results 
                                     if not r['safety_metrics']['hemispheric_asymmetry_normal'])
        subjects_overall_unsafe = sum(1 for r in individual_results 
                                     if not r['safety_metrics']['overall_safe'])
        
        # Behavioral issues
        subjects_with_behavioral_issues = sum(1 for r in individual_results 
                                             if not r['behavioral_metrics']['no_adverse_behaviors'])
        
        return {
            'total_subjects': total_subjects,
            'safety_concerns': {
                'seizure_risk': {
                    'count': subjects_with_seizure_risk,
                    'percent': (subjects_with_seizure_risk / total_subjects) * 100
                },
                'abnormal_amplitude': {
                    'count': subjects_with_abnormal_amplitude,
                    'percent': (subjects_with_abnormal_amplitude / total_subjects) * 100
                },
                'poor_frequency_diversity': {
                    'count': subjects_with_poor_diversity,
                    'percent': (subjects_with_poor_diversity / total_subjects) * 100
                },
                'hemispheric_asymmetry': {
                    'count': subjects_with_asymmetry,
                    'percent': (subjects_with_asymmetry / total_subjects) * 100
                },
                'overall_unsafe': {
                    'count': subjects_overall_unsafe,
                    'percent': (subjects_overall_unsafe / total_subjects) * 100
                }
            },
            'behavioral_concerns': {
                'adverse_behaviors': {
                    'count': subjects_with_behavioral_issues,
                    'percent': (subjects_with_behavioral_issues / total_subjects) * 100
                }
            },
            'overall_assessment': self._interpret_safety(
                subjects_overall_unsafe, subjects_with_behavioral_issues, total_subjects
            )
        }
    
    def _interpret_safety(self, unsafe_count: int, behavioral_issues: int, total: int) -> str:
        """Interpret overall safety results"""
        
        unsafe_percent = (unsafe_count / total) * 100
        behavioral_percent = (behavioral_issues / total) * 100
        
        if unsafe_percent <= 5 and behavioral_percent <= 5:
            return "EXCELLENT: No significant safety concerns detected. Intervention appears safe."
        elif unsafe_percent <= 10 and behavioral_percent <= 10:
            return "GOOD: Minimal safety concerns. Intervention appears generally safe with low risk."
        elif unsafe_percent <= 20 and behavioral_percent <= 20:
            return "ACCEPTABLE: Some safety concerns noted. Further monitoring recommended."
        else:
            return "CONCERNING: Significant safety issues detected. Intervention parameters should be reviewed."

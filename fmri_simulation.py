"""
fMRI Simulation Module

Simulates functional Magnetic Resonance Imaging (fMRI) BOLD signals
to complement EEG analysis in animal studies.
"""

import numpy as np
from scipy import signal, stats
from typing import Dict, Tuple


class fMRISimulator:
    """Generates realistic fMRI BOLD signals for animal subjects"""
    
    def __init__(self, tr: float = 2.0):
        """
        Initialize fMRI simulator
        
        Args:
            tr: Repetition time in seconds (typically 2.0s for animal fMRI)
        """
        self.tr = tr
        
    def generate_bold_signal(
        self,
        duration_seconds: float,
        mood_state: str = "neutral",
        brain_region: str = "prefrontal_cortex"
    ) -> np.ndarray:
        """
        Generate BOLD signal for a specific brain region
        
        Args:
            duration_seconds: Length of recording
            mood_state: 'stressed', 'neutral', or 'positive'
            brain_region: Brain region to simulate
            
        Returns:
            BOLD signal time series
        """
        n_timepoints = int(duration_seconds / self.tr)
        
        # Region-specific baseline activation
        baseline_activations = {
            'prefrontal_cortex': 1.0,
            'amygdala': 0.8,
            'hippocampus': 0.7,
            'nucleus_accumbens': 0.6,
            'anterior_cingulate': 0.9,
            'ventral_striatum': 0.65,
            'insula': 0.75
        }
        
        baseline = baseline_activations.get(brain_region, 0.8)
        
        # Mood-specific modulation
        if mood_state == "stressed":
            if brain_region == "amygdala":
                modulation = 0.3  # Increased amygdala activity
            elif brain_region == "prefrontal_cortex":
                modulation = -0.2  # Decreased PFC activity
            else:
                modulation = 0.0
        elif mood_state == "positive":
            if brain_region == "nucleus_accumbens":
                modulation = 0.4  # Increased reward center activity
            elif brain_region == "prefrontal_cortex":
                modulation = 0.2  # Increased PFC activity
            elif brain_region == "amygdala":
                modulation = -0.15  # Decreased amygdala activity
            else:
                modulation = 0.1
        else:  # neutral
            modulation = 0.0
        
        # Generate signal
        signal_mean = baseline + modulation
        
        # Add physiological noise (cardiac, respiratory)
        t = np.arange(n_timepoints) * self.tr
        
        # Cardiac noise (~6 Hz in rats, aliased to BOLD frequency)
        cardiac_freq = 0.15  # After aliasing
        cardiac_noise = 0.05 * np.sin(2 * np.pi * cardiac_freq * t + np.random.uniform(0, 2*np.pi))
        
        # Respiratory noise (~1.5 Hz in rats, aliased)
        resp_freq = 0.08
        resp_noise = 0.03 * np.sin(2 * np.pi * resp_freq * t + np.random.uniform(0, 2*np.pi))
        
        # Scanner drift (slow linear trend)
        drift = np.linspace(0, 0.02, n_timepoints)
        
        # White noise
        white_noise = np.random.randn(n_timepoints) * 0.08
        
        # Combine
        bold_signal = signal_mean + cardiac_noise + resp_noise + drift + white_noise
        
        # Add hemodynamic response smoothing
        bold_signal = self._apply_hemodynamic_smoothing(bold_signal)
        
        return bold_signal
    
    def _apply_hemodynamic_smoothing(self, signal: np.ndarray) -> np.ndarray:
        """Apply hemodynamic response function smoothing"""
        # Simple Gaussian smoothing to mimic slow hemodynamic response
        window_size = 3
        kernel = np.exp(-np.linspace(-2, 2, window_size)**2)
        kernel = kernel / kernel.sum()
        
        # Pad signal
        padded = np.pad(signal, window_size//2, mode='edge')
        smoothed = np.convolve(padded, kernel, mode='valid')
        
        return smoothed
    
    def apply_mood_shift_bold(
        self,
        baseline_signal: np.ndarray,
        shift_direction: str,
        shift_magnitude: float,
        brain_region: str
    ) -> np.ndarray:
        """
        Apply mood shift effects to BOLD signal
        
        Args:
            baseline_signal: Original BOLD signal
            shift_direction: 'positive', 'negative', or 'neutral'
            shift_magnitude: Effect strength (0-1)
            brain_region: Which brain region
            
        Returns:
            Modified BOLD signal
        """
        modified = baseline_signal.copy()
        
        # Region-specific responses to mood amplifier
        if shift_direction == 'positive':
            if brain_region == 'prefrontal_cortex':
                # Increased PFC activation
                modified += shift_magnitude * 0.3
            elif brain_region == 'nucleus_accumbens':
                # Strong reward center activation
                modified += shift_magnitude * 0.5
            elif brain_region == 'amygdala':
                # Decreased amygdala (less threat processing)
                modified -= shift_magnitude * 0.25
            elif brain_region == 'anterior_cingulate':
                # Increased emotional regulation
                modified += shift_magnitude * 0.35
            else:
                modified += shift_magnitude * 0.1
                
        elif shift_direction == 'negative':
            if brain_region == 'amygdala':
                # Increased threat processing
                modified += shift_magnitude * 0.4
            elif brain_region == 'prefrontal_cortex':
                # Decreased executive control
                modified -= shift_magnitude * 0.3
            elif brain_region == 'nucleus_accumbens':
                # Decreased reward sensitivity
                modified -= shift_magnitude * 0.2
            else:
                modified -= shift_magnitude * 0.1
        
        return modified
    
    def compute_functional_connectivity(
        self,
        signal1: np.ndarray,
        signal2: np.ndarray
    ) -> float:
        """
        Compute functional connectivity between two brain regions
        
        Args:
            signal1, signal2: BOLD signals from two regions
            
        Returns:
            Correlation coefficient (functional connectivity strength)
        """
        # Pearson correlation
        correlation, _ = stats.pearsonr(signal1, signal2)
        return correlation
    
    def generate_whole_brain_activation(
        self,
        duration_seconds: float,
        mood_state: str = "neutral"
    ) -> Dict[str, np.ndarray]:
        """
        Generate BOLD signals for multiple brain regions
        
        Returns:
            Dictionary mapping region names to BOLD signals
        """
        regions = [
            'prefrontal_cortex',
            'amygdala',
            'hippocampus',
            'nucleus_accumbens',
            'anterior_cingulate',
            'ventral_striatum',
            'insula'
        ]
        
        signals = {}
        for region in regions:
            signals[region] = self.generate_bold_signal(
                duration_seconds, mood_state, region
            )
        
        return signals
    
    def analyze_network_changes(
        self,
        baseline_signals: Dict[str, np.ndarray],
        post_signals: Dict[str, np.ndarray]
    ) -> Dict:
        """
        Analyze changes in functional connectivity networks
        
        Args:
            baseline_signals: Pre-intervention BOLD signals
            post_signals: Post-intervention BOLD signals
            
        Returns:
            Network analysis results
        """
        regions = list(baseline_signals.keys())
        n_regions = len(regions)
        
        # Compute connectivity matrices
        baseline_fc = np.zeros((n_regions, n_regions))
        post_fc = np.zeros((n_regions, n_regions))
        
        for i, region1 in enumerate(regions):
            for j, region2 in enumerate(regions):
                if i != j:
                    baseline_fc[i, j] = self.compute_functional_connectivity(
                        baseline_signals[region1],
                        baseline_signals[region2]
                    )
                    post_fc[i, j] = self.compute_functional_connectivity(
                        post_signals[region1],
                        post_signals[region2]
                    )
        
        # Compute network metrics
        baseline_mean_fc = np.mean(np.abs(baseline_fc[np.triu_indices(n_regions, k=1)]))
        post_mean_fc = np.mean(np.abs(post_fc[np.triu_indices(n_regions, k=1)]))
        
        # Network integration (mean connectivity)
        integration_change = post_mean_fc - baseline_mean_fc
        
        # Network segregation (modularity-like measure)
        # Higher values = more segregated/modular
        baseline_segregation = np.std(baseline_fc[np.triu_indices(n_regions, k=1)])
        post_segregation = np.std(post_fc[np.triu_indices(n_regions, k=1)])
        segregation_change = post_segregation - baseline_segregation
        
        # Identify key connectivity changes
        fc_change = post_fc - baseline_fc
        
        # Find strongest increases
        triu_idx = np.triu_indices(n_regions, k=1)
        changes = fc_change[triu_idx]
        sorted_idx = np.argsort(np.abs(changes))[::-1]
        
        top_changes = []
        for idx in sorted_idx[:3]:  # Top 3 changes
            i, j = triu_idx[0][idx], triu_idx[1][idx]
            top_changes.append({
                'connection': f"{regions[i]} <-> {regions[j]}",
                'baseline_fc': baseline_fc[i, j],
                'post_fc': post_fc[i, j],
                'change': fc_change[i, j]
            })
        
        return {
            'baseline_mean_connectivity': baseline_mean_fc,
            'post_mean_connectivity': post_mean_fc,
            'integration_change': integration_change,
            'baseline_segregation': baseline_segregation,
            'post_segregation': post_segregation,
            'segregation_change': segregation_change,
            'connectivity_matrix_baseline': baseline_fc,
            'connectivity_matrix_post': post_fc,
            'top_connectivity_changes': top_changes,
            'interpretation': self._interpret_network_changes(
                integration_change, segregation_change
            )
        }
    
    def _interpret_network_changes(
        self,
        integration_change: float,
        segregation_change: float
    ) -> str:
        """Interpret network changes"""
        
        if integration_change > 0.05 and segregation_change < -0.05:
            return "Increased network integration with reduced segregation - brain regions working more cohesively"
        elif integration_change < -0.05 and segregation_change > 0.05:
            return "Decreased integration with increased segregation - brain regions becoming more independent"
        elif integration_change > 0.05:
            return "Increased functional connectivity overall - enhanced inter-regional communication"
        elif integration_change < -0.05:
            return "Decreased functional connectivity - reduced inter-regional communication"
        else:
            return "Subtle network reorganization with no major integration/segregation changes"
    
    def detect_bold_abnormalities(
        self,
        signals: Dict[str, np.ndarray]
    ) -> Dict:
        """
        Detect abnormal BOLD signal patterns
        
        Args:
            signals: Dictionary of BOLD signals by region
            
        Returns:
            Abnormality detection results
        """
        abnormalities = {
            'excessive_activation': [],
            'signal_dropout': [],
            'excessive_variability': [],
            'overall_safe': True
        }
        
        for region, signal in signals.items():
            # Check for excessive activation (>3 SD above normal)
            if np.mean(signal) > 2.0:  # Abnormally high
                abnormalities['excessive_activation'].append({
                    'region': region,
                    'mean_activation': np.mean(signal),
                    'severity': 'high' if np.mean(signal) > 2.5 else 'moderate'
                })
                abnormalities['overall_safe'] = False
            
            # Check for signal dropout (very low activation)
            if np.mean(signal) < 0.3:
                abnormalities['signal_dropout'].append({
                    'region': region,
                    'mean_activation': np.mean(signal),
                    'severity': 'concerning'
                })
                abnormalities['overall_safe'] = False
            
            # Check for excessive variability (unstable signal)
            if np.std(signal) > 0.5:
                abnormalities['excessive_variability'].append({
                    'region': region,
                    'std_dev': np.std(signal),
                    'severity': 'high' if np.std(signal) > 0.7 else 'moderate'
                })
        
        return abnormalities


class MultiModalAnalyzer:
    """Combines EEG and fMRI data for comprehensive analysis"""
    
    @staticmethod
    def compute_eeg_fmri_coupling(
        eeg_band_power: float,
        bold_signal: np.ndarray
    ) -> Dict:
        """
        Analyze coupling between EEG band power and fMRI BOLD signal
        
        Args:
            eeg_band_power: Power in specific frequency band
            bold_signal: BOLD signal time series
            
        Returns:
            Coupling analysis
        """
        # Simulate EEG-fMRI relationship
        # In reality, this requires complex temporal alignment
        
        # Alpha power typically anti-correlates with BOLD in task-related regions
        # Gamma power correlates positively with BOLD
        
        # Simplified correlation
        mean_bold = np.mean(bold_signal)
        
        # Estimate correlation based on neurophysiology
        if 8 <= eeg_band_power <= 13:  # Alpha-like
            # Alpha typically anti-correlates with metabolic activity
            coupling_strength = -0.3 + np.random.uniform(-0.2, 0.2)
        elif eeg_band_power >= 30:  # Gamma-like
            # Gamma correlates with local processing
            coupling_strength = 0.6 + np.random.uniform(-0.1, 0.2)
        else:
            coupling_strength = 0.2 + np.random.uniform(-0.3, 0.3)
        
        return {
            'coupling_strength': coupling_strength,
            'interpretation': 'Strong positive' if coupling_strength > 0.5 else
                            'Moderate positive' if coupling_strength > 0.2 else
                            'Weak' if abs(coupling_strength) <= 0.2 else
                            'Moderate negative' if coupling_strength > -0.5 else
                            'Strong negative'
        }
    
    @staticmethod
    def validate_mood_shift_multimodal(
        eeg_valence_shift: float,
        bold_network_change: Dict
    ) -> Dict:
        """
        Cross-validate mood shift using both EEG and fMRI
        
        Returns:
            Multimodal validation results
        """
        # Check consistency between modalities
        bold_integration_change = bold_network_change['integration_change']
        
        # Positive mood should show:
        # - Positive EEG valence shift
        # - Increased PFC-NAcc connectivity (integration)
        
        if eeg_valence_shift > 0.1 and bold_integration_change > 0.03:
            consistency = 'high'
            confidence = 0.9
            interpretation = "Both EEG and fMRI confirm positive mood shift"
        elif eeg_valence_shift > 0.1 or bold_integration_change > 0.03:
            consistency = 'moderate'
            confidence = 0.7
            interpretation = "One modality shows positive shift, other is ambiguous"
        elif eeg_valence_shift < -0.1 and bold_integration_change < -0.03:
            consistency = 'high'
            confidence = 0.9
            interpretation = "Both modalities confirm negative mood shift"
        else:
            consistency = 'low'
            confidence = 0.5
            interpretation = "Modalities show inconsistent results - needs further investigation"
        
        return {
            'consistency': consistency,
            'confidence': confidence,
            'eeg_valence': eeg_valence_shift,
            'bold_integration': bold_integration_change,
            'interpretation': interpretation,
            'recommendation': 'High confidence in findings' if confidence > 0.8 else
                            'Moderate confidence' if confidence > 0.6 else
                            'Low confidence - recommend additional validation'
        }

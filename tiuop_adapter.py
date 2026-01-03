"""
TI-UOP Framework Adapter for DEAP Dataset

Adapts the TI-UOP Existence State Space (ESS) representation
to work with DEAP EEG data structure.

Provides mapping between:
- EEG measurements → ESS dimensions (D, T, C, F, A, R)
- Truth metrics (E, M, V, A)
- LCC computation for human-AI coupling
"""

import numpy as np
from scipy import signal
from typing import Tuple, Dict
from dataclasses import dataclass, asdict
import sys
sys.path.append('attached_assets')

# Try to import from uploaded TI-UOP package
try:
    from TI_UOP_COMPLETE_EXPORT_PACKAGE_1762351688423 import (
        ESSState, TruthState, compute_lcc, compute_tralse_gradient
    )
    TIUOP_AVAILABLE = True
except ImportError:
    TIUOP_AVAILABLE = False
    print("Warning: TI-UOP package not found, using stub implementation")
    
    @dataclass
    class ESSState:
        D: float = 0.5
        T: float = 0.5
        C: float = 0.5
        F: float = 0.5
        A: float = 0.5
        R: float = 0.5
        
        def as_vector(self):
            return np.array([self.D, self.T, self.C, self.F, self.A, self.R])
    
    @dataclass
    class TruthState:
        E: float = 0.5
        M: float = 0.5
        V: float = 0.5
        A: float = 0.5
        
        def as_vector(self):
            return np.array([self.E, self.M, self.V, self.A])
    
    def compute_lcc(ess1, ess2):
        v1 = ess1.as_vector()
        v2 = ess2.as_vector()
        return float(np.corrcoef(v1, v2)[0, 1])
    
    def compute_tralse_gradient(truth):
        return float(np.linalg.norm(truth.as_vector() - 0.5))


from emotion_models import EEGFeatureExtractor, EmotionPrediction


class TIUOPModel:
    """
    TI-UOP Existence State Space (ESS) Model
    
    Maps EEG features to 6-dimensional emotional state:
    - D (Information Density): Gamma band power
    - T (Temporal Flow): Theta band dynamics
    - C (Coherence): Inter-channel synchrony
    - F (Flow State): Alpha/Theta ratio
    - A (Affective Resonance): Beta band activity
    - R (Resilience): Signal variability
    """
    
    def __init__(self, sampling_rate: int = 128):
        self.extractor = EEGFeatureExtractor(sampling_rate)
        self.model_name = "TI-UOP ESS"
        self.fs = sampling_rate
    
    def predict(self, eeg: np.ndarray) -> EmotionPrediction:
        """
        Predict emotional state using TI-UOP framework
        
        Args:
            eeg: (32 channels, timepoints)
            
        Returns:
            EmotionPrediction with ESS-derived valence/arousal
        """
        # Extract ESS state
        ess = self.eeg_to_ess(eeg)
        
        # Extract Truth state
        truth = self.eeg_to_truth(eeg)
        
        # Map ESS to valence/arousal
        # Heuristic mapping based on ESS dimensions
        valence = (ess.A + ess.F) / 2  # Affective Resonance + Flow
        arousal = (ess.D + ess.T) / 2  # Information Density + Temporal Flow
        
        # Confidence from Truth equilibrium (lower gradient = higher confidence)
        gradient = compute_tralse_gradient(truth)
        confidence = 1.0 / (1.0 + gradient)
        
        return EmotionPrediction(
            valence=valence,
            arousal=arousal,
            confidence=confidence,
            model_name=self.model_name,
            raw_features={
                'ess': asdict(ess),
                'truth': asdict(truth),
                'tralse_gradient': float(gradient)
            }
        )
    
    def eeg_to_ess(self, eeg: np.ndarray) -> ESSState:
        """
        Convert EEG measurements to Existence State Space
        
        Mappings (as specified in TI-UOP framework):
        - D: Information Density from gamma power
        - T: Temporal dynamics from theta
        - C: Coherence from inter-channel correlation
        - F: Flow state from alpha/theta ratio
        - A: Affective resonance from beta
        - R: Resilience from signal variability
        """
        bands = self.extractor.extract_all_band_powers(eeg)
        
        # D: Information Density (gamma power, normalized)
        D = self._normalize_power(bands['gamma'])
        
        # T: Temporal Flow (theta power dynamics)
        T = self._normalize_power(bands['theta'])
        
        # C: Coherence (inter-channel correlation)
        C = self._compute_coherence(eeg)
        
        # F: Flow State (alpha/theta ratio)
        alpha_theta_ratio = (np.mean(bands['alpha']) / 
                            (np.mean(bands['theta']) + 1e-10))
        F = np.tanh(alpha_theta_ratio / 5)  # Normalize to 0-1
        
        # A: Affective Resonance (beta power)
        A = self._normalize_power(bands['beta'])
        
        # R: Resilience (signal variability across time)
        R = self._compute_resilience(eeg)
        
        return ESSState(D=D, T=T, C=C, F=F, A=A, R=R)
    
    def eeg_to_truth(self, eeg: np.ndarray) -> TruthState:
        """
        Compute Truth dimensions from EEG
        
        - E: Empirical evidence (signal quality)
        - M: Measurement confidence (SNR)
        - V: Variance explained (stability)
        - A: Agreement (consistency across channels)
        """
        # E: Signal quality (inverse of noise)
        signal_power = np.mean(eeg ** 2)
        noise_estimate = np.std(np.diff(eeg, axis=-1))
        E = signal_power / (signal_power + noise_estimate + 1e-10)
        E = np.clip(E / 100, 0, 1)
        
        # M: Measurement confidence (overall power level)
        M = np.tanh(signal_power / 100)
        
        # V: Variance explained (temporal stability)
        temporal_variance = np.var(np.mean(eeg, axis=0))
        spatial_variance = np.var(np.mean(eeg, axis=1))
        V = temporal_variance / (spatial_variance + temporal_variance + 1e-10)
        
        # A: Agreement (inter-channel correlation)
        A = self._compute_coherence(eeg)
        
        return TruthState(E=float(E), M=float(M), V=float(V), A=float(A))
    
    def _normalize_power(self, power: np.ndarray) -> float:
        """Normalize power to 0-1 range"""
        mean_power = np.mean(power)
        return float(np.tanh(mean_power / 50))
    
    def _compute_coherence(self, eeg: np.ndarray) -> float:
        """
        Compute inter-channel coherence
        Average correlation across all channel pairs
        """
        # Downsample to reduce computation
        if eeg.shape[1] > 1000:
            eeg_ds = eeg[:, ::8]  # Every 8th sample
        else:
            eeg_ds = eeg
        
        # Compute correlation matrix
        corr_matrix = np.corrcoef(eeg_ds)
        
        # Average off-diagonal correlations
        n = corr_matrix.shape[0]
        mask = ~np.eye(n, dtype=bool)
        coherence = np.mean(np.abs(corr_matrix[mask]))
        
        return float(coherence)
    
    def _compute_resilience(self, eeg: np.ndarray) -> float:
        """
        Compute signal resilience (ability to maintain variance)
        """
        # Coefficient of variation across time
        channel_means = np.mean(eeg, axis=-1)
        channel_stds = np.std(eeg, axis=-1)
        cv = channel_stds / (np.abs(channel_means) + 1e-10)
        
        # Higher CV = higher resilience (within reason)
        resilience = np.tanh(np.mean(cv))
        
        return float(resilience)


class TIUOPCouplingAnalyzer:
    """
    Analyze coupling between two EEG recordings or ESS states
    
    Tests the LCC (Law of Correlational Causation) thresholds:
    - LCC < 0.6: Weak coupling
    - 0.6 ≤ LCC ≤ 0.85: Mutual causation zone
    - LCC > 0.85: Overcoupling
    """
    
    def __init__(self):
        self.model = TIUOPModel()
    
    def analyze_coupling(
        self, 
        eeg1: np.ndarray, 
        eeg2: np.ndarray
    ) -> Dict:
        """
        Analyze coupling between two EEG trials
        
        Args:
            eeg1, eeg2: (32 channels, timepoints) arrays
            
        Returns:
            dict with coupling metrics
        """
        # Convert to ESS
        ess1 = self.model.eeg_to_ess(eeg1)
        ess2 = self.model.eeg_to_ess(eeg2)
        
        # Compute LCC
        lcc = compute_lcc(ess1, ess2)
        
        # Classify coupling regime
        if lcc < 0.6:
            regime = "weak"
        elif lcc <= 0.85:
            regime = "mutual_causation"
        else:
            regime = "overcoupling"
        
        # Component-wise correlations
        v1 = ess1.as_vector()
        v2 = ess2.as_vector()
        
        dim_names = ['D', 'T', 'C', 'F', 'A', 'R']
        component_corrs = {
            name: float(np.corrcoef(v1[i:i+1], v2[i:i+1])[0, 1])
            for i, name in enumerate(dim_names)
        }
        
        return {
            'lcc': float(lcc),
            'regime': regime,
            'ess1': asdict(ess1),
            'ess2': asdict(ess2),
            'component_correlations': component_corrs,
            'in_target_zone': 0.6 <= lcc <= 0.85
        }
    
    def batch_coupling_analysis(
        self, 
        eeg_trials: np.ndarray
    ) -> Dict:
        """
        Analyze coupling across all pairs of trials
        
        Args:
            eeg_trials: (n_trials, 32 channels, timepoints)
            
        Returns:
            Statistics about coupling distribution
        """
        n_trials = eeg_trials.shape[0]
        
        lcc_values = []
        regimes = {'weak': 0, 'mutual_causation': 0, 'overcoupling': 0}
        
        # Sample pairs to avoid O(n^2) computation
        n_samples = min(100, n_trials * (n_trials - 1) // 2)
        
        for _ in range(n_samples):
            i, j = np.random.choice(n_trials, 2, replace=False)
            result = self.analyze_coupling(eeg_trials[i], eeg_trials[j])
            
            lcc_values.append(result['lcc'])
            regimes[result['regime']] += 1
        
        lcc_values = np.array(lcc_values)
        
        return {
            'mean_lcc': float(np.mean(lcc_values)),
            'std_lcc': float(np.std(lcc_values)),
            'median_lcc': float(np.median(lcc_values)),
            'min_lcc': float(np.min(lcc_values)),
            'max_lcc': float(np.max(lcc_values)),
            'regime_counts': regimes,
            'regime_percentages': {
                k: v / n_samples * 100 
                for k, v in regimes.items()
            },
            'threshold_analysis': {
                'below_0.6': float(np.mean(lcc_values < 0.6) * 100),
                'in_0.6_0.85': float(np.mean(
                    (lcc_values >= 0.6) & (lcc_values <= 0.85)
                ) * 100),
                'above_0.85': float(np.mean(lcc_values > 0.85) * 100),
            },
            'n_samples': n_samples
        }


if __name__ == '__main__':
    print("TI-UOP Adapter for DEAP Dataset\n")
    
    # Test with synthetic data
    np.random.seed(42)
    eeg = np.random.randn(32, 7680) * 10
    
    # Test ESS extraction
    model = TIUOPModel()
    prediction = model.predict(eeg)
    
    print(f"Model: {prediction.model_name}")
    print(f"  Valence: {prediction.valence:.3f}")
    print(f"  Arousal: {prediction.arousal:.3f}")
    print(f"  Confidence: {prediction.confidence:.3f}")
    
    if prediction.raw_features:
        print(f"\n  ESS State:")
        for key, value in prediction.raw_features['ess'].items():
            print(f"    {key}: {value:.3f}")
    
    # Test coupling analysis
    print("\n" + "="*60)
    print("Coupling Analysis Test\n")
    
    eeg2 = np.random.randn(32, 8064) * 10
    
    analyzer = TIUOPCouplingAnalyzer()
    coupling = analyzer.analyze_coupling(eeg, eeg2)
    
    print(f"LCC: {coupling['lcc']:.3f}")
    print(f"Regime: {coupling['regime']}")
    print(f"In target zone (0.6-0.85): {coupling['in_target_zone']}")

"""
Established Emotion Recognition Models from EEG

Implements well-validated models from neuroscience literature:
1. Russell's Circumplex Model (Valence-Arousal)
2. PANAS (Positive/Negative Affect Schedule)
3. Frontal Alpha Asymmetry
"""

import numpy as np
from scipy import signal
from scipy.stats import pearsonr
from typing import Tuple, Dict, Optional
from dataclasses import dataclass


@dataclass
class EmotionPrediction:
    """Standardized output for all emotion models"""
    valence: float  # -1 to 1 or 0 to 1
    arousal: float  # -1 to 1 or 0 to 1
    confidence: float  # 0 to 1
    model_name: str
    raw_features: Optional[Dict] = None


class EEGFeatureExtractor:
    """Common EEG feature extraction utilities"""
    
    def __init__(self, sampling_rate: int = 128):
        self.fs = sampling_rate
    
    def bandpass_filter(
        self, 
        data: np.ndarray, 
        lowcut: float, 
        highcut: float
    ) -> np.ndarray:
        """Apply bandpass filter"""
        nyq = 0.5 * self.fs
        low = lowcut / nyq
        high = highcut / nyq
        b, a = signal.butter(4, [low, high], btype='band')
        return signal.filtfilt(b, a, data, axis=-1)
    
    def extract_band_power(
        self, 
        data: np.ndarray, 
        lowcut: float, 
        highcut: float
    ) -> np.ndarray:
        """
        Extract power in frequency band
        
        Args:
            data: (channels, timepoints) or (timepoints,)
            lowcut, highcut: Frequency band in Hz
            
        Returns:
            power: Mean power in band
        """
        filtered = self.bandpass_filter(data, lowcut, highcut)
        power = np.mean(filtered ** 2, axis=-1)
        return power
    
    def extract_psd(
        self, 
        data: np.ndarray, 
        nperseg: int = 256
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Extract Power Spectral Density
        
        Returns:
            freqs: Frequency bins
            psd: Power spectral density
        """
        freqs, psd = signal.welch(data, self.fs, nperseg=nperseg, axis=-1)
        return freqs, psd
    
    def extract_all_band_powers(self, data: np.ndarray) -> Dict[str, np.ndarray]:
        """
        Extract power in all standard frequency bands
        
        Returns:
            dict with keys: delta, theta, alpha, beta, gamma
        """
        return {
            'delta': self.extract_band_power(data, 0.5, 4),
            'theta': self.extract_band_power(data, 4, 8),
            'alpha': self.extract_band_power(data, 8, 13),
            'beta': self.extract_band_power(data, 13, 30),
            'gamma': self.extract_band_power(data, 30, 45)
        }


class RussellCircumplexModel:
    """
    Russell's Circumplex Model of Affect
    
    Maps emotions to 2D space:
    - Valence (X-axis): Pleasant ↔ Unpleasant
    - Arousal (Y-axis): Activated ↔ Deactivated
    
    Implementation based on:
    - Frontal alpha asymmetry for valence
    - Gamma/beta power for arousal
    
    References:
    - Russell (1980) - Original circumplex model
    - Koelstra et al. (2012) - DEAP dataset EEG implementation
    """
    
    def __init__(self, sampling_rate: int = 128):
        self.extractor = EEGFeatureExtractor(sampling_rate)
        self.model_name = "Russell Circumplex"
        
        # Key channel indices for DEAP dataset (0-indexed)
        self.frontal_left = [0, 2, 3]   # Fp1, F3, F7
        self.frontal_right = [16, 19, 20]  # Fp2, F4, F8
    
    def predict(
        self, 
        eeg: np.ndarray, 
        channel_names: Optional[list] = None
    ) -> EmotionPrediction:
        """
        Predict valence and arousal from EEG
        
        Args:
            eeg: (32 channels, timepoints) - single trial
            
        Returns:
            EmotionPrediction with valence, arousal, confidence
        """
        # Extract band powers
        bands = self.extractor.extract_all_band_powers(eeg)
        
        # Valence from frontal alpha asymmetry
        # Left > Right alpha = positive valence
        alpha_left = np.mean(bands['alpha'][self.frontal_left])
        alpha_right = np.mean(bands['alpha'][self.frontal_right])
        
        # Asymmetry: positive = more left activation = positive emotion
        alpha_asymmetry = np.log(alpha_right) - np.log(alpha_left)
        
        # Normalize to -1 to 1 (typical range: -0.5 to 0.5)
        valence = np.tanh(alpha_asymmetry * 2)
        
        # Arousal from beta/gamma power (higher = more aroused)
        arousal_power = np.mean(bands['beta']) + np.mean(bands['gamma'])
        
        # Normalize (typical range varies, use adaptive scaling)
        arousal = np.tanh(arousal_power / (np.mean(bands['alpha']) + 1e-10) - 1)
        
        # Confidence based on signal quality (alpha power strength)
        confidence = np.clip(np.mean(bands['alpha']) / 100, 0, 1)
        
        return EmotionPrediction(
            valence=(valence + 1) / 2,  # Convert to 0-1
            arousal=(arousal + 1) / 2,  # Convert to 0-1
            confidence=confidence,
            model_name=self.model_name,
            raw_features={
                'alpha_left': float(alpha_left),
                'alpha_right': float(alpha_right),
                'alpha_asymmetry': float(alpha_asymmetry),
                'arousal_power': float(arousal_power),
                'band_powers': {k: float(np.mean(v)) for k, v in bands.items()}
            }
        )


class PANASModel:
    """
    PANAS (Positive and Negative Affect Schedule) Model
    
    Two independent dimensions:
    - Positive Affect (PA): enthusiasm, alertness, determination
    - Negative Affect (NA): distress, fear, nervousness
    
    Implementation:
    - PA correlates with left frontal activation
    - NA correlates with right frontal activation
    """
    
    def __init__(self, sampling_rate: int = 128):
        self.extractor = EEGFeatureExtractor(sampling_rate)
        self.model_name = "PANAS"
        
        self.frontal_left = [0, 2, 3]
        self.frontal_right = [16, 19, 20]
    
    def predict(self, eeg: np.ndarray) -> EmotionPrediction:
        """
        Predict positive and negative affect
        
        Returns:
            EmotionPrediction where:
            - valence = PA (positive affect)
            - arousal = NA (negative affect)
        """
        bands = self.extractor.extract_all_band_powers(eeg)
        
        # Positive Affect: left frontal activation (low alpha = high activation)
        alpha_left = np.mean(bands['alpha'][self.frontal_left])
        beta_left = np.mean(bands['beta'][self.frontal_left])
        
        # Higher beta/alpha ratio = more activation = higher PA
        pa = beta_left / (alpha_left + 1e-10)
        
        # Negative Affect: right frontal activation
        alpha_right = np.mean(bands['alpha'][self.frontal_right])
        beta_right = np.mean(bands['beta'][self.frontal_right])
        
        na = beta_right / (alpha_right + 1e-10)
        
        # Normalize to 0-1
        pa_norm = np.tanh(pa / 2)
        na_norm = np.tanh(na / 2)
        
        # Confidence from overall signal strength
        confidence = np.clip(
            (np.mean(bands['alpha']) + np.mean(bands['beta'])) / 200, 
            0, 1
        )
        
        return EmotionPrediction(
            valence=(pa_norm + 1) / 2,  # Use PA as valence proxy
            arousal=(na_norm + 1) / 2,  # Use NA as arousal proxy
            confidence=confidence,
            model_name=self.model_name,
            raw_features={
                'positive_affect': float(pa),
                'negative_affect': float(na),
                'alpha_left': float(alpha_left),
                'alpha_right': float(alpha_right),
                'beta_left': float(beta_left),
                'beta_right': float(beta_right)
            }
        )


class FrontalAlphaAsymmetry:
    """
    Frontal Alpha Asymmetry Model
    
    Most robust EEG marker for emotional valence:
    - Left > Right activation: Positive emotion, approach motivation
    - Right > Left activation: Negative emotion, withdrawal motivation
    
    Note: Alpha power is INVERSE of activation
    - High alpha = low activation
    - Low alpha = high activation
    
    References:
    - Davidson et al. (various) - Foundational work
    - Highly replicated in emotion neuroscience
    """
    
    def __init__(self, sampling_rate: int = 128):
        self.extractor = EEGFeatureExtractor(sampling_rate)
        self.model_name = "Frontal Alpha Asymmetry"
        
        # Standard electrode pairs
        self.pairs = [
            (0, 16),   # Fp1-Fp2
            (2, 19),   # F3-F4
            (3, 20),   # F7-F8
        ]
    
    def predict(self, eeg: np.ndarray) -> EmotionPrediction:
        """
        Predict emotional valence from frontal asymmetry
        
        Returns:
            EmotionPrediction with valence only (arousal set to 0.5)
        """
        bands = self.extractor.extract_all_band_powers(eeg)
        alpha = bands['alpha']
        
        # Compute asymmetry for each pair
        asymmetries = []
        for left_ch, right_ch in self.pairs:
            # Log transform to normalize power distribution
            asym = np.log(alpha[right_ch] + 1e-10) - np.log(alpha[left_ch] + 1e-10)
            asymmetries.append(asym)
        
        # Average across pairs
        mean_asymmetry = np.mean(asymmetries)
        
        # Convert to valence (positive asymmetry = positive valence)
        valence = np.tanh(mean_asymmetry * 3)
        
        # Confidence from consistency across pairs
        confidence = 1.0 - np.std(asymmetries) / (np.abs(mean_asymmetry) + 0.1)
        confidence = np.clip(confidence, 0, 1)
        
        return EmotionPrediction(
            valence=(valence + 1) / 2,
            arousal=0.5,  # This model doesn't predict arousal
            confidence=confidence,
            model_name=self.model_name,
            raw_features={
                'asymmetry': float(mean_asymmetry),
                'asymmetries': [float(a) for a in asymmetries],
                'alpha_left': [float(alpha[l]) for l, r in self.pairs],
                'alpha_right': [float(alpha[r]) for l, r in self.pairs]
            }
        )


# Model registry for easy access
AVAILABLE_MODELS = {
    'russell': RussellCircumplexModel,
    'panas': PANASModel,
    'frontal_asymmetry': FrontalAlphaAsymmetry
}


def get_model(model_name: str, sampling_rate: int = 128):
    """Factory function to create emotion models"""
    if model_name not in AVAILABLE_MODELS:
        raise ValueError(
            f"Unknown model: {model_name}. "
            f"Available: {list(AVAILABLE_MODELS.keys())}"
        )
    return AVAILABLE_MODELS[model_name](sampling_rate)


if __name__ == '__main__':
    # Test with synthetic data
    print("Testing Emotion Recognition Models\n")
    
    # Generate synthetic EEG (32 channels, 7680 timepoints @ 128 Hz - baseline removed)
    np.random.seed(42)
    eeg = np.random.randn(32, 7680) * 10
    
    # Test each model
    for model_name in AVAILABLE_MODELS:
        model = get_model(model_name)
        prediction = model.predict(eeg)
        
        print(f"Model: {prediction.model_name}")
        print(f"  Valence: {prediction.valence:.3f}")
        print(f"  Arousal: {prediction.arousal:.3f}")
        print(f"  Confidence: {prediction.confidence:.3f}")
        print()

"""
Mood Amplifier TI v2.0 - Integrated with Tralse Topos & Myrion Resolution
===========================================================================

Upgrades from baseline (77% accuracy) by integrating:
1. Myrion Resolution for conflicting EEG/fMRI signals
2. TI Consciousness Framework (GILE, ESS, LCC)
3. PSI Signal Amplification Principle
4. Tralse 4-valued emotional states

Keeps conventional emotion models (Russell, PANAS, etc.) as "good enough" 
but resolves conflicts using TI framework.

Author: TI Framework Team
Date: November 15, 2025
"""

import numpy as np
from dataclasses import dataclass
from typing import Tuple, Dict, Optional, List

# Import TI components
from tralse_topos_engine import TralseVector, TralseTopos, T_PURE, F_PURE, PHI_TYPICAL, PSI_PURE
from emotion_models import (
    RussellCircumplexModel, PANASModel, FrontalAlphaAsymmetry,
    EmotionPrediction, EEGFeatureExtractor
)

# Define TI-UOP classes inline for clean typing
@dataclass
class ESSState:
    """6-dimensional Existence State Space"""
    D: float = 0.5  # Information Density
    T: float = 0.5  # Tralse (contradiction tolerance)
    C: float = 0.5  # Coherence
    F: float = 0.5  # Flow
    A: float = 0.5  # Agency
    R: float = 0.5  # Resilience
    
    def as_vector(self) -> np.ndarray:
        return np.array([self.D, self.T, self.C, self.F, self.A, self.R])


@dataclass
class TralseEmotionState:
    """
    4-valued Tralse representation of emotional state
    
    Maps conventional emotion categories to Tralse logic:
    - T (True): Clear positive emotion (happy, joy, excitement)
    - F (False): Clear negative emotion (sad, angry, fear)
    - Φ (Phi): Mixed/ambivalent emotions (bittersweet, nostalgic, complex)
    - Ψ (Psi): Paradoxical emotions (cognitive dissonance, irony, contradiction)
    """
    tralse_vector: TralseVector
    valence: float  # -1 to 1
    arousal: float  # 0 to 1
    confidence: float  # 0 to 1
    source: str  # "EEG", "fMRI", "HRV", "MR-resolved"
    raw_predictions: Optional[Dict] = None
    
    def to_ess_state(self) -> ESSState:
        """
        Convert Tralse emotion to 6D ESS state
        
        Mapping:
        - D (Density): Arousal level
        - T (Tralse): Φ + Ψ components (contradiction/ambiguity)
        - C (Coherence): Confidence (signal quality)
        - F (Flow): Positive valence component
        - A (Agency): T component (clear decision/emotion)
        - R (Resilience): 1 - Ψ (paradox resistance)
        """
        return ESSState(
            D=self.arousal,
            T=self.tralse_vector.p_Phi + self.tralse_vector.p_Psi,
            C=self.confidence,
            F=max(0, self.valence),  # Positive valence only
            A=self.tralse_vector.p_T,
            R=1.0 - self.tralse_vector.p_Psi
        )


class PSISignalAmplifier:
    """
    PSI Signal Amplification Principle (Brandon's Insight)
    
    "Like the sense of hearing, PSI is about taking PURE NOISE, filtering 
    for what you need, and amplifying the signal. If you ignore the 'noise' 
    saying 'it doesn't matter,' you ignore hearing anything, especially the PSI."
    
    This applies to EEG/fMRI: Don't dismiss "noisy" signals - filter and amplify!
    """
    
    @staticmethod
    def amplify_signal(
        signals: List[float],
        noise_floor: float = 0.1,
        amplification_factor: float = 2.0
    ) -> float:
        """
        Filter noise and amplify meaningful signal
        
        Args:
            signals: Raw signal values
            noise_floor: Threshold below which signals are noise
            amplification_factor: How much to boost signal
        
        Returns:
            Amplified signal strength
        """
        # Filter: Keep signals above noise floor
        meaningful_signals = [s for s in signals if abs(s) > noise_floor]
        
        if not meaningful_signals:
            return 0.0
        
        # Amplify: Boost the filtered signal
        base_signal = np.mean(meaningful_signals)
        amplified = base_signal * amplification_factor
        
        # Bound to [0, 1]
        return float(np.clip(amplified, 0, 1))
    
    @staticmethod
    def extract_psi_correlation(
        eeg_features: Dict,
        fmri_features: Optional[Dict] = None
    ) -> float:
        """
        Extract PSI signal from correlation between modalities
        
        High correlation = strong PSI signal (resonance)
        Low correlation = noise/artifact
        """
        if fmri_features is None:
            # Single modality: Use internal consistency
            if 'band_powers' in eeg_features:
                powers = list(eeg_features['band_powers'].values())
                return PSISignalAmplifier.amplify_signal(powers)
            return 0.5
        
        # Multi-modal: Cross-correlation is PSI signal
        eeg_valence = eeg_features.get('valence', 0.5)
        fmri_valence = fmri_features.get('valence', 0.5)
        
        # Correlation strength
        correlation = 1 - abs(eeg_valence - fmri_valence)
        
        return PSISignalAmplifier.amplify_signal([correlation])


class MoodAmplifierTIv2:
    """
    Upgraded Mood Amplifier with TI Framework Integration
    
    Key improvements over v1 (77% baseline):
    1. Myrion Resolution resolves EEG/fMRI conflicts
    2. Tralse 4-valued emotion representation
    3. PSI signal amplification
    4. TI consciousness framework (ESS, GILE)
    """
    
    def __init__(self, sampling_rate: int = 128):
        self.sampling_rate = sampling_rate
        
        # Conventional models (kept as "good enough")
        self.russell_model = RussellCircumplexModel(sampling_rate)
        self.panas_model = PANASModel(sampling_rate)
        self.frontal_model = FrontalAlphaAsymmetry(sampling_rate)
        
        # PSI amplifier
        self.psi_amplifier = PSISignalAmplifier()
    
    def valence_to_tralse(
        self,
        valence: float,
        arousal: float,
        confidence: float
    ) -> TralseVector:
        """
        Convert conventional valence/arousal to Tralse 4-valued logic
        
        Mapping:
        - High positive valence (>0.7) + high confidence → T (True/Positive)
        - High negative valence (<0.3) + high confidence → F (False/Negative)
        - Mid valence (0.3-0.7) or low confidence → Φ (Mixed/Uncertain)
        - Contradictory signals or paradox → Ψ (Paradoxical)
        
        Args:
            valence: 0 to 1 (0=negative, 1=positive)
            arousal: 0 to 1
            confidence: 0 to 1
        
        Returns:
            TralseVector representing emotional state
        """
        # High confidence, clear valence
        if confidence > 0.7:
            if valence > 0.7:
                # Clear positive emotion
                p_T = valence * confidence
                p_F = (1 - valence) * 0.2
                p_Phi = 1 - p_T - p_F
                p_Psi = 0.0
            elif valence < 0.3:
                # Clear negative emotion
                p_F = (1 - valence) * confidence
                p_T = valence * 0.2
                p_Phi = 1 - p_T - p_F
                p_Psi = 0.0
            else:
                # Mid valence = mixed emotion (Φ dominant)
                p_Phi = 0.6
                p_T = valence * 0.4
                p_F = (1 - valence) * 0.4
                p_Psi = 0.0
        else:
            # Low confidence = uncertainty (Φ dominant)
            p_Phi = 0.7 * (1 - confidence)
            p_T = valence * confidence
            p_F = (1 - valence) * confidence
            p_Psi = 0.0
        
        # Check for paradox (high arousal + low confidence = cognitive dissonance)
        if arousal > 0.8 and confidence < 0.3:
            p_Psi = 0.3
            p_Phi *= 0.7  # Reduce Φ to make room for Ψ
        
        return TralseVector(p_T, p_F, p_Phi, p_Psi)
    
    def predict_eeg_tralse(
        self,
        eeg: np.ndarray,
        channel_names: Optional[List[str]] = None
    ) -> TralseEmotionState:
        """
        Predict Tralse emotional state from EEG using conventional models
        
        Args:
            eeg: (channels, timepoints) EEG data
        
        Returns:
            TralseEmotionState with resolved emotion
        """
        # Run all conventional models
        russell_pred = self.russell_model.predict(eeg, channel_names)
        panas_pred = self.panas_model.predict(eeg)
        frontal_pred = self.frontal_model.predict(eeg)
        
        # PSI signal amplification: Extract meaningful correlations
        psi_signal = self.psi_amplifier.extract_psi_correlation(
            russell_pred.raw_features or {}
        )
        
        # Aggregate predictions (weighted by confidence)
        total_conf = russell_pred.confidence + panas_pred.confidence + frontal_pred.confidence
        
        if total_conf > 0:
            valence = (
                russell_pred.valence * russell_pred.confidence +
                panas_pred.valence * panas_pred.confidence +
                frontal_pred.valence * frontal_pred.confidence
            ) / total_conf
            
            arousal = (
                russell_pred.arousal * russell_pred.confidence +
                panas_pred.arousal * panas_pred.confidence
            ) / (russell_pred.confidence + panas_pred.confidence)
            
            confidence = total_conf / 3.0
        else:
            valence = arousal = confidence = 0.5
        
        # Boost confidence with PSI signal
        confidence = min(1.0, confidence + 0.2 * psi_signal)
        
        # Convert to Tralse
        tralse = self.valence_to_tralse(valence, arousal, confidence)
        
        return TralseEmotionState(
            tralse_vector=tralse,
            valence=valence * 2 - 1,  # Convert to -1 to 1
            arousal=arousal,
            confidence=confidence,
            source="EEG",
            raw_predictions={
                'russell': russell_pred,
                'panas': panas_pred,
                'frontal': frontal_pred,
                'psi_signal': psi_signal
            }
        )
    
    def resolve_multimodal_conflict(
        self,
        eeg_emotion: TralseEmotionState,
        fmri_emotion: Optional[TralseEmotionState] = None,
        hrv_data: Optional[np.ndarray] = None
    ) -> TralseEmotionState:
        """
        Use Myrion Resolution to resolve conflicting signals from EEG/fMRI/HRV
        
        This is the KEY TI upgrade: When modalities disagree, use MR instead
        of simple averaging!
        
        Args:
            eeg_emotion: Emotion state from EEG
            fmri_emotion: Emotion state from fMRI (if available)
            hrv_data: Heart rate variability data (if available)
        
        Returns:
            Resolved TralseEmotionState using Myrion Resolution
        """
        if fmri_emotion is None:
            # Single modality: Just return EEG
            return eeg_emotion
        
        # Multi-modal conflict: Apply Myrion Resolution
        eeg_tralse = eeg_emotion.tralse_vector
        fmri_tralse = fmri_emotion.tralse_vector
        
        # Myrion Resolution: Resolve contradiction to balanced Φ state
        resolved_tralse = TralseTopos.myrion_resolution(
            eeg_tralse,
            fmri_tralse,
            iterations=50
        )
        
        # Aggregate valence/arousal (weighted by confidence)
        total_conf = eeg_emotion.confidence + fmri_emotion.confidence
        valence = (
            eeg_emotion.valence * eeg_emotion.confidence +
            fmri_emotion.valence * fmri_emotion.confidence
        ) / total_conf
        
        arousal = (
            eeg_emotion.arousal * eeg_emotion.confidence +
            fmri_emotion.arousal * fmri_emotion.confidence
        ) / total_conf
        
        # Confidence boosted by PSI correlation
        psi_correlation = self.psi_amplifier.extract_psi_correlation(
            eeg_emotion.raw_predictions or {},
            fmri_emotion.raw_predictions or {}
        )
        
        confidence = min(1.0, (eeg_emotion.confidence + fmri_emotion.confidence) / 2 + 0.15 * psi_correlation)
        
        return TralseEmotionState(
            tralse_vector=resolved_tralse,
            valence=valence,
            arousal=arousal,
            confidence=confidence,
            source="MR-resolved (EEG+fMRI)",
            raw_predictions={
                'eeg': eeg_emotion,
                'fmri': fmri_emotion,
                'psi_correlation': psi_correlation
            }
        )
    
    def predict_mood_shift(
        self,
        baseline_emotion: TralseEmotionState,
        post_intervention_emotion: TralseEmotionState
    ) -> Dict:
        """
        Predict mood shift from baseline to post-intervention
        
        Returns efficacy metrics for validation
        """
        # Valence shift (primary efficacy metric)
        valence_shift = post_intervention_emotion.valence - baseline_emotion.valence
        
        # Tralse-based metrics
        ess_baseline = baseline_emotion.to_ess_state()
        ess_post = post_intervention_emotion.to_ess_state()
        
        # ESS distance (how much did brain state change?)
        ess_distance = np.linalg.norm(
            ess_baseline.as_vector() - ess_post.as_vector()
        )
        
        # Success: Positive valence shift AND increased flow/agency
        success = (
            valence_shift > 0.15 and
            ess_post.F > ess_baseline.F and  # Flow increased
            ess_post.A > ess_baseline.A      # Agency increased
        )
        
        return {
            'valence_shift': float(valence_shift),
            'arousal_change': float(post_intervention_emotion.arousal - baseline_emotion.arousal),
            'ess_distance': float(ess_distance),
            'flow_increase': float(ess_post.F - ess_baseline.F),
            'agency_increase': float(ess_post.A - ess_baseline.A),
            'confidence': float((baseline_emotion.confidence + post_intervention_emotion.confidence) / 2),
            'success': bool(success),
            'tralse_phi_increase': float(
                post_intervention_emotion.tralse_vector.p_Phi - 
                baseline_emotion.tralse_vector.p_Phi
            )
        }


# ============================================================================
# USAGE EXAMPLE
# ============================================================================

def example_usage():
    """Demonstrate TI v2 mood amplifier usage"""
    
    # Initialize amplifier
    amplifier = MoodAmplifierTIv2(sampling_rate=128)
    
    # Simulate EEG data (32 channels, 5 seconds @ 128 Hz)
    eeg_baseline = np.random.randn(32, 640)
    eeg_post = np.random.randn(32, 640)
    
    # Predict emotions
    emotion_baseline = amplifier.predict_eeg_tralse(eeg_baseline)
    emotion_post = amplifier.predict_eeg_tralse(eeg_post)
    
    # Calculate mood shift
    shift = amplifier.predict_mood_shift(emotion_baseline, emotion_post)
    
    print("Mood Amplifier TI v2 Results:")
    print(f"  Valence Shift: {shift['valence_shift']:+.3f}")
    print(f"  Flow Increase: {shift['flow_increase']:+.3f}")
    print(f"  Success: {shift['success']}")
    print(f"  Baseline Tralse: {emotion_baseline.tralse_vector}")
    print(f"  Post Tralse: {emotion_post.tralse_vector}")


if __name__ == "__main__":
    example_usage()

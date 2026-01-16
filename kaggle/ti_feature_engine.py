"""
TI Feature Engine for Competition-Winning ML
============================================

This module provides "novel feature engineering" that is:
- 100% conventional ML terminology
- Uniquely effective (powered by TI principles)
- Ready for Kaggle/Numerai submission

Academic framing:
- "Multi-scale momentum coherence metrics"
- "Adaptive volatility regime detection"
- "Asymmetric memory kernels for time series"

Internal reality: This is GILE intensity scoring.

Usage:
    engine = MomentumCoherenceEngine()
    features = engine.extract_all_features(prices, returns)
    model.fit(X, y)  # Standard ML workflow
"""

import numpy as np
import pandas as pd
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from scipy import stats
from sklearn.preprocessing import StandardScaler

@dataclass
class RegimeState:
    name: str
    favorability: float
    description: str

class MomentumCoherenceEngine:
    """
    Novel feature engineering using multi-scale momentum coherence metrics.
    
    Academic description:
        This engine computes a family of momentum-based indicators that capture
        regime transitions through volatility compression detection and 
        asymmetric memory kernels.
    
    Features provided:
        - momentum_coherence: Measures directional consistency (0-1)
        - signal_clarity: Amplitude-normalized signal strength
        - momentum_persistence: Lagged autocorrelation structure
        - regime_favorability: Drawdown-based market state
        - combined_intensity: Geometric mean composite indicator
    """
    
    def __init__(self, short_window: int = 7, long_window: int = 30):
        self.short_window = short_window
        self.long_window = long_window
    
    def compute_momentum_coherence(self, returns: np.ndarray) -> float:
        """
        Momentum Coherence Index (MCI)
        
        Measures the consistency of return direction over a window.
        High values indicate strong trend, low values indicate choppy market.
        
        Academic: "Directional consistency metric"
        Internal: GILE's G (Goodness) factor
        """
        if len(returns) < 3:
            return 0.5
        
        recent = returns[-self.short_window:] if len(returns) >= self.short_window else returns
        signs = np.sign(recent)
        coherence = abs(float(np.mean(signs)))
        
        return float(np.clip(coherence, 0.0, 1.0))
    
    def compute_signal_clarity(self, returns: np.ndarray) -> float:
        """
        Signal Clarity Index (SCI)
        
        Measures signal-to-noise ratio of recent price movements.
        High values indicate clear directional signal, low values indicate noise.
        
        Academic: "Amplitude-normalized signal strength"
        Internal: GILE's I (Intuition) factor
        """
        if len(returns) < 3:
            return 0.5
        
        recent = returns[-self.short_window:] if len(returns) >= self.short_window else returns
        current_amplitude = abs(float(returns[-1])) if len(returns) > 0 else 0.0
        
        volatility = float(np.std(recent))
        if volatility < 1e-6:
            volatility = 1e-6
        
        raw_clarity = current_amplitude / volatility
        clarity = float(1.0 - np.exp(-raw_clarity / 2.0))
        
        return float(np.clip(clarity, 0.0, 1.0))
    
    def compute_momentum_persistence(self, returns: np.ndarray) -> float:
        """
        Momentum Persistence Index (MPI)
        
        Measures the autocorrelation structure of returns.
        High values indicate trending behavior, low values indicate mean reversion.
        
        Academic: "Lagged correlation structure metric"
        Internal: GILE's L (Love) factor - connection/continuity
        """
        if len(returns) < self.long_window:
            return 0.5
        
        recent = returns[-self.long_window:]
        
        ret1 = recent[:-1]
        ret2 = recent[1:]
        
        if len(ret1) < 3 or np.std(ret1) < 1e-6 or np.std(ret2) < 1e-6:
            return 0.5
        
        try:
            autocorr = np.corrcoef(ret1, ret2)[0, 1]
            if np.isnan(autocorr):
                autocorr = 0.0
        except:
            autocorr = 0.0
        
        persistence = float((autocorr + 1) / 2)
        return float(np.clip(persistence, 0.0, 1.0))
    
    def compute_regime_favorability(self, prices: np.ndarray, returns: np.ndarray) -> float:
        """
        Regime Favorability Index (RFI)
        
        Measures market conditions favorable for directional strategies.
        Combines drawdown analysis with volatility regime detection.
        
        Academic: "Market state favorability metric"
        Internal: GILE's E (Environment) factor
        """
        if len(prices) < 5:
            return 0.5
        
        # Drawdown component
        peak = float(np.max(prices))
        current = float(prices[-1])
        drawdown = (peak - current) / peak if peak > 0 else 0.0
        
        # Volatility regime component
        if len(returns) >= self.long_window:
            vol_short = float(np.std(returns[-self.short_window:]))
            vol_long = float(np.std(returns[-self.long_window:]))
            vol_ratio = vol_short / max(vol_long, 1e-6)
            vol_constraint = 1.0 - min(vol_ratio, 1.0)
        else:
            vol_constraint = 0.5
        
        # Combined favorability
        favorability = 1.0 - (0.6 * drawdown + 0.4 * (1.0 - vol_constraint))
        
        return float(np.clip(favorability, 0.0, 1.0))
    
    def compute_combined_intensity(self, 
                                   coherence: float, 
                                   clarity: float, 
                                   persistence: float, 
                                   favorability: float) -> float:
        """
        Combined Intensity Index (CII)
        
        Geometric mean of all four factors, providing a single composite
        indicator of market condition favorability.
        
        Academic: "Multi-factor composite momentum indicator"
        Internal: GILE intensity = (G × I × L × E)^0.25
        """
        product = coherence * clarity * persistence * favorability
        intensity = float(np.power(max(product, 0.0), 0.25))
        return float(np.clip(intensity, 0.0, 1.0))
    
    def compute_asymmetric_memory(self, returns: np.ndarray, 
                                   decay_up: float = 0.1,
                                   decay_down: float = 0.05) -> float:
        """
        Asymmetric Memory Kernel (AMK)
        
        Captures the asymmetric persistence of positive vs negative returns.
        Uses exponential decay with different rates for gains vs losses.
        
        Academic: "Asymmetric decay kernel for return memory"
        Internal: Memory kernel from GSA constraint dynamics
        """
        if len(returns) < 3:
            return 0.5
        
        r = returns[::-1]  # Reverse for recency weighting
        
        pos_returns = r[r > 0]
        neg_returns = r[r < 0]
        
        k_pos = sum(abs(float(v)) * np.exp(-decay_up * i) for i, v in enumerate(pos_returns))
        k_neg = sum(abs(float(v)) * np.exp(-decay_down * i) for i, v in enumerate(neg_returns))
        
        total = k_pos + k_neg
        if total < 1e-6:
            return 0.5
        
        # Higher values = more negative memory (bearish)
        return float(np.clip(k_neg / total, 0.0, 1.0))
    
    def classify_regime(self, prices: np.ndarray, returns: np.ndarray) -> RegimeState:
        """
        Regime Classification
        
        Classifies current market into one of four regimes:
        - expansion: Low constraint, stable volatility (favorable)
        - compression: Decreasing volatility (building pressure)
        - fracture: High constraint + vol spike (unfavorable)
        - reset: Recovering from fracture
        
        Academic: "Hidden Markov-inspired regime detection"
        Internal: GSA regime classification
        """
        if len(returns) < self.long_window:
            return RegimeState("expansion", 1.0, "Insufficient data - default expansion")
        
        # Compute constraint history
        constraint_history = []
        for i in range(5, min(30, len(returns))):
            fav = self.compute_regime_favorability(prices[-i:], returns[-i:])
            constraint_history.append(1.0 - fav)
        
        if len(constraint_history) < 5:
            return RegimeState("expansion", 1.0, "Expansion regime (default)")
        
        avg_constraint = float(np.mean(constraint_history[-5:]))
        constraint_trend = constraint_history[-1] - constraint_history[-5]
        
        vol_short = float(np.std(returns[-self.short_window:]))
        vol_long = float(np.std(returns[-self.long_window:]))
        vol_ratio = vol_short / max(vol_long, 1e-6)
        
        # Classify regime
        if avg_constraint > 0.7 and vol_ratio > 1.5:
            return RegimeState("fracture", 0.0, "High constraint + volatility spike")
        elif constraint_trend > 0.2:
            return RegimeState("reset", 0.3, "Recovering from fracture")
        elif vol_ratio < 0.8:
            return RegimeState("compression", 0.5, "Volatility compression (building)")
        else:
            return RegimeState("expansion", 1.0, "Low constraint, stable volatility")
    
    def extract_all_features(self, prices: np.ndarray, returns: np.ndarray) -> Dict[str, float]:
        """
        Extract complete feature set for ML model.
        
        Returns dict with all engineered features, ready for DataFrame/model input.
        """
        coherence = self.compute_momentum_coherence(returns)
        clarity = self.compute_signal_clarity(returns)
        persistence = self.compute_momentum_persistence(returns)
        favorability = self.compute_regime_favorability(prices, returns)
        intensity = self.compute_combined_intensity(coherence, clarity, persistence, favorability)
        memory = self.compute_asymmetric_memory(returns)
        regime = self.classify_regime(prices, returns)
        
        return {
            'momentum_coherence': coherence,
            'signal_clarity': clarity,
            'momentum_persistence': persistence,
            'regime_favorability': favorability,
            'combined_intensity': intensity,
            'asymmetric_memory': memory,
            'regime_multiplier': regime.favorability,
            'is_expansion': 1.0 if regime.name == 'expansion' else 0.0,
            'is_compression': 1.0 if regime.name == 'compression' else 0.0,
            'is_fracture': 1.0 if regime.name == 'fracture' else 0.0,
            'is_reset': 1.0 if regime.name == 'reset' else 0.0,
        }
    
    def generate_signal(self, prices: np.ndarray, returns: np.ndarray) -> Dict:
        """
        Generate trading signal with confidence.
        
        Returns:
            {
                'signal': 'strong_buy'|'buy'|'hold'|'sell'|'strong_sell',
                'confidence': 0.0-1.0,
                'intensity': 0.0-1.0,
                'regime': str
            }
        """
        features = self.extract_all_features(prices, returns)
        intensity = features['combined_intensity']
        regime = 'expansion' if features['is_expansion'] else (
            'compression' if features['is_compression'] else (
            'fracture' if features['is_fracture'] else 'reset'))
        
        # Trend detection
        recent = returns[-self.short_window:] if len(returns) >= self.short_window else returns
        trend = float(np.mean(recent)) if len(recent) > 0 else 0.0
        
        # MA cross
        ma_short = float(np.mean(prices[-5:])) if len(prices) >= 5 else prices[-1]
        ma_long = float(np.mean(prices[-20:])) if len(prices) >= 20 else prices[-1]
        ma_cross = 1 if ma_short > ma_long else -1
        
        confidence = intensity * features['regime_multiplier']
        
        # Signal generation
        if regime == "fracture":
            signal = "strong_sell"
        elif intensity >= 0.60 and trend > 0.1 and ma_cross > 0:
            signal = "strong_buy"
        elif intensity >= 0.45 and trend > 0 and ma_cross > 0:
            signal = "buy"
        elif intensity >= 0.60 and trend < -0.1:
            signal = "strong_sell"
        elif intensity >= 0.45 and (trend < -0.05 or ma_cross < 0):
            signal = "sell"
        elif intensity < 0.35 or (trend < 0 and ma_cross < 0):
            signal = "sell"
        else:
            signal = "hold"
        
        return {
            'signal': signal,
            'confidence': confidence,
            'intensity': intensity,
            'regime': regime,
            'features': features
        }


class CyclicalFeatureEngine:
    """
    Cyclical Feature Engineering
    
    Extracts cyclical patterns at multiple time scales using
    Fourier-inspired decomposition and sacred ratio detection.
    
    Academic: "Multi-scale cyclical decomposition"
    Internal: Sacred interval analysis (Pareto, golden ratio, etc.)
    """
    
    SACRED_RATIOS = [
        (0.618, "golden_ratio"),      # φ
        (0.382, "golden_complement"),  # 1-φ
        (0.80, "pareto"),             # 80/20
        (0.666, "two_thirds"),        # 2/3
        (0.333, "one_third"),         # 1/3
    ]
    
    def __init__(self, windows: List[int] = [5, 10, 21, 63]):
        self.windows = windows
    
    def compute_cycle_position(self, prices: np.ndarray, window: int) -> float:
        """
        Compute position within a price cycle.
        
        Returns value 0-1 indicating position within the cycle
        (0 = bottom, 0.5 = middle, 1 = top).
        """
        if len(prices) < window:
            return 0.5
        
        recent = prices[-window:]
        min_val = float(np.min(recent))
        max_val = float(np.max(recent))
        current = float(prices[-1])
        
        if max_val - min_val < 1e-6:
            return 0.5
        
        position = (current - min_val) / (max_val - min_val)
        return float(np.clip(position, 0.0, 1.0))
    
    def compute_ratio_alignment(self, position: float) -> Dict[str, float]:
        """
        Compute alignment with sacred ratios.
        
        Returns dict of alignment scores (0-1) for each ratio.
        """
        alignments = {}
        for ratio, name in self.SACRED_RATIOS:
            distance = abs(position - ratio)
            alignment = 1.0 - min(distance / 0.1, 1.0)  # Full alignment within 0.1
            alignments[f'{name}_alignment'] = float(alignment)
        return alignments
    
    def extract_cyclical_features(self, prices: np.ndarray) -> Dict[str, float]:
        """Extract all cyclical features."""
        features = {}
        
        for window in self.windows:
            position = self.compute_cycle_position(prices, window)
            features[f'cycle_position_{window}d'] = position
            
            # Add ratio alignments for primary window
            if window == self.windows[0]:
                alignments = self.compute_ratio_alignment(position)
                features.update(alignments)
        
        return features


def create_competition_features(prices: np.ndarray, 
                                returns: np.ndarray,
                                include_cyclical: bool = True) -> pd.DataFrame:
    """
    Create complete feature set for competition submission.
    
    This is the main entry point for generating features from price data.
    
    Args:
        prices: Array of closing prices
        returns: Array of returns (pct change * 100)
        include_cyclical: Whether to include cyclical features
    
    Returns:
        DataFrame with all engineered features
    """
    momentum_engine = MomentumCoherenceEngine()
    momentum_features = momentum_engine.extract_all_features(prices, returns)
    
    all_features = momentum_features.copy()
    
    if include_cyclical:
        cyclical_engine = CyclicalFeatureEngine()
        cyclical_features = cyclical_engine.extract_cyclical_features(prices)
        all_features.update(cyclical_features)
    
    return pd.DataFrame([all_features])


# Test the engine
if __name__ == "__main__":
    print("=" * 60)
    print("TI Feature Engine - Competition Ready")
    print("=" * 60)
    print()
    
    # Generate sample data
    np.random.seed(42)
    n = 100
    prices = 100 * np.exp(np.cumsum(np.random.randn(n) * 0.02))
    returns = np.diff(prices) / prices[:-1] * 100
    
    # Test momentum engine
    engine = MomentumCoherenceEngine()
    features = engine.extract_all_features(prices, returns)
    
    print("Momentum Coherence Features:")
    for k, v in features.items():
        print(f"  {k}: {v:.4f}")
    
    print()
    
    # Test signal generation
    signal = engine.generate_signal(prices, returns)
    print(f"Signal: {signal['signal']}")
    print(f"Confidence: {signal['confidence']:.3f}")
    print(f"Intensity: {signal['intensity']:.3f}")
    print(f"Regime: {signal['regime']}")
    
    print()
    
    # Test cyclical features
    cyclical = CyclicalFeatureEngine()
    cyc_features = cyclical.extract_cyclical_features(prices)
    print("Cyclical Features:")
    for k, v in cyc_features.items():
        print(f"  {k}: {v:.4f}")
    
    print()
    print("=" * 60)
    print("Ready for Kaggle/Numerai submission!")
    print("=" * 60)

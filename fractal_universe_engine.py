"""
Fractal Universe Engine
========================
Integration of Chris Lehto's "Our Fractal Universe" research with TI Sigma predictions.

Key Concepts:
- 24 orders of magnitude scaling (quantum to cosmic)
- Kleiber's Law: M^0.75 metabolic scaling across 21+ orders
- 42 total orders (TI sacred number alignment)
- Fractal self-similarity as fundamental reality structure

This module provides fractal scaling analysis for:
1. Stock market predictions (fractal regime detection)
2. Consciousness correlations (LCC fractal patterns)
3. Biometric resonance (cross-scale coherence)
4. TI Sigma enhancement (fractal-weighted predictions)
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime
import math


@dataclass
class FractalScale:
    """Represents a scale level in the fractal hierarchy"""
    name: str
    order_of_magnitude: int
    characteristic_size: float
    characteristic_time: float
    kleiber_factor: float
    consciousness_weight: float


FRACTAL_SCALES = [
    FractalScale("Planck", -35, 1.6e-35, 5.4e-44, 0.0, 1.0),
    FractalScale("String", -33, 1e-33, 1e-43, 0.01, 0.99),
    FractalScale("Quantum Foam", -25, 1e-25, 1e-35, 0.05, 0.95),
    FractalScale("Proton", -15, 1e-15, 1e-23, 0.15, 0.85),
    FractalScale("Atom", -10, 1e-10, 1e-15, 0.25, 0.75),
    FractalScale("Molecule", -9, 1e-9, 1e-12, 0.30, 0.70),
    FractalScale("Protein", -8, 1e-8, 1e-9, 0.35, 0.65),
    FractalScale("Organelle", -6, 1e-6, 1e-3, 0.45, 0.55),
    FractalScale("Cell", -5, 1e-5, 1e-2, 0.50, 0.50),
    FractalScale("Neuron", -4, 1e-4, 1e-1, 0.55, 0.45),
    FractalScale("Neural Network", -2, 1e-2, 1.0, 0.65, 0.42),
    FractalScale("Brain", 0, 0.15, 100, 0.75, 0.42),
    FractalScale("Human", 0, 1.7, 3.15e9, 0.75, 0.42),
    FractalScale("City", 4, 1e4, 3.15e10, 0.80, 0.35),
    FractalScale("Earth", 7, 1.27e7, 3.15e7, 0.85, 0.25),
    FractalScale("Solar System", 12, 1.5e11, 3.15e7, 0.88, 0.15),
    FractalScale("Galaxy", 21, 1e21, 1e15, 0.92, 0.08),
    FractalScale("Galaxy Cluster", 24, 1e24, 1e17, 0.95, 0.05),
    FractalScale("Observable Universe", 27, 8.8e26, 4.35e17, 0.99, 0.01),
    FractalScale("Multiverse", 42, float('inf'), float('inf'), 1.0, 0.42),
]


class KleiberScaling:
    """
    Kleiber's Law Implementation
    
    BMR = M^0.75 (metabolic rate scales with 3/4 power of mass)
    This extends across 21+ orders of magnitude in biology.
    
    TI Extension: Consciousness scales similarly:
    Consciousness_Intensity = Base * (Complexity)^0.75
    """
    
    KLEIBER_EXPONENT = 0.75
    SACRED_EXPONENT = 0.42
    
    @staticmethod
    def metabolic_rate(mass_kg: float) -> float:
        """Calculate metabolic rate using Kleiber's Law"""
        return 70 * (mass_kg ** KleiberScaling.KLEIBER_EXPONENT)
    
    @staticmethod
    def consciousness_intensity(complexity_units: float, base: float = 1.0) -> float:
        """
        Calculate consciousness intensity using TI-Kleiber synthesis.
        
        The 0.75 exponent appears because consciousness, like metabolism,
        operates through fractal network distribution.
        """
        return base * (complexity_units ** KleiberScaling.KLEIBER_EXPONENT)
    
    @staticmethod
    def cross_scale_coherence(scale1: int, scale2: int) -> float:
        """
        Calculate coherence between two scales (orders of magnitude).
        
        Fractal self-similarity means patterns repeat across scales,
        but with predictable attenuation following Kleiber scaling.
        """
        delta = abs(scale2 - scale1)
        coherence = (KleiberScaling.KLEIBER_EXPONENT ** delta)
        return max(0.01, coherence)
    
    @staticmethod
    def fractal_dimension(pattern_scales: List[float]) -> float:
        """
        Calculate fractal dimension from pattern measurements at different scales.
        Uses box-counting approximation.
        """
        if len(pattern_scales) < 2:
            return 1.0
        
        log_scales = np.log(np.array(pattern_scales))
        log_counts = np.arange(len(pattern_scales))
        
        slope, _ = np.polyfit(log_scales, log_counts, 1)
        return abs(slope)


class FractalMarketAnalyzer:
    """
    Apply fractal universe principles to market prediction.
    
    Markets exhibit fractal patterns across timeframes:
    - Minute charts resemble daily charts resemble monthly charts
    - This self-similarity follows Kleiber-like scaling
    - Regime changes occur at fractal boundaries
    """
    
    def __init__(self):
        self.hurst_threshold = 0.5
        self.ti_sacred_ratios = [0.42, 0.618, 0.75, 0.85, 0.92]
    
    def calculate_hurst_exponent(self, prices: List[float]) -> float:
        """
        Calculate Hurst exponent to measure fractal persistence.
        
        H > 0.5: Trending (persistent)
        H = 0.5: Random walk
        H < 0.5: Mean-reverting (anti-persistent)
        """
        if len(prices) < 20:
            return 0.5
        
        prices = np.array(prices)
        n = len(prices)
        
        mean = np.mean(prices)
        std = np.std(prices)
        
        if std == 0:
            return 0.5
        
        deviations = prices - mean
        cumulative = np.cumsum(deviations)
        
        R = np.max(cumulative) - np.min(cumulative)
        S = std
        
        if S == 0 or R == 0:
            return 0.5
        
        RS = R / S
        
        H = np.log(RS) / np.log(n)
        
        return max(0.0, min(1.0, H))
    
    def detect_fractal_regime(self, prices: List[float], volumes: List[float] = None) -> Dict:
        """
        Detect market regime using fractal analysis.
        
        Returns regime classification and confidence based on:
        - Hurst exponent (trend persistence)
        - Fractal dimension (complexity)
        - Kleiber coherence (cross-timeframe alignment)
        """
        if len(prices) < 10:
            return {
                "regime": "insufficient_data", 
                "confidence": 0.0,
                "hurst_exponent": 0.5,
                "volatility": 0.0,
                "fractal_coherence": 0.0,
                "kleiber_aligned": False,
                "ti_sacred_ratio": None
            }
        
        H = self.calculate_hurst_exponent(prices)
        
        returns = np.diff(np.log(np.array(prices) + 1e-10))
        volatility = np.std(returns) if len(returns) > 0 else 0
        
        short_prices = prices[-min(5, len(prices)):]
        long_prices = prices
        coherence = KleiberScaling.cross_scale_coherence(1, 3)
        
        if H > 0.65:
            regime = "FRACTAL_TREND"
            ti_alignment = abs(H - 0.75)
        elif H < 0.35:
            regime = "FRACTAL_MEAN_REVERT"
            ti_alignment = abs(H - 0.25)
        else:
            regime = "FRACTAL_RANDOM"
            ti_alignment = abs(H - 0.5)
        
        confidence = 1.0 - ti_alignment
        
        kleiber_boost = 0
        for ratio in self.ti_sacred_ratios:
            if abs(H - ratio) < 0.05:
                kleiber_boost = 0.15
                break
        
        return {
            "regime": regime,
            "hurst_exponent": round(H, 4),
            "confidence": round(min(1.0, confidence + kleiber_boost), 3),
            "volatility": round(volatility, 6),
            "fractal_coherence": round(coherence, 4),
            "kleiber_aligned": kleiber_boost > 0,
            "ti_sacred_ratio": 0.75 if kleiber_boost > 0 else None
        }
    
    def multi_scale_prediction(self, 
                                short_term: List[float],
                                medium_term: List[float],
                                long_term: List[float]) -> Dict:
        """
        Generate prediction using Lehto's fractal multi-scale analysis.
        
        Combines signals from multiple timeframes weighted by Kleiber scaling.
        """
        short_regime = self.detect_fractal_regime(short_term)
        medium_regime = self.detect_fractal_regime(medium_term)
        long_regime = self.detect_fractal_regime(long_term)
        
        weights = [0.25, 0.50, 0.75]
        
        weighted_hurst = (
            short_regime["hurst_exponent"] * weights[0] +
            medium_regime["hurst_exponent"] * weights[1] +
            long_regime["hurst_exponent"] * weights[2]
        ) / sum(weights)
        
        scale_coherence = (
            KleiberScaling.cross_scale_coherence(1, 2) *
            abs(short_regime["hurst_exponent"] - medium_regime["hurst_exponent"]) +
            KleiberScaling.cross_scale_coherence(2, 3) *
            abs(medium_regime["hurst_exponent"] - long_regime["hurst_exponent"])
        )
        scale_coherence = 1.0 - min(1.0, scale_coherence * 2)
        
        if weighted_hurst > 0.6:
            direction = "BULLISH"
            if short_regime["hurst_exponent"] > medium_regime["hurst_exponent"]:
                direction = "STRONGLY_BULLISH"
        elif weighted_hurst < 0.4:
            direction = "BEARISH"
            if short_regime["hurst_exponent"] < medium_regime["hurst_exponent"]:
                direction = "STRONGLY_BEARISH"
        else:
            direction = "NEUTRAL"
        
        confidence = (
            short_regime["confidence"] * 0.2 +
            medium_regime["confidence"] * 0.3 +
            long_regime["confidence"] * 0.3 +
            scale_coherence * 0.2
        )
        
        return {
            "direction": direction,
            "confidence": round(confidence, 3),
            "weighted_hurst": round(weighted_hurst, 4),
            "scale_coherence": round(scale_coherence, 4),
            "short_regime": short_regime["regime"],
            "medium_regime": medium_regime["regime"],
            "long_regime": long_regime["regime"],
            "fractal_alignment": scale_coherence > 0.7,
            "kleiber_weight": 0.75,
            "lehto_42_factor": 42 / (42 + abs(weighted_hurst - 0.5) * 100)
        }


class ConsciousnessFractalBridge:
    """
    Bridge between fractal universe theory and consciousness studies.
    
    Key insight: LCC (Limbic Correlational Connection) exhibits
    fractal patterns similar to Lehto's universal scaling.
    """
    
    def __init__(self):
        self.sacred_42 = 42
        self.kleiber = 0.75
        self.ti_threshold = 0.85
    
    def lcc_fractal_coherence(self, 
                               eeg_bands: Dict[str, float],
                               hrv_coherence: float) -> Dict:
        """
        Calculate LCC coherence using fractal scaling principles.
        
        EEG bands represent different scales of neural activity.
        HRV represents body-level coherence.
        Cross-scale coherence indicates non-local correlation.
        """
        band_order = ["delta", "theta", "alpha", "beta", "gamma"]
        band_values = [eeg_bands.get(b, 0.5) for b in band_order]
        
        cross_correlations = []
        for i in range(len(band_values) - 1):
            scale_factor = KleiberScaling.cross_scale_coherence(i, i+1)
            cross_correlations.append(
                abs(band_values[i] - band_values[i+1]) * scale_factor
            )
        
        neural_coherence = 1.0 - np.mean(cross_correlations) if cross_correlations else 0.5
        
        brain_heart_coherence = KleiberScaling.cross_scale_coherence(0, 2)
        integrated_coherence = (neural_coherence * 0.6 + hrv_coherence * 0.4) * brain_heart_coherence
        
        lcc_estimate = integrated_coherence * (self.kleiber ** 0.5)
        
        is_nonlocal = lcc_estimate < 1.0 and integrated_coherence > self.ti_threshold
        
        return {
            "lcc_estimate": round(lcc_estimate, 4),
            "neural_coherence": round(neural_coherence, 4),
            "brain_heart_coherence": round(brain_heart_coherence, 4),
            "integrated_coherence": round(integrated_coherence, 4),
            "potentially_nonlocal": is_nonlocal,
            "kleiber_factor": self.kleiber,
            "fractal_depth": len(band_order),
            "orders_of_magnitude": 5,
            "lehto_alignment": lcc_estimate < 0.42
        }
    
    def calculate_42_resonance(self, values: List[float]) -> Dict:
        """
        Check for resonance with the sacred number 42.
        
        In Lehto's fractal universe, 42 represents the total number
        of orders of magnitude from Planck to Multiverse.
        In TI, 42 = L × E maximum (6 × 7 or 7 × 6).
        """
        if not values:
            return {"resonance": 0, "alignment": "none"}
        
        sum_val = sum(values)
        mean_val = np.mean(values)
        
        sum_42_ratio = sum_val / 42 if sum_val != 0 else 0
        mean_42_ratio = mean_val / 0.42 if mean_val != 0 else 0
        
        sum_resonance = 1.0 - min(1.0, abs(1.0 - sum_42_ratio))
        mean_resonance = 1.0 - min(1.0, abs(1.0 - mean_42_ratio))
        
        combined = (sum_resonance + mean_resonance) / 2
        
        if combined > 0.8:
            alignment = "STRONG_42_RESONANCE"
        elif combined > 0.5:
            alignment = "MODERATE_42_RESONANCE"
        elif combined > 0.2:
            alignment = "WEAK_42_RESONANCE"
        else:
            alignment = "NO_42_RESONANCE"
        
        return {
            "resonance": round(combined, 4),
            "alignment": alignment,
            "sum_42_ratio": round(sum_42_ratio, 4),
            "mean_42_ratio": round(mean_42_ratio, 4),
            "lehto_orders": 42,
            "ti_le_product": "6×7 = 42"
        }


class FractalUniverseSynthesis:
    """
    Master class synthesizing all fractal universe concepts for TI integration.
    """
    
    def __init__(self):
        self.market_analyzer = FractalMarketAnalyzer()
        self.consciousness_bridge = ConsciousnessFractalBridge()
        self.creation_time = datetime.now()
    
    def get_framework_summary(self) -> Dict:
        """Get summary of the Fractal Universe Framework"""
        return {
            "name": "Our Fractal Universe Integration",
            "author_attribution": "Chris Lehto (Lehto Files)",
            "ti_integration": "TI Sigma 6 Enhancement",
            "key_concepts": {
                "kleiber_exponent": 0.75,
                "sacred_orders": 42,
                "scaling_range": "24+ orders of magnitude",
                "fractal_dimension": "Self-similar across all scales"
            },
            "applications": [
                "Market regime detection via Hurst exponent",
                "Consciousness coherence via cross-scale LCC",
                "Biometric integration via Kleiber scaling",
                "Prediction enhancement via fractal alignment"
            ],
            "ti_synthesis": {
                "42_alignment": "L×E maximum = 6×7 = 42 (TI sacred)",
                "0.75_connection": "Kleiber = 3/4 = metabolic fractal",
                "lcc_fractals": "Non-local correlation across scales"
            }
        }
    
    def full_fractal_analysis(self,
                               prices: List[float] = None,
                               eeg_bands: Dict[str, float] = None,
                               hrv_coherence: float = None) -> Dict:
        """
        Perform comprehensive fractal analysis across all domains.
        """
        results = {
            "timestamp": datetime.now().isoformat(),
            "framework": "Lehto Fractal Universe + TI Sigma"
        }
        
        if prices and len(prices) >= 10:
            third = len(prices) // 3
            short = prices[-third:] if third > 5 else prices[-5:]
            medium = prices[-2*third:] if 2*third > 10 else prices
            long_term = prices
            
            results["market_analysis"] = self.market_analyzer.multi_scale_prediction(
                short, medium, long_term
            )
        
        if eeg_bands and hrv_coherence is not None:
            results["consciousness_analysis"] = self.consciousness_bridge.lcc_fractal_coherence(
                eeg_bands, hrv_coherence
            )
        
        all_values = []
        if prices:
            all_values.extend([p/100 for p in prices[-10:]])
        if eeg_bands:
            all_values.extend(eeg_bands.values())
        if hrv_coherence is not None:
            all_values.append(hrv_coherence)
        
        if all_values:
            results["sacred_42_analysis"] = self.consciousness_bridge.calculate_42_resonance(all_values)
        
        results["fractal_scales"] = {
            "quantum_to_cosmic": "42 orders",
            "biological": "24 orders (Kleiber validated)",
            "consciousness": "5 orders (delta to gamma)",
            "market": "variable (timeframe dependent)"
        }
        
        return results


def demo_fractal_analysis():
    """Demonstrate fractal analysis capabilities"""
    engine = FractalUniverseSynthesis()
    
    np.random.seed(42)
    prices = 100 + np.cumsum(np.random.randn(100) * 2).tolist()
    
    eeg = {"delta": 0.3, "theta": 0.4, "alpha": 0.7, "beta": 0.5, "gamma": 0.3}
    hrv = 0.75
    
    results = engine.full_fractal_analysis(prices, eeg, hrv)
    
    print("\n" + "="*60)
    print("FRACTAL UNIVERSE ANALYSIS DEMO")
    print("="*60)
    print(f"\nFramework: {results['framework']}")
    
    if "market_analysis" in results:
        m = results["market_analysis"]
        print(f"\n📊 MARKET FRACTAL ANALYSIS:")
        print(f"   Direction: {m['direction']}")
        print(f"   Confidence: {m['confidence']*100:.1f}%")
        print(f"   Hurst Exponent: {m['weighted_hurst']:.4f}")
        print(f"   Scale Coherence: {m['scale_coherence']:.4f}")
        print(f"   Kleiber Weight: {m['kleiber_weight']}")
    
    if "consciousness_analysis" in results:
        c = results["consciousness_analysis"]
        print(f"\n🧠 CONSCIOUSNESS FRACTAL ANALYSIS:")
        print(f"   LCC Estimate: {c['lcc_estimate']:.4f}")
        print(f"   Neural Coherence: {c['neural_coherence']:.4f}")
        print(f"   Potentially Non-local: {c['potentially_nonlocal']}")
        print(f"   Lehto Alignment: {c['lehto_alignment']}")
    
    if "sacred_42_analysis" in results:
        s = results["sacred_42_analysis"]
        print(f"\n✨ SACRED 42 ANALYSIS:")
        print(f"   Resonance: {s['resonance']:.4f}")
        print(f"   Alignment: {s['alignment']}")
        print(f"   TI L×E: {s['ti_le_product']}")
    
    print("\n" + "="*60)
    return results


if __name__ == "__main__":
    demo_fractal_analysis()

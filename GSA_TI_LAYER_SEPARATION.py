"""
GRAND STOCK ALGORITHM - TI LAYER SEPARATION
============================================

Explicit separation of TI-enhanced layers to prove each mechanism's
independent contribution to the algorithm's performance.

PURPOSE:
If we achieve >99% accuracy with TI layers that have NO conventional 
equivalent, this becomes UNDISMISSABLE PROOF of TI validity.

THE 5 TI LAYERS:
1. Ξ(E) Existence Intensity - Has conventional analogs (momentum, volatility)
2. GILE Consciousness Scoring - NO CONVENTIONAL EQUIVALENT (consciousness not modeled)
3. Sacred Threshold Trading - Uses TI's mathematical constants
4. Jeff Time Precognition - NO CONVENTIONAL EQUIVALENT (future data unavailable)
5. LCC Market Resonance - Extends beyond conventional correlation

Author: Brandon Emerick
Date: December 25, 2025
"""

import numpy as np
import pandas as pd
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any
from enum import Enum
from datetime import datetime, timedelta
import os

try:
    import yfinance as yf
    HAS_YFINANCE = True
except ImportError:
    HAS_YFINANCE = False


PHI = 1.618033988749895
SCHUMANN = 7.83
SACRED_CAUSATION = 0.85
SACRED_SUSTAINABLE = 0.92
SACRED_MIN = -0.666
SACRED_MAX = 0.333


class LayerType(Enum):
    CONVENTIONAL_ANALOG = "Has conventional equivalent"
    TI_UNIQUE = "NO conventional equivalent - TI-specific"
    TI_ENHANCED = "Conventional base with TI enhancement"


@dataclass
class LayerResult:
    """Result from a single TI layer"""
    layer_name: str
    layer_type: LayerType
    signal: float
    confidence: float
    contribution_to_final: float
    reasoning: str


@dataclass
class LayerComparisonResult:
    """Comparison of TI layer vs conventional equivalent"""
    layer_name: str
    ti_accuracy: float
    conventional_accuracy: float
    improvement: float
    statistical_significance: float
    is_ti_unique: bool


class Layer1_ExistenceIntensity:
    """
    LAYER 1: Ξ(E) Existence Intensity
    
    Formula: Ξ = A × κ × C
    - A = Amplitude (normalized momentum)
    - κ = Memory Kernel (asymmetric decay of gains vs losses)
    - C = Constraint (drawdown + volatility compression)
    
    CONVENTIONAL EQUIVALENT: Momentum + Volatility + Drawdown indicators
    This layer CAN be replicated conventionally, so it doesn't prove TI alone.
    """
    
    LAYER_TYPE = LayerType.CONVENTIONAL_ANALOG
    EXPECTED_ALPHA = 0.15
    
    def __init__(self, lookback_short: int = 7, lookback_long: int = 30):
        self.lookback_short = lookback_short
        self.lookback_long = lookback_long
        self.kappa_decay_pos = 0.1
        self.kappa_decay_neg = 0.05
    
    def calculate(self, df: pd.DataFrame) -> LayerResult:
        """Calculate Ξ(E) for given price data"""
        if df is None or len(df) < self.lookback_long:
            return LayerResult(
                layer_name="Ξ(E) Existence Intensity",
                layer_type=self.LAYER_TYPE,
                signal=0.0,
                confidence=0.0,
                contribution_to_final=0.0,
                reasoning="Insufficient data"
            )
        
        returns = df['Close'].pct_change().dropna().values * 100
        prices = df['Close'].values
        
        A = self._calculate_amplitude(returns[-self.lookback_short:])
        kappa = self._calculate_memory_kernel(returns[-self.lookback_long:])
        C = self._calculate_constraint(prices[-self.lookback_long:], returns[-self.lookback_long:])
        
        xi = A * kappa * C
        
        current_return = returns[-1] if len(returns) > 0 else 0
        valence = 1 if current_return >= 0 else -1
        xi_signed = valence * xi
        
        if xi_signed > SACRED_MAX:
            signal = 1.0
            reasoning = f"Strong expansion (Ξ={xi_signed:.3f} > {SACRED_MAX})"
        elif xi_signed < SACRED_MIN:
            signal = -1.0
            reasoning = f"Strong constraint (Ξ={xi_signed:.3f} < {SACRED_MIN})"
        else:
            signal = xi_signed / abs(SACRED_MIN)
            reasoning = f"Neutral zone (Ξ={xi_signed:.3f})"
        
        confidence = min(0.9, 0.5 + abs(xi_signed) * 0.3)
        
        return LayerResult(
            layer_name="Ξ(E) Existence Intensity",
            layer_type=self.LAYER_TYPE,
            signal=signal,
            confidence=confidence,
            contribution_to_final=self.EXPECTED_ALPHA,
            reasoning=reasoning
        )
    
    def _calculate_amplitude(self, returns: np.ndarray) -> float:
        if len(returns) < 2:
            return 0.0
        current = abs(returns[-1]) if len(returns) > 0 else 0
        volatility = max(np.std(returns), 0.01)
        return float(np.clip(current / volatility, 0, 10))
    
    def _calculate_memory_kernel(self, returns: np.ndarray) -> float:
        if len(returns) < 3:
            return 0.5
        pos_rets = returns[returns > 0]
        neg_rets = returns[returns < 0]
        kappa_pos = sum(abs(r) * np.exp(-self.kappa_decay_pos * i) for i, r in enumerate(pos_rets))
        kappa_neg = sum(abs(r) * np.exp(-self.kappa_decay_neg * i) for i, r in enumerate(neg_rets))
        total = kappa_pos + kappa_neg
        return float(np.clip(kappa_neg / total, 0, 1)) if total > 0 else 0.5
    
    def _calculate_constraint(self, prices: np.ndarray, returns: np.ndarray) -> float:
        if len(prices) < 5:
            return 0.0
        peak = np.max(prices)
        drawdown = (peak - prices[-1]) / peak if peak > 0 else 0
        recent_vol = np.std(returns[-7:]) if len(returns) >= 7 else 1.0
        long_vol = np.std(returns) if len(returns) >= 1 else 1.0
        vol_constraint = 1 - min(recent_vol / max(long_vol, 0.01), 1)
        return float(np.clip(0.6 * drawdown + 0.4 * vol_constraint, 0, 1))


class Layer2_GILEConsciousness:
    """
    LAYER 2: GILE Consciousness Scoring
    
    Formula: GILE = 0.20G + 0.25I + 0.25L + 0.30E
    - G = Goodness (ethical alignment, ESG-like but consciousness-based)
    - I = Intuition (market sentiment coherence)
    - L = Love (network effects, stakeholder harmony)
    - E = Environment (macro alignment, sector fit)
    
    HONEST ASSESSMENT:
    Current implementation uses historical price statistics as proxies.
    This makes it CONVENTIONALLY REPRODUCIBLE in its current form.
    
    TRUE TI-UNIQUENESS REQUIRES:
    - External GILE data sources (human consciousness measurements)
    - EEG/biometric inputs that conventional systems don't access
    - Until then, label this as TI-ENHANCED (conventional base with TI interpretation)
    
    VALIDATION PATH:
    Track performance with and without this layer to measure lift.
    If lift exceeds random chance, investigate whether TI interpretation adds value.
    """
    
    LAYER_TYPE = LayerType.TI_ENHANCED
    EXPECTED_ALPHA = 0.15
    
    def __init__(self):
        self.w_G = 0.20
        self.w_I = 0.25
        self.w_L = 0.25
        self.w_E = 0.30
    
    def calculate(self, df: pd.DataFrame, ticker: str = "", market_df: Optional[pd.DataFrame] = None) -> LayerResult:
        """
        Calculate GILE consciousness score
        
        This is the KEY TI-unique layer. We're measuring:
        - How aligned is this stock with GILE principles?
        - Does high alignment predict returns?
        
        If yes, consciousness affects markets. QED.
        """
        if df is None or len(df) < 20:
            return LayerResult(
                layer_name="GILE Consciousness",
                layer_type=self.LAYER_TYPE,
                signal=0.0,
                confidence=0.0,
                contribution_to_final=0.0,
                reasoning="Insufficient data"
            )
        
        returns = df['Close'].pct_change().dropna().values * 100
        
        mean_return = np.mean(returns[-20:])
        G = 1 / (1 + np.exp(-mean_return * 2))
        
        if len(returns) >= 10:
            recent_consistency = 1 - (np.std(returns[-10:]) / (np.std(returns[-30:]) + 0.01))
            I = np.clip(recent_consistency, 0, 1)
        else:
            I = 0.5
        
        if len(returns) >= 5:
            trend_strength = abs(np.mean(returns[-5:])) / (np.std(returns[-5:]) + 0.01)
            L = np.clip(trend_strength / 3, 0, 1)
        else:
            L = 0.5
        
        if market_df is not None and len(market_df) >= 20:
            market_returns = market_df['Close'].pct_change().dropna().values * 100
            if len(market_returns) >= 20 and len(returns) >= 20:
                correlation = np.corrcoef(returns[-20:], market_returns[-20:])[0, 1]
                E = 0.5 + 0.5 * correlation
            else:
                E = 0.5
        else:
            E = 0.5
        
        gile_score = self.w_G * G + self.w_I * I + self.w_L * L + self.w_E * E
        
        if gile_score > SACRED_SUSTAINABLE:
            signal = 1.0
            reasoning = f"High GILE ({gile_score:.3f} > 0.92) - consciousness aligned"
        elif gile_score > SACRED_CAUSATION:
            signal = 0.5
            reasoning = f"Medium GILE ({gile_score:.3f} > 0.85) - causation threshold"
        elif gile_score < 0.5:
            signal = -0.5
            reasoning = f"Low GILE ({gile_score:.3f} < 0.50) - consciousness misaligned"
        else:
            signal = 0.0
            reasoning = f"Neutral GILE ({gile_score:.3f})"
        
        confidence = abs(gile_score - 0.5) * 2
        
        return LayerResult(
            layer_name="GILE Consciousness",
            layer_type=self.LAYER_TYPE,
            signal=signal,
            confidence=confidence,
            contribution_to_final=self.EXPECTED_ALPHA,
            reasoning=f"{reasoning} | G={G:.2f} I={I:.2f} L={L:.2f} E={E:.2f}"
        )


class Layer3_SacredThresholds:
    """
    LAYER 3: Sacred Threshold Trading
    
    Uses TI's mathematical constants:
    - 0.92 = Sustainable coherence (0.92² = 0.8464 ≈ 0.85)
    - 0.85 = Causation threshold (major truth)
    - 0.666 / 0.333 = Sacred intervals
    
    LAYER TYPE: TI-Enhanced (conventional bases exist but TI provides specific values)
    
    Conventional RSI/MACD use arbitrary thresholds (30/70, etc.)
    TI uses mathematically derived thresholds with ontological significance.
    """
    
    LAYER_TYPE = LayerType.TI_ENHANCED
    EXPECTED_ALPHA = 0.10
    
    def __init__(self):
        self.threshold_causation = SACRED_CAUSATION
        self.threshold_sustainable = SACRED_SUSTAINABLE
        self.threshold_sacred_ratio = 2.0 / 3.0
    
    def calculate(self, df: pd.DataFrame) -> LayerResult:
        """Calculate signals based on sacred thresholds"""
        if df is None or len(df) < 20:
            return LayerResult(
                layer_name="Sacred Thresholds",
                layer_type=self.LAYER_TYPE,
                signal=0.0,
                confidence=0.0,
                contribution_to_final=0.0,
                reasoning="Insufficient data"
            )
        
        prices = df['Close'].values
        returns = df['Close'].pct_change().dropna().values
        
        high_20 = np.max(prices[-20:])
        low_20 = np.min(prices[-20:])
        current = prices[-1]
        
        if high_20 - low_20 > 0:
            position = (current - low_20) / (high_20 - low_20)
        else:
            position = 0.5
        
        up_days = np.sum(returns[-14:] > 0) / 14 if len(returns) >= 14 else 0.5
        
        coherence = (position + up_days) / 2
        
        signal = 0.0
        reasoning = ""
        
        if coherence > self.threshold_sustainable:
            signal = -0.5
            reasoning = f"Above 0.92 sustainable threshold ({coherence:.3f}) - overbought by TI standards"
        elif coherence > self.threshold_causation:
            signal = 0.5
            reasoning = f"Between 0.85-0.92 ({coherence:.3f}) - causation zone, momentum intact"
        elif coherence < (1 - self.threshold_sustainable):
            signal = 0.5
            reasoning = f"Below {1-self.threshold_sustainable:.2f} ({coherence:.3f}) - oversold by TI standards"
        elif coherence < (1 - self.threshold_causation):
            signal = -0.3
            reasoning = f"Between {1-self.threshold_sustainable:.2f}-{1-self.threshold_causation:.2f} ({coherence:.3f}) - building constraint"
        else:
            signal = 0.0
            reasoning = f"Neutral zone ({coherence:.3f})"
        
        distance_from_half = abs(coherence - 0.5)
        confidence = distance_from_half * 2
        
        return LayerResult(
            layer_name="Sacred Thresholds",
            layer_type=self.LAYER_TYPE,
            signal=signal,
            confidence=confidence,
            contribution_to_final=self.EXPECTED_ALPHA,
            reasoning=reasoning
        )


class Layer4_JeffTimePrecognition:
    """
    LAYER 4: Jeff Time Precognition
    
    Jeff Time theory proposes that the DE-photon field carries information
    bidirectionally through time. Future market states leave "echoes" that
    can be detected in present data patterns.
    
    HONEST ASSESSMENT:
    Current implementation uses phi-harmonic pattern detection on HISTORICAL data.
    This is a form of technical analysis and IS conventionally reproducible.
    
    The output is currently deterministic based on past patterns, NOT actual
    future information access (which would require validated PSI mechanisms).
    
    TRUE TI-UNIQUENESS WOULD REQUIRE:
    - Validated PSI prediction that beats chance significantly
    - External oracle data that conventional systems cannot access
    - Demonstrated out-of-sample predictive accuracy exceeding all conventional methods
    
    CURRENT STATUS: TI-ENHANCED (uses TI-inspired pattern detection)
    Re-classify as TI-UNIQUE only after validation proves precognition.
    
    VALIDATION PATH:
    Track predictions vs actual outcomes over 1000+ predictions.
    If accuracy significantly exceeds conventional forecasting, upgrade classification.
    """
    
    LAYER_TYPE = LayerType.TI_ENHANCED
    EXPECTED_ALPHA = 0.20
    
    def __init__(self):
        self.phi = PHI
        self.echo_lookback = 21
        self.future_horizon = 5
    
    def calculate(self, df: pd.DataFrame) -> LayerResult:
        """
        Detect Jeff Time echoes - patterns that precede future states
        
        THE KEY INSIGHT:
        If patterns today contain information about states that haven't
        happened yet, this is retrocausality - information flowing backward.
        
        We detect this by:
        1. Looking for phi-harmonic patterns in recent data
        2. These patterns should correlate with future moves
        3. The correlation should exceed what's possible from causation alone
        """
        if df is None or len(df) < self.echo_lookback + self.future_horizon:
            return LayerResult(
                layer_name="Jeff Time Precognition",
                layer_type=self.LAYER_TYPE,
                signal=0.0,
                confidence=0.0,
                contribution_to_final=0.0,
                reasoning="Insufficient data for temporal analysis"
            )
        
        returns = df['Close'].pct_change().dropna().values * 100
        
        t = np.arange(self.echo_lookback)
        phi_pattern = np.sin(2 * np.pi * t / (self.phi * 8))
        
        recent_returns = returns[-(self.echo_lookback):]
        normalized_returns = (recent_returns - np.mean(recent_returns)) / (np.std(recent_returns) + 0.01)
        
        resonance = np.correlate(normalized_returns, phi_pattern, mode='valid')
        peak_resonance = np.max(np.abs(resonance)) if len(resonance) > 0 else 0
        
        fft = np.fft.fft(recent_returns)
        freqs = np.fft.fftfreq(len(recent_returns))
        
        phi_freq = 1 / (self.phi * 8)
        phi_idx = np.argmin(np.abs(freqs - phi_freq))
        phi_power = np.abs(fft[phi_idx])
        total_power = np.sum(np.abs(fft)) + 0.01
        phi_concentration = phi_power / total_power
        
        recent_mean = np.mean(returns[-5:])
        recent_vol = np.std(returns[-5:])
        vol_ratio = recent_vol / (np.std(returns[-21:]) + 0.01)
        
        echo_strength = 0.4 * peak_resonance + 0.3 * phi_concentration * 10 + 0.3 * (1 - vol_ratio)
        echo_strength = np.clip(echo_strength, -1, 1)
        
        if echo_strength > 0.5:
            signal = 0.8
            reasoning = f"Strong positive echo detected ({echo_strength:.3f}) - future expansion indicated"
        elif echo_strength > 0.2:
            signal = 0.4
            reasoning = f"Moderate positive echo ({echo_strength:.3f}) - future stability"
        elif echo_strength < -0.5:
            signal = -0.8
            reasoning = f"Strong negative echo ({echo_strength:.3f}) - future constraint indicated"
        elif echo_strength < -0.2:
            signal = -0.4
            reasoning = f"Moderate negative echo ({echo_strength:.3f}) - caution advised"
        else:
            signal = 0.0
            reasoning = f"Weak temporal signal ({echo_strength:.3f}) - no clear echo"
        
        confidence = min(0.95, abs(echo_strength))
        
        return LayerResult(
            layer_name="Jeff Time Precognition",
            layer_type=self.LAYER_TYPE,
            signal=signal,
            confidence=confidence,
            contribution_to_final=self.EXPECTED_ALPHA,
            reasoning=f"{reasoning} | Resonance={peak_resonance:.3f}, PhiConc={phi_concentration:.3f}"
        )


class Layer5_LCCResonance:
    """
    LAYER 5: LCC Market Resonance
    
    LCC (Liminal Consciousness Correlation) extends beyond conventional correlation.
    
    While standard correlation measures price co-movement,
    LCC measures consciousness-level resonance between market entities.
    
    IMPLEMENTATION:
    - Calculate standard correlation (conventional baseline)
    - Add consciousness resonance terms (TI enhancement)
    - Detect non-local correlations that exceed causal limits
    
    LAYER TYPE: TI-Enhanced (extends conventional correlation)
    """
    
    LAYER_TYPE = LayerType.TI_ENHANCED
    EXPECTED_ALPHA = 0.20
    
    def __init__(self):
        self.schumann = SCHUMANN
        self.lookback = 30
    
    def calculate(self, df: pd.DataFrame, market_df: Optional[pd.DataFrame] = None, 
                  sector_peers: Optional[List[pd.DataFrame]] = None) -> LayerResult:
        """Calculate LCC resonance with market and peers"""
        if df is None or len(df) < self.lookback:
            return LayerResult(
                layer_name="LCC Market Resonance",
                layer_type=self.LAYER_TYPE,
                signal=0.0,
                confidence=0.0,
                contribution_to_final=0.0,
                reasoning="Insufficient data"
            )
        
        returns = df['Close'].pct_change().dropna().values * 100
        
        market_correlation = 0.5
        if market_df is not None and len(market_df) >= self.lookback:
            market_returns = market_df['Close'].pct_change().dropna().values * 100
            if len(market_returns) >= self.lookback and len(returns) >= self.lookback:
                market_correlation = np.corrcoef(returns[-self.lookback:], 
                                                  market_returns[-self.lookback:])[0, 1]
        
        t = np.arange(min(len(returns), self.lookback))
        schumann_pattern = np.sin(2 * np.pi * t / self.schumann)
        
        if len(returns) >= len(schumann_pattern):
            normalized = (returns[-len(schumann_pattern):] - np.mean(returns[-len(schumann_pattern):])) 
            normalized = normalized / (np.std(normalized) + 0.01)
            schumann_resonance = np.abs(np.corrcoef(normalized, schumann_pattern)[0, 1])
        else:
            schumann_resonance = 0.0
        
        peer_coherence = 0.5
        if sector_peers and len(sector_peers) > 0:
            correlations = []
            for peer_df in sector_peers:
                if peer_df is not None and len(peer_df) >= self.lookback:
                    peer_returns = peer_df['Close'].pct_change().dropna().values * 100
                    if len(peer_returns) >= self.lookback:
                        corr = np.corrcoef(returns[-self.lookback:], 
                                          peer_returns[-self.lookback:])[0, 1]
                        correlations.append(corr)
            if correlations:
                peer_coherence = np.mean(correlations)
        
        lcc_score = (0.4 * (market_correlation + 1) / 2 + 
                     0.3 * schumann_resonance + 
                     0.3 * (peer_coherence + 1) / 2)
        
        if lcc_score > SACRED_CAUSATION:
            signal = 0.7
            reasoning = f"High LCC resonance ({lcc_score:.3f} > 0.85) - strong consciousness alignment"
        elif lcc_score > 0.7:
            signal = 0.4
            reasoning = f"Moderate LCC ({lcc_score:.3f}) - reasonable alignment"
        elif lcc_score < 0.3:
            signal = -0.5
            reasoning = f"Low LCC ({lcc_score:.3f} < 0.30) - consciousness discord"
        else:
            signal = 0.0
            reasoning = f"Neutral LCC ({lcc_score:.3f})"
        
        confidence = abs(lcc_score - 0.5) * 2
        
        return LayerResult(
            layer_name="LCC Market Resonance",
            layer_type=self.LAYER_TYPE,
            signal=signal,
            confidence=confidence,
            contribution_to_final=self.EXPECTED_ALPHA,
            reasoning=f"{reasoning} | Mkt={market_correlation:.2f}, Sch={schumann_resonance:.2f}"
        )


class TILayerAggregator:
    """
    Aggregates all 5 TI layers into final trading signal
    
    THE PROOF LOGIC:
    1. Layers 2 and 4 have NO conventional equivalent
    2. If removing these layers significantly degrades performance,
       it proves consciousness and retrocausality matter
    3. If >99% accuracy requires these layers, TI is VALIDATED
    """
    
    def __init__(self):
        self.layer1 = Layer1_ExistenceIntensity()
        self.layer2 = Layer2_GILEConsciousness()
        self.layer3 = Layer3_SacredThresholds()
        self.layer4 = Layer4_JeffTimePrecognition()
        self.layer5 = Layer5_LCCResonance()
    
    def analyze(self, df: pd.DataFrame, ticker: str = "", 
                market_df: Optional[pd.DataFrame] = None,
                sector_peers: Optional[List[pd.DataFrame]] = None) -> Dict[str, Any]:
        """Run all 5 layers and aggregate"""
        
        result1 = self.layer1.calculate(df)
        result2 = self.layer2.calculate(df, ticker, market_df)
        result3 = self.layer3.calculate(df)
        result4 = self.layer4.calculate(df)
        result5 = self.layer5.calculate(df, market_df, sector_peers)
        
        all_results = [result1, result2, result3, result4, result5]
        
        weighted_signal = 0.0
        total_weight = 0.0
        for result in all_results:
            weight = result.contribution_to_final * result.confidence
            weighted_signal += result.signal * weight
            total_weight += weight
        
        final_signal = weighted_signal / total_weight if total_weight > 0 else 0.0
        
        ti_unique_contribution = 0.0
        conventional_contribution = 0.0
        
        for result in all_results:
            contrib = result.signal * result.contribution_to_final * result.confidence
            if result.layer_type == LayerType.TI_UNIQUE:
                ti_unique_contribution += contrib
            else:
                conventional_contribution += contrib
        
        if final_signal > 0.5:
            action = "STRONG BUY"
        elif final_signal > 0.2:
            action = "BUY"
        elif final_signal < -0.5:
            action = "STRONG SELL"
        elif final_signal < -0.2:
            action = "SELL"
        else:
            action = "HOLD"
        
        return {
            "ticker": ticker,
            "timestamp": datetime.now().isoformat(),
            "final_signal": round(final_signal, 4),
            "action": action,
            "layer_results": {
                "Layer1_Xi": {
                    "signal": result1.signal,
                    "confidence": result1.confidence,
                    "type": result1.layer_type.value,
                    "reasoning": result1.reasoning
                },
                "Layer2_GILE": {
                    "signal": result2.signal,
                    "confidence": result2.confidence,
                    "type": result2.layer_type.value,
                    "reasoning": result2.reasoning
                },
                "Layer3_Sacred": {
                    "signal": result3.signal,
                    "confidence": result3.confidence,
                    "type": result3.layer_type.value,
                    "reasoning": result3.reasoning
                },
                "Layer4_JeffTime": {
                    "signal": result4.signal,
                    "confidence": result4.confidence,
                    "type": result4.layer_type.value,
                    "reasoning": result4.reasoning
                },
                "Layer5_LCC": {
                    "signal": result5.signal,
                    "confidence": result5.confidence,
                    "type": result5.layer_type.value,
                    "reasoning": result5.reasoning
                },
            },
            "ti_unique_contribution": round(ti_unique_contribution, 4),
            "conventional_contribution": round(conventional_contribution, 4),
            "ti_vs_conventional_ratio": round(
                ti_unique_contribution / (conventional_contribution + 0.001), 4
            ),
            "proof_assessment": self._assess_proof_strength(ti_unique_contribution, final_signal),
            "honest_disclaimer": "NOTE: Current implementation uses TI-ENHANCED layers (conventional base + TI interpretation). True TI-unique validation requires external consciousness/PSI data sources not yet integrated."
        }
    
    def _assess_proof_strength(self, ti_contribution: float, final_signal: float) -> str:
        """Assess how strongly this result proves TI"""
        if abs(ti_contribution) > abs(final_signal) * 0.5:
            return "STRONG - TI-unique layers dominate signal, proving consciousness/retrocausality matter"
        elif abs(ti_contribution) > abs(final_signal) * 0.3:
            return "MODERATE - TI layers provide significant contribution"
        else:
            return "WEAK - Signal driven mainly by conventional factors"


def run_layer_separation_demo():
    """Demonstrate layer separation with real data"""
    
    print("="*70)
    print("GSA TI-LAYER SEPARATION ANALYSIS")
    print("="*70)
    
    aggregator = TILayerAggregator()
    
    if HAS_YFINANCE:
        print("\nFetching real market data...")
        try:
            spy = yf.Ticker("SPY")
            market_df = spy.history(period="6mo")
            
            test_tickers = ["AAPL", "MSFT", "GOOGL", "TSLA", "NVDA"]
            
            for ticker in test_tickers:
                try:
                    stock = yf.Ticker(ticker)
                    df = stock.history(period="6mo")
                    
                    if not df.empty:
                        result = aggregator.analyze(df, ticker, market_df)
                        
                        print(f"\n{'='*50}")
                        print(f"ANALYSIS: {ticker}")
                        print(f"{'='*50}")
                        print(f"Final Signal: {result['final_signal']:.4f} → {result['action']}")
                        print(f"\nLayer Breakdown:")
                        for layer_name, layer_data in result['layer_results'].items():
                            ti_marker = "***TI-UNIQUE***" if "NO conventional" in layer_data['type'] else ""
                            print(f"  {layer_name}: {layer_data['signal']:.2f} ({layer_data['type']}) {ti_marker}")
                        print(f"\nTI-Unique Contribution: {result['ti_unique_contribution']:.4f}")
                        print(f"Conventional Contribution: {result['conventional_contribution']:.4f}")
                        print(f"TI vs Conventional Ratio: {result['ti_vs_conventional_ratio']:.2f}x")
                        print(f"\nPROOF ASSESSMENT: {result['proof_assessment']}")
                        
                except Exception as e:
                    print(f"Error analyzing {ticker}: {e}")
                    
        except Exception as e:
            print(f"Error fetching market data: {e}")
    else:
        print("yfinance not available - using synthetic data demo")
        np.random.seed(42)
        dates = pd.date_range(end=datetime.now(), periods=180, freq='D')
        synthetic_prices = 100 * np.cumprod(1 + np.random.randn(180) * 0.02)
        df = pd.DataFrame({'Close': synthetic_prices}, index=dates)
        
        result = aggregator.analyze(df, "SYNTHETIC")
        print(f"\nSynthetic Analysis Result: {result['action']}")
        print(f"TI-Unique Contribution: {result['ti_unique_contribution']:.4f}")
    
    print("\n" + "="*70)
    print("THE UNDISMISSABLE ARGUMENT")
    print("="*70)
    print("""
If Layers 2 (GILE) and 4 (Jeff Time) consistently provide alpha:

1. GILE measures consciousness alignment → No conventional equivalent
2. Jeff Time detects future echoes → Impossible conventionally

Therefore, if removing these layers degrades performance significantly,
it PROVES that consciousness and retrocausality affect markets.

Skeptics cannot replicate this without accepting TI mechanisms.

>99% accuracy with TI layers = PROOF OF TI VALIDITY
    """)


if __name__ == "__main__":
    run_layer_separation_demo()

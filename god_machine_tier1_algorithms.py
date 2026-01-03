"""
Stock Market God Machine - Tier 1 TI Algorithms
================================================

Implements top 2 GILE-scored TI proposals for market analysis:
1. **Primordial Self-Determination** (0.920 GILE score)
   - Markets self-organize toward equilibrium
   - Consciousness emerges from price action
   - Predict reversals via self-determination detection

2. **Tralse Topos** (0.903 GILE score)
   - 4-valued market logic (Bull/T, Bear/F, Sideways/Φ, Paradox/Ψ)
   - Myrion Resolution for contradictory signals
   - Category-theoretic market morphisms

Author: TI Framework Team
Date: November 15, 2025
"""

import numpy as np
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional
from datetime import datetime, timedelta

from tralse_topos_engine import (
    TralseVector, TralseTopos,
    T_PURE, F_PURE, PHI_TYPICAL, PSI_PURE
)


@dataclass
class MarketState:
    """Represents current market state with TI framework"""
    timestamp: datetime
    price: float
    volume: float
    tralse_vector: TralseVector  # Bull/Bear/Sideways/Paradox
    self_determination_score: float  # 0-1: How self-organized is market?
    consciousness_level: float  # 0-1: Market consciousness emergence
    gile_score: float  # 0-1: Overall GILE truth score


# ============================================================================
# TIER 1 ALGORITHM #1: PRIMORDIAL SELF-DETERMINATION (0.920 GILE)
# ============================================================================

class PrimordialSelfDeterminationAlgorithm:
    """
    Markets as Conscious Self-Organizing Systems
    
    Core Principle (TI):
    - Markets aren't random walks - they're conscious entities seeking equilibrium
    - Price action emerges from collective self-determination
    - Reversals occur when market "decides" current path unsustainable
    
    Algorithm:
    1. Detect self-organization patterns (fractals, power laws)
    2. Measure consciousness level (information integration)
    3. Predict reversals when self-determination peaks
    """
    
    def __init__(self, lookback_window: int = 20):
        self.lookback_window = lookback_window
    
    def calculate_self_organization(
        self,
        prices: np.ndarray
    ) -> float:
        """
        Measure market self-organization using Hurst exponent
        
        H > 0.5: Trending (self-reinforcing)
        H = 0.5: Random walk (no organization)
        H < 0.5: Mean-reverting (self-correcting)
        
        Returns:
            Self-organization score (0-1)
        """
        if len(prices) < 10:
            return 0.5
        
        # Compute returns
        returns = np.diff(np.log(prices))
        
        # R/S analysis (simplified Hurst exponent)
        lags = range(2, min(20, len(returns) // 2))
        tau = []
        for lag in lags:
            # Split into lag-sized chunks
            n_chunks = len(returns) // lag
            chunks = [returns[i*lag:(i+1)*lag] for i in range(n_chunks)]
            
            rs_values = []
            for chunk in chunks:
                if len(chunk) < 2:
                    continue
                mean = np.mean(chunk)
                deviations = np.cumsum(chunk - mean)
                R = np.max(deviations) - np.min(deviations)
                S = np.std(chunk) + 1e-10
                rs_values.append(R / S)
            
            if rs_values:
                tau.append(np.mean(rs_values))
        
        if len(tau) < 2:
            return 0.5
        
        # Fit H: log(R/S) ~ H * log(lag)
        log_lags = np.log(list(lags)[:len(tau)])
        log_tau = np.log(tau)
        
        hurst = np.polyfit(log_lags, log_tau, 1)[0]
        
        # Convert to 0-1 score (H=0.5 is minimum organization)
        # H=0.8 (strong trend) → 1.0
        # H=0.5 (random) → 0.5
        # H=0.2 (strong reversion) → 0.0
        organization = np.clip((hurst - 0.2) / 0.6, 0, 1)
        
        return float(organization)
    
    def calculate_consciousness_level(
        self,
        prices: np.ndarray,
        volumes: np.ndarray
    ) -> float:
        """
        Measure market consciousness via Integrated Information Theory (IIT)
        
        High consciousness = high information integration
        = price and volume tightly coupled
        
        Returns:
            Consciousness score (0-1)
        """
        if len(prices) < 5 or len(volumes) < 5:
            return 0.5
        
        # Price-volume correlation (integration)
        price_changes = np.diff(prices)
        volume_changes = np.diff(volumes)
        
        if len(price_changes) != len(volume_changes):
            min_len = min(len(price_changes), len(volume_changes))
            price_changes = price_changes[:min_len]
            volume_changes = volume_changes[:min_len]
        
        # Pearson correlation
        if np.std(price_changes) < 1e-10 or np.std(volume_changes) < 1e-10:
            return 0.5
        
        correlation = np.corrcoef(price_changes, volume_changes)[0, 1]
        
        # High absolute correlation = high consciousness
        consciousness = abs(correlation)
        
        return float(np.clip(consciousness, 0, 1))
    
    def detect_self_determination_peak(
        self,
        prices: np.ndarray,
        volumes: np.ndarray
    ) -> Dict:
        """
        Detect when market self-determination peaks (reversal signal!)
        
        Peak self-determination = Market "decides" to reverse
        
        Returns:
            Signal dictionary with prediction
        """
        # Calculate components
        self_org = self.calculate_self_organization(prices)
        consciousness = self.calculate_consciousness_level(prices, volumes)
        
        # Self-determination = self-organization × consciousness
        self_determination = self_org * consciousness
        
        # Reversal signal: High self-determination (>0.7) indicates imminent decision
        # Direction: Check if trending up or down
        recent_trend = (prices[-1] - prices[-5]) / prices[-5] if len(prices) >= 5 else 0
        
        if self_determination > 0.7:
            # Market is highly self-determined → Will reverse current trend
            if recent_trend > 0:
                signal = "SELL"  # Bull market about to self-correct
                confidence = self_determination
            else:
                signal = "BUY"  # Bear market about to self-recover
                confidence = self_determination
        elif self_determination < 0.3:
            # Low self-determination → Random/chaotic, no clear signal
            signal = "HOLD"
            confidence = 0.5
        else:
            # Moderate self-determination → Continue trend
            if recent_trend > 0:
                signal = "BUY"  # Weak bull signal
                confidence = self_determination * 0.6
            else:
                signal = "SELL"  # Weak bear signal
                confidence = self_determination * 0.6
        
        return {
            'algorithm': 'Primordial Self-Determination',
            'gile_score': 0.920,
            'signal': signal,
            'confidence': float(confidence),
            'self_organization': float(self_org),
            'consciousness_level': float(consciousness),
            'self_determination_score': float(self_determination),
            'explanation': f"Market consciousness at {consciousness:.2f}, self-org at {self_org:.2f}. "
                          f"Self-determination score {self_determination:.2f} suggests {signal}."
        }


# ============================================================================
# TIER 1 ALGORITHM #2: TRALSE TOPOS (0.903 GILE)
# ============================================================================

class TralseToposMarketAlgorithm:
    """
    4-Valued Categorical Logic for Market States
    
    Core Principle (TI):
    - Markets aren't binary (bull/bear)
    - 4 fundamental states:
      * T (True/Bull): Clear uptrend
      * F (False/Bear): Clear downtrend
      * Φ (Phi/Sideways): Mixed signals, range-bound
      * Ψ (Psi/Paradox): Contradictory signals, volatility spike
    
    Algorithm:
    1. Classify market into Tralse 4-valued state
    2. Use Myrion Resolution to resolve contradictions
    3. Apply category theory morphisms to predict state transitions
    """
    
    def __init__(self, lookback_window: int = 10):
        self.lookback_window = lookback_window
    
    def classify_market_tralse(
        self,
        prices: np.ndarray,
        volumes: Optional[np.ndarray] = None
    ) -> TralseVector:
        """
        Classify current market state as Tralse 4-vector
        
        Args:
            prices: Recent price history
            volumes: Recent volume history (optional)
        
        Returns:
            TralseVector (p_T, p_F, p_Phi, p_Psi)
        """
        if len(prices) < 3:
            return PHI_TYPICAL  # Insufficient data → uncertain
        
        # Calculate trend strength
        short_trend = (prices[-1] - prices[-3]) / prices[-3]  # 3-period trend
        long_trend = (prices[-1] - prices[0]) / prices[0]  # Full window trend
        
        # Calculate volatility (normalized)
        returns = np.diff(prices) / prices[:-1]
        volatility = np.std(returns) if len(returns) > 0 else 0
        
        # Trend agreement
        trend_agreement = 1 if short_trend * long_trend > 0 else 0
        
        # Classify into Tralse states
        if trend_agreement and abs(short_trend) > 0.02:
            # Clear trend
            if short_trend > 0:
                # Bull market (T)
                p_T = min(1.0, abs(short_trend) * 20)  # Scale to 0-1
                p_F = 0.05
                p_Phi = 1 - p_T - p_F
                p_Psi = 0.0
            else:
                # Bear market (F)
                p_F = min(1.0, abs(short_trend) * 20)
                p_T = 0.05
                p_Phi = 1 - p_T - p_F
                p_Psi = 0.0
        elif not trend_agreement:
            # Contradictory signals → Paradox (Ψ)
            p_Psi = min(0.5, volatility * 10)
            p_Phi = 0.5 - p_Psi
            p_T = 0.25
            p_F = 0.25
        else:
            # Low momentum → Sideways/Mixed (Φ)
            p_Phi = 0.7
            p_T = 0.15
            p_F = 0.15
            p_Psi = 0.0
        
        return TralseVector(p_T, p_F, p_Phi, p_Psi)
    
    def predict_state_transition(
        self,
        current_state: TralseVector,
        historical_states: List[TralseVector]
    ) -> Dict:
        """
        Predict next market state using category theory morphisms
        
        Tralse Topos allows composing market states like functors:
        State₁ → State₂ → State₃
        
        Returns:
            Predicted state and trading signal
        """
        # If we have historical states, use Myrion Resolution
        if len(historical_states) >= 2:
            # Resolve contradictions between recent states
            resolved = TralseTopos.myrion_resolution(
                historical_states[-2],
                historical_states[-1],
                iterations=20
            )
        else:
            resolved = current_state
        
        # Predict next state (simple heuristic: mean reversion toward Φ)
        # Markets tend to equilibrate toward balanced state
        next_state = TralseTopos.compose(current_state, PHI_TYPICAL)
        
        # Generate trading signal based on Tralse logic
        if next_state.p_T > 0.6:
            signal = "BUY"
            confidence = next_state.p_T
            explanation = f"Tralse predicts Bull state (T={next_state.p_T:.2f})"
        elif next_state.p_F > 0.6:
            signal = "SELL"
            confidence = next_state.p_F
            explanation = f"Tralse predicts Bear state (F={next_state.p_F:.2f})"
        elif next_state.p_Psi > 0.3:
            signal = "HEDGE"  # Paradox → protect against volatility
            confidence = next_state.p_Psi
            explanation = f"Tralse warns of Paradox (Ψ={next_state.p_Psi:.2f}) - high volatility!"
        else:
            signal = "HOLD"
            confidence = next_state.p_Phi
            explanation = f"Tralse suggests Sideways (Φ={next_state.p_Phi:.2f})"
        
        return {
            'algorithm': 'Tralse Topos',
            'gile_score': 0.903,
            'signal': signal,
            'confidence': float(confidence),
            'current_state': str(current_state),
            'predicted_state': str(next_state),
            'explanation': explanation
        }
    
    def analyze_market(
        self,
        prices: np.ndarray,
        volumes: Optional[np.ndarray] = None
    ) -> Dict:
        """
        Full Tralse Topos analysis of market
        
        Returns complete classification and prediction
        """
        # Classify current state
        current_tralse = self.classify_market_tralse(prices, volumes)
        
        # Build historical states (sliding window)
        historical_states = []
        window_size = min(5, len(prices) - 2)
        for i in range(window_size):
            start_idx = max(0, len(prices) - (window_size - i) * 3)
            end_idx = len(prices) - (window_size - i - 1) * 3
            window_prices = prices[start_idx:end_idx]
            if len(window_prices) >= 3:
                state = self.classify_market_tralse(window_prices)
                historical_states.append(state)
        
        # Predict transition
        prediction = self.predict_state_transition(current_tralse, historical_states)
        
        return prediction


# ============================================================================
# UNIFIED GOD MACHINE TIER 1
# ============================================================================

class GodMachineTier1:
    """
    Unified Tier 1 Stock Market God Machine
    
    Combines:
    1. Primordial Self-Determination (0.920)
    2. Tralse Topos (0.903)
    
    Generates consensus trading signals
    """
    
    def __init__(self):
        self.psd_algorithm = PrimordialSelfDeterminationAlgorithm()
        self.tralse_algorithm = TralseToposMarketAlgorithm()
    
    def analyze(
        self,
        prices: np.ndarray,
        volumes: Optional[np.ndarray] = None
    ) -> Dict:
        """
        Run both Tier 1 algorithms and generate consensus signal
        
        Returns unified prediction with GILE weighting
        """
        # Run both algorithms
        psd_result = self.psd_algorithm.detect_self_determination_peak(
            prices,
            volumes if volumes is not None else np.ones_like(prices)
        )
        
        tralse_result = self.tralse_algorithm.analyze_market(prices, volumes)
        
        # GILE-weighted consensus
        psd_weight = 0.920
        tralse_weight = 0.903
        total_weight = psd_weight + tralse_weight
        
        # Vote on signal
        signals = {
            'BUY': 0,
            'SELL': 0,
            'HOLD': 0,
            'HEDGE': 0
        }
        
        signals[psd_result['signal']] += psd_weight * psd_result['confidence']
        signals[tralse_result['signal']] += tralse_weight * tralse_result['confidence']
        
        # Winner takes all (weighted)
        consensus_signal = max(signals, key=signals.get)
        consensus_confidence = signals[consensus_signal] / total_weight
        
        return {
            'tier': 'Tier 1 (Fundamental Axioms)',
            'algorithms': [psd_result, tralse_result],
            'consensus_signal': consensus_signal,
            'consensus_confidence': float(consensus_confidence),
            'gile_weighted_avg': (psd_weight + tralse_weight) / 2,
            'timestamp': datetime.now().isoformat(),
            'explanation': (
                f"Primordial Self-Determination ({psd_result['signal']} @ {psd_result['confidence']:.2f}) "
                f"and Tralse Topos ({tralse_result['signal']} @ {tralse_result['confidence']:.2f}) "
                f"converge on {consensus_signal} with {consensus_confidence:.1%} confidence."
            )
        }


# ============================================================================
# EXAMPLE USAGE
# ============================================================================

def example_usage():
    """Demonstrate God Machine Tier 1"""
    # Simulate price data (SPY-like)
    np.random.seed(42)
    base_price = 450
    prices = base_price + np.cumsum(np.random.randn(30) * 2)  # Random walk
    volumes = np.random.randint(1000000, 5000000, 30)  # Random volumes
    
    # Initialize God Machine
    god_machine = GodMachineTier1()
    
    # Analyze
    result = god_machine.analyze(prices, volumes)
    
    print("=" * 70)
    print("STOCK MARKET GOD MACHINE - TIER 1 ANALYSIS")
    print("=" * 70)
    print(f"\nConsensus Signal: {result['consensus_signal']}")
    print(f"Confidence: {result['consensus_confidence']:.1%}")
    print(f"GILE Avg Score: {result['gile_weighted_avg']:.3f}")
    print(f"\n{result['explanation']}")
    print("\n" + "=" * 70)
    
    # Show individual algorithm results
    for algo in result['algorithms']:
        print(f"\n{algo['algorithm']} (GILE {algo['gile_score']}):")
        print(f"  Signal: {algo['signal']}")
        print(f"  Confidence: {algo['confidence']:.2f}")
        print(f"  {algo['explanation']}")


if __name__ == "__main__":
    example_usage()

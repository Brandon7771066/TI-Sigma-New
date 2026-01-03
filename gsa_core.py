"""
GSA CORE ENGINE - Pure TI Framework Logic
Platform-agnostic: works with QuantConnect, Numerai, or standalone research

Grand Stock Algorithm (GSA) - Existence Intensity Framework
Ξ(E) = A(t) · κ(t,τ) · C(t) -> PD -> GILE -> Signal
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from enum import Enum

class MarketRegime(Enum):
    EXPANSION = "expansion"
    COMPRESSION = "compression"
    FRACTURE = "fracture"
    RESET = "reset"

@dataclass
class XiMetrics:
    """Existence Intensity decomposition"""
    amplitude: float  # A(t) - normalized current move
    memory_kernel: float  # κ(t,τ) - negative memory dominance [0,1]
    constraint: float  # C(t) - drawdown + volatility constraint [0,1]
    xi_unsigned: float  # A * κ * C
    xi_signed: float  # with valence weight
    pd: float  # Probability Distribution score [-3, +2]

@dataclass
class GILEScore:
    """Four-dimensional GILE assessment"""
    goodness: float  # G - risk-adjusted returns
    intuition: float  # I - trend alignment
    love: float  # L - market correlation
    environment: float  # E - momentum alignment
    composite: float  # Weighted combination

@dataclass
class Signal:
    """Trading signal with metadata"""
    action: str  # strong_buy, buy, hold, sell, strong_sell
    confidence: float  # 0-1
    gile: float
    xi_metrics: XiMetrics
    regime: MarketRegime
    reasons: List[str]


class GSACore:
    """
    Core GSA Engine - Platform Agnostic
    
    Feed it price/return arrays, get back Xi metrics, GILE scores, and signals.
    """
    
    def __init__(
        self,
        lookback_short: int = 7,
        lookback_long: int = 60,
        kappa_decay_pos: float = 0.10,
        kappa_decay_neg: float = 0.05,
        gile_weights: Tuple[float, float, float, float] = (0.20, 0.25, 0.25, 0.30)
    ):
        self.lookback_short = lookback_short
        self.lookback_long = lookback_long
        self.kappa_decay_pos = kappa_decay_pos
        self.kappa_decay_neg = kappa_decay_neg
        self.gile_weights = gile_weights
        
        # Valence weights from TI PD theory
        self.W_GREAT = 1.0
        self.W_TERRIBLE = 2.0
        self.W_EXCEPTIONAL = 1.5
        self.W_WICKED = 6.0
        
        # Regime adjustment factors
        self.regime_adj = {
            MarketRegime.EXPANSION: 1.0,
            MarketRegime.COMPRESSION: 0.5,
            MarketRegime.FRACTURE: 0.0,
            MarketRegime.RESET: 0.3
        }
        
        # History for regime detection
        self.constraint_history: List[float] = []
        self.pd_history: List[float] = []
    
    def compute_xi_metrics(self, returns: np.ndarray, prices: np.ndarray) -> XiMetrics:
        """
        Compute full Ξ(E) = A(t) · κ(t,τ) · C(t) decomposition
        
        Args:
            returns: Array of percentage returns (oldest to newest)
            prices: Array of prices (oldest to newest)
        
        Returns:
            XiMetrics dataclass with all components
        """
        if len(returns) < 10 or len(prices) < 10:
            return XiMetrics(0, 0.5, 0, 0, 0, 0)
        
        A = self._amplitude(returns[-self.lookback_short:])
        kappa = self._memory_kernel(returns[-self.lookback_long:])
        C = self._constraint(prices, returns)
        
        xi_unsigned = A * kappa * C
        
        curr_ret = float(returns[-1])
        valence = 1.0 if curr_ret >= 0 else -1.0
        W = self._valence_weight(curr_ret)
        
        xi_signed = valence * xi_unsigned * W
        
        pd = np.sign(xi_signed) * np.log1p(abs(xi_signed))
        pd = float(np.clip(pd, -3.0, 2.0))
        
        return XiMetrics(
            amplitude=float(A),
            memory_kernel=float(kappa),
            constraint=float(C),
            xi_unsigned=float(xi_unsigned),
            xi_signed=float(xi_signed),
            pd=float(pd)
        )
    
    def _amplitude(self, rets: np.ndarray) -> float:
        """A(t) - Current move normalized by volatility"""
        if len(rets) < 2:
            return 0.0
        current = abs(rets[-1])
        vol = max(float(np.std(rets)), 0.01)
        return float(np.clip(current / vol, 0.0, 10.0))
    
    def _memory_kernel(self, rets: np.ndarray) -> float:
        """κ(t,τ) - Negative memory dominance fraction [0,1]"""
        if len(rets) < 3:
            return 0.5
        
        kpos, kneg = 0.0, 0.0
        for i in range(len(rets)):
            r = float(rets[-1 - i])
            if r >= 0:
                kpos += abs(r) * np.exp(-self.kappa_decay_pos * i)
            else:
                kneg += abs(r) * np.exp(-self.kappa_decay_neg * i)
        
        total = kpos + kneg
        if total <= 0:
            return 0.5
        return float(np.clip(kneg / total, 0.0, 1.0))
    
    def _constraint(self, prices: np.ndarray, rets: np.ndarray) -> float:
        """C(t) - Combined drawdown + volatility constraint [0,1]"""
        if len(prices) < 5 or len(rets) < 5:
            return 0.0
        
        peak = float(np.max(prices))
        dd = (peak - float(prices[-1])) / peak if peak > 0 else 0.0
        
        rs = rets[-min(len(rets), self.lookback_short):]
        rl = rets[-min(len(rets), self.lookback_long):]
        v_recent = float(np.std(rs)) if len(rs) >= 2 else 1.0
        v_long = float(np.std(rl)) if len(rl) >= 2 else 1.0
        
        ratio = v_recent / max(v_long, 0.01)
        vol_constraint = 1.0 - min(ratio, 1.0)
        
        return float(np.clip(0.6 * dd + 0.4 * vol_constraint, 0.0, 1.0))
    
    def _valence_weight(self, ret_pct: float) -> float:
        """PD valence weighting from TI framework"""
        if ret_pct > 5.0:
            return self.W_EXCEPTIONAL
        if ret_pct > 0.333:
            return self.W_GREAT
        if ret_pct > -0.666:
            return 1.0
        if ret_pct > -5.0:
            return self.W_TERRIBLE
        return self.W_WICKED
    
    def compute_gile(
        self,
        returns: np.ndarray,
        prices: np.ndarray,
        market_returns: Optional[np.ndarray] = None
    ) -> GILEScore:
        """
        Compute GILE score for a security
        
        G - Goodness: Risk-adjusted return quality
        I - Intuition: Trend alignment (MA crossover proxy)
        L - Love: Correlation with market
        E - Environment: Momentum alignment
        """
        if len(returns) < 30 or len(prices) < 30:
            return GILEScore(0.5, 0.5, 0.5, 0.5, 0.5)
        
        r20 = returns[-20:]
        mean_ret = float(np.mean(r20))
        std_ret = max(float(np.std(r20)), 0.01)
        goodness = 1.0 / (1.0 + np.exp(-mean_ret / std_ret))
        
        ma5 = float(np.mean(prices[-5:]))
        ma15 = float(np.mean(prices[-15:]))
        intuition = 1.0 / (1.0 + np.exp(-((ma5 - ma15) / max(ma15, 0.01)) * 50.0))
        
        love = 0.5
        if market_returns is not None and len(market_returns) >= 20:
            a = returns[-20:]
            b = market_returns[-20:]
            try:
                corr = float(np.corrcoef(a, b)[0, 1])
                if not np.isnan(corr):
                    love = (corr + 1.0) / 2.0
            except:
                love = 0.5
        
        m10 = float(np.sum(returns[-10:]))
        m30 = float(np.sum(returns[-30:]))
        env = 1.0 / (1.0 + np.exp(-(m10 * m30) * 0.01))
        
        w_g, w_i, w_l, w_e = self.gile_weights
        composite = w_g * goodness + w_i * intuition + w_l * love + w_e * env
        
        return GILEScore(
            goodness=float(goodness),
            intuition=float(intuition),
            love=float(love),
            environment=float(env),
            composite=float(np.clip(composite, 0.0, 1.0))
        )
    
    def classify_regime(
        self,
        pd: float,
        constraint: float,
        vol_ratio: float
    ) -> Tuple[MarketRegime, float, float]:
        """
        Classify market regime based on Ξ metrics
        
        Returns: (regime, confidence, constraint_rate)
        """
        self.constraint_history.append(float(constraint))
        self.pd_history.append(float(pd))
        
        self.constraint_history = self.constraint_history[-self.lookback_long:]
        self.pd_history = self.pd_history[-self.lookback_long:]
        
        constraint_rate = 0.0
        if len(self.constraint_history) >= 10:
            recent_c = float(np.mean(self.constraint_history[-5:]))
            older_c = float(np.mean(self.constraint_history[-10:-5]))
            constraint_rate = recent_c - older_c
        
        regime = MarketRegime.EXPANSION
        confidence = 0.55
        
        if constraint_rate > 0.10 and vol_ratio > 1.5 and pd < -1.0:
            regime = MarketRegime.FRACTURE
            confidence = min(0.90, 0.50 + abs(constraint_rate) + abs(pd) / 3.0)
        
        elif constraint_rate > 0.05 and vol_ratio < 0.7:
            regime = MarketRegime.COMPRESSION
            confidence = min(0.85, 0.50 + constraint_rate * 2.0 + (1.0 - vol_ratio))
        
        elif constraint_rate < -0.05 and vol_ratio > 1.0:
            regime = MarketRegime.RESET
            confidence = min(0.80, 0.50 + abs(constraint_rate) + (vol_ratio - 1.0) * 0.5)
        
        else:
            confidence = max(0.40, 0.70 - abs(constraint_rate) * 2.0)
        
        return regime, float(confidence), float(constraint_rate)
    
    def generate_signal(
        self,
        xi_metrics: XiMetrics,
        gile: GILEScore,
        regime: MarketRegime,
        regime_confidence: float
    ) -> Signal:
        """
        Generate trading signal from Ξ metrics, GILE score, and regime
        """
        reasons = []
        
        if gile.composite > 0.65:
            base, conf = "strong_buy", 0.80
            reasons.append(f"GILE {gile.composite:.2f} > 0.65")
        elif gile.composite > 0.55:
            base, conf = "buy", 0.60
            reasons.append(f"GILE {gile.composite:.2f} > 0.55")
        elif gile.composite > 0.45:
            base, conf = "hold", 0.50
        elif gile.composite > 0.35:
            base, conf = "sell", 0.60
            reasons.append(f"GILE {gile.composite:.2f} < 0.45")
        else:
            base, conf = "strong_sell", 0.80
            reasons.append(f"GILE {gile.composite:.2f} < 0.35")
        
        if regime == MarketRegime.FRACTURE:
            return Signal(
                action="strong_sell",
                confidence=min(0.95, max(0.70, regime_confidence)),
                gile=gile.composite,
                xi_metrics=xi_metrics,
                regime=regime,
                reasons=["FRACTURE REGIME - Exit all positions"]
            )
        
        if regime == MarketRegime.COMPRESSION:
            if base in ["buy", "strong_buy"]:
                base = "hold"
                reasons.append("Compression gate - holding")
            conf *= 0.70
        
        elif regime == MarketRegime.RESET:
            conf *= 0.60
            reasons.append("Reset regime - reduced confidence")
        
        elif regime == MarketRegime.EXPANSION and xi_metrics.pd > 0.5:
            conf = min(conf * 1.20, 0.90)
            reasons.append("Expansion + positive PD boost")
        
        if xi_metrics.xi_signed < -2.0:
            base, conf = "strong_sell", max(conf, 0.70)
            reasons.append(f"Ξ override: {xi_metrics.xi_signed:.2f} < -2.0")
        
        if xi_metrics.memory_kernel > 0.70 and base in ["buy", "strong_buy"]:
            base = "hold"
            reasons.append(f"κ negative dominance: {xi_metrics.memory_kernel:.2f}")
        
        return Signal(
            action=base,
            confidence=float(np.clip(conf, 0.0, 1.0)),
            gile=gile.composite,
            xi_metrics=xi_metrics,
            regime=regime,
            reasons=reasons
        )
    
    def rank_candidates(
        self,
        candidates: List[Tuple[str, Signal]]
    ) -> List[Tuple[str, Signal, float]]:
        """
        Rank candidates by composite score
        
        Returns: List of (symbol, signal, score) sorted by score descending
        """
        scored = []
        for symbol, signal in candidates:
            score = (
                (signal.gile - 0.5) +
                0.25 * signal.xi_metrics.pd +
                0.10 * np.tanh(signal.xi_metrics.xi_signed)
            )
            scored.append((symbol, signal, float(score)))
        
        scored.sort(key=lambda x: x[2], reverse=True)
        return scored
    
    def calculate_position_size(
        self,
        signal: Signal,
        regime: MarketRegime,
        max_position: float = 0.15,
        num_positions: int = 4
    ) -> float:
        """Calculate position size based on signal and regime"""
        regime_scale = self.regime_adj.get(regime, 1.0)
        base_weight = min(max_position, 1.0 / num_positions) * regime_scale
        weight = base_weight * signal.confidence
        return float(np.clip(weight, 0.0, max_position))

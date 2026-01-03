"""
GSA QUANTCONNECT BRIDGE - Adapts GSA Core for QuantConnect deployment
Copy this file content into QuantConnect's main.py

This bridges the platform-agnostic GSA Core to QuantConnect's API
"""

from AlgorithmImports import *
import numpy as np
from typing import Dict, List, Tuple
from enum import Enum
from dataclasses import dataclass


class MarketRegime(Enum):
    EXPANSION = "expansion"
    COMPRESSION = "compression"
    FRACTURE = "fracture"
    RESET = "reset"


@dataclass
class XiMetrics:
    amplitude: float
    memory_kernel: float
    constraint: float
    xi_unsigned: float
    xi_signed: float
    pd: float


@dataclass
class GILEScore:
    goodness: float
    intuition: float
    love: float
    environment: float
    composite: float


class GSACoreEmbedded:
    """
    GSA Core Engine embedded for QuantConnect
    (Inlined to avoid import issues on QC platform)
    """
    
    def __init__(
        self,
        lookback_short: int = 7,
        lookback_long: int = 60,
        kappa_decay_pos: float = 0.10,
        kappa_decay_neg: float = 0.05
    ):
        self.lookback_short = lookback_short
        self.lookback_long = lookback_long
        self.kappa_decay_pos = kappa_decay_pos
        self.kappa_decay_neg = kappa_decay_neg
        
        self.W_GREAT = 1.0
        self.W_TERRIBLE = 2.0
        self.W_EXCEPTIONAL = 1.5
        self.W_WICKED = 6.0
        
        self.constraint_history: List[float] = []
        self.pd_history: List[float] = []
    
    def compute_xi_metrics(self, returns: np.ndarray, prices: np.ndarray) -> XiMetrics:
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
        
        return XiMetrics(float(A), float(kappa), float(C), float(xi_unsigned), float(xi_signed), float(pd))
    
    def _amplitude(self, rets: np.ndarray) -> float:
        if len(rets) < 2:
            return 0.0
        current = abs(rets[-1])
        vol = max(float(np.std(rets)), 0.01)
        return float(np.clip(current / vol, 0.0, 10.0))
    
    def _memory_kernel(self, rets: np.ndarray) -> float:
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
        if ret_pct > 5.0:
            return self.W_EXCEPTIONAL
        if ret_pct > 0.333:
            return self.W_GREAT
        if ret_pct > -0.666:
            return 1.0
        if ret_pct > -5.0:
            return self.W_TERRIBLE
        return self.W_WICKED
    
    def compute_gile(self, returns: np.ndarray, prices: np.ndarray, market_returns: np.ndarray = None) -> GILEScore:
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
            try:
                corr = float(np.corrcoef(returns[-20:], market_returns[-20:])[0, 1])
                if not np.isnan(corr):
                    love = (corr + 1.0) / 2.0
            except:
                love = 0.5
        
        m10 = float(np.sum(returns[-10:]))
        m30 = float(np.sum(returns[-30:]))
        env = 1.0 / (1.0 + np.exp(-(m10 * m30) * 0.01))
        
        composite = 0.20 * goodness + 0.25 * intuition + 0.25 * love + 0.30 * env
        return GILEScore(float(goodness), float(intuition), float(love), float(env), float(np.clip(composite, 0, 1)))
    
    def classify_regime(self, pd: float, constraint: float, vol_ratio: float) -> Tuple[MarketRegime, float, float]:
        self.constraint_history.append(float(constraint))
        self.pd_history.append(float(pd))
        self.constraint_history = self.constraint_history[-60:]
        self.pd_history = self.pd_history[-60:]
        
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


class GrandStockAlgorithmQC(QCAlgorithm):
    """
    GRAND STOCK ALGORITHM (GSA) - QuantConnect Deployable
    
    TI Framework: Ξ(E) = A(t) · κ(t,τ) · C(t) -> PD -> GILE -> Signal
    Regimes: Expansion / Compression / Fracture / Reset
    """
    
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 1)
        self.SetCash(100000)
        
        self.spy = self.AddEquity("SPY", Resolution.Daily).Symbol
        tickers = ["AAPL", "MSFT", "GOOGL", "NVDA", "TSLA", "META", "AMZN"]
        self.symbols = [self.AddEquity(t, Resolution.Daily).Symbol for t in tickers]
        
        self.lookback_short = 7
        self.lookback_long = 60
        self.max_position = 0.15
        self.top_n = 4
        
        self.core = GSACoreEmbedded(
            lookback_short=self.lookback_short,
            lookback_long=self.lookback_long
        )
        
        self.regime_adj = {
            MarketRegime.EXPANSION: 1.0,
            MarketRegime.COMPRESSION: 0.5,
            MarketRegime.FRACTURE: 0.0,
            MarketRegime.RESET: 0.3
        }
        
        self.prices = {}
        self.returns = {}
        for s in [self.spy] + self.symbols:
            self.prices[s] = RollingWindow[float](self.lookback_long + 5)
            self.returns[s] = RollingWindow[float](self.lookback_long + 5)
        
        hist = self.History([self.spy] + self.symbols, self.lookback_long + 10, Resolution.Daily)
        if not hist.empty:
            for s in [self.spy] + self.symbols:
                if s in hist.index.levels[0]:
                    closes = hist.loc[s]["close"].values
                    for c in closes:
                        self._push_price_return(s, float(c))
        
        self.SetWarmUp(self.lookback_long + 5)
        
        self.SetSecurityInitializer(
            lambda sec: sec.SetSlippageModel(VolumeShareSlippageModel(0.01, 0.10))
        )
        
        self.Schedule.On(
            self.DateRules.EveryDay(self.spy),
            self.TimeRules.AfterMarketOpen(self.spy, 30),
            self.Rebalance
        )
        
        self.trade_count = 0
    
    def _push_price_return(self, symbol, price: float):
        if price <= 0:
            return
        if self.prices[symbol].Count > 0:
            prev = float(self.prices[symbol][0])
            if prev > 0:
                r = (price / prev - 1.0) * 100.0
                self.returns[symbol].Add(float(r))
        self.prices[symbol].Add(float(price))
    
    def _get_arrays(self, symbol, n: int) -> Tuple[np.ndarray, np.ndarray]:
        m = min(self.returns[symbol].Count, n)
        if m <= 0:
            return np.array([]), np.array([])
        
        rets = np.array([float(self.returns[symbol][i]) for i in range(m)][::-1])
        prices = np.array([float(self.prices[symbol][i]) for i in range(min(self.prices[symbol].Count, n))][::-1])
        return rets, prices
    
    def _get_vol_ratio(self, symbol) -> float:
        rets, _ = self._get_arrays(symbol, 60)
        if len(rets) < 30:
            return 1.0
        recent = float(np.std(rets[-10:])) if len(rets) >= 10 else 1.0
        long_v = float(np.std(rets[-30:])) if len(rets) >= 30 else 1.0
        return recent / max(long_v, 0.01)
    
    def OnData(self, data: Slice):
        for s in [self.spy] + self.symbols:
            bar = data.Bars.get(s)
            if bar:
                self._push_price_return(s, float(bar.Close))
    
    def Rebalance(self):
        if self.IsWarmingUp:
            return
        
        market_rets, market_prices = self._get_arrays(self.spy, self.lookback_long)
        if len(market_rets) < 30:
            return
        
        market_xi = self.core.compute_xi_metrics(market_rets, market_prices)
        vol_ratio = self._get_vol_ratio(self.spy)
        regime, regime_conf, c_rate = self.core.classify_regime(market_xi.pd, market_xi.constraint, vol_ratio)
        
        if regime == MarketRegime.FRACTURE:
            for s in self.symbols:
                if self.Portfolio[s].Invested:
                    self.Liquidate(s, "FRACTURE")
            self.Debug(f"[FRACTURE] conf={regime_conf:.2f} pd={market_xi.pd:.2f}")
            return
        
        candidates = []
        for s in self.symbols:
            rets, prices = self._get_arrays(s, self.lookback_long)
            if len(rets) < 30:
                continue
            
            xi = self.core.compute_xi_metrics(rets, prices)
            gile = self.core.compute_gile(rets, prices, market_rets)
            
            action, conf = self._decide(gile.composite, xi, regime)
            score = (gile.composite - 0.5) + 0.25 * xi.pd + 0.10 * np.tanh(xi.xi_signed)
            
            candidates.append((s, action, conf, gile.composite, score, xi))
        
        candidates.sort(key=lambda x: x[4], reverse=True)
        picks = [(c[0], c[1], c[2], c[3], c[5]) for c in candidates if c[1] in ["buy", "strong_buy"]][:self.top_n]
        
        pick_syms = set([p[0] for p in picks])
        for s in self.symbols:
            if self.Portfolio[s].Invested and s not in pick_syms:
                self.Liquidate(s, "Not in picks")
        
        if not picks:
            return
        
        regime_scale = self.regime_adj.get(regime, 1.0)
        base_w = min(self.max_position, 1.0 / len(picks)) * regime_scale
        
        for s, action, conf, gile, xi in picks:
            w = float(np.clip(base_w * conf, 0.0, self.max_position))
            self.SetHoldings(s, w)
            self.trade_count += 1
        
        self.Debug(f"[{regime.value.upper()}] picks={[self.Securities[p[0]].Symbol.Value for p in picks]}")
    
    def _decide(self, gile: float, xi: XiMetrics, regime: MarketRegime) -> Tuple[str, float]:
        if gile > 0.65:
            base, conf = "strong_buy", 0.80
        elif gile > 0.55:
            base, conf = "buy", 0.60
        elif gile > 0.45:
            base, conf = "hold", 0.50
        elif gile > 0.35:
            base, conf = "sell", 0.60
        else:
            base, conf = "strong_sell", 0.80
        
        if regime == MarketRegime.COMPRESSION:
            if base in ["buy", "strong_buy"]:
                base = "hold"
            conf *= 0.70
        elif regime == MarketRegime.RESET:
            conf *= 0.60
        
        if xi.xi_signed < -2.0:
            base, conf = "strong_sell", max(conf, 0.70)
        
        if xi.memory_kernel > 0.70 and base in ["buy", "strong_buy"]:
            base = "hold"
        
        return base, float(np.clip(conf, 0, 1))
    
    def OnEndOfAlgorithm(self):
        self.Log(f"GSA done. Trades={self.trade_count}. Final=${self.Portfolio.TotalPortfolioValue:,.2f}")

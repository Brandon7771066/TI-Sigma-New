# region imports
from AlgorithmImports import *
import numpy as np
from enum import Enum
from collections import deque
# endregion

class MarketRegime(Enum):
    EXPANSION = "expansion"
    COMPRESSION = "compression"
    FRACTURE = "fracture"
    RESET = "reset"

class GrandStockAlgorithm(QCAlgorithm):
    """
    GRAND STOCK ALGORITHM (GSA) - TI Framework for QuantConnect
    Ξ Metrics: Amplitude (A), Memory Kernel (κ), Constraint (C)
    Regime Classification: Expansion/Compression/Fracture/Reset
    Author: Brandon Charles Emerick | Date: December 14, 2025
    """

    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 1)
        self.SetCash(100000)
        
        self.tickers = ["AAPL", "MSFT", "GOOGL", "NVDA", "TSLA", "META", "AMZN"]
        self.symbols = {}
        for ticker in self.tickers:
            self.symbols[ticker] = self.AddEquity(ticker, Resolution.Daily).Symbol
        
        self.market_symbol = self.AddEquity("SPY", Resolution.Daily).Symbol
        
        self.lookback_short = 7
        self.lookback_long = 30
        self.lookback_regime = 60
        self.max_position_size = 0.15
        
        self.kappa_decay_positive = 0.1
        self.kappa_decay_negative = 0.05
        self.W_GREAT, self.W_TERRIBLE = 1.0, 2.0
        self.W_EXCEPTIONAL, self.W_WICKED = 1.5, 6.0
        
        self.constraint_history = {t: deque(maxlen=self.lookback_regime) for t in self.tickers}
        self.pd_history = {t: deque(maxlen=self.lookback_regime) for t in self.tickers}
        
        self.regime_adjustments = {
            MarketRegime.EXPANSION: 1.0,
            MarketRegime.COMPRESSION: 0.5,
            MarketRegime.FRACTURE: 0.0,
            MarketRegime.RESET: 0.3
        }
        
        self.Schedule.On(
            self.DateRules.EveryDay("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.Rebalance
        )

    def Rebalance(self):
        history = self.History(list(self.symbols.values()) + [self.market_symbol], self.lookback_long + 30, Resolution.Daily)
        if history.empty:
            return
        
        market_history = None
        if self.market_symbol in history.index.get_level_values(0):
            market_history = history.loc[self.market_symbol]
        
        signals = {}
        for ticker, symbol in self.symbols.items():
            if symbol not in history.index.get_level_values(0):
                continue
            
            df = history.loc[symbol]
            if len(df) < 30:
                continue
            
            closes = df['close'].values
            returns = np.diff(closes) / closes[:-1] * 100
            
            xi_metrics = self.ComputeXi(closes, returns, ticker)
            regime = self.ClassifyRegime(xi_metrics, returns, ticker)
            gile = self.CalculateGILE(closes, returns, market_history)
            
            signal, confidence = self.GenerateSignal(xi_metrics, regime, gile, returns)
            signals[ticker] = {
                'signal': signal,
                'confidence': confidence,
                'regime': regime,
                'gile': gile
            }
        
        for ticker, sig in signals.items():
            symbol = self.symbols[ticker]
            target = 0.0
            
            if sig['signal'] == 'strong_buy':
                target = self.max_position_size * 1.2
            elif sig['signal'] == 'buy':
                target = self.max_position_size * 0.8
            elif sig['signal'] == 'hold':
                if self.Portfolio[symbol].Invested:
                    target = self.Portfolio[symbol].HoldingsValue / self.Portfolio.TotalPortfolioValue
                else:
                    target = 0.0
            elif sig['signal'] in ['sell', 'strong_sell']:
                target = 0.0
            
            target *= self.regime_adjustments.get(sig['regime'], 1.0) * sig['confidence']
            target = min(target, self.max_position_size * 1.5)
            
            current = 0.0
            if self.Portfolio[symbol].Invested:
                current = self.Portfolio[symbol].HoldingsValue / self.Portfolio.TotalPortfolioValue
            
            if abs(target - current) > 0.02:
                self.SetHoldings(symbol, target)

    def ComputeXi(self, prices, returns, ticker):
        if len(returns) < 5:
            return {'amplitude': 0, 'memory_kernel': 0.5, 'constraint': 0, 'xi_signed': 0, 'pd_score': 0}
        
        A = self.CalculateAmplitude(returns[-self.lookback_short:])
        kappa = self.CalculateMemoryKernel(returns[-self.lookback_long:])
        C = self.CalculateConstraint(prices[-self.lookback_long:], returns[-self.lookback_long:])
        
        xi_unsigned = A * kappa * C
        current_return = returns[-1] if len(returns) > 0 else 0
        valence = 1 if current_return >= 0 else -1
        valence_weight = self.CalculateValenceWeight(current_return)
        xi_signed = valence * xi_unsigned * valence_weight
        
        pd_score = float(np.clip(np.sign(xi_signed) * np.log1p(abs(xi_signed)), -3, 2))
        
        return {
            'amplitude': A,
            'memory_kernel': kappa,
            'constraint': C,
            'xi_signed': xi_signed,
            'pd_score': pd_score
        }

    def CalculateAmplitude(self, returns):
        if len(returns) < 2:
            return 0.0
        current_return = abs(returns[-1]) if len(returns) > 0 else 0
        volatility = max(np.std(returns), 0.01)
        return float(np.clip(current_return / volatility, 0, 10))

    def CalculateMemoryKernel(self, returns):
        if len(returns) < 3:
            return 0.5
        pos_rets = returns[returns > 0]
        neg_rets = returns[returns < 0]
        kappa_pos = sum(abs(r) * np.exp(-self.kappa_decay_positive * i) for i, r in enumerate(pos_rets))
        kappa_neg = sum(abs(r) * np.exp(-self.kappa_decay_negative * i) for i, r in enumerate(neg_rets))
        total = kappa_pos + kappa_neg
        return float(np.clip(kappa_neg / total, 0, 1)) if total > 0 else 0.5

    def CalculateConstraint(self, prices, returns):
        if len(prices) < 5:
            return 0.0
        peak = np.max(prices)
        drawdown = (peak - prices[-1]) / peak if peak > 0 else 0
        recent_vol = np.std(returns[-self.lookback_short:]) if len(returns) >= self.lookback_short else 1.0
        long_vol = np.std(returns) if len(returns) > 1 else 1.0
        vol_constraint = 1 - min(recent_vol / max(long_vol, 0.01), 1)
        return float(np.clip(0.6 * drawdown + 0.4 * vol_constraint, 0, 1))

    def CalculateValenceWeight(self, return_pct):
        if return_pct > 5.0:
            return self.W_EXCEPTIONAL
        elif return_pct > 0.333:
            return self.W_GREAT
        elif return_pct > -0.666:
            return 1.0
        elif return_pct > -5.0:
            return self.W_TERRIBLE
        else:
            return self.W_WICKED

    def ClassifyRegime(self, xi_metrics, returns, ticker):
        if len(returns) < 10:
            return MarketRegime.EXPANSION
        
        self.constraint_history[ticker].append(xi_metrics['constraint'])
        self.pd_history[ticker].append(xi_metrics['pd_score'])
        
        constraint_list = list(self.constraint_history[ticker])
        constraint_rate = 0.0
        if len(constraint_list) >= 5:
            recent_c = np.mean(constraint_list[-5:])
            older_c = np.mean(constraint_list[-10:-5]) if len(constraint_list) >= 10 else recent_c
            constraint_rate = recent_c - older_c
        
        recent_vol = np.std(returns[-10:]) if len(returns) >= 10 else 1.0
        long_vol = np.std(returns[-30:]) if len(returns) >= 30 else 1.0
        vol_ratio = recent_vol / max(long_vol, 0.01)
        
        if constraint_rate > 0.1 and recent_vol > long_vol * 1.5 and xi_metrics['pd_score'] < -1:
            return MarketRegime.FRACTURE
        elif constraint_rate > 0.05 and vol_ratio < 0.7:
            return MarketRegime.COMPRESSION
        elif constraint_rate < -0.05 and recent_vol > long_vol:
            return MarketRegime.RESET
        else:
            return MarketRegime.EXPANSION

    def CalculateGILE(self, prices, returns, market_history):
        if len(returns) < 20:
            return 0.5
        
        mean_ret = np.mean(returns[-20:])
        std_ret = np.std(returns[-20:])
        g_score = 1 / (1 + np.exp(-mean_ret / max(std_ret, 0.01)))
        
        short_ma = np.mean(prices[-5:])
        long_ma = np.mean(prices[-15:])
        i_score = 1 / (1 + np.exp(-(short_ma - long_ma) / max(long_ma, 0.01) * 50))
        
        l_score = 0.5
        if market_history is not None and len(market_history) >= 20:
            market_closes = market_history['close'].values
            market_returns = np.diff(market_closes) / market_closes[:-1] * 100
            if len(market_returns) >= 20:
                try:
                    corr = np.corrcoef(market_returns[-20:], returns[-20:])[0, 1]
                    l_score = (corr + 1) / 2
                except:
                    pass
        
        m30 = np.sum(returns[-30:]) if len(returns) >= 30 else 0
        m10 = np.sum(returns[-10:])
        e_score = 1 / (1 + np.exp(-(m10 * m30) * 0.01))
        
        w_g, w_i, w_l, w_e = 0.20, 0.25, 0.25, 0.30
        return float(np.clip(w_g * g_score + w_i * i_score + w_l * l_score + w_e * e_score, 0, 1))

    def GenerateSignal(self, xi, regime, gile, returns):
        if regime == MarketRegime.FRACTURE:
            return 'strong_sell', 0.9
        
        if gile > 0.65:
            base_signal, base_conf = 'strong_buy', 0.8
        elif gile > 0.55:
            base_signal, base_conf = 'buy', 0.6
        elif gile > 0.45:
            base_signal, base_conf = 'hold', 0.5
        elif gile > 0.35:
            base_signal, base_conf = 'sell', 0.6
        else:
            base_signal, base_conf = 'strong_sell', 0.8
        
        if regime == MarketRegime.COMPRESSION:
            if base_signal in ['buy', 'strong_buy']:
                base_signal = 'hold'
            base_conf *= 0.7
        elif regime == MarketRegime.RESET:
            base_conf *= 0.6
        elif regime == MarketRegime.EXPANSION and xi['pd_score'] > 0.5:
            base_conf = min(base_conf * 1.2, 0.9)
        
        if xi['xi_signed'] < -2.0:
            base_signal, base_conf = 'strong_sell', max(base_conf, 0.7)
        
        if xi['memory_kernel'] > 0.7:
            if base_signal in ['buy', 'strong_buy']:
                base_signal = 'hold'
        
        return base_signal, base_conf

    def OnData(self, data):
        pass

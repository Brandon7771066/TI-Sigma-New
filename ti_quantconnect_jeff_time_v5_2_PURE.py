"""
TI FRAMEWORK V5.2: PURE V3/V7 CLONE WITH TI NAMING ONLY
========================================================
This is EXACTLY V7's code with only variable names changed.
NO logic changes. Just τ_I instead of t1_quantum, etc.

V3 BASELINE: 277.76%
EXPECTED: Should match V3/V7 exactly

COPY EVERYTHING BELOW FOR QUANTCONNECT:
"""

from AlgorithmImports import *
import numpy as np

class TIJeffTime3DV52PureAlgorithm(QCAlgorithm):
    """
    TI Framework V5.2: Pure V3/V7 clone with TI naming
    
    τ_I = t1_quantum (SAME LOGIC)
    τ_J = t2_interaction (SAME LOGIC)  
    τ_C = t3_cosmological (SAME LOGIC)
    L = love_correlation (SAME LOGIC)
    """
    
    SACRED_MIN = -0.666
    SACRED_MAX = 0.333
    GREAT_THRESHOLD = 5.0
    TERRIBLE_THRESHOLD = -5.0
    ULTRA_GREAT_THRESHOLD = 20.0
    ULTRA_TERRIBLE_THRESHOLD = -10.0
    GILE_GREAT = 1.5
    GILE_GOOD = 0.3
    GILE_BAD = -0.3
    GILE_TERRIBLE = -1.5
    TAU_I_LOOKBACK = 3
    TAU_C_SHORT = 20
    TAU_C_LONG = 50
    
    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        
        self.symbols = [
            self.add_equity("SPY", Resolution.DAILY).symbol,
            self.add_equity("QQQ", Resolution.DAILY).symbol,
            self.add_equity("AAPL", Resolution.DAILY).symbol,
            self.add_equity("MSFT", Resolution.DAILY).symbol,
            self.add_equity("GOOGL", Resolution.DAILY).symbol,
            self.add_equity("TSLA", Resolution.DAILY).symbol,
            self.add_equity("NVDA", Resolution.DAILY).symbol,
            self.add_equity("AMD", Resolution.DAILY).symbol,
            self.add_equity("META", Resolution.DAILY).symbol,
            self.add_equity("AMZN", Resolution.DAILY).symbol,
        ]
        
        self.price_history = {symbol: [] for symbol in self.symbols}
        self.gile_history = {symbol: [] for symbol in self.symbols}
        self.temporal_scores = {symbol: {} for symbol in self.symbols}
        self.dimension_efficacy = {symbol: {'tau_i': [], 'tau_j': [], 'tau_c': [], 'love': []} for symbol in self.symbols}
        self.max_history = 60
        self.max_position = 0.12
        self.efficacy_window = 10
        self.BASE_WEIGHTS = {'tau_i': 0.25, 'tau_j': 0.35, 'tau_c': 0.25, 'love': 0.15}
        
        self.set_warmup(60, Resolution.DAILY)
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.after_market_open("SPY", 30),
            self.ti_temporal_rebalance
        )
        self.trade_count = 0
        self.winning_trades = 0
    
    def price_to_gile(self, pct_change):
        if pct_change > self.ULTRA_GREAT_THRESHOLD:
            excess = pct_change - self.ULTRA_GREAT_THRESHOLD
            return float(2.0 + np.log1p(excess / 20) * 0.5)
        elif pct_change < self.ULTRA_TERRIBLE_THRESHOLD:
            excess = abs(pct_change) - abs(self.ULTRA_TERRIBLE_THRESHOLD)
            return float(-3.0 - np.log1p(excess / 10) * 0.5)
        elif pct_change > self.GREAT_THRESHOLD:
            return float(1.5 + (pct_change - 5) / (20 - 5) * 0.5)
        elif pct_change < self.TERRIBLE_THRESHOLD:
            return float(-3.0 + (pct_change + 10) / (10 - 5) * 1.5)
        elif pct_change > self.SACRED_MAX:
            return float(0.3 + (pct_change - 0.333) / (5 - 0.333) * 1.2)
        elif pct_change < self.SACRED_MIN:
            return float(-1.5 + (pct_change + 5) / (5 - 0.666) * 1.2)
        else:
            if pct_change < 0:
                return float((pct_change / 0.666) * 0.3)
            else:
                return float((pct_change / 0.333) * 0.3)
    
    def calculate_tau_i(self, symbol):
        """τ_I (I-Cell Time) = V7's t1_quantum - EXACT SAME"""
        history = self.price_history.get(symbol, [])
        if len(history) < self.TAU_I_LOOKBACK:
            return 0.0
        recent = history[-self.TAU_I_LOOKBACK:]
        momentum = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] != 0 else 0
        returns = np.diff(recent) / recent[:-1] * 100
        volatility = float(np.std(returns)) if len(returns) > 1 else 0
        tau_i_score = self.price_to_gile(momentum) * (1 + volatility * 0.1)
        return float(np.clip(tau_i_score, -3, 3))
    
    def calculate_tau_j(self, symbol):
        """τ_J (Jeff Moment) = V7's t2_interaction - EXACT SAME"""
        history = self.price_history.get(symbol, [])
        if len(history) < 2:
            return 0.0
        today_change = (history[-1] - history[-2]) / history[-2] * 100 if history[-2] != 0 else 0
        tau_j_score = self.price_to_gile(today_change)
        return float(tau_j_score)
    
    def calculate_tau_c(self, symbol):
        """τ_C (CCC Time) = V7's t3_cosmological - EXACT SAME"""
        history = self.price_history.get(symbol, [])
        if len(history) < self.TAU_C_LONG:
            return 0.0
        sma_short = float(np.mean(history[-self.TAU_C_SHORT:]))
        sma_long = float(np.mean(history[-self.TAU_C_LONG:]))
        current = history[-1]
        trend_divergence = (sma_short - sma_long) / sma_long * 100 if sma_long != 0 else 0
        price_position = (current - sma_long) / sma_long * 100 if sma_long != 0 else 0
        cosmo_pct = (trend_divergence + price_position) / 2
        tau_c_score = self.price_to_gile(cosmo_pct)
        return float(tau_c_score)
    
    def calculate_love(self, symbol):
        """Love = V7's love_correlation - EXACT SAME"""
        if len(self.price_history.get(symbol, [])) < 21:
            return 0.0
        sym_history = self.price_history[symbol][-21:]
        sym_returns = np.diff(sym_history) / sym_history[:-1] * 100
        spy_history = self.price_history.get(self.symbols[0], [])
        if len(spy_history) < 21:
            return 0.0
        spy_prices = spy_history[-21:]
        spy_returns = np.diff(spy_prices) / spy_prices[:-1] * 100
        if len(sym_returns) != len(spy_returns):
            min_len = min(len(sym_returns), len(spy_returns))
            sym_returns = sym_returns[-min_len:]
            spy_returns = spy_returns[-min_len:]
        if len(sym_returns) != len(spy_returns) or len(sym_returns) < 10:
            return 0.0
        try:
            corr_matrix = np.corrcoef(sym_returns, spy_returns)
            correlation = float(corr_matrix[0, 1]) if not np.isnan(corr_matrix[0, 1]) else 0.0
        except:
            correlation = 0.0
        spy_trend = float(np.mean(spy_returns)) if len(spy_returns) > 0 else 0
        if spy_trend > 0:
            love_score = correlation * abs(spy_trend) * 0.5
        else:
            love_score = (1 - abs(correlation)) * abs(spy_trend) * 0.5
        return float(np.clip(love_score, -1.5, 1.5))
    
    def update_dimension_efficacy(self, symbol, dimension, signal_value, actual_outcome):
        """V7's efficacy tracking - EXACT SAME"""
        if dimension not in self.dimension_efficacy[symbol]:
            self.dimension_efficacy[symbol][dimension] = []
        if signal_value == 0:
            return
        correct_direction = 1.0 if (signal_value > 0 and actual_outcome > 0) or (signal_value < 0 and actual_outcome < 0) else 0.0
        self.dimension_efficacy[symbol][dimension].append(correct_direction)
        if len(self.dimension_efficacy[symbol][dimension]) > self.efficacy_window * 2:
            self.dimension_efficacy[symbol][dimension] = self.dimension_efficacy[symbol][dimension][-self.efficacy_window * 2:]
    
    def get_dynamic_weights(self, symbol):
        """V7's dynamic weights - EXACT SAME (with TI naming)"""
        efficacy = self.dimension_efficacy.get(symbol, {})
        tau_i_eff = efficacy.get('tau_i', [])
        tau_j_eff = efficacy.get('tau_j', [])
        tau_c_eff = efficacy.get('tau_c', [])
        love_eff = efficacy.get('love', [])
        if len(tau_i_eff) < 5 or len(tau_j_eff) < 5:
            return self.BASE_WEIGHTS.copy()
        tau_i_score = float(np.mean(tau_i_eff[-self.efficacy_window:])) + 0.1
        tau_j_score = float(np.mean(tau_j_eff[-self.efficacy_window:])) + 0.1
        tau_c_score = float(np.mean(tau_c_eff[-self.efficacy_window:])) + 0.1 if len(tau_c_eff) >= 5 else 0.35
        love_score = float(np.mean(love_eff[-self.efficacy_window:])) + 0.1 if len(love_eff) >= 5 else 0.25
        total = tau_i_score + tau_j_score + tau_c_score + love_score
        if total == 0:
            return self.BASE_WEIGHTS.copy()
        base_tau_i = self.BASE_WEIGHTS['tau_i']
        base_tau_j = self.BASE_WEIGHTS['tau_j']
        base_tau_c = self.BASE_WEIGHTS['tau_c']
        base_love = self.BASE_WEIGHTS['love']
        eff_tau_i = tau_i_score / total
        eff_tau_j = tau_j_score / total
        eff_tau_c = tau_c_score / total
        eff_love = love_score / total
        blend = 0.5
        return {
            'tau_i': base_tau_i * (1 - blend) + eff_tau_i * blend,
            'tau_j': base_tau_j * (1 - blend) + eff_tau_j * blend,
            'tau_c': base_tau_c * (1 - blend) + eff_tau_c * blend,
            'love': base_love * (1 - blend) + eff_love * blend
        }
    
    def calculate_unified_gile(self, symbol):
        """V7's unified calculation - EXACT SAME"""
        tau_i = self.calculate_tau_i(symbol)
        tau_j = self.calculate_tau_j(symbol)
        tau_c = self.calculate_tau_c(symbol)
        love = self.calculate_love(symbol)
        weights = self.get_dynamic_weights(symbol)
        unified = (weights['tau_i'] * tau_i + weights['tau_j'] * tau_j + weights['tau_c'] * tau_c + weights['love'] * love)
        result = {
            'tau_i': tau_i,
            'tau_j': tau_j,
            'tau_c': tau_c,
            'love': love,
            'unified': float(unified),
            'weights': weights
        }
        self.temporal_scores[symbol] = result
        return result
    
    def get_zone_name(self, gile):
        if gile > 2.0:
            return "ULTRA_GREAT"
        elif gile >= self.GILE_GREAT:
            return "GREAT"
        elif gile >= self.GILE_GOOD:
            return "GOOD"
        elif gile >= self.GILE_BAD:
            return "INDETERMINATE"
        elif gile >= self.GILE_TERRIBLE:
            return "BAD"
        elif gile >= -3.0:
            return "TERRIBLE"
        else:
            return "ULTRA_TERRIBLE"
    
    def ti_temporal_rebalance(self):
        """V7's rebalance - EXACT SAME LOGIC"""
        if self.is_warming_up:
            return
        for symbol in self.symbols:
            security = self.securities.get(symbol)
            if security is None or security.price <= 0:
                continue
            price = float(security.price)
            history = self.price_history.get(symbol, [])
            if len(history) >= 2:
                prev_tau_i = self.calculate_tau_i(symbol)
                prev_tau_j = self.calculate_tau_j(symbol)
                prev_tau_c = self.calculate_tau_c(symbol)
                prev_love = self.calculate_love(symbol)
                actual_return = (price - history[-1]) / history[-1] * 100 if history[-1] != 0 else 0
                self.update_dimension_efficacy(symbol, 'tau_i', prev_tau_i, actual_return)
                self.update_dimension_efficacy(symbol, 'tau_j', prev_tau_j, actual_return)
                self.update_dimension_efficacy(symbol, 'tau_c', prev_tau_c, actual_return)
                self.update_dimension_efficacy(symbol, 'love', prev_love, actual_return)
            self.price_history[symbol].append(price)
            if len(self.price_history[symbol]) > self.max_history:
                self.price_history[symbol] = self.price_history[symbol][-self.max_history:]
        signals = {}
        for symbol in self.symbols:
            if len(self.price_history.get(symbol, [])) < self.TAU_C_LONG:
                continue
            temporal = self.calculate_unified_gile(symbol)
            unified_gile = temporal['unified']
            signals[symbol] = {
                'gile': unified_gile,
                'zone': self.get_zone_name(unified_gile),
                'components': temporal
            }
            self.gile_history[symbol].append(unified_gile)
            if len(self.gile_history[symbol]) > 30:
                self.gile_history[symbol] = self.gile_history[symbol][-30:]
        ranked = sorted(signals.items(), key=lambda x: x[1]['gile'], reverse=True)
        buy_candidates = [(s, sig) for s, sig in ranked if sig['gile'] >= self.GILE_GOOD][:3]
        for symbol in list(self.portfolio.keys()):
            if symbol not in signals:
                continue
            sig = signals[symbol]
            holding = self.portfolio[symbol]
            if not holding.invested:
                continue
            should_sell = False
            if sig['gile'] < self.GILE_BAD:
                should_sell = True
            elif sig['zone'] == "ULTRA_GREAT":
                should_sell = True
            elif sig['components']['tau_c'] < -1.0:
                should_sell = True
            if should_sell:
                self.liquidate(symbol)
                self.trade_count += 1
                if holding.unrealized_profit > 0:
                    self.winning_trades += 1
        for symbol, sig in buy_candidates:
            if self.portfolio[symbol].invested:
                continue
            base_size = self.max_position
            if sig['zone'] == "GREAT":
                size = base_size * 1.0
            elif sig['zone'] == "GOOD":
                size = base_size * 0.7
            else:
                size = base_size * 0.5
            components = sig['components']
            if (components['tau_i'] > 0 and 
                components['tau_j'] > 0 and 
                components['tau_c'] > 0):
                size = min(size * 1.2, base_size)
            self.set_holdings(symbol, size)
            self.trade_count += 1
    
    def on_end_of_algorithm(self):
        win_rate = self.winning_trades / max(self.trade_count, 1) * 100
        self.debug(f"V5.2 PURE - Trades: {self.trade_count}, Win Rate: {win_rate:.1f}%")

from AlgorithmImports import *
import numpy as np

class TIFrameworkGTFEv5Algorithm(QCAlgorithm):
    """
    GTFE V5: Grand Tralse Field Equation with Sacred Geometry Integration
    
    PHILOSOPHICAL INTEGRATIONS:
    1. Jeff Moment Primacy: t2 gets 5/15 (present moment consciousness)
    2. Love Resonance Amplification: Love boosts during collective alignment
    3. Dynamic Sacred Thresholds: Adapt based on market regime
    4. MR from Sacred Interval Geometry: 0.333/0.666 ratio derivation
    5. GM Resonance Detection: Amplify when ALL stocks align
    
    Psi_TI = [T(t1) x J(t2) x C(t3)] * GILE * MR * ResonanceBoost
    """
    
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        
        self.SACRED_MIN = -0.666
        self.SACRED_MAX = 0.333
        self.SACRED_RATIO = 0.333 / 0.666
        self.GILE_GREAT = 1.5
        self.GILE_GOOD = 0.3
        self.GILE_BAD = -0.3
        self.GILE_TERRIBLE = -1.5
        self.ULTRA_GREAT_THRESHOLD = 20.0
        self.ULTRA_TERRIBLE_THRESHOLD = -10.0
        self.GREAT_THRESHOLD = 5.0
        self.TERRIBLE_THRESHOLD = -5.0
        self.T1_QUANTUM_LOOKBACK = 3
        self.T2_JEFF_LOOKBACK = 1
        self.T3_COSMO_SHORT = 20
        self.T3_COSMO_LONG = 50
        self.BASE_WEIGHTS = {'t1': 4/15, 't2': 5/15, 't3': 4/15, 'love': 2/15}
        self.TRUE_THRESHOLD = 0.3
        self.FALSE_THRESHOLD = -0.3
        self.max_position = 0.15
        self.MR_ALIGNED = 1.0
        self.MR_PARTIAL = 1.0 - self.SACRED_RATIO * 0.3
        self.MR_MAJOR = 1.0 - self.SACRED_RATIO * 0.8
        self.RESONANCE_THRESHOLD = 0.6
        self.RESONANCE_BOOST = 1.25
        
        self.symbols = [
            self.AddEquity("SPY", Resolution.Daily).Symbol,
            self.AddEquity("QQQ", Resolution.Daily).Symbol,
            self.AddEquity("AAPL", Resolution.Daily).Symbol,
            self.AddEquity("MSFT", Resolution.Daily).Symbol,
            self.AddEquity("GOOGL", Resolution.Daily).Symbol,
            self.AddEquity("TSLA", Resolution.Daily).Symbol,
            self.AddEquity("NVDA", Resolution.Daily).Symbol,
            self.AddEquity("AMD", Resolution.Daily).Symbol,
            self.AddEquity("META", Resolution.Daily).Symbol,
            self.AddEquity("AMZN", Resolution.Daily).Symbol,
        ]
        
        self.price_history = {symbol: [] for symbol in self.symbols}
        self.gile_history = {symbol: [] for symbol in self.symbols}
        self.gtfe_scores = {symbol: {} for symbol in self.symbols}
        self.max_history = 60
        self.SetWarmup(60, Resolution.Daily)
        self.Schedule.On(self.DateRules.EveryDay(), self.TimeRules.AfterMarketOpen("SPY", 30), self.GTFERebalance)
        self.trade_count = 0
        self.winning_trades = 0
        self.resonance_events = 0
        self.market_regime = 'NEUTRAL'
        
    def price_to_gile(self, pct_change):
        if pct_change > self.ULTRA_GREAT_THRESHOLD:
            return float(2.0 + np.log1p((pct_change - self.ULTRA_GREAT_THRESHOLD) / 20) * 0.5)
        elif pct_change < self.ULTRA_TERRIBLE_THRESHOLD:
            return float(-3.0 - np.log1p((abs(pct_change) - abs(self.ULTRA_TERRIBLE_THRESHOLD)) / 10) * 0.5)
        elif pct_change > self.GREAT_THRESHOLD:
            return float(1.5 + (pct_change - 5) / 15 * 0.5)
        elif pct_change < self.TERRIBLE_THRESHOLD:
            return float(-3.0 + (pct_change + 10) / 5 * 1.5)
        elif pct_change > self.SACRED_MAX:
            return float(0.3 + (pct_change - 0.333) / 4.667 * 1.2)
        elif pct_change < self.SACRED_MIN:
            return float(-1.5 + (pct_change + 5) / 4.334 * 1.2)
        else:
            return float((pct_change / 0.666) * 0.3) if pct_change < 0 else float((pct_change / 0.333) * 0.3)
    
    def detect_market_regime(self):
        spy_history = self.price_history.get(self.symbols[0], [])
        if len(spy_history) < 20:
            return 'NEUTRAL'
        recent_returns = []
        for i in range(1, min(20, len(spy_history))):
            ret = (spy_history[-i] - spy_history[-i-1]) / spy_history[-i-1] * 100 if spy_history[-i-1] != 0 else 0
            recent_returns.append(ret)
        avg_return = float(np.mean(recent_returns)) if recent_returns else 0
        volatility = float(np.std(recent_returns)) if len(recent_returns) > 1 else 0
        if avg_return > 0.1 and volatility < 2.0:
            return 'BULL'
        elif avg_return < -0.1 and volatility > 1.5:
            return 'BEAR'
        elif volatility > 2.5:
            return 'HIGH_VOL'
        else:
            return 'NEUTRAL'
    
    def get_dynamic_weights(self, regime):
        if regime == 'BULL':
            return {'t1': 3/15, 't2': 6/15, 't3': 4/15, 'love': 2/15}
        elif regime == 'BEAR':
            return {'t1': 4/15, 't2': 4/15, 't3': 5/15, 'love': 2/15}
        elif regime == 'HIGH_VOL':
            return {'t1': 5/15, 't2': 4/15, 't3': 3/15, 'love': 3/15}
        else:
            return self.BASE_WEIGHTS
    
    def calculate_t1_quantum(self, symbol):
        history = self.price_history.get(symbol, [])
        if len(history) < self.T1_QUANTUM_LOOKBACK:
            return 0.0
        recent = history[-self.T1_QUANTUM_LOOKBACK:]
        momentum = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] != 0 else 0
        returns = np.diff(recent) / recent[:-1] * 100 if len(recent) > 1 else [0]
        volatility = float(np.std(returns)) if len(returns) > 1 else 0.0
        return float(np.clip(self.price_to_gile(momentum) * (1 + volatility * 0.1), -3, 3))
    
    def calculate_t2_jeff(self, symbol):
        history = self.price_history.get(symbol, [])
        if len(history) < 2:
            return 0.0
        today_change = (history[-1] - history[-2]) / history[-2] * 100 if history[-2] != 0 else 0
        return float(self.price_to_gile(today_change))
    
    def calculate_t3_cosmological(self, symbol):
        history = self.price_history.get(symbol, [])
        if len(history) < self.T3_COSMO_LONG:
            return 0.0
        sma_short = float(np.mean(history[-self.T3_COSMO_SHORT:]))
        sma_long = float(np.mean(history[-self.T3_COSMO_LONG:]))
        trend_divergence = (sma_short - sma_long) / sma_long * 100 if sma_long != 0 else 0
        price_position = (history[-1] - sma_long) / sma_long * 100 if sma_long != 0 else 0
        return float(self.price_to_gile((trend_divergence + price_position) / 2))
    
    def calculate_love_correlation(self, symbol, resonance_count=0):
        if len(self.price_history.get(symbol, [])) < 21:
            return 0.0
        sym_history = self.price_history[symbol][-21:]
        sym_returns = np.diff(sym_history) / sym_history[:-1] * 100
        spy_history = self.price_history.get(self.symbols[0], [])
        if len(spy_history) < 21:
            return 0.0
        spy_prices = spy_history[-21:]
        spy_returns = np.diff(spy_prices) / spy_prices[:-1] * 100
        if len(sym_returns) != len(spy_returns) or len(sym_returns) < 10:
            return 0.0
        try:
            corr_matrix = np.corrcoef(sym_returns, spy_returns)
            correlation = float(corr_matrix[0, 1]) if not np.isnan(corr_matrix[0, 1]) else 0.0
        except:
            correlation = 0.0
        spy_trend = float(np.mean(spy_returns)) if len(spy_returns) > 0 else 0.0
        base_love = correlation * abs(spy_trend) * 0.5 if spy_trend > 0 else (1 - abs(correlation)) * abs(spy_trend) * 0.5
        resonance_boost = 1.0 + (resonance_count / len(self.symbols)) * 0.5 if resonance_count > 3 else 1.0
        return float(np.clip(base_love * resonance_boost, -1.5, 2.0))
    
    def calculate_myrion_resolution(self, t1, t2, t3):
        signs = [np.sign(t1), np.sign(t2), np.sign(t3)]
        non_zero_signs = [s for s in signs if s != 0]
        if len(non_zero_signs) == 0:
            return {'level': 0.0, 'factor': self.MR_ALIGNED, 'status': 'NEUTRAL'}
        agreement = len(set(non_zero_signs))
        if agreement == 1:
            return {'level': 0.0, 'factor': self.MR_ALIGNED, 'status': 'ALIGNED'}
        elif agreement == 2:
            return {'level': 0.5, 'factor': self.MR_PARTIAL, 'status': 'PARTIAL_CONFLICT'}
        else:
            return {'level': 1.0, 'factor': self.MR_MAJOR, 'status': 'MAJOR_CONFLICT'}
    
    def get_tralse_state(self, psi_ti):
        if psi_ti >= self.TRUE_THRESHOLD:
            return 'TRUE'
        elif psi_ti <= self.FALSE_THRESHOLD:
            return 'FALSE'
        else:
            return 'TRALSE'
    
    def get_zone_name(self, psi_ti):
        if psi_ti > 2.0:
            return "ULTRA_GREAT"
        elif psi_ti >= self.GILE_GREAT:
            return "GREAT"
        elif psi_ti >= self.GILE_GOOD:
            return "GOOD"
        elif psi_ti >= self.GILE_BAD:
            return "INDETERMINATE"
        elif psi_ti >= self.GILE_TERRIBLE:
            return "BAD"
        else:
            return "TERRIBLE"
    
    def calculate_gtfe(self, symbol, weights, resonance_count=0):
        t1 = self.calculate_t1_quantum(symbol)
        t2 = self.calculate_t2_jeff(symbol)
        t3 = self.calculate_t3_cosmological(symbol)
        love = self.calculate_love_correlation(symbol, resonance_count)
        mr = self.calculate_myrion_resolution(t1, t2, t3)
        psi_raw = weights['t1'] * t1 + weights['t2'] * t2 + weights['t3'] * t3 + weights['love'] * love
        tralse_state = self.get_tralse_state(psi_raw)
        zone = self.get_zone_name(psi_raw)
        return {
            'psi_ti': float(psi_raw),
            'psi_raw': float(psi_raw),
            'mr_factor': float(mr['factor']),
            't1': float(t1), 't2': float(t2), 't3': float(t3),
            'love': float(love), 'mr': mr,
            'tralse_state': tralse_state, 'zone': zone
        }
    
    def detect_gm_resonance(self, signals):
        true_count = sum(1 for s in signals.values() if s['tralse_state'] == 'TRUE')
        false_count = sum(1 for s in signals.values() if s['tralse_state'] == 'FALSE')
        total = len(signals)
        if total == 0:
            return {'detected': False, 'type': 'NONE', 'strength': 0.0}
        true_ratio = true_count / total
        false_ratio = false_count / total
        if true_ratio >= self.RESONANCE_THRESHOLD:
            self.resonance_events += 1
            return {'detected': True, 'type': 'BULLISH', 'strength': true_ratio, 'boost': self.RESONANCE_BOOST}
        elif false_ratio >= self.RESONANCE_THRESHOLD:
            return {'detected': True, 'type': 'BEARISH', 'strength': false_ratio, 'boost': 0.5}
        else:
            return {'detected': False, 'type': 'NONE', 'strength': 0.0, 'boost': 1.0}
    
    def GTFERebalance(self):
        if self.IsWarmingUp:
            return
        for symbol in self.symbols:
            if self.Securities[symbol].HasData:
                price = float(self.Securities[symbol].Price)
                self.price_history[symbol].append(price)
                if len(self.price_history[symbol]) > self.max_history:
                    self.price_history[symbol] = self.price_history[symbol][-self.max_history:]
        self.market_regime = self.detect_market_regime()
        weights = self.get_dynamic_weights(self.market_regime)
        preliminary_signals = {}
        for symbol in self.symbols:
            if len(self.price_history.get(symbol, [])) >= self.T3_COSMO_LONG:
                gtfe = self.calculate_gtfe(symbol, weights, 0)
                preliminary_signals[symbol] = gtfe
        resonance = self.detect_gm_resonance(preliminary_signals)
        resonance_count = sum(1 for s in preliminary_signals.values() if s['tralse_state'] == 'TRUE')
        signals = {}
        for symbol in self.symbols:
            if len(self.price_history.get(symbol, [])) >= self.T3_COSMO_LONG:
                gtfe = self.calculate_gtfe(symbol, weights, resonance_count)
                self.gtfe_scores[symbol] = gtfe
                signals[symbol] = gtfe
                self.gile_history[symbol].append(gtfe['psi_ti'])
                if len(self.gile_history[symbol]) > 30:
                    self.gile_history[symbol] = self.gile_history[symbol][-30:]
        if not signals:
            return
        ranked = sorted(signals.items(), key=lambda x: x[1]['psi_ti'], reverse=True)
        buy_candidates = [(s, sig) for s, sig in ranked if sig['tralse_state'] == 'TRUE'][:5]
        for symbol in list(self.Portfolio.Keys):
            if symbol not in signals:
                continue
            sig = signals[symbol]
            holding = self.Portfolio[symbol]
            if not holding.Invested:
                continue
            should_sell = False
            if sig['tralse_state'] == 'FALSE':
                should_sell = True
            elif sig['zone'] == "ULTRA_GREAT":
                should_sell = True
            elif sig['t3'] < -1.0:
                should_sell = True
            elif resonance['type'] == 'BEARISH' and resonance['detected']:
                should_sell = True
            if should_sell:
                self.Liquidate(symbol)
                self.trade_count += 1
                if holding.UnrealizedProfit > 0:
                    self.winning_trades += 1
        for symbol, sig in buy_candidates:
            if self.Portfolio[symbol].Invested:
                continue
            if sig['zone'] == "ULTRA_GREAT":
                base_size = self.max_position * 1.2
            elif sig['zone'] == "GREAT":
                base_size = self.max_position * 1.0
            elif sig['zone'] == "GOOD":
                base_size = self.max_position * 0.8
            else:
                base_size = self.max_position * 0.6
            if sig['t1'] > 0 and sig['t2'] > 0 and sig['t3'] > 0:
                base_size = min(base_size * 1.2, self.max_position * 1.3)
            mr_factor = sig.get('mr_factor', 1.0)
            resonance_boost = resonance.get('boost', 1.0) if resonance['detected'] and resonance['type'] == 'BULLISH' else 1.0
            size = base_size * mr_factor * resonance_boost
            size = min(size, 0.20)
            self.SetHoldings(symbol, size)
            self.trade_count += 1
    
    def OnEndOfAlgorithm(self):
        win_rate = self.winning_trades / max(self.trade_count, 1) * 100
        self.Debug(f"GTFE V5 SACRED Complete - Trades: {self.trade_count}, Wins: {self.winning_trades}, Rate: {win_rate:.1f}%, Resonance Events: {self.resonance_events}")

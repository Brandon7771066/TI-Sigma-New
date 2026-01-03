from AlgorithmImports import *
import numpy as np

class TIFrameworkGTFEAlgorithm(QCAlgorithm):
    """
    GTFE V4: Grand Tralse Field Equation with V3-style aggressive trading
    Psi_TI = [T(t1) x J(t2) x C(t3)] * GILE(g,i,l,e) * MR(omega)
    
    FIXED: Uses V3's position sizing and direct SetHoldings (no 2% gate)
    """
    
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        
        self.SACRED_MIN = -0.666
        self.SACRED_MAX = 0.333
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
        self.JEFF_WEIGHTS = {'t1': 4/15, 't2': 5/15, 't3': 4/15, 'love': 2/15}
        self.TRUE_THRESHOLD = 0.3
        self.FALSE_THRESHOLD = -0.3
        self.max_position = 0.12
        
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
        self.tralse_count = 0
        
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
    
    def calculate_love_correlation(self, symbol):
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
        love_score = correlation * abs(spy_trend) * 0.5 if spy_trend > 0 else (1 - abs(correlation)) * abs(spy_trend) * 0.5
        return float(np.clip(love_score, -1.5, 1.5))
    
    def calculate_myrion_resolution(self, t1, t2, t3):
        signs = [np.sign(t1), np.sign(t2), np.sign(t3)]
        non_zero_signs = [s for s in signs if s != 0]
        if len(non_zero_signs) == 0:
            return {'level': 0.0, 'factor': 1.0, 'status': 'NEUTRAL'}
        agreement = len(set(non_zero_signs))
        if agreement == 1:
            return {'level': 0.0, 'factor': 1.0, 'status': 'ALIGNED'}
        elif agreement == 2:
            return {'level': 0.5, 'factor': 0.85, 'status': 'PARTIAL_CONFLICT'}
        else:
            return {'level': 1.0, 'factor': 0.6, 'status': 'MAJOR_CONFLICT'}
    
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
    
    def calculate_gtfe(self, symbol):
        t1 = self.calculate_t1_quantum(symbol)
        t2 = self.calculate_t2_jeff(symbol)
        t3 = self.calculate_t3_cosmological(symbol)
        love = self.calculate_love_correlation(symbol)
        mr = self.calculate_myrion_resolution(t1, t2, t3)
        psi_raw = self.JEFF_WEIGHTS['t1'] * t1 + self.JEFF_WEIGHTS['t2'] * t2 + self.JEFF_WEIGHTS['t3'] * t3 + self.JEFF_WEIGHTS['love'] * love
        tralse_state = self.get_tralse_state(psi_raw)
        zone = self.get_zone_name(psi_raw)
        if tralse_state == 'TRALSE':
            self.tralse_count += 1
        return {
            'psi_ti': float(psi_raw),
            'psi_raw': float(psi_raw),
            'mr_factor': float(mr['factor']),
            't1': float(t1), 't2': float(t2), 't3': float(t3),
            'love': float(love), 'mr': mr,
            'tralse_state': tralse_state, 'zone': zone
        }
    
    def GTFERebalance(self):
        if self.IsWarmingUp:
            return
        for symbol in self.symbols:
            if self.Securities[symbol].HasData:
                price = float(self.Securities[symbol].Price)
                self.price_history[symbol].append(price)
                if len(self.price_history[symbol]) > self.max_history:
                    self.price_history[symbol] = self.price_history[symbol][-self.max_history:]
        signals = {}
        for symbol in self.symbols:
            if len(self.price_history.get(symbol, [])) >= self.T3_COSMO_LONG:
                gtfe = self.calculate_gtfe(symbol)
                self.gtfe_scores[symbol] = gtfe
                signals[symbol] = gtfe
                self.gile_history[symbol].append(gtfe['psi_ti'])
                if len(self.gile_history[symbol]) > 30:
                    self.gile_history[symbol] = self.gile_history[symbol][-30:]
        if not signals:
            return
        ranked = sorted(signals.items(), key=lambda x: x[1]['psi_ti'], reverse=True)
        buy_candidates = [(s, sig) for s, sig in ranked if sig['tralse_state'] == 'TRUE'][:3]
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
            if should_sell:
                self.Liquidate(symbol)
                self.trade_count += 1
                if holding.UnrealizedProfit > 0:
                    self.winning_trades += 1
        for symbol, sig in buy_candidates:
            if self.Portfolio[symbol].Invested:
                continue
            if sig['zone'] == "GREAT" or sig['zone'] == "ULTRA_GREAT":
                base_size = self.max_position * 1.0
            elif sig['zone'] == "GOOD":
                base_size = self.max_position * 0.7
            else:
                base_size = self.max_position * 0.5
            if sig['t1'] > 0 and sig['t2'] > 0 and sig['t3'] > 0:
                base_size = min(base_size * 1.2, self.max_position)
            mr_factor = sig.get('mr_factor', 1.0)
            size = base_size * mr_factor
            self.SetHoldings(symbol, size)
            self.trade_count += 1
    
    def OnEndOfAlgorithm(self):
        win_rate = self.winning_trades / max(self.trade_count, 1) * 100
        self.Debug(f"GTFE V4 Complete - Trades: {self.trade_count}, Wins: {self.winning_trades}, Rate: {win_rate:.1f}%, TRALSE: {self.tralse_count}")

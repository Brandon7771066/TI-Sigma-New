"""
TI FRAMEWORK V8: REGIME-AWARE ALGORITHM
========================================

Built from diagnostic lab findings:
1. Individual prediction accuracy is ~51% (barely above random)
2. LCC (Love Correlation) is STRONGEST predictor at 52.7%
3. V3's success came from TRADING RULES, not prediction
4. Market was 78% SIDEWAYS - need REGIME DETECTION

KEY CHANGES FROM V3:
- Adds REGIME DETECTION (Bull/Bear/Sideways)
- Adapts trading rules per regime
- LCC gets higher weight (it's the best predictor!)
- Keeps V3's proven trading rules structure

REGIME-SPECIFIC RULES:
- BULL: Aggressive, full positions, ride momentum
- SIDEWAYS: Conservative, tighter zones, wait for breakout
- BEAR: Defensive, reduce exposure, inverse signals

Target: Beat V3's 277.76% by adapting to market conditions
"""

from AlgorithmImports import *
import numpy as np

class TIFrameworkV8RegimeAlgorithm(QCAlgorithm):
    
    # GILE Thresholds (same as V3)
    GILE_GREAT = 1.5
    GILE_GOOD = 0.3
    GILE_BAD = -0.3
    GILE_TERRIBLE = -1.5
    ULTRA_GREAT = 2.0
    
    # Regime thresholds
    BULL_THRESHOLD = 0.03  # 3% above SMA
    BEAR_THRESHOLD = -0.03  # 3% below SMA
    
    # LCC Threshold (Love Correlation)
    LCC_SYNC_THRESHOLD = 0.42
    
    # V8 Weights: LCC gets boost (best predictor from diagnostic)
    W_T1 = 0.20  # Potential
    W_T2 = 0.30  # Actualized  
    W_T3 = 0.20  # Contextual
    W_LCC = 0.30  # Love Correlation - BOOSTED (was 0.15)
    
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
        
        self.spy = self.symbols[0]
        self.price_history = {s: [] for s in self.symbols}
        self.return_history = {s: [] for s in self.symbols}
        self.max_history = 100
        
        # Regime tracking
        self.current_regime = "UNKNOWN"
        self.regime_strength = 0.0
        
        # Position sizing per regime
        self.regime_position_mult = {
            "BULL": 1.2,      # Aggressive
            "SIDEWAYS": 0.7,  # Conservative
            "BEAR": 0.3,      # Defensive
            "UNKNOWN": 0.5
        }
        
        self.max_position = 0.15
        
        self.set_warmup(60, Resolution.DAILY)
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.after_market_open("SPY", 30),
            self.regime_aware_rebalance
        )
        
        self.trade_count = 0
        self.winning_trades = 0
    
    def detect_regime(self):
        """
        Detect market regime: BULL, BEAR, or SIDEWAYS
        Uses SPY relative to 50-day SMA
        """
        spy_prices = self.price_history.get(self.spy, [])
        if len(spy_prices) < 50:
            self.current_regime = "UNKNOWN"
            self.regime_strength = 0.0
            return
        
        current = spy_prices[-1]
        sma50 = float(np.mean(spy_prices[-50:]))
        
        if sma50 == 0:
            self.current_regime = "UNKNOWN"
            self.regime_strength = 0.0
            return
        
        deviation = (current - sma50) / sma50
        self.regime_strength = abs(deviation)
        
        if deviation > self.BULL_THRESHOLD:
            self.current_regime = "BULL"
        elif deviation < self.BEAR_THRESHOLD:
            self.current_regime = "BEAR"
        else:
            self.current_regime = "SIDEWAYS"
    
    def price_to_gile(self, pct_change):
        """Map percentage to GILE scale"""
        if pct_change > 20:
            return float(2.0 + np.log1p((pct_change - 20) / 20) * 0.5)
        elif pct_change < -10:
            return float(-3.0 - np.log1p((abs(pct_change) - 10) / 10) * 0.5)
        elif pct_change > 5:
            return float(1.5 + (pct_change - 5) / 15 * 0.5)
        elif pct_change < -5:
            return float(-3.0 + (pct_change + 10) / 5 * 1.5)
        elif pct_change > 0.333:
            return float(0.3 + (pct_change - 0.333) / 4.667 * 1.2)
        elif pct_change < -0.666:
            return float(-1.5 + (pct_change + 5) / 4.334 * 1.2)
        else:
            return float((pct_change / 0.666) * 0.3) if pct_change < 0 else float((pct_change / 0.333) * 0.3)
    
    def calculate_t1_potential(self, symbol):
        """Jeff Time POTENTIAL: Momentum + volatility"""
        prices = self.price_history.get(symbol, [])
        if len(prices) < 3:
            return 0.0
        recent = prices[-3:]
        momentum = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] != 0 else 0
        returns = np.diff(recent) / recent[:-1] * 100
        vol = float(np.std(returns)) if len(returns) > 1 else 0
        return float(np.clip(self.price_to_gile(momentum) * (1 + vol * 0.1), -3, 3))
    
    def calculate_t2_actualized(self, symbol):
        """Jeff Time ACTUALIZED: Today's observation"""
        rets = self.return_history.get(symbol, [])
        if len(rets) < 1:
            return 0.0
        return float(self.price_to_gile(rets[-1]))
    
    def calculate_t3_contextual(self, symbol):
        """Jeff Time CONTEXTUAL: Trend context"""
        prices = self.price_history.get(symbol, [])
        if len(prices) < 50:
            return 0.0
        sma20 = float(np.mean(prices[-20:]))
        sma50 = float(np.mean(prices[-50:]))
        trend_div = (sma20 - sma50) / sma50 * 100 if sma50 != 0 else 0
        price_pos = (prices[-1] - sma50) / sma50 * 100 if sma50 != 0 else 0
        return float(self.price_to_gile((trend_div + price_pos) / 2))
    
    def calculate_lcc(self, symbol):
        """
        LCC (Love Correlation): 52.7% accuracy - BEST predictor
        Returns correlation value and sync status
        """
        sym_rets = self.return_history.get(symbol, [])
        spy_rets = self.return_history.get(self.spy, [])
        
        if len(sym_rets) < 20 or len(spy_rets) < 20:
            return 0.0, False
        
        sym_recent = sym_rets[-20:]
        spy_recent = spy_rets[-20:]
        
        min_len = min(len(sym_recent), len(spy_recent))
        if min_len < 10:
            return 0.0, False
        
        sym_recent = sym_recent[-min_len:]
        spy_recent = spy_recent[-min_len:]
        
        try:
            corr = float(np.corrcoef(sym_recent, spy_recent)[0, 1])
            if np.isnan(corr):
                corr = 0.0
        except:
            corr = 0.0
        
        is_sync = corr >= self.LCC_SYNC_THRESHOLD
        return corr, is_sync
    
    def calculate_unified_signal(self, symbol):
        """Calculate unified GILE with LCC boost"""
        t1 = self.calculate_t1_potential(symbol)
        t2 = self.calculate_t2_actualized(symbol)
        t3 = self.calculate_t3_contextual(symbol)
        lcc_corr, lcc_sync = self.calculate_lcc(symbol)
        
        # LCC contribution: positive sync = boost, negative = dampen
        if lcc_sync:
            lcc_signal = 0.5  # Strong positive contribution
        elif lcc_corr < -self.LCC_SYNC_THRESHOLD:
            lcc_signal = -0.3  # Negative contribution
        else:
            lcc_signal = lcc_corr * 0.2  # Scaled contribution
        
        # Unified signal with V8 weights (LCC boosted)
        unified = self.W_T1 * t1 + self.W_T2 * t2 + self.W_T3 * t3 + self.W_LCC * lcc_signal
        
        # Alignment bonus
        aligned = t1 > 0 and t2 > 0 and t3 > 0
        if aligned:
            unified *= 1.15
        
        # Zone classification
        if unified > self.ULTRA_GREAT:
            zone = "ULTRA_GREAT"
        elif unified >= self.GILE_GREAT:
            zone = "GREAT"
        elif unified >= self.GILE_GOOD:
            zone = "GOOD"
        elif unified >= self.GILE_BAD:
            zone = "INDETERMINATE"
        elif unified >= self.GILE_TERRIBLE:
            zone = "BAD"
        else:
            zone = "TERRIBLE"
        
        return {
            't1': t1, 't2': t2, 't3': t3,
            'lcc': lcc_corr, 'lcc_sync': lcc_sync,
            'unified': float(unified), 'zone': zone,
            'aligned': aligned
        }
    
    def get_regime_adjusted_thresholds(self):
        """Adjust thresholds based on regime"""
        if self.current_regime == "BULL":
            return {
                'buy_threshold': self.GILE_GOOD * 0.8,  # More permissive
                'sell_threshold': self.GILE_BAD * 1.2,  # Less likely to sell
                'top_n': 4  # Take more positions
            }
        elif self.current_regime == "BEAR":
            return {
                'buy_threshold': self.GILE_GREAT,  # Very strict
                'sell_threshold': 0.0,  # Sell on any weakness
                'top_n': 1  # Minimal positions
            }
        else:  # SIDEWAYS
            return {
                'buy_threshold': self.GILE_GOOD,
                'sell_threshold': self.GILE_BAD,
                'top_n': 2  # Conservative
            }
    
    def regime_aware_rebalance(self):
        """Main rebalancing with regime awareness"""
        if self.is_warming_up:
            return
        
        # Update price/return history
        for symbol in self.symbols:
            sec = self.securities.get(symbol)
            if sec is None or sec.price <= 0:
                continue
            
            price = float(sec.price)
            hist = self.price_history.get(symbol, [])
            
            if len(hist) > 0:
                ret = (price - hist[-1]) / hist[-1] * 100 if hist[-1] != 0 else 0
                self.return_history[symbol].append(ret)
                if len(self.return_history[symbol]) > self.max_history:
                    self.return_history[symbol] = self.return_history[symbol][-self.max_history:]
            
            self.price_history[symbol].append(price)
            if len(self.price_history[symbol]) > self.max_history:
                self.price_history[symbol] = self.price_history[symbol][-self.max_history:]
        
        # Detect regime
        self.detect_regime()
        thresholds = self.get_regime_adjusted_thresholds()
        
        # Calculate signals
        signals = {}
        for symbol in self.symbols:
            if len(self.price_history.get(symbol, [])) < 50:
                continue
            signals[symbol] = self.calculate_unified_signal(symbol)
        
        # Rank and select buy candidates
        ranked = sorted(signals.items(), key=lambda x: x[1]['unified'], reverse=True)
        buy_candidates = [
            (s, sig) for s, sig in ranked 
            if sig['unified'] >= thresholds['buy_threshold']
        ][:thresholds['top_n']]
        
        # SELL LOGIC - regime aware
        for symbol in list(self.portfolio.keys()):
            if symbol not in signals:
                continue
            
            sig = signals[symbol]
            holding = self.portfolio[symbol]
            
            if not holding.invested:
                continue
            
            should_sell = False
            
            # Standard V3 sell conditions
            if sig['unified'] < thresholds['sell_threshold']:
                should_sell = True
            elif sig['zone'] == "ULTRA_GREAT":
                should_sell = True
            elif sig['t3'] < -1.0:
                should_sell = True
            
            # BEAR regime: extra caution
            if self.current_regime == "BEAR":
                if sig['lcc'] < 0:  # Losing market sync
                    should_sell = True
                if not sig['aligned']:  # Any misalignment
                    should_sell = True
            
            if should_sell:
                self.liquidate(symbol)
                self.trade_count += 1
                if holding.unrealized_profit > 0:
                    self.winning_trades += 1
        
        # BUY LOGIC - regime aware
        regime_mult = self.regime_position_mult.get(self.current_regime, 0.5)
        
        for symbol, sig in buy_candidates:
            if self.portfolio[symbol].invested:
                continue
            
            # Base size from zone
            if sig['zone'] == "GREAT":
                base = 1.0
            elif sig['zone'] == "GOOD":
                base = 0.7
            else:
                base = 0.5
            
            # Alignment boost
            if sig['aligned']:
                base *= 1.2
            
            # LCC boost (best predictor!)
            if sig['lcc_sync']:
                base *= 1.15
            
            # Regime adjustment
            size = self.max_position * base * regime_mult
            size = min(size, self.max_position * 1.5)
            
            self.set_holdings(symbol, size)
            self.trade_count += 1
    
    def on_end_of_algorithm(self):
        win_rate = self.winning_trades / max(self.trade_count, 1) * 100
        self.debug(f"V8 REGIME - Trades: {self.trade_count}, Win Rate: {win_rate:.1f}%")
        self.debug(f"Final Regime: {self.current_regime}")

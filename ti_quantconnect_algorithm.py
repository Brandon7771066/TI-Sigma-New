"""
TI FRAMEWORK STOCK TRADING ALGORITHM - QUANTCONNECT READY
==========================================================
GILE PD Distribution aligned with Ternary (3) × GILE Range (5) = 15

VERIFIED PERCENTAGES (Nov 29, 2025):
- Great (≥+2):        1/15 = 6.667%
- Good (0 to +2):     3/15 = 20%
- Indeterminate:      3/15 = 20% (Sacred Interval: -0.666 to +0.333)
- Bad (-3 to 0):      6/15 = 40%
- Terrible (≤-3):     2/15 = 13.333%
                      -----
                       100%

BLACK SWAN EXTENSIONS (within extremes):
- Ultra-Great (>+2):  1/225 = 0.444%
- Ultra-Terrible (<-3): 4/225 = 1.778%

COPY EVERYTHING BELOW THIS LINE FOR QUANTCONNECT:
"""

# ============================================================================
# PASTE THIS INTO QUANTCONNECT:
# ============================================================================

from AlgorithmImports import *
import numpy as np

class TIFrameworkGILEAlgorithm(QCAlgorithm):
    """
    TI Framework GILE Trading Algorithm
    
    Based on the Cosmic Prisoner's Dilemma distribution:
    15 = 3 (Ternary) × 5 (GILE Range)
    
    Zone Probabilities (from 15-based fractions):
    - Great:        6.667%  (1/15)
    - Good:         20%     (3/15)
    - Indeterminate: 20%    (3/15) - Sacred Interval
    - Bad:          40%     (6/15)
    - Terrible:     13.333% (2/15)
    
    Black Swans (from 225 = 15²):
    - Ultra-Great:   0.444% (1/225)
    - Ultra-Terrible: 1.778% (4/225)
    """
    
    # =========================================================================
    # SACRED CONSTANTS (Ternary-aligned)
    # =========================================================================
    
    # Sacred Interval boundaries (Indeterminate zone)
    SACRED_MIN = -0.666    # -2/3 in ternary
    SACRED_MAX = 0.333     # +1/3 in ternary
    
    # Everyday extreme boundaries (price change %)
    GREAT_THRESHOLD = 5.0       # +5% daily → approaching Great
    TERRIBLE_THRESHOLD = -5.0   # -5% daily → approaching Terrible
    
    # Black swan thresholds
    ULTRA_GREAT_THRESHOLD = 20.0    # +20% daily = Ultra-Great
    ULTRA_TERRIBLE_THRESHOLD = -10.0 # -10% daily = Ultra-Terrible
    
    # GILE signal thresholds
    GILE_GREAT = 1.5        # GILE ≥ 1.5 = Great zone (signal strength: strong buy)
    GILE_GOOD = 0.3         # GILE > 0.3 = Good zone (signal: buy)
    GILE_BAD = -0.3         # GILE < -0.3 = Bad zone (signal: sell)
    GILE_TERRIBLE = -1.5    # GILE ≤ -1.5 = Terrible zone (signal strength: strong sell)
    
    def initialize(self):
        """Initialize with TI Framework parameters"""
        
        self.set_start_date(2020, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        
        # Universe of stocks
        self.symbols = [
            self.add_equity("SPY", Resolution.DAILY).symbol,
            self.add_equity("QQQ", Resolution.DAILY).symbol,
            self.add_equity("AAPL", Resolution.DAILY).symbol,
            self.add_equity("MSFT", Resolution.DAILY).symbol,
            self.add_equity("GOOGL", Resolution.DAILY).symbol,
            self.add_equity("TSLA", Resolution.DAILY).symbol,
            self.add_equity("NVDA", Resolution.DAILY).symbol,
            self.add_equity("AMD", Resolution.DAILY).symbol,
        ]
        
        # GILE history for momentum calculation
        self.gile_history = {symbol: [] for symbol in self.symbols}
        self.gile_lookback = 20
        
        # Position sizing
        self.max_position = 0.15
        
        # Warmup
        self.set_warmup(30, Resolution.DAILY)
        
        # Schedule daily rebalance
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.after_market_open("SPY", 30),
            self.gile_rebalance
        )
    
    def price_to_gile(self, pct_change: float) -> float:
        """
        Convert daily price change (%) to GILE score
        
        Mapping aligned with 15-based distribution:
        - Ultra-Great (>+20%): GILE > +2.0 (log extension)
        - Great (+5% to +20%): GILE +1.5 to +2.0
        - Good (+0.333% to +5%): GILE +0.3 to +1.5
        - Indeterminate (-0.666% to +0.333%): GILE -0.3 to +0.3
        - Bad (-5% to -0.666%): GILE -0.3 to -1.5
        - Terrible (-10% to -5%): GILE -1.5 to -3.0
        - Ultra-Terrible (<-10%): GILE < -3.0 (log extension)
        """
        
        # Ultra-Great: Black Swan positive (1/225 = 0.444%)
        if pct_change > self.ULTRA_GREAT_THRESHOLD:
            excess = pct_change - self.ULTRA_GREAT_THRESHOLD
            return 2.0 + np.log1p(excess / 20) * 0.5
        
        # Ultra-Terrible: Black Swan negative (4/225 = 1.778%)
        elif pct_change < self.ULTRA_TERRIBLE_THRESHOLD:
            excess = abs(pct_change) - abs(self.ULTRA_TERRIBLE_THRESHOLD)
            return -3.0 - np.log1p(excess / 10) * 0.5
        
        # Great zone (1/15 = 6.667%): +5% to +20% → GILE +1.5 to +2.0
        elif pct_change > self.GREAT_THRESHOLD:
            return 1.5 + (pct_change - 5) / (20 - 5) * 0.5
        
        # Terrible zone (2/15 = 13.333%): -10% to -5% → GILE -3.0 to -1.5
        elif pct_change < self.TERRIBLE_THRESHOLD:
            return -3.0 + (pct_change + 10) / (10 - 5) * 1.5
        
        # Good zone (3/15 = 20%): +0.333% to +5% → GILE +0.3 to +1.5
        elif pct_change > self.SACRED_MAX:
            return 0.3 + (pct_change - 0.333) / (5 - 0.333) * 1.2
        
        # Bad zone (6/15 = 40%): -5% to -0.666% → GILE -0.3 to -1.5
        elif pct_change < self.SACRED_MIN:
            return -1.5 + (pct_change + 5) / (5 - 0.666) * 1.2
        
        # Sacred Interval (3/15 = 20%): -0.666% to +0.333% → GILE -0.3 to +0.3
        else:
            if pct_change < 0:
                return (pct_change / 0.666) * 0.3
            else:
                return (pct_change / 0.333) * 0.3
    
    def get_gile_momentum(self, symbol) -> float:
        """Calculate GILE momentum (5-day vs 20-day average)"""
        history = self.gile_history.get(symbol, [])
        if len(history) < 5:
            return 0.0
        
        recent = np.mean(history[-5:])
        longer = np.mean(history[-20:]) if len(history) >= 20 else np.mean(history)
        return float(recent - longer)
    
    def get_zone_name(self, gile: float) -> str:
        """Get zone name from GILE score"""
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
    
    def calculate_signal(self, gile: float, momentum: float) -> float:
        """
        Calculate trading signal from GILE score and momentum
        
        Signal strength:
        +3 = Ultra-Great (strong long)
        +2 = Great
        +1 = Good
         0 = Indeterminate (hold/neutral)
        -1 = Bad
        -2 = Terrible
        -3 = Ultra-Terrible (strong short/exit)
        """
        signal = 0
        
        # Base signal from GILE zone
        if gile > 2.0:
            signal = 3  # Ultra-Great: black swan long
        elif gile >= self.GILE_GREAT:
            signal = 2  # Great
        elif gile >= self.GILE_GOOD:
            signal = 1  # Good
        elif gile >= self.GILE_BAD:
            signal = 0  # Indeterminate
        elif gile >= self.GILE_TERRIBLE:
            signal = -1  # Bad
        elif gile >= -3.0:
            signal = -2  # Terrible
        else:
            signal = -3  # Ultra-Terrible: black swan exit
        
        # Momentum adjustment
        if momentum > 0.2:
            signal += 0.5
        elif momentum < -0.2:
            signal -= 0.5
        
        return signal
    
    def gile_rebalance(self):
        """Main GILE-based rebalancing logic"""
        
        if self.is_warming_up:
            return
        
        signals = {}
        
        for symbol in self.symbols:
            history = self.history(symbol, 2, Resolution.DAILY)
            if history.empty or len(history) < 2:
                continue
            
            # Calculate daily return
            prev_close = history['close'].iloc[-2]
            curr_close = history['close'].iloc[-1]
            pct_change = ((curr_close - prev_close) / prev_close) * 100
            
            # Convert to GILE score
            gile = self.price_to_gile(pct_change)
            
            # Update history
            self.gile_history[symbol].append(gile)
            if len(self.gile_history[symbol]) > self.gile_lookback:
                self.gile_history[symbol] = self.gile_history[symbol][-self.gile_lookback:]
            
            # Calculate momentum and signal
            momentum = self.get_gile_momentum(symbol)
            signal = self.calculate_signal(gile, momentum)
            zone = self.get_zone_name(gile)
            
            signals[symbol] = {
                'signal': signal,
                'gile': gile,
                'momentum': momentum,
                'zone': zone,
                'pct_change': pct_change
            }
        
        self.execute_gile_trades(signals)
    
    def execute_gile_trades(self, signals: dict):
        """Execute trades based on GILE signals"""
        
        # Sort by signal strength
        sorted_signals = sorted(
            signals.items(),
            key=lambda x: x[1]['signal'],
            reverse=True
        )
        
        # Strong exits: signal <= -2 (Terrible or worse)
        for symbol, data in sorted_signals:
            if data['signal'] <= -2 and self.portfolio[symbol].invested:
                self.liquidate(symbol)
                self.debug(f"GILE EXIT {symbol}: Zone={data['zone']}, GILE={data['gile']:.2f}")
        
        # Strong entries: signal >= 2 (Great or better)
        strong_buys = [(s, d) for s, d in sorted_signals if d['signal'] >= 2]
        
        if strong_buys:
            position_size = min(self.max_position, 0.9 / len(strong_buys))
            
            for symbol, data in strong_buys:
                if not self.portfolio[symbol].invested:
                    self.set_holdings(symbol, position_size)
                    self.debug(f"GILE BUY {symbol}: Zone={data['zone']}, GILE={data['gile']:.2f}")
    
    def on_data(self, data):
        """Data handler (using scheduled rebalance instead)"""
        pass


# ============================================================================
# END OF QUANTCONNECT CODE
# ============================================================================

"""
SUMMARY OF GILE PD DISTRIBUTION:
================================

Based on 15 = 3 × 5 (Ternary × GILE Range)

ZONE              | FRACTION | PERCENTAGE | PRICE CHANGE | GILE SCORE
------------------|----------|------------|--------------|------------
Ultra-Great       | 1/225    | 0.444%     | > +20%       | > +2.0
Great             | 1/15     | 6.667%     | +5% to +20%  | +1.5 to +2.0
Good              | 3/15     | 20%        | +0.333% to +5% | +0.3 to +1.5
Indeterminate     | 3/15     | 20%        | -0.666% to +0.333% | -0.3 to +0.3
Bad               | 6/15     | 40%        | -5% to -0.666% | -0.3 to -1.5
Terrible          | 2/15     | 13.333%    | -10% to -5%  | -1.5 to -3.0
Ultra-Terrible    | 4/225    | 1.778%     | < -10%       | < -3.0

KEY INSIGHT:
Bad : Good = 2:1 (Pareto asymmetry preserved at all levels)
Terrible : Great = 2:1
Ultra-Terrible : Ultra-Great = 4:1 (squared at black swan level)
"""

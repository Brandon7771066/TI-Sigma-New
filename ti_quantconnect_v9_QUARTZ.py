"""
TI QUANTCONNECT V9 - QUARTZ CRYSTAL FILTERING
=============================================

HYPOTHESIS: Quartz crystals filter noise and amplify coherent signals.
We apply this principle algorithmically to stock market prediction.

KEY QUARTZ PROPERTIES (mapped to algorithm):
1. Piezoelectric Effect: Convert signal pressure → voltage (momentum → action)
2. High Q-Factor (10,000): Only resonate at specific frequencies (filter noise)
3. Resonance Frequency: 32,768 Hz in watches (we use market rhythm detection)
4. Curie Temperature: Above threshold, loses properties (regime detection)

QUARTZ FILTERING MECHANISMS:
- Crystal Clarity Filter: Only trade when signal is "crystalline" (high coherence)
- Resonance Gate: Only act when signal resonates with market rhythm
- Noise Suppression: High Q-factor filtering removes random fluctuations
- Piezo Amplification: Amplify signals that survive the filter

TARGET: Beat V3's 277.76% by filtering out noisy trades while amplifying high-quality signals.

Author: Brandon Emerick / BlissGene Therapeutics
Based on: TI Framework, Quartz PSI Amplification, V3 Trading Rules
"""

from AlgorithmImports import *
import numpy as np
from collections import deque
from datetime import datetime, timedelta

class TIQuartzCrystalAlgorithm(QCAlgorithm):
    """
    TI Framework algorithm with Quartz Crystal Filtering.
    
    Core Insight: Just as quartz filters electromagnetic noise,
    we filter market noise to find pure TI signals.
    """
    
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        
        self.symbols = [
            "SPY", "QQQ", "AAPL", "MSFT", "GOOGL", "TSLA", "NVDA", 
            "AMD", "META", "AMZN"
        ]
        
        self.data = {}
        for symbol in self.symbols:
            equity = self.AddEquity(symbol, Resolution.Daily)
            equity.SetDataNormalizationMode(DataNormalizationMode.Adjusted)
            self.data[symbol] = SymbolData(self)
        
        self.QUARTZ_Q_FACTOR = 10000  # Quality factor - higher = more selective
        self.QUARTZ_RESONANCE_THRESHOLD = 0.42  # Minimum coherence for resonance
        self.PIEZO_AMPLIFICATION = 1.5  # Signal amplification factor
        self.CURIE_TEMPERATURE = 2.0  # Volatility threshold (regime break)
        
        self.SACRED_MIN = -0.666
        self.SACRED_MAX = 0.333
        self.ULTRA_GREAT_THRESHOLD = 2.0
        self.POSITION_SIZE_PCT = 0.45  # Increased from 0.30 for more aggressive trading
        self.MAX_POSITIONS = 5  # Increased from 3 to allow more diversification
        self.STOP_LOSS_PCT = 0.08
        self.TAKE_PROFIT_PCT = 0.35  # Increased from 0.25 to let winners run longer
        
        self.entry_prices = {}
        self.crystal_clarity_scores = {}
        self.quartz_signals = {}
        self.filtered_trade_count = 0
        self.amplified_trade_count = 0
        
        self.trade_log = []
    
    def OnData(self, data):
        if self.IsWarmingUp:
            return
        
        # CRITICAL: Update price data for all symbols
        for symbol in self.symbols:
            if symbol in data and data[symbol]:
                self.data[symbol].Update(data[symbol].Close)
        
        spy_data = self.data.get("SPY")
        if spy_data and spy_data.IsReady():
            spy_history = spy_data.GetHistory()
            if len(spy_history) >= 20:
                spy_returns = np.diff(spy_history[-21:]) / spy_history[-21:-1] * 100
                market_volatility = np.std(spy_returns) if len(spy_returns) > 0 else 1.0
                
                if market_volatility > self.CURIE_TEMPERATURE:
                    self.Log(f"CURIE THRESHOLD: Market volatility {market_volatility:.2f} exceeds {self.CURIE_TEMPERATURE} - Quartz properties disabled")
                    return
        
        analysis_results = []
        
        for symbol in self.symbols:
            if symbol not in data or not data[symbol]:
                continue
            
            sym_data = self.data[symbol]
            if not sym_data.IsReady():
                continue
            
            history = sym_data.GetHistory()
            if len(history) < 60:
                continue
            
            ti_signal = self.CalculateTISignal(history, symbol)
            
            quartz_filtered = self.ApplyQuartzFilter(ti_signal, history, symbol)
            
            if quartz_filtered['passed_filter']:
                analysis_results.append({
                    'symbol': symbol,
                    'gile': quartz_filtered['amplified_gile'],
                    'zone': quartz_filtered['zone'],
                    'crystal_clarity': quartz_filtered['crystal_clarity'],
                    'resonance_strength': quartz_filtered['resonance_strength'],
                    'signal_type': quartz_filtered['signal_type'],
                    'raw_gile': ti_signal['gile']
                })
                self.amplified_trade_count += 1
            else:
                self.filtered_trade_count += 1
        
        analysis_results.sort(key=lambda x: abs(x['gile']), reverse=True)
        top_candidates = analysis_results[:self.MAX_POSITIONS]
        
        self.ManageExistingPositions(data)
        
        for candidate in top_candidates:
            symbol = candidate['symbol']
            gile = candidate['gile']
            zone = candidate['zone']
            
            if zone == "TRUE" and gile > 0:
                self.EnterPosition(symbol, "long", candidate)
            elif zone == "FALSE" and gile < 0:
                self.EnterPosition(symbol, "short", candidate)
    
    def CalculateTISignal(self, history: list, symbol: str) -> dict:
        """
        Calculate TI dimensions using evolved weights from cartography.
        
        Evolution found: t1=74.6%, t2=1.5%, t3=0%, lcc=23.8%
        """
        recent_3 = history[-3:]
        momentum = (recent_3[-1] - recent_3[0]) / recent_3[0] * 100 if recent_3[0] != 0 else 0
        t1 = momentum * 0.5  # Potential
        
        daily_return = (history[-1] - history[-2]) / history[-2] * 100 if history[-2] != 0 else 0
        t2 = daily_return  # Actualized
        
        sma20 = np.mean(history[-20:])
        sma50 = np.mean(history[-50:])
        t3 = (sma20 - sma50) / sma50 * 100 if sma50 != 0 else 0  # Contextual
        
        spy_data = self.data.get("SPY")
        if spy_data and spy_data.IsReady():
            spy_history = spy_data.GetHistory()
            if len(history) >= 20 and len(spy_history) >= 20:
                sym_returns = np.diff(history[-21:]) / history[-21:-1]
                spy_returns = np.diff(spy_history[-21:]) / spy_history[-21:-1]
                
                min_len = min(len(sym_returns), len(spy_returns))
                if min_len > 5:
                    try:
                        lcc = float(np.corrcoef(sym_returns[-min_len:], spy_returns[-min_len:])[0, 1])
                        if np.isnan(lcc):
                            lcc = 0.0
                    except:
                        lcc = 0.0
                else:
                    lcc = 0.0
            else:
                lcc = 0.0
        else:
            lcc = 0.0
        
        gile = 0.746 * t1 + 0.015 * t2 + 0.0 * t3 + 0.238 * lcc
        
        if gile > self.SACRED_MAX:
            zone = "TRUE"
        elif gile < self.SACRED_MIN:
            zone = "FALSE"
        else:
            zone = "TRALSE"
        
        return {
            't1': t1, 't2': t2, 't3': t3, 'lcc': lcc,
            'gile': gile, 'zone': zone
        }
    
    def ApplyQuartzFilter(self, ti_signal: dict, history: list, symbol: str) -> dict:
        """
        Apply quartz crystal filtering to the TI signal.
        
        QUARTZ FILTERING PRINCIPLES:
        1. Crystal Clarity: Signal must be clear (low noise ratio)
        2. Resonance Gate: Must resonate with market rhythm
        3. Q-Factor Filter: Only pass high-quality signals
        4. Piezo Amplification: Amplify signals that pass
        """
        
        returns = np.diff(history[-21:]) / history[-21:-1] * 100
        
        signal_power = abs(ti_signal['gile'])
        noise_power = np.std(returns) if len(returns) > 0 else 1.0
        snr = signal_power / (noise_power + 0.001)
        
        crystal_clarity = min(snr / 2.0, 1.0)
        self.crystal_clarity_scores[symbol] = crystal_clarity
        
        sma5 = np.mean(history[-5:])
        sma10 = np.mean(history[-10:])
        sma20 = np.mean(history[-20:])
        
        alignment = 0
        if sma5 > sma10 > sma20:  # Bullish alignment
            alignment = 1
        elif sma5 < sma10 < sma20:  # Bearish alignment
            alignment = -1
        
        signal_direction = 1 if ti_signal['gile'] > 0 else -1
        resonance_strength = abs(alignment * signal_direction)
        
        if abs(ti_signal['lcc']) > self.QUARTZ_RESONANCE_THRESHOLD:
            resonance_strength *= 1.3
        
        q_score = crystal_clarity * resonance_strength * (1 + abs(ti_signal['lcc']))
        
        normalized_q = min(q_score * self.QUARTZ_Q_FACTOR / 10000, 1.0)
        
        # Relaxed thresholds to allow more signals through while still filtering noise
        CLARITY_THRESHOLD = 0.20  # Reduced from 0.35
        RESONANCE_THRESHOLD = 0.15  # Reduced from 0.3
        Q_THRESHOLD = 0.15  # Reduced from 0.25
        
        # Allow TRALSE signals if they have high clarity (potential breakouts)
        passed_filter = (
            crystal_clarity >= CLARITY_THRESHOLD and
            resonance_strength >= RESONANCE_THRESHOLD and
            normalized_q >= Q_THRESHOLD and
            (ti_signal['zone'] != "TRALSE" or crystal_clarity > 0.5)  # High clarity TRALSE can pass
        )
        
        if passed_filter:
            amplified_gile = ti_signal['gile'] * self.PIEZO_AMPLIFICATION * (1 + crystal_clarity)
        else:
            amplified_gile = ti_signal['gile']
        
        if crystal_clarity > 0.7 and abs(ti_signal['gile']) > self.ULTRA_GREAT_THRESHOLD:
            signal_type = "ULTRA_GREAT_CRYSTALLINE"
        elif crystal_clarity > 0.5 and passed_filter:
            signal_type = "HIGH_CLARITY"
        elif passed_filter:
            signal_type = "FILTERED_PASS"
        else:
            signal_type = "FILTERED_OUT"
        
        self.quartz_signals[symbol] = {
            'crystal_clarity': crystal_clarity,
            'resonance_strength': resonance_strength,
            'q_score': normalized_q,
            'signal_type': signal_type
        }
        
        return {
            'passed_filter': passed_filter,
            'crystal_clarity': crystal_clarity,
            'resonance_strength': resonance_strength,
            'q_score': normalized_q,
            'amplified_gile': amplified_gile,
            'zone': ti_signal['zone'],
            'signal_type': signal_type
        }
    
    def ManageExistingPositions(self, data):
        """Manage exits with quartz-enhanced clarity"""
        for symbol, entry_price in list(self.entry_prices.items()):
            if symbol not in data or not data[symbol]:
                continue
            
            current_price = float(data[symbol].Close)
            pnl_pct = (current_price - entry_price) / entry_price
            
            clarity = self.crystal_clarity_scores.get(symbol, 0.5)
            adjusted_stop = self.STOP_LOSS_PCT * (1 + clarity * 0.3)
            adjusted_profit = self.TAKE_PROFIT_PCT * (1 - clarity * 0.2)
            
            if pnl_pct <= -adjusted_stop:
                self.Liquidate(symbol)
                del self.entry_prices[symbol]
                self.Log(f"STOP LOSS: {symbol} at {pnl_pct:.2%} (adjusted: {adjusted_stop:.2%})")
            
            elif pnl_pct >= adjusted_profit:
                self.Liquidate(symbol)
                del self.entry_prices[symbol]
                self.Log(f"TAKE PROFIT: {symbol} at {pnl_pct:.2%} (adjusted: {adjusted_profit:.2%})")
            
            elif symbol in self.quartz_signals:
                signal = self.quartz_signals[symbol]
                if signal['signal_type'] == "FILTERED_OUT" and pnl_pct > 0.05:
                    self.Liquidate(symbol)
                    del self.entry_prices[symbol]
                    self.Log(f"CLARITY EXIT: {symbol} signal degraded, taking {pnl_pct:.2%} profit")
    
    def EnterPosition(self, symbol: str, direction: str, candidate: dict):
        """Enter position with quartz-enhanced sizing"""
        if symbol in self.entry_prices:
            return
        
        if len(self.entry_prices) >= self.MAX_POSITIONS:
            return
        
        clarity = candidate['crystal_clarity']
        resonance = candidate['resonance_strength']
        
        size_multiplier = 1.0 + (clarity * 0.4) + (resonance * 0.3)  # Higher bonuses
        position_size = self.POSITION_SIZE_PCT * size_multiplier
        position_size = min(position_size, 0.60)  # Increased cap from 0.40 to 0.60
        
        if direction == "long":
            self.SetHoldings(symbol, position_size)
        else:
            self.SetHoldings(symbol, -position_size)
        
        self.entry_prices[symbol] = float(self.Securities[symbol].Price)
        
        self.Log(f"QUARTZ ENTRY: {symbol} {direction.upper()} @ ${self.entry_prices[symbol]:.2f}")
        self.Log(f"  Crystal Clarity: {clarity:.3f}")
        self.Log(f"  Resonance: {resonance:.3f}")
        self.Log(f"  Signal Type: {candidate['signal_type']}")
        self.Log(f"  GILE: {candidate['gile']:.4f} (raw: {candidate['raw_gile']:.4f})")
    
    def OnEndOfAlgorithm(self):
        """Report quartz filtering effectiveness"""
        total_signals = self.filtered_trade_count + self.amplified_trade_count
        filter_rate = self.filtered_trade_count / total_signals if total_signals > 0 else 0
        
        self.Log("="*60)
        self.Log("QUARTZ CRYSTAL FILTERING REPORT")
        self.Log("="*60)
        self.Log(f"Total Signals Analyzed: {total_signals}")
        self.Log(f"Signals Filtered Out: {self.filtered_trade_count} ({filter_rate:.1%})")
        self.Log(f"Signals Amplified: {self.amplified_trade_count} ({1-filter_rate:.1%})")
        self.Log(f"")
        self.Log("QUARTZ PARAMETERS:")
        self.Log(f"  Q-Factor: {self.QUARTZ_Q_FACTOR}")
        self.Log(f"  Resonance Threshold: {self.QUARTZ_RESONANCE_THRESHOLD}")
        self.Log(f"  Piezo Amplification: {self.PIEZO_AMPLIFICATION}x")
        self.Log(f"  Curie Temperature: {self.CURIE_TEMPERATURE}")
        self.Log("="*60)


class SymbolData:
    """Symbol data handler for price history"""
    
    def __init__(self, algorithm, window_size=60):
        self.algorithm = algorithm
        self.window_size = window_size
        self.prices = deque(maxlen=window_size)
    
    def Update(self, price):
        self.prices.append(float(price))
    
    def IsReady(self):
        return len(self.prices) >= self.window_size
    
    def GetHistory(self):
        return list(self.prices)

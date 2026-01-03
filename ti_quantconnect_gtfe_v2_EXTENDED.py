"""
TI QUANTCONNECT GTFE V2.0 - EXTENDED GRAND TRALSE FIELD EQUATION
================================================================

The MASTER Algorithm incorporating ALL TI Theory Extensions discovered through testing.

GTFE v2.0 EQUATION:
    Ψ_TI = Filter(Q) × Amplify(P) × ∫∫∫ [w₁·T(t₁) + w₂·J(t₂) + w₃·C(t₃)] · GILE · MR · dω dt

EXTENSIONS INCORPORATED:
1. EVOLVED WEIGHTS (from TI Performance Cartography)
   - t1 (Potential): 74.6% (was 25%) - MAJOR CORRECTION
   - t2 (Jeff Moment): 1.5% (was 35%) - Observation matters LESS than thought
   - t3 (Cosmological): 0% (was 25%) - ELIMINATED
   - LCC (Love): 23.8% (was 15%) - Correlation matters MORE

2. QUARTZ CRYSTAL FILTERING
   - Crystal Clarity (SNR): Filter noisy signals
   - Q-Factor Gate: Only high-quality signals pass
   - Resonance Detection: Market rhythm alignment

3. PIEZO AMPLIFICATION
   - Amplify signals that survive filtering by 1.5x

4. TI TENSOR FLOW
   - Velocity (d(GILE)/dt): First derivative for timing
   - Curvature (d²(GILE)/dt²): Second derivative for regime transitions

5. CURIE TEMPERATURE
   - Volatility threshold above which Quartz properties disable
   - Regime break detection

6. MYRION RESOLUTION
   - Detect and handle market contradictions
   - Tralse (TRUE/FALSE/INDETERMINATE) state classification

TARGET: Beat V3's 277.76% return by 50%+ (target: 400%+)

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 30, 2025
Based on: GTFE Theory Unification Test findings
"""

from AlgorithmImports import *
import numpy as np
from collections import deque

class TIFrameworkGTFEv2Algorithm(QCAlgorithm):
    """
    GTFE v2.0: The Extended Grand Tralse Field Equation
    
    Incorporates all discoveries from the Theory Unification Test:
    - Evolved weights from evolutionary optimization
    - Quartz crystal filtering for noise reduction
    - Tensor flow for timing signals
    - Curie temperature for regime detection
    """
    
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        
        self.EVOLVED_WEIGHTS = {
            't1_potential': 0.746,
            't2_jeff_moment': 0.015,
            't3_cosmological': 0.0,
            'lcc_love': 0.238
        }
        
        self.QUARTZ_Q_FACTOR = 10000
        self.CRYSTAL_CLARITY_THRESHOLD = 0.35
        self.RESONANCE_THRESHOLD = 0.30
        self.PIEZO_AMPLIFICATION = 1.5
        
        self.CURIE_TEMPERATURE = 2.5
        self.REGIME_BREAK_THRESHOLD = 3.0
        
        self.VELOCITY_WEIGHT = 0.15
        self.CURVATURE_WEIGHT = 0.10
        
        self.SACRED_MIN = -0.666
        self.SACRED_MAX = 0.333
        self.TRUE_THRESHOLD = 0.5
        self.FALSE_THRESHOLD = -0.5
        
        self.MAX_POSITION = 0.15
        self.MAX_POSITIONS = 4
        self.STOP_LOSS_PCT = 0.07
        self.TAKE_PROFIT_PCT = 0.30
        
        self.symbols_list = [
            "SPY", "QQQ", "AAPL", "MSFT", "GOOGL", "TSLA", "NVDA",
            "AMD", "META", "AMZN"
        ]
        
        self.symbols = []
        self.data = {}
        for ticker in self.symbols_list:
            equity = self.AddEquity(ticker, Resolution.Daily)
            equity.SetDataNormalizationMode(DataNormalizationMode.Adjusted)
            self.symbols.append(equity.Symbol)
            self.data[ticker] = SymbolData(self)
        
        self.gile_history = {ticker: deque(maxlen=30) for ticker in self.symbols_list}
        self.entry_prices = {}
        
        self.trade_count = 0
        self.winning_trades = 0
        self.filtered_trades = 0
        self.amplified_trades = 0
        self.curie_blocks = 0
        self.tensor_signals = 0
        
        self.Schedule.On(
            self.DateRules.EveryDay("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.GTFEv2Rebalance
        )
    
    def OnData(self, data):
        """Update price data for all symbols - CRITICAL for SymbolData to work"""
        for ticker in self.symbols_list:
            symbol = self.Symbol(ticker)
            if symbol in data and data[symbol]:
                self.data[ticker].Update(data[symbol].Close)
    
    def CalculateT1Potential(self, history: list) -> float:
        """
        t1 - Quantum Potential (Pre-observation)
        
        Evolution found this should be 74.6% of the signal!
        Measures momentum and potential energy buildup.
        """
        if len(history) < 5:
            return 0.0
        
        momentum_3d = (history[-1] - history[-3]) / history[-3] * 100 if history[-3] != 0 else 0
        momentum_5d = (history[-1] - history[-5]) / history[-5] * 100 if history[-5] != 0 else 0
        
        returns = np.diff(history[-5:]) / history[-5:-1] * 100
        volatility = np.std(returns) if len(returns) > 1 else 1.0
        
        potential = (momentum_3d * 0.6 + momentum_5d * 0.4) * (1 + volatility * 0.05)
        
        return float(np.clip(potential * 0.3, -3, 3))
    
    def CalculateT2JeffMoment(self, history: list) -> float:
        """
        t2 - Jeff Moment (Current Observation)
        
        Evolution found this should only be 1.5% of the signal!
        The "present moment" matters much less than we thought.
        """
        if len(history) < 2:
            return 0.0
        
        daily_return = (history[-1] - history[-2]) / history[-2] * 100 if history[-2] != 0 else 0
        
        return float(np.clip(daily_return * 0.2, -2, 2))
    
    def CalculateT3Cosmological(self, history: list) -> float:
        """
        t3 - Cosmological Context (Long-term Evolution)
        
        Evolution found this should be 0% - ELIMINATED!
        Long-term trends don't predict short-term movements in our timeframe.
        """
        return 0.0
    
    def CalculateLCCLove(self, ticker: str, history: list) -> float:
        """
        LCC - Love Correlation Component
        
        Evolution found this should be 23.8% of the signal.
        Cross-asset correlation (market entanglement) matters!
        """
        spy_data = self.data.get("SPY")
        if not spy_data or not spy_data.IsReady():
            return 0.0
        
        spy_history = spy_data.GetHistory()
        if len(history) < 21 or len(spy_history) < 21:
            return 0.0
        
        try:
            sym_returns = np.diff(history[-21:]) / history[-21:-1]
            spy_returns = np.diff(spy_history[-21:]) / spy_history[-21:-1]
            
            min_len = min(len(sym_returns), len(spy_returns))
            if min_len < 10:
                return 0.0
            
            correlation = float(np.corrcoef(sym_returns[-min_len:], spy_returns[-min_len:])[0, 1])
            if np.isnan(correlation):
                return 0.0
            
            spy_momentum = (spy_history[-1] - spy_history[-5]) / spy_history[-5] * 100 if spy_history[-5] != 0 else 0
            
            love_signal = correlation * spy_momentum * 0.1 if spy_momentum > 0 else (1 - abs(correlation)) * 0.5
            
            return float(np.clip(love_signal, -1.5, 1.5))
            
        except Exception:
            return 0.0
    
    def CalculateCrystalClarity(self, gile: float, history: list) -> float:
        """
        Quartz Crystal Clarity Filter - Signal-to-Noise Ratio
        
        Higher clarity = more crystalline signal (less noise)
        """
        if len(history) < 21:
            return 0.0
        
        returns = np.diff(history[-21:]) / history[-21:-1] * 100
        noise = np.std(returns) if len(returns) > 0 else 1.0
        
        snr = abs(gile) / (noise + 0.001)
        
        clarity = min(snr / 2.0, 1.0)
        
        return float(clarity)
    
    def CalculateResonanceStrength(self, gile: float, history: list) -> float:
        """
        Quartz Resonance Gate - Does signal resonate with market rhythm?
        
        Measures alignment of signal direction with moving average structure.
        """
        if len(history) < 20:
            return 0.0
        
        sma5 = np.mean(history[-5:])
        sma10 = np.mean(history[-10:])
        sma20 = np.mean(history[-20:])
        
        alignment = 0
        if sma5 > sma10 > sma20:
            alignment = 1.0
        elif sma5 < sma10 < sma20:
            alignment = -1.0
        elif sma5 > sma10 or sma5 > sma20:
            alignment = 0.5 if gile > 0 else -0.5
        elif sma5 < sma10 or sma5 < sma20:
            alignment = -0.5 if gile < 0 else 0.5
        
        signal_direction = 1 if gile > 0 else -1
        resonance = alignment * signal_direction
        
        return float(np.clip(resonance, 0, 1))
    
    def ApplyQuartzFilter(self, gile: float, history: list) -> dict:
        """
        Apply Quartz Crystal Filtering
        
        Returns:
            passed_filter: Whether signal passes quality gate
            amplified_gile: Signal after filtering and amplification
            crystal_clarity: Clarity score
            resonance_strength: Resonance score
        """
        clarity = self.CalculateCrystalClarity(gile, history)
        resonance = self.CalculateResonanceStrength(gile, history)
        
        q_factor = clarity * resonance * (1 + abs(gile) * 0.1)
        
        passed_filter = (clarity >= self.CRYSTAL_CLARITY_THRESHOLD and 
                        resonance >= self.RESONANCE_THRESHOLD)
        
        if passed_filter:
            amplified_gile = gile * self.PIEZO_AMPLIFICATION * (1 + clarity * 0.5)
            self.amplified_trades += 1
        else:
            amplified_gile = gile * 0.5
            self.filtered_trades += 1
        
        return {
            'passed_filter': passed_filter,
            'amplified_gile': float(amplified_gile),
            'crystal_clarity': float(clarity),
            'resonance_strength': float(resonance),
            'q_factor': float(q_factor)
        }
    
    def CalculateTensorFlow(self, ticker: str, current_gile: float) -> dict:
        """
        TI Tensor Flow - Differential dynamics of GILE
        
        Velocity: d(GILE)/dt - rate of change
        Curvature: d²(GILE)/dt² - acceleration/regime transitions
        """
        gile_hist = list(self.gile_history.get(ticker, []))
        
        if len(gile_hist) < 3:
            return {
                'velocity': 0.0,
                'curvature': 0.0,
                'tensor_signal': 0.0
            }
        
        velocity = current_gile - gile_hist[-1] if len(gile_hist) >= 1 else 0.0
        
        if len(gile_hist) >= 2:
            prev_velocity = gile_hist[-1] - gile_hist[-2]
            curvature = velocity - prev_velocity
        else:
            curvature = 0.0
        
        tensor_signal = (
            self.VELOCITY_WEIGHT * velocity +
            self.CURVATURE_WEIGHT * curvature
        )
        
        if abs(tensor_signal) > 0.5:
            self.tensor_signals += 1
        
        return {
            'velocity': float(velocity),
            'curvature': float(curvature),
            'tensor_signal': float(tensor_signal)
        }
    
    def CheckCurieTemperature(self) -> bool:
        """
        Curie Temperature Check - Is market volatility too high?
        
        Above Curie temperature, Quartz properties disable.
        This represents regime breaks where normal patterns fail.
        """
        spy_data = self.data.get("SPY")
        if not spy_data or not spy_data.IsReady():
            return False
        
        spy_history = spy_data.GetHistory()
        if len(spy_history) < 21:
            return False
        
        returns = np.diff(spy_history[-21:]) / spy_history[-21:-1] * 100
        volatility = np.std(returns) if len(returns) > 0 else 0.0
        
        if volatility > self.CURIE_TEMPERATURE:
            self.curie_blocks += 1
            return True
        
        return False
    
    def CalculateMyrionResolution(self, t1: float, t2: float, lcc: float, 
                                   tensor: dict) -> dict:
        """
        Myrion Resolution - Detect and resolve market contradictions
        
        When signals disagree, we're in TRALSE state.
        """
        signals = [t1, t2, lcc, tensor['tensor_signal']]
        signs = [np.sign(s) for s in signals if s != 0]
        
        if len(signs) == 0:
            return {
                'status': 'NEUTRAL',
                'resolution_factor': 1.0,
                'agreement_level': 0.0
            }
        
        positive = sum(1 for s in signs if s > 0)
        negative = sum(1 for s in signs if s < 0)
        
        if positive == len(signs):
            return {
                'status': 'ALIGNED_BULLISH',
                'resolution_factor': 1.2,
                'agreement_level': 1.0
            }
        elif negative == len(signs):
            return {
                'status': 'ALIGNED_BEARISH',
                'resolution_factor': 1.2,
                'agreement_level': 1.0
            }
        elif abs(positive - negative) >= len(signs) - 1:
            return {
                'status': 'PARTIAL_AGREEMENT',
                'resolution_factor': 1.0,
                'agreement_level': 0.7
            }
        else:
            return {
                'status': 'CONTRADICTION',
                'resolution_factor': 0.6,
                'agreement_level': 0.3
            }
    
    def CalculateGTFEv2(self, ticker: str, history: list) -> dict:
        """
        The Complete GTFE v2.0 Calculation
        
        Ψ_TI = Filter(Q) × Amplify(P) × ∫∫∫ [w₁·T(t₁) + w₂·J(t₂) + w₃·C(t₃)] · GILE · MR · dω dt
        """
        t1 = self.CalculateT1Potential(history)
        t2 = self.CalculateT2JeffMoment(history)
        t3 = self.CalculateT3Cosmological(history)
        lcc = self.CalculateLCCLove(ticker, history)
        
        raw_gile = (
            self.EVOLVED_WEIGHTS['t1_potential'] * t1 +
            self.EVOLVED_WEIGHTS['t2_jeff_moment'] * t2 +
            self.EVOLVED_WEIGHTS['t3_cosmological'] * t3 +
            self.EVOLVED_WEIGHTS['lcc_love'] * lcc
        )
        
        self.gile_history[ticker].append(raw_gile)
        
        tensor = self.CalculateTensorFlow(ticker, raw_gile)
        
        gile_with_tensor = raw_gile + tensor['tensor_signal']
        
        quartz = self.ApplyQuartzFilter(gile_with_tensor, history)
        
        mr = self.CalculateMyrionResolution(t1, t2, lcc, tensor)
        
        psi_ti = quartz['amplified_gile'] * mr['resolution_factor']
        
        if psi_ti > self.TRUE_THRESHOLD:
            tralse_state = 'TRUE'
        elif psi_ti < self.FALSE_THRESHOLD:
            tralse_state = 'FALSE'
        else:
            tralse_state = 'TRALSE'
        
        if psi_ti > 2.0:
            zone = 'ULTRA_GREAT'
        elif psi_ti > 1.0:
            zone = 'GREAT'
        elif psi_ti > 0.3:
            zone = 'GOOD'
        elif psi_ti > -0.3:
            zone = 'INDETERMINATE'
        elif psi_ti > -1.0:
            zone = 'BAD'
        else:
            zone = 'TERRIBLE'
        
        return {
            'psi_ti': float(psi_ti),
            'raw_gile': float(raw_gile),
            't1_potential': float(t1),
            't2_jeff_moment': float(t2),
            't3_cosmological': float(t3),
            'lcc_love': float(lcc),
            'tensor': tensor,
            'quartz': quartz,
            'myrion': mr,
            'tralse_state': tralse_state,
            'zone': zone
        }
    
    def GTFEv2Rebalance(self):
        """Main rebalancing logic using GTFE v2.0"""
        if self.IsWarmingUp:
            return
        
        if self.CheckCurieTemperature():
            self.Log("CURIE BLOCK: Market volatility exceeds threshold - reducing positions")
            for symbol in self.Portfolio.Keys:
                if self.Portfolio[symbol].Invested:
                    current_size = self.Portfolio[symbol].Quantity
                    self.SetHoldings(symbol, self.Portfolio[symbol].HoldingsValue / self.Portfolio.TotalPortfolioValue * 0.5)
            return
        
        signals = {}
        
        for ticker in self.symbols_list:
            sym_data = self.data.get(ticker)
            if not sym_data or not sym_data.IsReady():
                continue
            
            history = sym_data.GetHistory()
            if len(history) < 60:
                continue
            
            gtfe = self.CalculateGTFEv2(ticker, history)
            signals[ticker] = gtfe
        
        if not signals:
            return
        
        ranked = sorted(signals.items(), key=lambda x: x[1]['psi_ti'], reverse=True)
        
        for ticker, sig in signals.items():
            symbol = self.Symbol(ticker)
            if not self.Portfolio[symbol].Invested:
                continue
            
            holding = self.Portfolio[symbol]
            entry_price = self.entry_prices.get(ticker, holding.AveragePrice)
            current_price = self.Securities[symbol].Price
            
            if entry_price > 0:
                pnl_pct = (current_price - entry_price) / entry_price
                
                if pnl_pct <= -self.STOP_LOSS_PCT:
                    self.Liquidate(symbol)
                    self.trade_count += 1
                    if ticker in self.entry_prices:
                        del self.entry_prices[ticker]
                    continue
                
                if pnl_pct >= self.TAKE_PROFIT_PCT:
                    self.Liquidate(symbol)
                    self.trade_count += 1
                    self.winning_trades += 1
                    if ticker in self.entry_prices:
                        del self.entry_prices[ticker]
                    continue
            
            should_exit = False
            
            if sig['tralse_state'] == 'FALSE':
                should_exit = True
            elif sig['zone'] == 'ULTRA_GREAT' and pnl_pct > 0.1:
                should_exit = True
            elif sig['myrion']['status'] == 'CONTRADICTION':
                should_exit = True
            elif not sig['quartz']['passed_filter'] and sig['psi_ti'] < 0:
                should_exit = True
            
            if should_exit:
                self.Liquidate(symbol)
                self.trade_count += 1
                if holding.UnrealizedProfit > 0:
                    self.winning_trades += 1
                if ticker in self.entry_prices:
                    del self.entry_prices[ticker]
        
        current_positions = sum(1 for s in self.Portfolio.Values if s.Invested)
        available_slots = self.MAX_POSITIONS - current_positions
        
        buy_candidates = [
            (ticker, sig) for ticker, sig in ranked
            if sig['tralse_state'] == 'TRUE' and sig['quartz']['passed_filter']
        ][:available_slots]
        
        for ticker, sig in buy_candidates:
            symbol = self.Symbol(ticker)
            
            if self.Portfolio[symbol].Invested:
                continue
            
            if sig['zone'] in ['GREAT', 'ULTRA_GREAT']:
                position_size = self.MAX_POSITION * 1.0
            elif sig['zone'] == 'GOOD':
                position_size = self.MAX_POSITION * 0.7
            else:
                position_size = self.MAX_POSITION * 0.5
            
            position_size *= sig['quartz']['q_factor']
            
            if sig['myrion']['status'] == 'ALIGNED_BULLISH':
                position_size *= 1.1
            elif sig['myrion']['status'] == 'PARTIAL_AGREEMENT':
                position_size *= 0.9
            
            position_size = min(position_size, self.MAX_POSITION)
            
            self.SetHoldings(symbol, position_size)
            self.entry_prices[ticker] = self.Securities[symbol].Price
            self.trade_count += 1
    
    def OnEndOfAlgorithm(self):
        """Log final statistics"""
        win_rate = self.winning_trades / max(self.trade_count, 1) * 100
        
        self.Log("=" * 60)
        self.Log("GTFE V2.0 EXTENDED - FINAL STATISTICS")
        self.Log("=" * 60)
        self.Log(f"Total Trades: {self.trade_count}")
        self.Log(f"Winning Trades: {self.winning_trades}")
        self.Log(f"Win Rate: {win_rate:.1f}%")
        self.Log(f"Quartz Filtered: {self.filtered_trades}")
        self.Log(f"Quartz Amplified: {self.amplified_trades}")
        self.Log(f"Curie Blocks: {self.curie_blocks}")
        self.Log(f"Tensor Signals: {self.tensor_signals}")
        self.Log("=" * 60)
        self.Log("EVOLVED WEIGHTS USED:")
        for key, val in self.EVOLVED_WEIGHTS.items():
            self.Log(f"  {key}: {val:.1%}")
        self.Log("=" * 60)


class SymbolData:
    """Helper class for per-symbol data management"""
    
    def __init__(self, algorithm):
        self.algorithm = algorithm
        self.history = deque(maxlen=100)
        self.ready = False
    
    def Update(self, price: float):
        self.history.append(float(price))
        if len(self.history) >= 60:
            self.ready = True
    
    def IsReady(self) -> bool:
        return self.ready and len(self.history) >= 60
    
    def GetHistory(self) -> list:
        return list(self.history)

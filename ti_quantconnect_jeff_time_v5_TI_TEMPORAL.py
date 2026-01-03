"""
TI FRAMEWORK V5: JEFF TIME 3D - THE TI TEMPORAL SYNTHESIS
==========================================================
December 2025 | Brandon Emerick

KLETETSCHKA'S 3D TIME (K's Framework):
- t₁: Quantum scale (Planck phenomena)
- t₂: Interaction scale (particle physics) 
- t₃: Cosmological scale (universe evolution)

TI'S TRANSFORMATION (Making It Our Own):
=========================================

K says time has 3 dimensions. TI says: YES, but those dimensions correspond
to CONSCIOUSNESS SCALES, not just physics scales!

TI TEMPORAL DIMENSIONS:
-----------------------
τ_I (I-Cell Time) = Quantum/micro correlations [K's t₁]
    → The individual i-cell's reading speed through photon field
    → In trading: ultra-short momentum (1-3 day patterns)
    → Captures: Trader psychology, micro-structure

τ_J (Jeff Moment) = Interaction/present fiction [K's t₂]  
    → The collapse of possibility into action
    → In trading: TODAY's price action
    → Captures: The only "real" moment (as fiction!)

τ_C (CCC Time) = Cosmological/universal standard [K's t₃]
    → The background clock that coordinates all i-cells
    → In trading: Long-term trend context (20-50 days)
    → Captures: Secular market forces, institutional flows

LOVE DIMENSION (TI's Addition):
-------------------------------
L (Love Entanglement) = The binding force across time dimensions
    → Not a 4th time dimension, but what CONNECTS the three
    → In trading: Cross-asset correlation
    → Captures: Market-wide coherence, systemic risk/opportunity

THE UNIFIED FORMULA:
--------------------
GILE_temporal = w_I·τ_I + w_J·τ_J + w_C·τ_C + w_L·L

Where Love (L) MODULATES the temporal weights, not just adds to them.
When Love is high (market coherence), temporal signals amplify each other.
When Love is low (fragmentation), each dimension stands alone.

SYNERGY MECHANISM:
------------------
Temporal Coherence = Agreement across τ_I, τ_J, τ_C
When Coherent + High Love → SYNERGY BOOST (nonlinear amplification)
This captures your insight: complementary aspects of reality that boost together.

TEST PERIODS:
- 5-year: 2020-2024 (recent, includes COVID, AI boom)
- 10-year: 2015-2024 (includes 2018 volatility, QE end)
- 20-year: 2005-2024 (includes 2008 crisis, full cycles)

COPY EVERYTHING BELOW FOR QUANTCONNECT:
"""

# ============================================================================
# PASTE THIS INTO QUANTCONNECT:
# ============================================================================

try:
    from AlgorithmImports import *
    IN_QUANTCONNECT = True
except ImportError:
    IN_QUANTCONNECT = False
    class QCAlgorithm:
        pass

import numpy as np

class TIJeffTime3DV5Algorithm(QCAlgorithm):
    """
    TI Framework V5: Jeff Time 3D - TI Temporal Synthesis
    
    K's 3D time made TI's own:
    - τ_I (I-Cell): Micro correlations (1-3 day)
    - τ_J (Jeff): Present moment fiction (today)
    - τ_C (CCC): Universal time standard (20-50 day)
    - L (Love): Binding force that creates synergy
    """
    
    # =========================================================================
    # SACRED PD CONSTANTS (UNCHANGED - THIS WORKS!)
    # =========================================================================
    
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
    
    # =========================================================================
    # TI TEMPORAL PARAMETERS (THE UPDATE!)
    # =========================================================================
    
    # τ_I (I-Cell Time): Individual consciousness reading speed
    # Short lookback captures micro-structure
    TAU_I_LOOKBACK = 3  # 3 days - quantum/micro scale
    TAU_I_WEIGHT = 0.25  # Base weight
    
    # τ_J (Jeff Moment): The present as lived fiction
    # TODAY is all we can ever know (highest base weight)
    TAU_J_WEIGHT = 0.35  # Highest - present is primary
    
    # τ_C (CCC Time): Universal coordination standard
    # Long lookback captures secular trends
    TAU_C_SHORT = 20   # Intention horizon
    TAU_C_LONG = 50    # Full CCC window
    TAU_C_WEIGHT = 0.25  # Cosmic context
    
    # L (Love): The binding force
    # Love MODULATES the other dimensions, not just adds
    LOVE_WEIGHT = 0.15  # Direct contribution
    LOVE_SYNERGY_BOOST = 0.20  # Boost when love + temporal alignment
    
    # SYNERGY: When all dimensions agree
    SYNERGY_THRESHOLD = 0.5  # Minimum agreement for synergy
    SYNERGY_MULTIPLIER = 1.25  # 25% boost for full synergy
    
    def initialize(self):
        """Initialize with configurable test period"""
        
        # =====================================================================
        # CHANGE THESE FOR DIFFERENT TEST PERIODS:
        # =====================================================================
        
        # 5-YEAR TEST (2020-2024) - Default
        self.set_start_date(2020, 1, 1)
        self.set_end_date(2024, 12, 31)
        
        # 10-YEAR TEST (2015-2024) - Uncomment to use
        # self.set_start_date(2015, 1, 1)
        # self.set_end_date(2024, 12, 31)
        
        # 20-YEAR TEST (2005-2024) - Uncomment to use
        # self.set_start_date(2005, 1, 1)
        # self.set_end_date(2024, 12, 31)
        
        # =====================================================================
        
        self.set_cash(100000)
        
        # Universe: Diverse for Love dimension measurement
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
        
        # Price history for temporal calculations
        self.price_history = {symbol: [] for symbol in self.symbols}
        self.gile_history = {symbol: [] for symbol in self.symbols}
        
        # Temporal scores storage
        self.temporal_scores = {symbol: {
            'tau_i': 0,
            'tau_j': 0,
            'tau_c': 0,
            'love': 0,
            'synergy': False,
            'unified': 0
        } for symbol in self.symbols}
        
        self.max_history = 60
        self.max_position = 0.12  # 12% per position
        
        self.set_warmup(60, Resolution.DAILY)
        
        self.schedule.on(
            self.date_rules.every_day(),
            self.time_rules.after_market_open("SPY", 30),
            self.ti_temporal_rebalance
        )
        
        # Performance tracking
        self.trade_count = 0
        self.winning_trades = 0
        self.synergy_trades = 0
    
    def price_to_gile(self, pct_change: float) -> float:
        """
        Convert price change to GILE score using PD (Pareto Distribution).
        THIS IS UNCHANGED - IT WORKS!
        """
        if pct_change > self.ULTRA_GREAT_THRESHOLD:
            excess = pct_change - self.ULTRA_GREAT_THRESHOLD
            return 2.0 + np.log1p(excess / 20) * 0.5
        elif pct_change < self.ULTRA_TERRIBLE_THRESHOLD:
            excess = abs(pct_change) - abs(self.ULTRA_TERRIBLE_THRESHOLD)
            return -3.0 - np.log1p(excess / 10) * 0.5
        elif pct_change > self.GREAT_THRESHOLD:
            return 1.5 + (pct_change - 5) / (20 - 5) * 0.5
        elif pct_change < self.TERRIBLE_THRESHOLD:
            return -3.0 + (pct_change + 10) / (10 - 5) * 1.5
        elif pct_change > self.SACRED_MAX:
            return 0.3 + (pct_change - 0.333) / (5 - 0.333) * 1.2
        elif pct_change < self.SACRED_MIN:
            return -1.5 + (pct_change + 5) / (5 - 0.666) * 1.2
        else:
            if pct_change < 0:
                return (pct_change / 0.666) * 0.3
            else:
                return (pct_change / 0.333) * 0.3
    
    # =========================================================================
    # TI TEMPORAL DIMENSIONS (THE NEW STUFF!)
    # =========================================================================
    
    def calculate_tau_i(self, symbol) -> float:
        """
        τ_I (I-Cell Time): Individual i-cell reading speed through photon field.
        
        This is K's t₁ (quantum scale) made TI:
        - Each i-cell reads correlations at its own pace
        - Fast readers = high volatility traders
        - Slow readers = patient investors
        
        In trading: 3-day micro-momentum captures this scale.
        """
        history = self.price_history.get(symbol, [])
        if len(history) < self.TAU_I_LOOKBACK:
            return 0.0
        
        recent = history[-self.TAU_I_LOOKBACK:]
        
        # Micro-momentum: how fast is the i-cell "reading" change?
        momentum = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] != 0 else 0
        
        # Volatility captures reading "jitter" - high vol = uncertain reading
        returns = np.diff(recent) / recent[:-1] * 100
        volatility = float(np.std(returns)) if len(returns) > 1 else 0
        
        # Low volatility amplifies momentum (clearer reading)
        # High volatility dampens it (noisy reading)
        clarity_factor = 1.0 / (1.0 + volatility * 0.1)
        
        tau_i_score = self.price_to_gile(momentum) * clarity_factor
        
        return float(np.clip(tau_i_score, -3, 3))
    
    def calculate_tau_j(self, symbol) -> float:
        """
        τ_J (Jeff Moment): The present as lived fiction.
        
        This is K's t₂ (interaction scale) made TI:
        - The present cannot be spoken of or directly experienced
        - Yet it IS all we can ever know - AS A FICTION
        - The "Jeff Moment" is when fiction collapses into trade action
        
        In trading: TODAY's price change is the only "real" data.
        We weight this highest because it's our only access point.
        """
        history = self.price_history.get(symbol, [])
        if len(history) < 2:
            return 0.0
        
        # Today's change: the fiction we're living
        today_change = (history[-1] - history[-2]) / history[-2] * 100 if history[-2] != 0 else 0
        
        # The Jeff Fiction includes expectation deviation
        # Reality often "surprises" the fiction - this captures it
        if len(history) >= 3:
            yesterday_change = (history[-2] - history[-3]) / history[-3] * 100 if history[-3] != 0 else 0
            surprise = today_change - yesterday_change
            
            # Positive surprise = reality exceeding fiction (bullish)
            # Negative surprise = reality falling short (bearish)
            surprise_bonus = 0.1 * np.sign(surprise) * min(abs(surprise), 2)
        else:
            surprise_bonus = 0
        
        tau_j_score = self.price_to_gile(today_change) + surprise_bonus
        
        return float(np.clip(tau_j_score, -3, 3))
    
    def calculate_tau_c(self, symbol) -> float:
        """
        τ_C (CCC Time): The universal coordination standard.
        
        This is K's t₃ (cosmological scale) made TI:
        - CCC provides the background clock for all i-cells
        - Without CCC, each i-cell would have completely independent time
        - CCC creates market-wide coordination
        
        In trading: 20/50 day trends capture institutional/secular forces.
        """
        history = self.price_history.get(symbol, [])
        if len(history) < self.TAU_C_LONG:
            return 0.0
        
        # Short-term coordination (20-day)
        sma_short = float(np.mean(history[-self.TAU_C_SHORT:]))
        
        # Long-term universal standard (50-day)
        sma_long = float(np.mean(history[-self.TAU_C_LONG:]))
        
        current = history[-1]
        
        # CCC divergence: how much is current price deviating from universal standard?
        ccc_divergence = (sma_short - sma_long) / sma_long * 100 if sma_long != 0 else 0
        
        # Price position relative to CCC
        price_vs_ccc = (current - sma_long) / sma_long * 100 if sma_long != 0 else 0
        
        # Combined CCC score: trend + position
        ccc_pct = (ccc_divergence + price_vs_ccc) / 2
        
        tau_c_score = self.price_to_gile(ccc_pct)
        
        return float(np.clip(tau_c_score, -3, 3))
    
    def calculate_love(self, symbol) -> float:
        """
        L (Love Dimension): The binding force across temporal dimensions.
        
        TI's unique contribution to K's framework:
        - Love is NOT a 4th time dimension
        - Love is what BINDS the three time dimensions together
        - Without Love, temporal dimensions are isolated
        - With Love, they create SYNERGY
        
        In trading: Correlation with market captures this binding.
        High correlation in uptrend = loving the rising tide together
        Low correlation in downtrend = loving independence from falling tide
        """
        if len(self.price_history.get(symbol, [])) < 21:
            return 0.0
        
        sym_history = self.price_history[symbol][-21:]
        sym_returns = np.diff(sym_history) / sym_history[:-1] * 100
        
        # Market consciousness (SPY)
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
        
        spy_trend = float(np.mean(spy_returns)) if len(spy_returns) > 0 else 0
        
        # Love logic:
        # Uptrend: High correlation = moving together in love
        # Downtrend: Low correlation = independent, not falling together
        if spy_trend > 0:
            # In uptrend, we WANT high correlation (rising together)
            love_score = correlation * abs(spy_trend) * 0.6
        else:
            # In downtrend, we WANT low correlation (not falling together)
            love_score = (1 - abs(correlation)) * abs(spy_trend) * 0.4
        
        return float(np.clip(love_score, -1.5, 1.5))
    
    def calculate_synergy(self, tau_i: float, tau_j: float, tau_c: float, love: float) -> tuple:
        """
        Calculate temporal synergy - the nonlinear boost when dimensions align.
        
        Your insight: Different variables describe complementary aspects of reality.
        When they agree, they should boost each other nonlinearly!
        
        Synergy conditions:
        1. All three tau dimensions have same sign (agreement)
        2. At least 2 dimensions exceed threshold (conviction)
        3. Love is positive (binding force active)
        
        Returns: (is_synergy, synergy_multiplier)
        """
        # Check sign agreement
        signs = [np.sign(tau_i), np.sign(tau_j), np.sign(tau_c)]
        all_same_sign = len(set(signs)) == 1 and 0 not in signs
        
        # Check conviction (at least 2 dimensions strong)
        strong_count = sum([
            abs(tau_i) > self.SYNERGY_THRESHOLD,
            abs(tau_j) > self.SYNERGY_THRESHOLD,
            abs(tau_c) > self.SYNERGY_THRESHOLD
        ])
        
        # Check love binding
        love_active = love > 0
        
        # Synergy = all agree + at least 2 strong + love active
        is_synergy = all_same_sign and strong_count >= 2 and love_active
        
        if is_synergy:
            # Love amplifies the synergy boost
            love_amplification = 1.0 + love * self.LOVE_SYNERGY_BOOST
            multiplier = self.SYNERGY_MULTIPLIER * love_amplification
        else:
            multiplier = 1.0
        
        return is_synergy, multiplier
    
    def calculate_unified_gile(self, symbol) -> dict:
        """
        Unified GILE: The complete TI temporal integration.
        
        Formula:
        GILE_unified = synergy_multiplier × (w_I·τ_I + w_J·τ_J + w_C·τ_C + w_L·L)
        
        Where synergy_multiplier = 1.0 (no synergy) or 1.25+ (synergy active)
        """
        tau_i = self.calculate_tau_i(symbol)
        tau_j = self.calculate_tau_j(symbol)
        tau_c = self.calculate_tau_c(symbol)
        love = self.calculate_love(symbol)
        
        # Calculate synergy
        is_synergy, synergy_mult = self.calculate_synergy(tau_i, tau_j, tau_c, love)
        
        # Weighted combination
        base_gile = (
            self.TAU_I_WEIGHT * tau_i +
            self.TAU_J_WEIGHT * tau_j +
            self.TAU_C_WEIGHT * tau_c +
            self.LOVE_WEIGHT * love
        )
        
        # Apply synergy multiplier
        unified = base_gile * synergy_mult
        
        result = {
            'tau_i': tau_i,
            'tau_j': tau_j,
            'tau_c': tau_c,
            'love': love,
            'synergy': is_synergy,
            'synergy_mult': synergy_mult,
            'unified': unified
        }
        
        self.temporal_scores[symbol] = result
        return result
    
    def get_zone_name(self, gile: float) -> str:
        """Get GILE zone name"""
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
        """Main rebalancing using TI 3D Jeff Time"""
        
        if self.is_warming_up:
            return
        
        # Update price history
        for symbol in self.symbols:
            security = self.securities.get(symbol)
            if security is None or security.price <= 0:
                continue
            
            price = security.price
            self.price_history[symbol].append(price)
            
            if len(self.price_history[symbol]) > self.max_history:
                self.price_history[symbol] = self.price_history[symbol][-self.max_history:]
        
        # Calculate unified GILE for all symbols
        signals = {}
        for symbol in self.symbols:
            if len(self.price_history.get(symbol, [])) < self.TAU_C_LONG:
                continue
            
            temporal = self.calculate_unified_gile(symbol)
            unified_gile = temporal['unified']
            
            signals[symbol] = {
                'gile': unified_gile,
                'zone': self.get_zone_name(unified_gile),
                'components': temporal,
                'synergy': temporal['synergy']
            }
            
            self.gile_history[symbol].append(unified_gile)
            if len(self.gile_history[symbol]) > 30:
                self.gile_history[symbol] = self.gile_history[symbol][-30:]
        
        # Rank by unified GILE
        ranked = sorted(signals.items(), key=lambda x: x[1]['gile'], reverse=True)
        
        # Top 4 buy candidates (synergy first, then GILE)
        buy_candidates = [(s, sig) for s, sig in ranked if sig['gile'] >= self.GILE_GOOD][:4]
        
        # Prioritize synergy signals
        synergy_first = sorted(buy_candidates, key=lambda x: (x[1]['synergy'], x[1]['gile']), reverse=True)
        
        # SELL LOGIC
        for symbol in list(self.portfolio.keys()):
            if symbol not in signals:
                continue
            
            sig = signals[symbol]
            holding = self.portfolio[symbol]
            
            if not holding.invested:
                continue
            
            should_sell = False
            reason = ""
            
            # Sell conditions:
            
            # 1. Jeff Moment strongly negative (present is bad)
            if sig['components']['tau_j'] < -1.0:
                should_sell = True
                reason = f"Negative Jeff Moment {sig['components']['tau_j']:.2f}"
            
            # 2. CCC trend reversal (cosmological shift)
            elif sig['components']['tau_c'] < -1.2:
                should_sell = True
                reason = f"CCC trend reversal {sig['components']['tau_c']:.2f}"
            
            # 3. Overall GILE negative
            elif sig['gile'] < self.GILE_BAD:
                should_sell = True
                reason = f"Negative GILE {sig['gile']:.2f}"
            
            # 4. Take profits in ULTRA_GREAT
            elif sig['zone'] == "ULTRA_GREAT":
                should_sell = True
                reason = "Take profit in ULTRA_GREAT"
            
            if should_sell:
                self.liquidate(symbol, reason)
                self.trade_count += 1
                if holding.unrealized_profit > 0:
                    self.winning_trades += 1
        
        # BUY LOGIC
        for symbol, sig in synergy_first:
            if self.portfolio[symbol].invested:
                continue
            
            # Base position size
            base_size = self.max_position
            
            # Zone-based sizing
            if sig['zone'] == "ULTRA_GREAT":
                size = base_size * 1.1
            elif sig['zone'] == "GREAT":
                size = base_size * 1.0
            elif sig['zone'] == "GOOD":
                size = base_size * 0.75
            else:
                size = base_size * 0.5
            
            # Synergy bonus: 20% boost when temporal dimensions align
            if sig['synergy']:
                size = min(size * 1.2, base_size * 1.25)
                self.synergy_trades += 1
            
            self.set_holdings(symbol, size)
            self.trade_count += 1
            
            self.debug(f"BUY {symbol}: GILE={sig['gile']:.2f} Zone={sig['zone']} Synergy={sig['synergy']}")
    
    def on_end_of_algorithm(self):
        """Final statistics"""
        win_rate = self.winning_trades / max(self.trade_count, 1) * 100
        synergy_pct = self.synergy_trades / max(self.trade_count, 1) * 100
        
        self.debug("=" * 60)
        self.debug("TI FRAMEWORK V5: JEFF TIME 3D - FINAL RESULTS")
        self.debug("=" * 60)
        self.debug(f"Total Trades: {self.trade_count}")
        self.debug(f"Winning Trades: {self.winning_trades}")
        self.debug(f"Win Rate: {win_rate:.1f}%")
        self.debug(f"Synergy Trades: {self.synergy_trades} ({synergy_pct:.1f}%)")
        self.debug("=" * 60)


# ============================================================================
# FOR 10-YEAR TEST: Change initialize() dates to:
#   self.set_start_date(2015, 1, 1)
#   self.set_end_date(2024, 12, 31)
#
# FOR 20-YEAR TEST: Change initialize() dates to:
#   self.set_start_date(2005, 1, 1)  
#   self.set_end_date(2024, 12, 31)
# ============================================================================

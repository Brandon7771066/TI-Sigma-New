"""
QuantConnect Algorithm - TI-UOP Sigma Prediction Engine
High-Tralse Stock Prediction System with Active Trading

BACKTEST READY: 10-year multi-market validation
FIXED: More active trading to generate actual results
"""

from AlgorithmImports import *
import numpy as np


class TIUOPSigmaAlgorithm(QCAlgorithm):
    """
    TI-UOP Sigma: Active trading using momentum and mean-reversion signals
    """
    
    def initialize(self):
        """Initialize algorithm with TI Framework parameters"""
        
        # Backtest period: 10 years for validation
        self.set_start_date(2014, 1, 1)
        self.set_end_date(2024, 12, 31)
        
        # Starting capital
        self.set_cash(100000)
        
        # Track symbols
        self.symbol_objects = {}
        # Universe: Multiple markets (tech, finance, consumer, energy)
        symbols_list = ["SPY", "QQQ", "AAPL", "MSFT", "GOOGL", "JPM", "BAC", "XOM", "CVX", "WMT"]
        
        # Add securities
        for ticker in symbols_list:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.set_data_normalization_mode(DataNormalizationMode.ADJUSTED)
            self.symbol_objects[ticker] = equity.symbol
        
        # Data tracking
        self.lookback = 20
        self.price_history = {}
        
        
        # Performance tracking
        self.trade_count = 0
        
        # Risk management
        self.max_position = 0.12  # 12% per position
        
        # Schedule weekly rebalance
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.daily_check
        )
        
        self.log("TI-UOP Sigma Algorithm Initialized")
    
    def daily_check(self):
        """Daily signal check and trading"""
        
        for ticker, symbol in self.symbol_objects.items():
            # Get historical data
            history = self.history(symbol, self.lookback + 1, Resolution.DAILY)
            
            if history.empty or len(history) < 10:
                continue
            
            # Calculate returns
            closes = history['close'].values
            
            # Calculate metrics
            returns = np.diff(closes) / closes[:-1]
            
            # Current price vs moving averages
            current_price = closes[-1]
            ma5 = np.mean(closes[-5:])
            ma20 = np.mean(closes)
            
            # Momentum signals
            short_momentum = (current_price - ma5) / ma5
            long_momentum = (current_price - ma20) / ma20
            
            # Volatility
            volatility = np.std(returns)
            
            # Recent trend (last 5 days)
            recent_return = (closes[-1] - closes[-6]) / closes[-6] if len(closes) > 5 else 0
            
            # Calculate TI Score combining momentum and mean reversion
            ti_score = self.calculate_ti_score(short_momentum, long_momentum, recent_return, volatility)
            
            # Get current holding
            holding = self.portfolio[symbol]
            
            # Trading logic with ACTIVE thresholds
            if ti_score > 0.3 and not holding.invested:
                # BUY signal
                weight = min(self.max_position, ti_score * 0.15)
                self.set_holdings(symbol, weight)
                self.trade_count += 1
                self.log(f"BUY {ticker}: TI={ti_score:.2f}, Weight={weight:.1%}")
                
            elif ti_score < -0.3 and holding.invested:
                # SELL signal
                self.liquidate(symbol)
                self.trade_count += 1
                self.log(f"SELL {ticker}: TI={ti_score:.2f}")
                
            elif holding.invested:
                # Check stop loss / take profit
                pnl = holding.unrealized_profit_percent
                
                if pnl < -0.08:  # 8% stop loss
                    self.liquidate(symbol)
                    self.log(f"STOP LOSS {ticker}: {pnl:.1%}")
                    
                elif pnl > 0.20:  # 20% take profit
                    self.liquidate(symbol)
                    self.log(f"TAKE PROFIT {ticker}: {pnl:.1%}")
    
    def calculate_ti_score(self, short_mom, long_mom, recent_ret, vol):
        """
        TI Score: Combines multiple signals
        Range: -1.0 to +1.0
        """
        # Momentum component (follow the trend)
        momentum_score = 0.0
        
        # Short-term momentum (more weight)
        if short_mom > 0.02:  # Price above 5-day MA by 2%+
            momentum_score += 0.4
        elif short_mom < -0.02:
            momentum_score -= 0.4
        else:
            momentum_score += short_mom * 10  # Scale small moves
        
        # Long-term momentum
        if long_mom > 0.03:  # Price above 20-day MA by 3%+
            momentum_score += 0.3
        elif long_mom < -0.03:
            momentum_score -= 0.3
        else:
            momentum_score += long_mom * 5
        
        # Recent trend bonus
        if recent_ret > 0.05:  # Up 5%+ in last week
            momentum_score += 0.2
        elif recent_ret < -0.05:
            momentum_score -= 0.3  # Asymmetric - losses hurt more
        
        # Volatility adjustment (reduce score in high volatility)
        if vol > 0.03:  # High volatility
            momentum_score *= 0.7
        
        # Clamp to range
        return max(-1.0, min(1.0, momentum_score))
    
    def on_data(self, data):
        """Process incoming data"""
        pass  # Using scheduled events instead
    
    def on_end_of_algorithm(self):
        """Final performance summary"""
        
        self.log("=" * 60)
        self.log("TI-UOP SIGMA BACKTEST COMPLETE")
        self.log("=" * 60)
        self.log(f"Total Trades: {self.trade_count}")
        self.log(f"Final Portfolio Value: ${self.portfolio.total_portfolio_value:,.2f}")
        total_return = (self.portfolio.total_portfolio_value / 100000 - 1) * 100
        self.log(f"Total Return: {total_return:.2f}%")
        self.log("=" * 60)

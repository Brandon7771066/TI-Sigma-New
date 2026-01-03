"""
Alpaca Paper Trading Integration for GSA
Real-time signals, paper trading simulation, performance tracking
"""

import os
import json
from datetime import datetime, timedelta
import pandas as pd
import numpy as np
from typing import List, Dict, Tuple
import yfinance as yf
from gsa_core import GSACore, MarketRegime
import time

# Alpaca SDK (install: pip install alpaca-trade-api)
try:
    from alpaca_trade_api import REST, TimeFrame
    ALPACA_AVAILABLE = True
except ImportError:
    ALPACA_AVAILABLE = False
    print("WARNING: alpaca-trade-api not installed. Install with: pip install alpaca-trade-api")


class AlpacaGSAPaperTrader:
    """
    Alpaca paper trading client for GSA algorithm
    Generates signals and executes paper trades
    """
    
    # Green-light stocks (from comprehensive validation)
    GREEN_LIGHT_STOCKS = {
        'Technology': ['GOOGL', 'NVDA', 'MSFT', 'META'],
        'Industrials': ['CAT', 'GE'],
        'Financials': ['GS', 'MS'],
        'Energy': ['XOM', 'CVX', 'COP'],
        'Consumer': ['WMT', 'TJX'],
    }
    
    # Red-flag stocks (avoid entirely)
    RED_FLAG_STOCKS = [
        'AAPL', 'PFE', 'MRK', 'UNH', 'WFC', 'SLB', 'MMM',  # Losers
        'DUK', 'NEE', 'AEP', 'SO', 'D'  # All utilities except DUK
    ]
    
    def __init__(self, paper_trading: bool = True, initial_cash: float = 10000):
        """
        Initialize Alpaca GSA trader
        
        Args:
            paper_trading: If True, use paper trading account (recommended)
            initial_cash: Starting cash for paper account
        """
        self.paper_trading = paper_trading
        self.initial_cash = initial_cash
        self.gsa = GSACore(lookback_short=7, lookback_long=60)
        
        # Flatten green-light stocks
        self.allowed_stocks = []
        for sector, stocks in self.GREEN_LIGHT_STOCKS.items():
            self.allowed_stocks.extend(stocks)
        
        self.universe = self.allowed_stocks
        self.positions = {}
        self.trade_log = []
        self.performance = {
            'date': [],
            'portfolio_value': [],
            'daily_return': [],
            'cumulative_return': []
        }
        
        # Try to initialize Alpaca client
        if ALPACA_AVAILABLE:
            self.client = self._init_alpaca_client()
        else:
            self.client = None
        
        print(f"Initialized GSA Paper Trader")
        print(f"  Universe: {len(self.universe)} stocks")
        print(f"  Paper trading: {paper_trading}")
        print(f"  Initial cash: ${initial_cash:,.2f}")
    
    def _init_alpaca_client(self):
        """Initialize Alpaca API client"""
        try:
            api_key = os.environ.get('APCA_API_KEY_ID')
            secret_key = os.environ.get('APCA_API_SECRET_KEY')
            
            if not api_key or not secret_key:
                print("WARNING: Alpaca credentials not found. Set APCA_API_KEY_ID and APCA_API_SECRET_KEY")
                return None
            
            client = REST(
                key_id=api_key,
                secret_key=secret_key,
                base_url='https://paper-api.alpaca.markets' if self.paper_trading 
                         else 'https://api.alpaca.markets'
            )
            
            # Test connection
            account = client.get_account()
            print(f"✓ Connected to Alpaca")
            print(f"  Account: {account.account_number}")
            print(f"  Buying power: ${float(account.buying_power):,.2f}")
            
            return client
        except Exception as e:
            print(f"ERROR initializing Alpaca: {e}")
            return None
    
    def download_universe_data(self, period: str = "60d") -> Dict[str, pd.DataFrame]:
        """Download latest OHLCV data for universe"""
        print(f"\nDownloading {len(self.universe)} stocks ({period})...")
        data = {}
        
        for ticker in self.universe:
            try:
                df = yf.download(ticker, period=period, progress=False)
                if df is not None and len(df) > 0:
                    data[ticker] = df
                    print(f"  ✓ {ticker}: {len(df)} bars")
            except Exception as e:
                print(f"  ✗ {ticker}: {str(e)[:40]}")
        
        return data
    
    def generate_signals(self, universe_data: Dict[str, pd.DataFrame]) -> Dict[str, Dict]:
        """Generate GSA signals for all stocks in universe"""
        print(f"\nGenerating signals for {len(universe_data)} stocks...")
        signals = {}
        
        for ticker, price_df in universe_data.items():
            try:
                close_values = price_df['Close'].values
                closes = np.array(close_values.flatten() if hasattr(close_values, 'flatten') 
                                else close_values, dtype=float)
                
                if len(closes) < 60:
                    continue
                
                price_diff = np.diff(closes)
                returns = (price_diff / closes[:-1]) * 100
                
                xi = self.gsa.compute_xi_metrics(returns[-60:], closes[-60:])
                gile = self.gsa.compute_gile(returns[-60:], closes[-60:])
                regime, regime_conf, _ = self.gsa.classify_regime(xi.pd, xi.constraint, 1.0)
                signal = self.gsa.generate_signal(xi, gile, regime, regime_conf)
                
                signals[ticker] = {
                    'action': signal.action,
                    'confidence': signal.confidence,
                    'gile': signal.gile,
                    'price': float(closes[-1]),
                    'xi_pd': xi.pd,
                    'regime': regime.value,
                    'timestamp': datetime.now().isoformat()
                }
                
            except Exception as e:
                print(f"  Error generating signal for {ticker}: {str(e)[:40]}")
        
        return signals
    
    def rank_signals(self, signals: Dict[str, Dict], top_n: int = 8) -> List[Tuple[str, Dict]]:
        """Rank signals by composite score and return top N"""
        scored = []
        
        for ticker, sig in signals.items():
            score = sig['gile'] * 0.6 + sig['confidence'] * 0.4
            scored.append((ticker, sig, score))
        
        scored.sort(key=lambda x: x[2], reverse=True)
        
        print(f"\nTop {top_n} Signals:")
        for i, (ticker, sig, score) in enumerate(scored[:top_n]):
            print(f"  {i+1}. {ticker}: {sig['action']:12s} | "
                  f"GILE {sig['gile']:.2f} | Conf {sig['confidence']:.2f} | ${sig['price']:.2f}")
        
        return scored[:top_n]
    
    def paper_trade(self, top_signals: List[Tuple[str, Dict]], 
                   portfolio_value: float = 10000, 
                   position_size: float = 0.10):
        """
        Simulate paper trading execution
        
        Args:
            top_signals: List of (ticker, signal) tuples
            portfolio_value: Current portfolio value
            position_size: Max % per position (default 10%)
        """
        print(f"\n{'='*60}")
        print(f"PAPER TRADING EXECUTION")
        print(f"Portfolio value: ${portfolio_value:,.2f}")
        print(f"Position size: {position_size*100:.1f}%")
        print(f"{'='*60}")
        
        self.positions = {}
        total_deployed = 0
        
        for ticker, sig, score in top_signals:
            if sig['action'] in ['strong_buy', 'buy']:
                position_value = portfolio_value * position_size
                shares = position_value / sig['price']
                
                self.positions[ticker] = {
                    'shares': shares,
                    'entry_price': sig['price'],
                    'entry_value': position_value,
                    'signal_confidence': sig['confidence'],
                    'signal_action': sig['action'],
                    'entry_time': datetime.now().isoformat(),
                }
                
                total_deployed += position_value
                
                print(f"  BUY {ticker:8s}: {shares:7.2f} shares @ ${sig['price']:8.2f} = ${position_value:10,.2f}")
            
            elif sig['action'] in ['sell', 'strong_sell']:
                if ticker in self.positions:
                    pos = self.positions.pop(ticker)
                    exit_value = pos['shares'] * sig['price']
                    pnl = exit_value - pos['entry_value']
                    pnl_pct = (pnl / pos['entry_value']) * 100
                    
                    print(f"  SELL {ticker:8s}: {pos['shares']:7.2f} shares @ ${sig['price']:8.2f} = "
                          f"${exit_value:10,.2f} (PnL: {pnl_pct:+6.2f}%)")
        
        cash_remaining = portfolio_value - total_deployed
        
        print(f"\nPortfolio Allocation:")
        print(f"  Deployed: ${total_deployed:,.2f} ({total_deployed/portfolio_value*100:.1f}%)")
        print(f"  Cash: ${cash_remaining:,.2f} ({cash_remaining/portfolio_value*100:.1f}%)")
        print(f"  Positions: {len(self.positions)}")
        
        return self.positions
    
    def calculate_portfolio_metrics(self, current_prices: Dict[str, float]) -> Dict:
        """Calculate current portfolio metrics"""
        total_value = 0
        total_entry_value = 0
        
        for ticker, position in self.positions.items():
            if ticker in current_prices:
                current_value = position['shares'] * current_prices[ticker]
                total_value += current_value
                total_entry_value += position['entry_value']
        
        unrealized_pnl = total_value - total_entry_value
        unrealized_pnl_pct = (unrealized_pnl / total_entry_value * 100) if total_entry_value > 0 else 0
        
        return {
            'total_value': total_value,
            'entry_value': total_entry_value,
            'unrealized_pnl': unrealized_pnl,
            'unrealized_pnl_pct': unrealized_pnl_pct,
            'positions': len(self.positions)
        }
    
    def run_paper_trading_session(self, duration_hours: int = 1, refresh_interval_min: int = 15):
        """
        Run continuous paper trading session
        
        Args:
            duration_hours: How long to run
            refresh_interval_min: Minutes between signal updates
        """
        print(f"\n{'='*60}")
        print(f"STARTING PAPER TRADING SESSION")
        print(f"Duration: {duration_hours} hour(s)")
        print(f"Refresh interval: {refresh_interval_min} min")
        print(f"{'='*60}")
        
        start_time = datetime.now()
        session_pnl = []
        
        while (datetime.now() - start_time).seconds < duration_hours * 3600:
            try:
                # Download fresh data
                universe_data = self.download_universe_data(period="60d")
                
                if not universe_data:
                    print("No data available")
                    time.sleep(60)
                    continue
                
                # Generate signals
                signals = self.generate_signals(universe_data)
                
                # Rank and execute
                top_signals = self.rank_signals(signals, top_n=8)
                self.paper_trade(top_signals)
                
                # Get current prices for metrics
                current_prices = {}
                for ticker in self.positions:
                    current_prices[ticker] = self.universe[-1] if ticker in self.universe else None
                
                metrics = self.calculate_portfolio_metrics(current_prices)
                
                print(f"\n[{datetime.now().strftime('%H:%M:%S')}] Portfolio Metrics:")
                print(f"  Unrealized P&L: {metrics['unrealized_pnl_pct']:+.2f}%")
                print(f"  Positions: {metrics['positions']}")
                
                session_pnl.append(metrics['unrealized_pnl_pct'])
                
                # Wait for next refresh
                print(f"  Next refresh in {refresh_interval_min} min...")
                time.sleep(refresh_interval_min * 60)
                
            except Exception as e:
                print(f"ERROR in session: {e}")
                time.sleep(60)
        
        print(f"\n{'='*60}")
        print(f"PAPER TRADING SESSION COMPLETE")
        print(f"Duration: {(datetime.now() - start_time).seconds / 60:.1f} min")
        print(f"Peak P&L: {max(session_pnl):+.2f}%" if session_pnl else "N/A")
        print(f"{'='*60}")
        
        return session_pnl


def main():
    """Quick start: initialize and run paper trading demo"""
    
    trader = AlpacaGSAPaperTrader(paper_trading=True, initial_cash=10000)
    
    # Download data
    universe_data = trader.download_universe_data(period="60d")
    
    if not universe_data:
        print("Failed to download data")
        return
    
    # Generate signals
    signals = trader.generate_signals(universe_data)
    
    # Rank and execute paper trade
    top_signals = trader.rank_signals(signals, top_n=8)
    positions = trader.paper_trade(top_signals, portfolio_value=10000, position_size=0.10)
    
    print(f"\n✓ Paper trading demo complete")
    print(f"  Positions created: {len(positions)}")
    print(f"  Ready for live monitoring!")


if __name__ == "__main__":
    main()

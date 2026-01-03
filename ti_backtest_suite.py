"""
TI-UOP Sigma Backtesting Suite
Comprehensive performance analysis with investor-grade metrics

Generates:
- Sharpe Ratio
- Max Drawdown
- Win Rate
- Annual Return
- Calmar Ratio
- Sortino Ratio
- Risk-adjusted metrics
"""

import pandas as pd
import numpy as np
import yfinance as yf
from datetime import datetime, timedelta
from typing import Dict, List, Tuple
import json


class TIBacktester:
    """
    Professional backtesting engine for TI-UOP Sigma
    """
    
    # Optimal Trading Interval
    OPTIMAL_INTERVAL_MIN = -0.666
    OPTIMAL_INTERVAL_MAX = 0.333
    
    # Asymmetric thresholds
    BEARISH_EXTREME = -10.0
    BULLISH_EXTREME = 20.0
    
    def __init__(self, initial_capital: float = 100000):
        """Initialize backtester with starting capital"""
        self.initial_capital = initial_capital
        self.current_capital = initial_capital
        self.positions = {}
        self.trade_history = []
        self.equity_curve = []
    
    def calculate_market_score(self, price_change_pct: float) -> float:
        """Calculate Market Score (same as production system)"""
        if price_change_pct >= self.BULLISH_EXTREME:
            return 2.0 + 0.1 * np.log(price_change_pct / self.BULLISH_EXTREME)
        elif price_change_pct <= self.BEARISH_EXTREME:
            return -3.0 - 0.1 * np.log(abs(price_change_pct) / abs(self.BEARISH_EXTREME))
        elif price_change_pct >= 10.0:
            return 1.5 + ((price_change_pct - 10.0) / 10.0) * 0.5
        elif price_change_pct <= -5.0:
            return -3.0 + ((price_change_pct - self.BEARISH_EXTREME) / 5.0) * 1.5
        elif price_change_pct >= 5.0:
            return 1.0 + ((price_change_pct - 5.0) / 5.0) * 0.5
        elif price_change_pct > self.OPTIMAL_INTERVAL_MAX:
            return 0.3 + ((price_change_pct - self.OPTIMAL_INTERVAL_MAX) / (5.0 - self.OPTIMAL_INTERVAL_MAX)) * 1.2
        elif price_change_pct < self.OPTIMAL_INTERVAL_MIN:
            return -0.3 + ((price_change_pct - self.OPTIMAL_INTERVAL_MIN) / (-5.0 - self.OPTIMAL_INTERVAL_MIN)) * -1.2
        else:
            if price_change_pct == 0.0:
                return 0.0
            elif price_change_pct < 0.0:
                return -0.3 + ((price_change_pct - self.OPTIMAL_INTERVAL_MIN) / (0.0 - self.OPTIMAL_INTERVAL_MIN)) * 0.3
            else:
                return 0.0 + ((price_change_pct - 0.0) / (self.OPTIMAL_INTERVAL_MAX - 0.0)) * 0.3
    
    def run_backtest(self, ticker: str, start_date: str, end_date: str, 
                    position_size: float = 0.2) -> Dict:
        """
        Run backtest for single ticker
        
        Args:
            ticker: Stock symbol
            start_date: Start date (YYYY-MM-DD)
            end_date: End date (YYYY-MM-DD)
            position_size: Fraction of capital to allocate (0.0-1.0)
        
        Returns:
            Dict with backtest results
        """
        print(f"\n{'='*60}")
        print(f"BACKTESTING {ticker}: {start_date} to {end_date}")
        print(f"{'='*60}")
        
        # Fetch historical data
        stock = yf.Ticker(ticker)
        df = stock.history(start=start_date, end=end_date)
        
        if df.empty:
            print(f"❌ No data available for {ticker}")
            return None
        
        # Reset state
        self.current_capital = self.initial_capital
        self.positions = {}
        self.trade_history = []
        self.equity_curve = [(df.index[0], self.current_capital)]
        
        # Calculate daily returns
        df['Daily_Return'] = df['Close'].pct_change() * 100
        df['Market_Score'] = df['Daily_Return'].apply(self.calculate_market_score)
        
        # Simulate trading
        in_position = False
        entry_price = 0
        entry_date = None
        shares = 0
        
        for i in range(1, len(df)):
            date = df.index[i]
            close_price = df['Close'].iloc[i]
            market_score = df['Market_Score'].iloc[i]
            daily_return = df['Daily_Return'].iloc[i]
            
            # BUY SIGNAL: Market score > 0.5
            if not in_position and market_score > 0.5:
                # Enter position
                allocation = self.current_capital * position_size
                shares = allocation / close_price
                entry_price = close_price
                entry_date = date
                in_position = True
                
                # CRITICAL FIX: Deduct capital when buying
                self.current_capital -= allocation
                
                self.trade_history.append({
                    'action': 'BUY',
                    'date': date,
                    'price': close_price,
                    'shares': shares,
                    'capital_used': allocation,
                    'market_score': market_score
                })
            
            # SELL SIGNAL: Market score < -0.3 OR take profit
            elif in_position:
                # Calculate unrealized P&L
                pnl_pct = (close_price - entry_price) / entry_price
                
                # Exit conditions
                should_exit = (
                    market_score < -0.3 or  # Bearish signal
                    pnl_pct < -0.10 or      # Stop loss: -10%
                    pnl_pct > 0.25          # Take profit: +25%
                )
                
                if should_exit:
                    # Exit position
                    exit_value = shares * close_price
                    pnl = exit_value - (shares * entry_price)
                    
                    # CRITICAL FIX: Credit full exit proceeds (not just profit)
                    self.current_capital += exit_value
                    
                    self.trade_history.append({
                        'action': 'SELL',
                        'date': date,
                        'price': close_price,
                        'shares': shares,
                        'exit_value': exit_value,
                        'pnl': pnl,
                        'pnl_pct': pnl_pct * 100,
                        'market_score': market_score,
                        'holding_period': (date - entry_date).days
                    })
                    
                    in_position = False
                    shares = 0
            
            # Track equity curve
            if in_position:
                position_value = shares * close_price
                total_equity = self.current_capital + position_value
            else:
                total_equity = self.current_capital
            
            self.equity_curve.append((date, total_equity))
        
        # Close any open positions at end
        if in_position:
            close_price = df['Close'].iloc[-1]
            exit_value = shares * close_price
            pnl = exit_value - (shares * entry_price)
            
            # CRITICAL FIX: Credit full exit proceeds
            self.current_capital += exit_value
            
            self.trade_history.append({
                'action': 'SELL (EOD)',
                'date': df.index[-1],
                'price': close_price,
                'shares': shares,
                'exit_value': exit_value,
                'pnl': pnl,
                'pnl_pct': (close_price - entry_price) / entry_price * 100,
                'market_score': df['Market_Score'].iloc[-1],
                'holding_period': (df.index[-1] - entry_date).days
            })
        
        # Calculate metrics
        metrics = self.calculate_metrics(df)
        
        return {
            'ticker': ticker,
            'start_date': start_date,
            'end_date': end_date,
            'metrics': metrics,
            'trade_history': self.trade_history,
            'equity_curve': self.equity_curve
        }
    
    def calculate_metrics(self, df: pd.DataFrame) -> Dict:
        """Calculate comprehensive performance metrics"""
        
        # Buy & Hold benchmark
        buy_hold_return = (df['Close'].iloc[-1] - df['Close'].iloc[0]) / df['Close'].iloc[0] * 100
        
        # TI Strategy performance
        total_return = (self.current_capital - self.initial_capital) / self.initial_capital * 100
        
        # Equity curve analysis
        equity_df = pd.DataFrame(self.equity_curve, columns=['date', 'equity'])
        equity_df['returns'] = equity_df['equity'].pct_change()
        
        # Sharpe Ratio (annualized, assuming 252 trading days)
        if len(equity_df) > 1:
            mean_return = equity_df['returns'].mean() * 252
            std_return = equity_df['returns'].std() * np.sqrt(252)
            sharpe_ratio = mean_return / std_return if std_return > 0 else 0
        else:
            sharpe_ratio = 0
        
        # Max Drawdown
        equity_df['cummax'] = equity_df['equity'].cummax()
        equity_df['drawdown'] = (equity_df['equity'] - equity_df['cummax']) / equity_df['cummax'] * 100
        max_drawdown = equity_df['drawdown'].min()
        
        # Sortino Ratio (penalizes only downside volatility)
        downside_returns = equity_df['returns'][equity_df['returns'] < 0]
        downside_std = downside_returns.std() * np.sqrt(252) if len(downside_returns) > 0 else 0.001
        sortino_ratio = mean_return / downside_std if downside_std > 0 else 0
        
        # Calmar Ratio (return / max drawdown)
        calmar_ratio = abs(total_return / max_drawdown) if max_drawdown != 0 else 0
        
        # Win Rate
        winning_trades = [t for t in self.trade_history if t['action'].startswith('SELL') and t.get('pnl', 0) > 0]
        losing_trades = [t for t in self.trade_history if t['action'].startswith('SELL') and t.get('pnl', 0) < 0]
        total_trades = len(winning_trades) + len(losing_trades)
        win_rate = len(winning_trades) / total_trades * 100 if total_trades > 0 else 0
        
        # Average win/loss
        avg_win = np.mean([t['pnl'] for t in winning_trades]) if winning_trades else 0
        avg_loss = np.mean([t['pnl'] for t in losing_trades]) if losing_trades else 0
        profit_factor = abs(avg_win / avg_loss) if avg_loss != 0 else 0
        
        # Number of trading days
        trading_days = len(df)
        years = trading_days / 252
        annual_return = total_return / years if years > 0 else total_return
        
        metrics = {
            'total_return_pct': total_return,
            'annual_return_pct': annual_return,
            'buy_hold_return_pct': buy_hold_return,
            'outperformance_pct': total_return - buy_hold_return,
            'sharpe_ratio': sharpe_ratio,
            'sortino_ratio': sortino_ratio,
            'max_drawdown_pct': max_drawdown,
            'calmar_ratio': calmar_ratio,
            'win_rate_pct': win_rate,
            'total_trades': total_trades,
            'winning_trades': len(winning_trades),
            'losing_trades': len(losing_trades),
            'avg_win': avg_win,
            'avg_loss': avg_loss,
            'profit_factor': profit_factor,
            'final_capital': self.current_capital,
            'trading_days': trading_days,
            'years': years
        }
        
        return metrics
    
    def print_results(self, results: Dict):
        """Print formatted backtest results"""
        
        metrics = results['metrics']
        
        print(f"\n{'='*60}")
        print(f"BACKTEST RESULTS: {results['ticker']}")
        print(f"{'='*60}")
        print(f"\n📊 PERFORMANCE METRICS")
        print(f"   Total Return:        {metrics['total_return_pct']:>8.2f}%")
        print(f"   Annual Return:       {metrics['annual_return_pct']:>8.2f}%")
        print(f"   Buy & Hold:          {metrics['buy_hold_return_pct']:>8.2f}%")
        print(f"   Outperformance:      {metrics['outperformance_pct']:>8.2f}%")
        
        print(f"\n📈 RISK METRICS")
        print(f"   Sharpe Ratio:        {metrics['sharpe_ratio']:>8.2f}")
        print(f"   Sortino Ratio:       {metrics['sortino_ratio']:>8.2f}")
        print(f"   Max Drawdown:        {metrics['max_drawdown_pct']:>8.2f}%")
        print(f"   Calmar Ratio:        {metrics['calmar_ratio']:>8.2f}")
        
        print(f"\n🎯 TRADE ANALYSIS")
        print(f"   Total Trades:        {metrics['total_trades']:>8}")
        print(f"   Win Rate:            {metrics['win_rate_pct']:>8.2f}%")
        print(f"   Winning Trades:      {metrics['winning_trades']:>8}")
        print(f"   Losing Trades:       {metrics['losing_trades']:>8}")
        print(f"   Profit Factor:       {metrics['profit_factor']:>8.2f}")
        print(f"   Avg Win:            ${metrics['avg_win']:>8.2f}")
        print(f"   Avg Loss:           ${metrics['avg_loss']:>8.2f}")
        
        print(f"\n💰 CAPITAL")
        print(f"   Initial Capital:    ${self.initial_capital:>10,.2f}")
        print(f"   Final Capital:      ${metrics['final_capital']:>10,.2f}")
        print(f"   Profit:             ${metrics['final_capital'] - self.initial_capital:>10,.2f}")
        
        print(f"\n⏱️  PERIOD")
        print(f"   Start Date:          {results['start_date']}")
        print(f"   End Date:            {results['end_date']}")
        print(f"   Trading Days:        {metrics['trading_days']}")
        print(f"   Years:               {metrics['years']:.2f}")
        
        print(f"\n{'='*60}")
    
    def export_results(self, results: Dict, filename: str = None) -> str:
        """Export results to JSON for reporting"""
        
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"backtest_results_{results['ticker']}_{timestamp}.json"
        
        # Convert equity curve to JSON-serializable format
        results_copy = results.copy()
        results_copy['equity_curve'] = [
            {'date': date.strftime('%Y-%m-%d'), 'equity': float(equity)}
            for date, equity in results['equity_curve']
        ]
        
        # Convert trade history dates
        for trade in results_copy['trade_history']:
            if 'date' in trade:
                trade['date'] = trade['date'].strftime('%Y-%m-%d')
        
        with open(filename, 'w') as f:
            json.dump(results_copy, f, indent=2, default=str)
        
        print(f"\n✅ Results exported to: {filename}")
        return filename


def main():
    """
    Run comprehensive backtests for investor reporting
    """
    print("="*60)
    print("TI-UOP SIGMA BACKTESTING SUITE")
    print("High-Tralse Prediction Engine - Performance Validation")
    print("="*60)
    
    # Initialize backtester
    backtester = TIBacktester(initial_capital=100000)
    
    # Test multiple tickers
    tickers = ["AAPL", "MSFT", "SPY", "TSLA"]
    
    # 3-year backtest
    end_date = datetime.now().strftime("%Y-%m-%d")
    start_date = (datetime.now() - timedelta(days=3*365)).strftime("%Y-%m-%d")
    
    all_results = []
    
    for ticker in tickers:
        results = backtester.run_backtest(ticker, start_date, end_date)
        
        if results:
            backtester.print_results(results)
            filename = backtester.export_results(results)
            all_results.append(results)
    
    print(f"\n✅ BACKTESTING COMPLETE")
    print(f"   Tickers Tested: {len(all_results)}")
    print(f"   Period: {start_date} to {end_date}")
    print("\n🎯 Next: Use these results for investor PDF and pitch deck")


if __name__ == "__main__":
    main()

"""
VectorBT GSA Backtest - Fast vectorized backtesting
Works with GSA core engine to run rapid portfolio backtests
"""

import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import yfinance as yf
from gsa_core import GSACore, MarketRegime

class VectorBTGSABacktest:
    """Run GSA on vectorized price data"""
    
    def __init__(self, lookback_short=7, lookback_long=60):
        self.gsa = GSACore(lookback_short=lookback_short, lookback_long=lookback_long)
        self.results = {}
    
    def download_data(self, symbols: list, period: str = "1y") -> dict:
        """Download OHLCV data for multiple symbols"""
        print(f"Downloading {len(symbols)} symbols for {period}...")
        data = {}
        
        for ticker in symbols:
            try:
                df = yf.download(ticker, period=period, progress=False)
                if df is not None and len(df) > 0:
                    data[ticker] = df
                    print(f"  ✓ {ticker}: {len(df)} bars")
            except Exception as e:
                print(f"  ✗ {ticker}: {e}")
        
        return data
    
    def compute_signals_vectorized(self, symbol: str, price_data: pd.DataFrame) -> pd.DataFrame:
        """Compute GSA signals for all bars"""
        close_values = price_data['Close'].values
        if hasattr(close_values, 'flatten'):
            closes = np.array(close_values.flatten(), dtype=float)
        else:
            closes = np.array(close_values, dtype=float)
        price_diff = np.diff(closes)
        returns = (price_diff / closes[:-1]) * 100
        
        signals = []
        start_idx = max(60, self.gsa.lookback_long)
        
        for i in range(start_idx, len(returns) + 1):
            hist_returns = returns[:i-1]
            hist_prices = closes[:i]
            
            xi = self.gsa.compute_xi_metrics(hist_returns, hist_prices)
            gile = self.gsa.compute_gile(hist_returns, hist_prices)
            regime, regime_conf, _ = self.gsa.classify_regime(xi.pd, xi.constraint, 1.0)
            signal = self.gsa.generate_signal(xi, gile, regime, regime_conf)
            
            signals.append({
                'timestamp': price_data.index[i],
                'close': closes[i],
                'return': returns[i-1] if i > 0 else 0,
                'signal': signal.action,
                'confidence': signal.confidence,
                'gile': signal.gile,
                'xi_pd': xi.pd,
            })
        
        return pd.DataFrame(signals)
    
    def backtest_symbol(self, symbol: str, price_data: pd.DataFrame, initial_cash: float = 10000):
        """Backtest GSA on single symbol"""
        signals_df = self.compute_signals_vectorized(symbol, price_data)
        
        if len(signals_df) == 0:
            return None
        
        action_map = {
            'strong_buy': 2,
            'buy': 1,
            'hold': 0,
            'sell': -1,
            'strong_sell': -2
        }
        signals_df['action_numeric'] = signals_df['signal'].map(action_map)
        
        signals_df['position'] = (signals_df['action_numeric'] > 0).astype(int)
        signals_df['position'] = signals_df['position'].shift(1).fillna(0)
        
        signals_df['daily_return'] = signals_df['return'] / 100
        signals_df['strategy_return'] = signals_df['position'] * signals_df['daily_return']
        signals_df['cumulative_return'] = (1 + signals_df['strategy_return']).cumprod()
        
        total_return = (signals_df['cumulative_return'].iloc[-1] - 1) * 100
        annual_return = (signals_df['cumulative_return'].iloc[-1] ** (252 / len(signals_df)) - 1) * 100
        max_dd = (signals_df['cumulative_return'] / signals_df['cumulative_return'].cummax() - 1).min() * 100
        
        if signals_df['strategy_return'].std() > 0:
            sharpe = signals_df['strategy_return'].mean() / signals_df['strategy_return'].std() * np.sqrt(252)
        else:
            sharpe = 0.0
        
        return {
            'symbol': symbol,
            'total_return': total_return,
            'annual_return': annual_return,
            'max_drawdown': max_dd,
            'sharpe': sharpe,
            'trades': int((signals_df['position'].diff() != 0).sum()),
            'signals_df': signals_df
        }
    
    def backtest_portfolio(self, symbols: list, period: str = "1y"):
        """Run full backtest on portfolio"""
        print("\n" + "="*60)
        print("GSA VECTORBT BACKTEST")
        print("="*60)
        
        data = self.download_data(symbols, period)
        
        if not data:
            print("No data downloaded!")
            return
        
        results = []
        for symbol, price_df in data.items():
            print(f"\nBacktesting {symbol}...")
            result = self.backtest_symbol(symbol, price_df)
            
            if result:
                results.append(result)
                print(f"  Total Return: {result['total_return']:.2f}%")
                print(f"  Annual Return: {result['annual_return']:.2f}%")
                print(f"  Max Drawdown: {result['max_drawdown']:.2f}%")
                print(f"  Sharpe Ratio: {result['sharpe']:.2f}")
        
        return results


def main():
    """Quick start: backtest GSA on S&P 500 stocks"""
    
    backtest = VectorBTGSABacktest(lookback_short=7, lookback_long=60)
    
    top_stocks = [
        "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", 
        "META", "TSLA", "JPM", "V", "JNJ",
        "PG", "MA", "HD", "CVX", "MRK",
        "ABBV", "PEP", "KO", "COST", "WMT"
    ]
    
    results = backtest.backtest_portfolio(top_stocks, period="1y")
    
    if results:
        print("\n" + "="*60)
        print("SUMMARY")
        print("="*60)
        
        df_summary = pd.DataFrame([{
            'Symbol': r['symbol'],
            'Return': f"{r['total_return']:.2f}%",
            'Annual': f"{r['annual_return']:.2f}%",
            'MaxDD': f"{r['max_drawdown']:.2f}%",
            'Sharpe': f"{r['sharpe']:.2f}"
        } for r in results])
        
        print(df_summary.to_string(index=False))
        
        avg_annual = np.mean([r['annual_return'] for r in results])
        avg_sharpe = np.mean([r['sharpe'] for r in results])
        
        print(f"\nPortfolio Average Annual Return: {avg_annual:.2f}%")
        print(f"Portfolio Average Sharpe: {avg_sharpe:.2f}")


if __name__ == "__main__":
    main()

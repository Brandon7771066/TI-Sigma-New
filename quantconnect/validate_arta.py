"""
ARTA Validation Script - Conventional Version
Validates the Adaptive Regime Trading Algorithm for external release
"""

import numpy as np
import pandas as pd
import yfinance as yf
from datetime import datetime
from gsa_conventional import AdaptiveRegimeTrader, compute_intensity_score, MarketRegime

def download_stock(ticker: str, period: str = "2y") -> pd.DataFrame:
    """Download stock data from Yahoo Finance"""
    try:
        df = yf.download(ticker, period=period, progress=False)
        return df
    except Exception as e:
        print(f"Error downloading {ticker}: {e}")
        return None

def backtest_arta(ticker: str, data: pd.DataFrame) -> dict:
    """
    Backtest ARTA on single stock
    Returns performance metrics
    """
    if data is None or len(data) < 60:
        return None
    
    closes = data['Close'].values.flatten()
    prices = np.array(closes, dtype=float)
    returns_pct = np.diff(prices) / prices[:-1] * 100
    
    trader = AdaptiveRegimeTrader(lookback_short=7, lookback_long=30)
    
    signals = []
    start_idx = 60
    
    for i in range(start_idx, len(returns_pct)):
        result = trader.process(prices[:i+1], returns_pct[:i])
        signals.append({
            'date': data.index[i],
            'price': prices[i],
            'return_pct': returns_pct[i-1] if i > 0 else 0,
            'signal': result['signal'],
            'confidence': result['confidence'],
            'intensity': result['intensity'],
            'regime': result['regime'],
            'factors': result['factors']
        })
    
    if not signals:
        return None
    
    df = pd.DataFrame(signals)
    
    # Position: 1 if buy/strong_buy, 0 otherwise (lagged by 1 day)
    action_map = {'strong_buy': 1, 'buy': 1, 'hold': 0, 'sell': -1, 'strong_sell': -1}
    df['position'] = df['signal'].map(action_map).shift(1).fillna(0)
    
    # Long-only for simplicity
    df['position'] = df['position'].apply(lambda x: 1 if x > 0 else 0)
    
    # Strategy returns
    df['daily_return'] = df['return_pct'] / 100
    df['strategy_return'] = df['position'] * df['daily_return']
    df['cumulative'] = (1 + df['strategy_return']).cumprod()
    df['buy_hold'] = (1 + df['daily_return']).cumprod()
    
    # Metrics
    total_return = (df['cumulative'].iloc[-1] - 1) * 100
    buy_hold_return = (df['buy_hold'].iloc[-1] - 1) * 100
    
    trading_days = len(df)
    years = trading_days / 252
    cagr = (df['cumulative'].iloc[-1] ** (1/years) - 1) * 100 if years > 0 else 0
    
    std = df['strategy_return'].std()
    sharpe = (df['strategy_return'].mean() / std * np.sqrt(252)) if std > 0 else 0
    
    max_dd = ((df['cumulative'] / df['cumulative'].cummax()) - 1).min() * 100
    
    trades = int((df['position'].diff() != 0).sum())
    win_days = int((df['strategy_return'] > 0).sum())
    lose_days = int((df['strategy_return'] < 0).sum())
    win_rate = win_days / (win_days + lose_days) if (win_days + lose_days) > 0 else 0
    
    # Regime distribution
    regime_counts = df['regime'].value_counts(normalize=True).to_dict()
    
    return {
        'ticker': ticker,
        'days': trading_days,
        'years': round(years, 2),
        'total_return': round(total_return, 2),
        'buy_hold_return': round(buy_hold_return, 2),
        'alpha': round(total_return - buy_hold_return, 2),
        'cagr': round(cagr, 2),
        'sharpe': round(sharpe, 2),
        'max_drawdown': round(max_dd, 2),
        'trades': trades,
        'win_rate': round(win_rate * 100, 1),
        'regime_distribution': regime_counts
    }

def run_validation(tickers: list = None, period: str = "2y"):
    """
    Run full validation on stock universe
    """
    if tickers is None:
        tickers = ['AAPL', 'MSFT', 'GOOGL', 'NVDA', 'AMZN', 'META', 'TSLA', 'JPM', 'JNJ', 'XOM']
    
    print("=" * 70)
    print("ARTA VALIDATION REPORT")
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print(f"Period: {period}")
    print("=" * 70)
    
    results = []
    
    for ticker in tickers:
        print(f"\nProcessing {ticker}...", end=" ")
        data = download_stock(ticker, period)
        if data is not None and len(data) > 60:
            result = backtest_arta(ticker, data)
            if result:
                results.append(result)
                print(f"Return: {result['total_return']:.1f}%, Sharpe: {result['sharpe']:.2f}")
            else:
                print("Insufficient data")
        else:
            print("Download failed")
    
    if not results:
        print("\nNo valid results")
        return None
    
    # Summary statistics
    df = pd.DataFrame(results)
    
    print("\n" + "=" * 70)
    print("SUMMARY STATISTICS")
    print("=" * 70)
    
    print(f"\nStocks Tested: {len(results)}")
    print(f"Average Return: {df['total_return'].mean():.2f}%")
    print(f"Average Alpha: {df['alpha'].mean():.2f}%")
    print(f"Average Sharpe: {df['sharpe'].mean():.2f}")
    print(f"Average CAGR: {df['cagr'].mean():.2f}%")
    print(f"Average Max DD: {df['max_drawdown'].mean():.2f}%")
    print(f"Average Win Rate: {df['win_rate'].mean():.1f}%")
    
    print("\n" + "-" * 70)
    print("PER-STOCK RESULTS")
    print("-" * 70)
    for r in results:
        print(f"{r['ticker']:6s} | Return: {r['total_return']:7.1f}% | Alpha: {r['alpha']:7.1f}% | Sharpe: {r['sharpe']:5.2f} | MaxDD: {r['max_drawdown']:6.1f}%")
    
    print("\n" + "=" * 70)
    print("VALIDATION COMPLETE")
    print("=" * 70)
    
    return df

if __name__ == "__main__":
    # Quick validation on 10 stocks
    run_validation(period="2y")

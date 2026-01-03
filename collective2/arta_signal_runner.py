"""
ARTA Signal Runner for Collective2
Generates daily signals and optionally submits to C2

Run modes:
1. Backtest (local validation)
2. Live signals (paper trading)
3. Submit to C2 (requires API keys)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import numpy as np
import pandas as pd
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
import yfinance as yf

SACRED_MIN, SACRED_MAX = -0.666, 0.333

@dataclass
class ARTASignal:
    ticker: str
    signal: str
    confidence: float
    intensity: float
    regime: str
    timestamp: datetime

def safe_std(x, floor=1e-6):
    if len(x) < 2:
        return floor
    s = float(np.std(x))
    return max(s, floor)

def calculate_amplitude(returns):
    if len(returns) < 2:
        return 0.0
    cur = abs(float(returns[-1]))
    vol = safe_std(returns, 0.01)
    return float(np.clip(cur / vol, 0.0, 10.0))

def calculate_memory_kernel(returns, decay_pos=0.1, decay_neg=0.05):
    if len(returns) < 3:
        return 0.5
    r = returns[::-1]
    pos = r[r > 0]
    neg = r[r < 0]
    k_pos = sum(abs(float(v)) * np.exp(-decay_pos * i) for i, v in enumerate(pos))
    k_neg = sum(abs(float(v)) * np.exp(-decay_neg * i) for i, v in enumerate(neg))
    tot = k_pos + k_neg
    return float(np.clip(k_neg / tot, 0.0, 1.0)) if tot > 0 else 0.5

def calculate_constraint(prices, returns, lb_short=7, lb_long=30):
    if len(prices) < 5:
        return 0.0
    peak = float(np.max(prices))
    last = float(prices[-1])
    dd = (peak - last) / peak if peak > 0 else 0.0
    
    r_short = returns[-lb_short:] if len(returns) >= lb_short else returns
    r_long = returns[-lb_long:] if len(returns) >= lb_long else returns
    vol_short = safe_std(r_short, 0.01)
    vol_long = safe_std(r_long, 0.01)
    
    vol_constraint = 1.0 - min(vol_short / max(vol_long, 0.01), 1.0)
    return float(np.clip(0.6 * dd + 0.4 * vol_constraint, 0.0, 1.0))

def compute_intensity(prices, returns, lb_short=7, lb_long=30):
    if len(returns) < max(10, lb_short):
        return 0.5
    
    recent = returns[-lb_short:]
    signs = np.sign(recent)
    G = float(np.clip(abs(np.mean(signs)), 0.0, 1.0))
    
    A_raw = calculate_amplitude(returns[-lb_short:])
    I = float(1.0 - np.exp(-A_raw / 2.0))
    
    if len(returns) >= lb_long:
        ret1 = returns[-lb_long:-1]
        ret2 = returns[-lb_long+1:]
        if len(ret1) > 2 and np.std(ret1) > 0 and np.std(ret2) > 0:
            autocorr = np.corrcoef(ret1, ret2)[0, 1]
            if np.isnan(autocorr):
                autocorr = 0.0
            L = float(np.clip((autocorr + 1) / 2, 0.0, 1.0))
        else:
            L = 0.5
    else:
        L = 0.5
    
    C_raw = calculate_constraint(prices[-lb_long:], returns[-lb_long:], lb_short, lb_long)
    E = float(np.clip(1.0 - C_raw, 0.0, 1.0))
    
    product = G * I * L * E
    intensity = float(np.power(max(product, 0.0), 0.25))
    
    return intensity

def classify_regime(constraint_history, recent_vol, long_vol):
    if len(constraint_history) < 5:
        return "expansion", 1.0
    
    avg_constraint = np.mean(constraint_history[-5:])
    constraint_trend = constraint_history[-1] - constraint_history[-5]
    vol_ratio = recent_vol / max(long_vol, 0.01)
    
    if avg_constraint > 0.7 and vol_ratio > 1.5:
        return "fracture", 0.0
    elif constraint_trend > 0.2:
        return "reset", 0.3
    elif vol_ratio < 0.8:
        return "compression", 0.5
    else:
        return "expansion", 1.0

def generate_signal(ticker: str, prices: np.ndarray, returns: np.ndarray) -> ARTASignal:
    """Generate ARTA signal for a single ticker"""
    
    lb_short, lb_long = 7, 30
    
    intensity = compute_intensity(prices, returns, lb_short, lb_long)
    
    constraint_history = []
    for i in range(5, min(30, len(returns))):
        c = calculate_constraint(prices[-i:], returns[-i:], lb_short, lb_long)
        constraint_history.append(c)
    
    recent_vol = safe_std(returns[-lb_short:])
    long_vol = safe_std(returns[-lb_long:])
    
    regime, multiplier = classify_regime(constraint_history, recent_vol, long_vol)
    
    recent_returns = returns[-lb_short:]
    trend = np.mean(recent_returns) if len(recent_returns) > 0 else 0.0
    
    ma_short = np.mean(prices[-5:]) if len(prices) >= 5 else prices[-1]
    ma_long = np.mean(prices[-20:]) if len(prices) >= 20 else prices[-1]
    ma_cross = 1 if ma_short > ma_long else -1
    
    confidence = intensity * multiplier
    
    if regime == "fracture":
        signal = "strong_sell"
    elif intensity >= 0.60 and trend > 0.1 and ma_cross > 0:
        signal = "strong_buy"
    elif intensity >= 0.45 and trend > 0 and ma_cross > 0:
        signal = "buy"
    elif intensity >= 0.60 and trend < -0.1:
        signal = "strong_sell"
    elif intensity >= 0.45 and (trend < -0.05 or ma_cross < 0):
        signal = "sell"
    elif intensity < 0.35 or (trend < 0 and ma_cross < 0):
        signal = "sell"
    else:
        signal = "hold"
    
    return ARTASignal(
        ticker=ticker,
        signal=signal,
        confidence=confidence,
        intensity=intensity,
        regime=regime,
        timestamp=datetime.now()
    )

class ARTABacktester:
    """Local backtester for ARTA algorithm validation"""
    
    def __init__(self, tickers: List[str], start_date: str, end_date: str):
        self.tickers = tickers
        self.start_date = start_date
        self.end_date = end_date
        self.data: Dict[str, pd.DataFrame] = {}
        self.results: List[Dict] = []
    
    def load_data(self):
        """Load historical data for all tickers"""
        print(f"Loading data for {len(self.tickers)} tickers...")
        
        for ticker in self.tickers:
            try:
                df = yf.download(ticker, start=self.start_date, end=self.end_date, progress=False)
                if not df.empty and len(df) > 50:
                    df['Return'] = df['Close'].pct_change() * 100
                    self.data[ticker] = df
                    print(f"  {ticker}: {len(df)} days")
            except Exception as e:
                print(f"  {ticker}: Failed - {e}")
        
        print(f"Loaded {len(self.data)} tickers")
    
    def run_backtest(self, initial_capital: float = 100000.0) -> Dict:
        """Run backtest across all tickers"""
        
        if not self.data:
            self.load_data()
        
        all_results = []
        
        for ticker, df in self.data.items():
            result = self._backtest_ticker(ticker, df, initial_capital / len(self.data))
            all_results.append(result)
            print(f"{ticker}: Return={result['total_return']:.2f}%, Sharpe={result['sharpe']:.2f}, Trades={result['trades']}")
        
        avg_return = np.mean([r['total_return'] for r in all_results])
        avg_sharpe = np.mean([r['sharpe'] for r in all_results])
        total_trades = sum(r['trades'] for r in all_results)
        avg_win_rate = np.mean([r['win_rate'] for r in all_results if r['trades'] > 0])
        
        summary = {
            'avg_return': avg_return,
            'avg_sharpe': avg_sharpe,
            'total_trades': total_trades,
            'avg_win_rate': avg_win_rate,
            'individual_results': all_results
        }
        
        print("\n" + "="*50)
        print("BACKTEST SUMMARY")
        print("="*50)
        print(f"Average Return: {avg_return:.2f}%")
        print(f"Average Sharpe: {avg_sharpe:.2f}")
        print(f"Total Trades: {total_trades}")
        print(f"Average Win Rate: {avg_win_rate:.1f}%")
        print("="*50)
        
        return summary
    
    def _backtest_ticker(self, ticker: str, df: pd.DataFrame, capital: float) -> Dict:
        """Backtest single ticker"""
        
        if df.columns.nlevels > 1:
            df.columns = df.columns.get_level_values(0)
        
        prices = df['Close'].values.flatten()
        returns = df['Return'].dropna().values.flatten()
        
        if len(returns) < 50:
            return {'ticker': ticker, 'total_return': 0, 'sharpe': 0, 'trades': 0, 'win_rate': 0}
        
        portfolio_value = float(capital)
        position = 0.0
        entry_price = 0.0
        trades = []
        daily_returns = []
        
        lookback = 40
        
        for i in range(lookback, len(prices)):
            price_window = prices[i-lookback:i+1].astype(float)
            return_window = returns[max(0, i-lookback):i].astype(float)
            
            if len(return_window) < 10:
                continue
            
            signal = generate_signal(ticker, price_window, return_window)
            current_price = float(prices[i])
            prev_price = float(prices[i-1])
            
            if signal.signal in ('strong_buy', 'buy') and position == 0:
                position = portfolio_value / current_price
                entry_price = current_price
                
            elif signal.signal in ('strong_sell', 'sell') and position > 0:
                exit_value = position * current_price
                pnl = exit_value - (position * entry_price)
                trades.append(float(pnl))
                portfolio_value = exit_value
                position = 0.0
            
            if position > 0 and prev_price > 0:
                daily_return = float((current_price - prev_price) / prev_price)
            else:
                daily_return = 0.0
            daily_returns.append(daily_return)
        
        if position > 0:
            portfolio_value = position * float(prices[-1])
        
        total_return = (portfolio_value / capital - 1) * 100
        
        daily_returns_arr = np.array(daily_returns, dtype=float)
        if len(daily_returns_arr) > 1 and np.std(daily_returns_arr) > 0:
            sharpe = float(np.mean(daily_returns_arr) / np.std(daily_returns_arr) * np.sqrt(252))
        else:
            sharpe = 0.0
        
        winning = [t for t in trades if t > 0]
        win_rate = len(winning) / len(trades) * 100 if trades else 0
        
        return {
            'ticker': ticker,
            'total_return': float(total_return),
            'sharpe': float(sharpe),
            'trades': len(trades),
            'win_rate': float(win_rate)
        }


def run_live_signals(tickers: List[str]) -> List[ARTASignal]:
    """Generate live signals for current market data"""
    
    signals = []
    end_date = datetime.now()
    start_date = end_date - timedelta(days=60)
    
    for ticker in tickers:
        try:
            df = yf.download(
                ticker, 
                start=start_date.strftime('%Y-%m-%d'),
                end=end_date.strftime('%Y-%m-%d'),
                progress=False
            )
            
            if df.empty or len(df) < 40:
                continue
            
            prices = df['Close'].values
            returns = (df['Close'].pct_change() * 100).dropna().values
            
            signal = generate_signal(ticker, prices, returns)
            signals.append(signal)
            
            print(f"{ticker}: {signal.signal.upper()} (intensity={signal.intensity:.2f}, regime={signal.regime})")
            
        except Exception as e:
            print(f"{ticker}: Error - {e}")
    
    return signals


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="ARTA Signal Runner")
    parser.add_argument("--mode", choices=["backtest", "live", "submit"], default="backtest")
    parser.add_argument("--tickers", default="SPY,QQQ,AAPL,MSFT,GOOGL,NVDA,AMZN,META,TSLA,JPM")
    parser.add_argument("--start", default="2022-01-01")
    parser.add_argument("--end", default="2024-12-31")
    
    args = parser.parse_args()
    tickers = args.tickers.split(",")
    
    if args.mode == "backtest":
        print("\n" + "="*50)
        print("ARTA BACKTEST MODE")
        print("="*50)
        backtester = ARTABacktester(tickers, args.start, args.end)
        backtester.run_backtest()
        
    elif args.mode == "live":
        print("\n" + "="*50)
        print("ARTA LIVE SIGNALS")
        print("="*50)
        signals = run_live_signals(tickers)
        
        print("\n--- ACTIONABLE SIGNALS ---")
        for s in signals:
            if s.signal != "hold":
                print(f"  {s.ticker}: {s.signal.upper()} @ {s.confidence:.2f}")
        
    elif args.mode == "submit":
        print("\n" + "="*50)
        print("ARTA C2 SUBMISSION MODE")
        print("="*50)
        
        try:
            from collective2_integration import Collective2Client, ARTASignalGenerator
            
            client = Collective2Client()
            generator = ARTASignalGenerator(client)
            
            print("Refreshing current positions from C2...")
            try:
                generator.refresh_positions()
                print(f"  Current positions: {generator.current_positions}")
            except Exception as e:
                print(f"  Warning: Could not refresh positions ({e})")
                print("  Proceeding with local state (may cause duplicate orders)")
            
            signals = run_live_signals(tickers)
            
            for s in signals:
                if s.signal != "hold":
                    result = generator.submit_arta_signal(s.ticker, s.signal, s.confidence)
                    status = "OK" if result.success else "SKIP"
                    print(f"  {s.ticker}: {status} - {result.message}")
                    
        except Exception as e:
            print(f"Error: {e}")
            print("\nSet COLLECTIVE2_API_KEY and COLLECTIVE2_SYSTEM_ID secrets first.")

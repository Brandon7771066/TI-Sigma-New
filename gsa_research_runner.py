"""
GSA RESEARCH RUNNER - Standalone backtesting and analysis
Uses GSA Core engine for TI Framework logic
"""

import numpy as np
import pandas as pd
from datetime import datetime
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
import yfinance as yf

from gsa_core import GSACore, MarketRegime, XiMetrics, GILEScore, Signal


@dataclass
class BacktestResult:
    """Results from a backtest run"""
    total_return: float
    cagr: float
    sharpe_ratio: float
    max_drawdown: float
    win_rate: float
    total_trades: int
    equity_curve: pd.Series
    trade_log: List[Dict]


class GSAResearchRunner:
    """
    Standalone research and backtesting for GSA
    
    Usage:
        runner = GSAResearchRunner()
        runner.add_symbols(['AAPL', 'MSFT', 'GOOGL'])
        runner.load_data(start='2020-01-01', end='2024-12-01')
        result = runner.run_backtest()
    """
    
    def __init__(
        self,
        lookback_short: int = 7,
        lookback_long: int = 60,
        max_position: float = 0.15,
        top_n: int = 4,
        initial_capital: float = 100000
    ):
        self.core = GSACore(
            lookback_short=lookback_short,
            lookback_long=lookback_long
        )
        self.max_position = max_position
        self.top_n = top_n
        self.initial_capital = initial_capital
        
        self.symbols: List[str] = []
        self.market_symbol = 'SPY'
        self.price_data: Dict[str, pd.DataFrame] = {}
        self.return_data: Dict[str, np.ndarray] = {}
    
    def add_symbols(self, symbols: List[str]):
        """Add symbols to universe"""
        self.symbols = symbols
    
    def load_data(self, start: str, end: str):
        """Load price data from yfinance"""
        all_symbols = [self.market_symbol] + self.symbols
        
        print(f"Loading data for {len(all_symbols)} symbols...")
        
        for symbol in all_symbols:
            try:
                df = yf.download(symbol, start=start, end=end, progress=False)
                if len(df) > 0:
                    df = df[['Close']].copy()
                    df.columns = ['close']
                    df['return'] = df['close'].pct_change() * 100
                    self.price_data[symbol] = df
                    print(f"  {symbol}: {len(df)} days")
            except Exception as e:
                print(f"  {symbol}: ERROR - {e}")
        
        print(f"Loaded {len(self.price_data)} symbols")
    
    def _get_arrays(self, symbol: str, end_idx: int, lookback: int) -> Tuple[np.ndarray, np.ndarray]:
        """Get price and return arrays up to index"""
        if symbol not in self.price_data:
            return np.array([]), np.array([])
        
        df = self.price_data[symbol]
        start_idx = max(0, end_idx - lookback)
        
        prices = df['close'].iloc[start_idx:end_idx].values
        returns = df['return'].iloc[start_idx:end_idx].dropna().values
        
        return returns, prices
    
    def _get_vol_ratio(self, symbol: str, end_idx: int) -> float:
        """Calculate recent/long volatility ratio"""
        returns, _ = self._get_arrays(symbol, end_idx, 60)
        if len(returns) < 30:
            return 1.0
        
        recent_vol = float(np.std(returns[-10:])) if len(returns) >= 10 else 1.0
        long_vol = float(np.std(returns[-30:])) if len(returns) >= 30 else 1.0
        
        return recent_vol / max(long_vol, 0.01)
    
    def run_backtest(self) -> BacktestResult:
        """Run full backtest"""
        if not self.price_data:
            raise ValueError("No data loaded. Call load_data() first.")
        
        market_df = self.price_data[self.market_symbol]
        dates = market_df.index
        
        warmup_period = self.core.lookback_long + 10
        
        capital = self.initial_capital
        positions: Dict[str, float] = {}
        equity_curve = []
        trade_log = []
        
        print(f"\nRunning backtest from {dates[warmup_period]} to {dates[-1]}...")
        
        for i in range(warmup_period, len(dates)):
            date = dates[i]
            
            market_returns, market_prices = self._get_arrays(self.market_symbol, i, 60)
            if len(market_returns) < 30:
                equity_curve.append(capital)
                continue
            
            market_xi = self.core.compute_xi_metrics(market_returns, market_prices)
            vol_ratio = self._get_vol_ratio(self.market_symbol, i)
            regime, regime_conf, _ = self.core.classify_regime(
                market_xi.pd, market_xi.constraint, vol_ratio
            )
            
            if regime == MarketRegime.FRACTURE:
                for sym in list(positions.keys()):
                    trade_log.append({
                        'date': date,
                        'symbol': sym,
                        'action': 'SELL',
                        'reason': 'FRACTURE EXIT',
                        'pnl': 0
                    })
                positions = {}
                equity_curve.append(capital)
                continue
            
            candidates = []
            for symbol in self.symbols:
                if symbol not in self.price_data:
                    continue
                
                returns, prices = self._get_arrays(symbol, i, 60)
                if len(returns) < 30:
                    continue
                
                xi_metrics = self.core.compute_xi_metrics(returns, prices)
                gile = self.core.compute_gile(returns, prices, market_returns)
                signal = self.core.generate_signal(xi_metrics, gile, regime, regime_conf)
                
                candidates.append((symbol, signal))
            
            ranked = self.core.rank_candidates(candidates)
            
            picks = [
                (sym, sig, score) 
                for sym, sig, score in ranked 
                if sig.action in ['buy', 'strong_buy']
            ][:self.top_n]
            
            pick_symbols = set([p[0] for p in picks])
            
            for sym in list(positions.keys()):
                if sym not in pick_symbols:
                    trade_log.append({
                        'date': date,
                        'symbol': sym,
                        'action': 'SELL',
                        'reason': 'Not in picks',
                        'position': positions[sym]
                    })
                    del positions[sym]
            
            if picks:
                for sym, sig, score in picks:
                    weight = self.core.calculate_position_size(
                        sig, regime, self.max_position, len(picks)
                    )
                    positions[sym] = weight
                    
                    if weight > 0:
                        trade_log.append({
                            'date': date,
                            'symbol': sym,
                            'action': 'BUY',
                            'weight': weight,
                            'gile': sig.gile,
                            'regime': regime.value
                        })
            
            daily_return = 0.0
            for sym, weight in positions.items():
                if sym in self.price_data:
                    sym_ret = self.price_data[sym]['return'].iloc[i]
                    if not np.isnan(sym_ret):
                        daily_return += weight * (sym_ret / 100)
            
            capital *= (1 + daily_return)
            equity_curve.append(capital)
        
        equity_series = pd.Series(equity_curve, index=dates[warmup_period:])
        
        total_return = (capital / self.initial_capital - 1) * 100
        years = len(equity_curve) / 252
        cagr = ((capital / self.initial_capital) ** (1 / years) - 1) * 100 if years > 0 else 0
        
        daily_returns = equity_series.pct_change().dropna()
        sharpe = float(np.mean(daily_returns) / np.std(daily_returns) * np.sqrt(252)) if len(daily_returns) > 0 else 0
        
        rolling_max = equity_series.cummax()
        drawdown = (equity_series - rolling_max) / rolling_max
        max_dd = abs(float(drawdown.min())) * 100
        
        buy_trades = [t for t in trade_log if t['action'] == 'BUY']
        
        print(f"\n{'='*50}")
        print(f"BACKTEST RESULTS")
        print(f"{'='*50}")
        print(f"Total Return:  {total_return:.1f}%")
        print(f"CAGR:          {cagr:.1f}%")
        print(f"Sharpe Ratio:  {sharpe:.2f}")
        print(f"Max Drawdown:  {max_dd:.1f}%")
        print(f"Total Trades:  {len(buy_trades)}")
        print(f"{'='*50}")
        
        return BacktestResult(
            total_return=total_return,
            cagr=cagr,
            sharpe_ratio=sharpe,
            max_drawdown=max_dd,
            win_rate=0,
            total_trades=len(buy_trades),
            equity_curve=equity_series,
            trade_log=trade_log
        )
    
    def analyze_symbol(self, symbol: str, as_of_idx: int = -1) -> Dict:
        """Analyze a single symbol at a point in time"""
        if symbol not in self.price_data:
            return {'error': f'{symbol} not in data'}
        
        returns, prices = self._get_arrays(
            symbol, 
            len(self.price_data[symbol]) if as_of_idx == -1 else as_of_idx,
            60
        )
        
        market_returns, _ = self._get_arrays(
            self.market_symbol,
            len(self.price_data[self.market_symbol]) if as_of_idx == -1 else as_of_idx,
            60
        )
        
        xi = self.core.compute_xi_metrics(returns, prices)
        gile = self.core.compute_gile(returns, prices, market_returns)
        
        return {
            'symbol': symbol,
            'xi_metrics': {
                'amplitude': xi.amplitude,
                'memory_kernel': xi.memory_kernel,
                'constraint': xi.constraint,
                'xi_signed': xi.xi_signed,
                'pd': xi.pd
            },
            'gile': {
                'goodness': gile.goodness,
                'intuition': gile.intuition,
                'love': gile.love,
                'environment': gile.environment,
                'composite': gile.composite
            }
        }


def main():
    """Example usage"""
    runner = GSAResearchRunner(
        lookback_short=7,
        lookback_long=60,
        max_position=0.15,
        top_n=4,
        initial_capital=100000
    )
    
    runner.add_symbols([
        'AAPL', 'MSFT', 'GOOGL', 'NVDA', 'TSLA', 'META', 'AMZN'
    ])
    
    runner.load_data(start='2020-01-01', end='2024-12-01')
    
    result = runner.run_backtest()
    
    print("\nSymbol Analysis (current):")
    for sym in runner.symbols[:3]:
        analysis = runner.analyze_symbol(sym)
        print(f"\n{sym}:")
        print(f"  GILE: {analysis['gile']['composite']:.2f}")
        print(f"  Ξ signed: {analysis['xi_metrics']['xi_signed']:.2f}")
        print(f"  PD: {analysis['xi_metrics']['pd']:.2f}")


if __name__ == '__main__':
    main()

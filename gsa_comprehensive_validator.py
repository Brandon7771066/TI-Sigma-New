"""
GSA COMPREHENSIVE VALIDATOR
Tests: Sector generalization, stress scenarios, slippage impact, regime detection
"""

import pandas as pd
import numpy as np
from datetime import datetime, timedelta
import yfinance as yf
from gsa_core import GSACore, MarketRegime
from typing import Dict, List, Tuple

class GSAComprehensiveValidator:
    """Full validation suite for GSA algorithm"""
    
    def __init__(self):
        self.gsa = GSACore(lookback_short=7, lookback_long=60)
        self.results = {}
    
    SECTORS = {
        'Technology': ['AAPL', 'MSFT', 'GOOGL', 'NVDA', 'META'],
        'Financials': ['JPM', 'BAC', 'WFC', 'GS', 'MS'],
        'Healthcare': ['JNJ', 'UNH', 'PFE', 'ABBV', 'MRK'],
        'Industrials': ['BA', 'CAT', 'GE', 'RTX', 'MMM'],
        'Consumer': ['AMZN', 'WMT', 'HD', 'TJX', 'MCD'],
        'Energy': ['XOM', 'CVX', 'COP', 'SLB', 'EOG'],
        'Utilities': ['DUK', 'NEE', 'SO', 'D', 'AEP']
    }
    
    CRISIS_PERIODS = {
        '2008_crisis': ('2008-09-15', '2008-12-31'),  # Lehman collapse
        '2020_covid': ('2020-02-15', '2020-04-15'),   # COVID crash
        '2022_bear': ('2022-01-01', '2022-10-31'),    # Fed hiking cycle
    }
    
    def download_sector_data(self, sector_name: str, period: str = "1y") -> Dict[str, pd.DataFrame]:
        """Download data for entire sector"""
        print(f"\n{'='*60}")
        print(f"DOWNLOADING {sector_name.upper()}")
        print(f"{'='*60}")
        
        data = {}
        stocks = self.SECTORS.get(sector_name, [])
        
        for ticker in stocks:
            try:
                df = yf.download(ticker, period=period, progress=False)
                if df is not None and len(df) > 0:
                    data[ticker] = df
                    print(f"  ✓ {ticker}: {len(df)} bars")
            except Exception as e:
                print(f"  ✗ {ticker}: {str(e)[:50]}")
        
        return data
    
    def backtest_symbol(self, symbol: str, price_data: pd.DataFrame, 
                       slippage: float = 0.0) -> Dict:
        """Single symbol backtest with optional slippage"""
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
                'close': closes[i],
                'return': returns[i-1] if i > 0 else 0,
                'signal': signal.action,
                'confidence': signal.confidence,
                'gile': signal.gile,
                'regime': regime.value,
                'xi_pd': xi.pd,
                'constraint': xi.constraint,
            })
        
        signals_df = pd.DataFrame(signals)
        
        action_map = {
            'strong_buy': 2, 'buy': 1, 'hold': 0,
            'sell': -1, 'strong_sell': -2
        }
        signals_df['action_numeric'] = signals_df['signal'].map(action_map)
        signals_df['position'] = (signals_df['action_numeric'] > 0).astype(int)
        signals_df['position'] = signals_df['position'].shift(1).fillna(0)
        
        signals_df['daily_return'] = signals_df['return'] / 100
        
        # Apply slippage if specified
        if slippage > 0:
            signals_df['daily_return'] = signals_df['daily_return'] * (1 - slippage)
        
        signals_df['strategy_return'] = signals_df['position'] * signals_df['daily_return']
        signals_df['cumulative_return'] = (1 + signals_df['strategy_return']).cumprod()
        
        total_ret = (signals_df['cumulative_return'].iloc[-1] - 1) * 100
        annual_ret = (signals_df['cumulative_return'].iloc[-1] ** (252 / len(signals_df)) - 1) * 100
        max_dd = (signals_df['cumulative_return'] / signals_df['cumulative_return'].cummax() - 1).min() * 100
        
        if signals_df['strategy_return'].std() > 0:
            sharpe = signals_df['strategy_return'].mean() / signals_df['strategy_return'].std() * np.sqrt(252)
        else:
            sharpe = 0.0
        
        trades = int((signals_df['position'].diff() != 0).sum())
        
        # Regime analysis
        regime_numeric = signals_df['regime'].map(lambda x: hash(x) % 1000)
        regime_changes = int((regime_numeric.diff() != 0).sum())
        fracture_count = int((signals_df['regime'] == 'fracture').sum())
        
        return {
            'symbol': symbol,
            'total_return': total_ret,
            'annual_return': annual_ret,
            'max_drawdown': max_dd,
            'sharpe': sharpe,
            'trades': trades,
            'regime_changes': regime_changes,
            'fracture_signals': fracture_count,
        }
    
    def validate_sector(self, sector_name: str, period: str = "1y"):
        """Backtest entire sector"""
        data = self.download_sector_data(sector_name, period)
        
        if not data:
            print(f"No data for {sector_name}")
            return None
        
        results = []
        for symbol, price_df in data.items():
            result = self.backtest_symbol(symbol, price_df)
            results.append(result)
            print(f"  {symbol}: {result['annual_return']:+6.2f}% ann | "
                  f"{result['sharpe']:5.2f} Sharpe | {result['max_drawdown']:6.2f}% MaxDD")
        
        return results
    
    def stress_test_crisis(self, crisis_name: str, start_date: str, end_date: str):
        """Backtest during crisis period"""
        print(f"\n{'='*60}")
        print(f"STRESS TEST: {crisis_name.upper()}")
        print(f"Period: {start_date} to {end_date}")
        print(f"{'='*60}")
        
        test_stocks = ['AAPL', 'SPY', 'GLD', 'TLT']  # Mix of equity/defensive
        results = []
        
        for ticker in test_stocks:
            try:
                df = yf.download(ticker, start=start_date, end=end_date, progress=False)
                if df is not None and len(df) > 10:
                    result = self.backtest_symbol(ticker, df)
                    results.append(result)
                    print(f"  {ticker}: {result['annual_return']:+6.2f}% | "
                          f"MaxDD: {result['max_drawdown']:6.2f}% | "
                          f"Fractures: {result['fracture_signals']}")
            except Exception as e:
                print(f"  {ticker}: ERROR {str(e)[:40]}")
        
        return results
    
    def slippage_sensitivity(self, symbol: str = 'AAPL', slippages: List[float] = None):
        """Test impact of slippage on returns"""
        if slippages is None:
            slippages = [0.0, 0.001, 0.005, 0.01, 0.02]
        
        print(f"\n{'='*60}")
        print(f"SLIPPAGE SENSITIVITY ANALYSIS: {symbol}")
        print(f"{'='*60}")
        
        df = yf.download(symbol, period="1y", progress=False)
        if df is None or len(df) < 60:
            print("Insufficient data")
            return []
        
        results = []
        for slip in slippages:
            result = self.backtest_symbol(symbol, df, slippage=slip)
            results.append({**result, 'slippage': slip})
            print(f"  {slip*100:5.2f}% slippage: {result['annual_return']:+6.2f}% | "
                  f"Sharpe: {result['sharpe']:5.2f}")
        
        return results
    
    def regime_detection_accuracy(self):
        """Test regime detection during known market events"""
        print(f"\n{'='*60}")
        print(f"REGIME DETECTION ACCURACY")
        print(f"{'='*60}")
        
        test_cases = [
            ('2020-02-01', '2020-04-30', 'COVID Crash → Recovery'),
            ('2022-01-01', '2022-12-31', '2022 Bear Market'),
            ('2023-01-01', '2024-12-31', '2023-24 Bull Market'),
        ]
        
        for start, end, label in test_cases:
            df = yf.download('SPY', start=start, end=end, progress=False)
            
            if df is None or len(df) < 20:
                continue
            
            result = self.backtest_symbol('SPY', df)
            
            # Analyze regime distribution
            close_values = df['Close'].values
            closes = np.array(close_values.flatten() if hasattr(close_values, 'flatten') else close_values, dtype=float)
            dd = (np.max(closes) - closes) / np.max(closes) * 100
            
            print(f"  {label}")
            print(f"    Max Drawdown: {dd.max():.1f}%")
            print(f"    Fracture Signals: {result['fracture_signals']}")
            print(f"    Regime Changes: {result['regime_changes']}")
            print(f"    Strategy Return: {result['annual_return']:.2f}%")
        
        return test_cases
    
    def run_full_validation(self):
        """Execute complete validation suite"""
        print("\n" + "="*60)
        print("GSA COMPREHENSIVE VALIDATION SUITE")
        print("="*60)
        
        # 1. Sector validation
        print("\n[PHASE 1] SECTOR GENERALIZATION TEST")
        sector_results = {}
        for sector in self.SECTORS.keys():
            sector_results[sector] = self.validate_sector(sector, period="1y")
        
        # 2. Stress testing
        print("\n[PHASE 2] CRISIS STRESS TESTS")
        stress_results = {}
        for crisis_name, (start, end) in self.CRISIS_PERIODS.items():
            stress_results[crisis_name] = self.stress_test_crisis(crisis_name, start, end)
        
        # 3. Slippage sensitivity
        print("\n[PHASE 3] SLIPPAGE IMPACT ANALYSIS")
        slippage_results = self.slippage_sensitivity('AAPL')
        
        # 4. Regime detection
        print("\n[PHASE 4] REGIME DETECTION VALIDATION")
        self.regime_detection_accuracy()
        
        # Summary statistics
        print("\n" + "="*60)
        print("VALIDATION SUMMARY")
        print("="*60)
        
        all_sector_results = [r for results in sector_results.values() for r in (results or [])]
        if all_sector_results:
            avg_annual = np.mean([r['annual_return'] for r in all_sector_results])
            avg_sharpe = np.mean([r['sharpe'] for r in all_sector_results])
            avg_dd = np.mean([r['max_drawdown'] for r in all_sector_results])
            
            print(f"Sectors Tested: {len(sector_results)}")
            print(f"Stocks Tested: {len(all_sector_results)}")
            print(f"Average Annual Return: {avg_annual:.2f}%")
            print(f"Average Sharpe Ratio: {avg_sharpe:.2f}")
            print(f"Average Max Drawdown: {avg_dd:.2f}%")
        
        # Slippage impact
        if slippage_results:
            no_slip = slippage_results[0]['annual_return']
            high_slip = slippage_results[-1]['annual_return']
            impact = no_slip - high_slip
            print(f"\nSlippage Impact (0% → 2%): {impact:.2f}% return reduction")
        
        return {
            'sector_results': sector_results,
            'stress_results': stress_results,
            'slippage_results': slippage_results,
        }


if __name__ == "__main__":
    validator = GSAComprehensiveValidator()
    results = validator.run_full_validation()

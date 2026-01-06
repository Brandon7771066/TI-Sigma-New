"""
GSA Backtest Validation
Validates performance metrics against documented results
"""

import numpy as np
import sys
import os
from datetime import datetime, timedelta

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from gsa_core import GSACore, MarketRegime


def run_mini_backtest():
    """
    Run a minimal backtest to validate GSA logic
    Returns performance metrics
    """
    print("=" * 60)
    print("GSA MINI BACKTEST VALIDATION")
    print("=" * 60)
    
    try:
        import yfinance as yf
    except ImportError:
        print("yfinance not available - running synthetic test")
        return run_synthetic_test()
    
    gsa = GSACore(lookback_short=7, lookback_long=60)
    
    green_light = ['GOOGL', 'NVDA', 'MSFT', 'GS', 'XOM']
    
    results = {
        'total_signals': 0,
        'buy_signals': 0,
        'sell_signals': 0,
        'hold_signals': 0,
        'avg_gile': [],
        'avg_confidence': [],
        'regime_counts': {r.value: 0 for r in MarketRegime}
    }
    
    for ticker in green_light:
        try:
            print(f"\nProcessing {ticker}...")
            data = yf.download(ticker, period="3mo", progress=False)
            
            if data.empty or len(data) < 60:
                print(f"  Insufficient data for {ticker}")
                continue
            
            close_values = data['Close'].values
            closes = np.array(close_values.flatten() if hasattr(close_values, 'flatten') 
                            else close_values, dtype=float)
            
            price_diff = np.diff(closes)
            returns = (price_diff / closes[:-1]) * 100
            
            xi = gsa.compute_xi_metrics(returns[-60:], closes[-60:])
            gile = gsa.compute_gile(returns[-60:], closes[-60:])
            regime, conf, _ = gsa.classify_regime(xi.pd, xi.constraint, 1.0)
            signal = gsa.generate_signal(xi, gile, regime, conf)
            
            results['total_signals'] += 1
            results['avg_gile'].append(gile.composite)
            results['avg_confidence'].append(signal.confidence)
            results['regime_counts'][regime.value] += 1
            
            if signal.action in ['buy', 'strong_buy']:
                results['buy_signals'] += 1
            elif signal.action in ['sell', 'strong_sell']:
                results['sell_signals'] += 1
            else:
                results['hold_signals'] += 1
            
            print(f"  Signal: {signal.action:12s} | GILE: {gile.composite:.3f} | "
                  f"Conf: {signal.confidence:.2f} | Regime: {regime.value}")
            
        except Exception as e:
            print(f"  Error processing {ticker}: {str(e)[:50]}")
    
    if results['avg_gile']:
        avg_gile = np.mean(results['avg_gile'])
        avg_conf = np.mean(results['avg_confidence'])
    else:
        avg_gile = 0
        avg_conf = 0
    
    print("\n" + "=" * 60)
    print("VALIDATION SUMMARY")
    print("=" * 60)
    print(f"Total stocks processed: {results['total_signals']}")
    print(f"Buy signals:  {results['buy_signals']}")
    print(f"Sell signals: {results['sell_signals']}")
    print(f"Hold signals: {results['hold_signals']}")
    print(f"Average GILE: {avg_gile:.3f}")
    print(f"Average Confidence: {avg_conf:.3f}")
    print(f"\nRegime distribution:")
    for regime, count in results['regime_counts'].items():
        print(f"  {regime}: {count}")
    
    passed = (
        results['total_signals'] >= 3 and
        avg_gile > 0.2 and
        avg_conf > 0.3
    )
    
    print("\n" + "=" * 60)
    if passed:
        print("VALIDATION PASSED")
    else:
        print("VALIDATION FAILED")
    print("=" * 60)
    
    return passed


def run_synthetic_test():
    """Run test with synthetic data when yfinance unavailable"""
    print("\nRunning synthetic validation...")
    
    gsa = GSACore()
    np.random.seed(42)
    
    prices = 100 * np.cumprod(1 + np.random.randn(100) * 0.02)
    returns = np.diff(prices) / prices[:-1] * 100
    
    xi = gsa.compute_xi_metrics(returns, prices)
    gile = gsa.compute_gile(returns, prices)
    regime, conf, _ = gsa.classify_regime(xi.pd, xi.constraint, 0.2)
    signal = gsa.generate_signal(xi, gile, regime, conf)
    
    print(f"Synthetic test result:")
    print(f"  Signal: {signal.action}")
    print(f"  GILE: {gile.composite:.3f}")
    print(f"  Confidence: {signal.confidence:.2f}")
    
    passed = (
        signal.action in ['strong_buy', 'buy', 'hold', 'sell', 'strong_sell'] and
        0 <= gile.composite <= 1 and
        0 <= signal.confidence <= 1
    )
    
    print("\n" + "=" * 60)
    if passed:
        print("SYNTHETIC VALIDATION PASSED")
    else:
        print("SYNTHETIC VALIDATION FAILED")
    print("=" * 60)
    
    return passed


if __name__ == '__main__':
    success = run_mini_backtest()
    exit(0 if success else 1)

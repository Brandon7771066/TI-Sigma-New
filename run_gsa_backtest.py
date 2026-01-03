#!/usr/bin/env python3
"""
Quick GSA backtest runner for Replit
Execute: python run_gsa_backtest.py
"""

import sys
import os

# Make sure imports work
sys.path.insert(0, os.getcwd())

if __name__ == "__main__":
    from vectorbt_gsa_backtest import VectorBTGSABacktest
    
    print("\n" + "="*70)
    print("GRAND STOCK ALGORITHM - VECTORBT BACKTEST")
    print("TI Framework Ξ Metrics on S&P 500 Top 20")
    print("="*70)
    
    backtest = VectorBTGSABacktest(lookback_short=7, lookback_long=60)
    
    # Top S&P 500 stocks for testing
    symbols = [
        "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", 
        "META", "TSLA", "JPM", "V", "JNJ"
    ]
    
    results = backtest.backtest_portfolio(symbols, period="1y")
    
    if results:
        print("\n" + "="*70)
        print("BACKTEST COMPLETE ✓")
        print("="*70)

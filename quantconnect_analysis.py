Can """
QuantConnect Performance Analysis - HONEST Assessment

The 108% return over the FULL backtest period needs proper annualization.

Rule of 72: Money doubles every ~7 years at 10% annual return
S&P 500 historical average: ~10% annually
"""

import numpy as np

def analyze_backtest_performance(
    total_return_pct: float,
    start_year: int,
    end_year: int
):
    """
    Analyze backtest performance with proper annualization
    """
    years = end_year - start_year
    
    # Compound Annual Growth Rate (CAGR)
    cagr = ((1 + total_return_pct/100) ** (1/years) - 1) * 100
    
    # S&P 500 benchmark (historical average ~10%)
    sp500_benchmark = 10.0
    sp500_total_over_period = ((1 + sp500_benchmark/100) ** years - 1) * 100
    
    print("=" * 60)
    print("QUANTCONNECT BACKTEST - HONEST ANALYSIS")
    print("=" * 60)
    
    print(f"\nBacktest Period: {start_year} - {end_year} ({years} years)")
    print(f"Total Return: {total_return_pct:.2f}%")
    print(f"CAGR (Annualized): {cagr:.2f}%")
    
    print(f"\n--- BENCHMARK COMPARISON ---")
    print(f"S&P 500 Average Annual: 10%")
    print(f"S&P 500 Total over {years} years: {sp500_total_over_period:.1f}%")
    
    if cagr > sp500_benchmark:
        alpha = cagr - sp500_benchmark
        print(f"\nAlpha (excess return): +{alpha:.2f}% annually")
        verdict = "OUTPERFORMING BENCHMARK"
    else:
        underperformance = sp500_benchmark - cagr
        print(f"\nUnderperformance: -{underperformance:.2f}% annually")
        verdict = "UNDERPERFORMING BENCHMARK"
    
    print(f"\nVERDICT: {verdict}")
    
    # Calculate what the algorithm should have returned to be impressive
    print(f"\n--- WHAT WOULD BE IMPRESSIVE ---")
    for target_cagr in [15, 20, 25, 30]:
        target_total = ((1 + target_cagr/100) ** years - 1) * 100
        print(f"  {target_cagr}% CAGR = {target_total:.0f}% total over {years} years")
    
    return {
        'years': years,
        'total_return': total_return_pct,
        'cagr': cagr,
        'sp500_total': sp500_total_over_period,
        'verdict': verdict
    }


# Brandon's actual results
result = analyze_backtest_performance(
    total_return_pct=108.18,
    start_year=2014,
    end_year=2024
)

print("\n" + "=" * 60)
print("REALITY CHECK")
print("=" * 60)
print("""
108% over 10 years = 7.6% CAGR
S&P 500 over same period = ~150-200% (it was a bull run!)

This means the current algorithm is actually UNDERPERFORMING
a simple buy-and-hold of the S&P 500.

HOWEVER: This could still be valuable if:
1. Lower volatility (smoother returns)
2. Lower max drawdown (less risk)
3. Better Sharpe ratio (risk-adjusted returns)
4. Uncorrelated to market (diversification value)

Check the Sharpe Ratio in the full report!
Target: > 1.5 for institutional interest
""")

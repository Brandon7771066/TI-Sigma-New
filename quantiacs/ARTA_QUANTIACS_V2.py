# =============================================================================
# ARTA V2 - Quantiacs Optimized
# =============================================================================
# Simplified momentum-based algorithm tuned for Quantiacs environment
# Uses proven factors: momentum, volatility-adjusted returns, trend
# =============================================================================

import xarray as xr
import numpy as np
import qnt.data as qndata
import qnt.output as output
import qnt.ta as qnta
import qnt.backtester as qnbt

def strategy(data):
    """
    ARTA V2 - Momentum + Trend + Volatility Filter
    
    Long-only NASDAQ-100 strategy optimized for Quantiacs
    """
    close = data.sel(field='close')
    
    # Technical indicators using Quantiacs built-in functions
    sma_fast = qnta.sma(close, 20)
    sma_slow = qnta.sma(close, 50)
    sma_trend = qnta.sma(close, 200)
    
    # Get latest values
    sma_fast_last = sma_fast.isel(time=-1)
    sma_slow_last = sma_slow.isel(time=-1)
    sma_trend_last = sma_trend.isel(time=-1)
    close_last = close.isel(time=-1)
    
    # Momentum: 20-day return
    if close.time.size >= 21:
        close_20d_ago = close.isel(time=-21)
        momentum = (close_last - close_20d_ago) / close_20d_ago
    else:
        momentum = xr.zeros_like(close_last)
    
    # Volatility filter: 20-day rolling std
    returns = close.diff('time') / close.shift(time=1)
    volatility = returns.rolling(time=20).std().isel(time=-1)
    vol_median = float(volatility.median())
    
    # Weight calculation
    weights = xr.zeros_like(close_last)
    
    # Conditions for going long:
    # 1. Price above 200 SMA (uptrend)
    # 2. Fast SMA above slow SMA (momentum confirmation)
    # 3. Positive momentum
    # 4. Not excessive volatility
    
    uptrend = close_last > sma_trend_last
    ma_bullish = sma_fast_last > sma_slow_last
    positive_momentum = momentum > 0
    low_vol = volatility < (vol_median * 1.5)
    
    # Combine signals
    signal = uptrend & ma_bullish & positive_momentum & low_vol
    
    # Weight by momentum strength (normalized)
    momentum_normalized = momentum / (momentum.std() + 1e-8)
    momentum_normalized = momentum_normalized.clip(-2, 2)
    
    # Apply weights
    weights = xr.where(signal, 0.5 + 0.5 * (momentum_normalized / 2), 0)
    weights = weights.clip(0, 1)
    
    # Apply liquidity filter
    is_liquid = data.sel(field="is_liquid").isel(time=-1)
    weights = weights * is_liquid
    
    # Normalize to sum to 1
    total = float(weights.sum())
    if total > 1:
        weights = weights / total
    elif total > 0:
        # Scale up if under-invested
        weights = weights / total * 0.8  # 80% invested
    
    return weights

# Run backtest
weights = qnbt.backtest(
    competition_type="stocks_nasdaq100",
    load_data=lambda period: qndata.stocks.load_ndx_data(tail=period),
    lookback_period=365,
    test_period=5*365,  # 5 years for better stats
    strategy=strategy,
    analyze=True
)

# Clean and validate
weights = output.clean(weights, qndata.stocks.load_ndx_data(tail=365*6), "stocks_nasdaq100")
output.write(weights)

print("\n" + "="*60)
print("ARTA V2 BACKTEST COMPLETE")
print("="*60)
print("If Sharpe > 0.7, click 'Submit to the contest' button!")
print("="*60)

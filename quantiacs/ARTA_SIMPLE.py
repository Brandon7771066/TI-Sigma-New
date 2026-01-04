# =============================================================================
# ARTA SIMPLE - Proven Quantiacs Strategy
# =============================================================================
# Ultra-simple momentum strategy that should definitely work
# Copy this ENTIRE file into a Quantiacs notebook cell
# =============================================================================

import xarray as xr
import numpy as np
import qnt.data as qndata
import qnt.output as output
import qnt.ta as qnta
import qnt.backtester as qnbt

def strategy(data):
    """
    Simple momentum strategy: 
    - Buy stocks in uptrend (price > 200 SMA)
    - With positive short-term momentum (price > 20 SMA)
    - Equal weight among qualifying stocks
    """
    close = data.sel(field='close')
    is_liquid = data.sel(field='is_liquid')
    
    # Moving averages
    sma_20 = qnta.sma(close, 20).isel(time=-1)
    sma_200 = qnta.sma(close, 200).isel(time=-1)
    close_now = close.isel(time=-1)
    
    # Long signal: price above both SMAs
    signal = (close_now > sma_20) & (close_now > sma_200)
    
    # Apply liquidity filter
    liquid = is_liquid.isel(time=-1)
    signal = signal * liquid
    
    # Equal weight among signals
    weights = xr.where(signal > 0, 1.0, 0.0)
    
    # Normalize
    total = float(weights.sum())
    if total > 0:
        weights = weights / total
    
    return weights

# Run backtest with 5 years of data
weights = qnbt.backtest(
    competition_type="stocks_nasdaq100",
    load_data=lambda period: qndata.stocks.load_ndx_data(tail=period),
    lookback_period=365,
    test_period=5*365,
    strategy=strategy,
    analyze=True
)

output.write(weights)
print("Done! Check Sharpe ratio above.")

# =============================================================================
# ARTA ALGORITHM FOR QUANTIACS - COPY THIS INTO strategy.ipynb
# =============================================================================
# Instructions:
# 1. In Quantiacs, click on "strategy.ipynb" 
# 2. Delete all existing cells
# 3. Create a new cell and paste all the code below
# 4. Run the cell (Shift+Enter)
# 5. Wait for backtest to complete
# 6. Click "Submit to the contest" button (top right)
# =============================================================================

import xarray as xr
import numpy as np
import qnt.data as qndata
import qnt.output as output
import qnt.stats as qnstats
import qnt.ta as qnta
import qnt.backtester as qnbt

def strategy(data):
    """
    ARTA Algorithm - Adaptive Regime-Transition Algorithm
    Uses GILE-inspired factors for signal generation
    """
    close = data.sel(field='close')
    high = data.sel(field='high')
    low = data.sel(field='low')
    vol = data.sel(field='vol')
    
    lb_short = 7
    lb_long = 30
    
    weights = xr.zeros_like(close.isel(time=-1))
    
    for asset in data.asset.values:
        try:
            prices = close.sel(asset=asset).values
            prices_clean = prices[~np.isnan(prices)]
            
            if len(prices_clean) < lb_long + 5:
                continue
                
            returns = np.diff(prices_clean) / prices_clean[:-1]
            returns = returns[~np.isnan(returns)]
            
            if len(returns) < lb_long:
                continue
            
            recent_returns = returns[-lb_short:]
            long_returns = returns[-lb_long:]
            
            G = np.corrcoef(np.arange(lb_short), prices_clean[-lb_short:])[0,1] if len(prices_clean) >= lb_short else 0
            G = 0 if np.isnan(G) else G
            
            I = 1.0 - (np.std(recent_returns) / (np.std(long_returns) + 1e-8)) if np.std(long_returns) > 0 else 0
            I = np.clip(I, 0, 1)
            
            L = np.mean(recent_returns) / (np.std(recent_returns) + 1e-8) if np.std(recent_returns) > 0 else 0
            L = np.clip(L * 2, -1, 1)
            
            vol_ratio = np.std(recent_returns) / (np.std(long_returns) + 1e-8) if np.std(long_returns) > 0 else 1
            E = 1.0 if 0.5 < vol_ratio < 1.5 else 0.5
            
            intensity = 0.25 * (abs(G) + I + (L + 1) / 2 + E)
            
            trend = np.mean(recent_returns)
            
            ma_short = np.mean(prices_clean[-5:]) if len(prices_clean) >= 5 else prices_clean[-1]
            ma_long = np.mean(prices_clean[-20:]) if len(prices_clean) >= 20 else prices_clean[-1]
            ma_cross = 1 if ma_short > ma_long else -1
            
            recent_vol = np.std(recent_returns)
            long_vol = np.std(long_returns)
            constraint = np.mean(np.abs(returns[-5:])) / (np.std(returns[-5:]) + 1e-8)
            
            if constraint > 3.0 and recent_vol > long_vol * 1.5:
                regime = "fracture"
                multiplier = 0.0
            elif recent_vol < long_vol * 0.8:
                regime = "compression"
                multiplier = 0.5
            else:
                regime = "expansion"
                multiplier = 1.0
            
            if regime == "fracture":
                weight = 0.0
            elif intensity >= 0.60 and trend > 0.001 and ma_cross > 0:
                weight = intensity * multiplier
            elif intensity >= 0.45 and trend > 0 and ma_cross > 0:
                weight = intensity * multiplier * 0.7
            elif intensity >= 0.45 and (trend < -0.0005 or ma_cross < 0):
                weight = 0.0
            elif intensity < 0.35 or (trend < 0 and ma_cross < 0):
                weight = 0.0
            else:
                weight = intensity * multiplier * 0.3
            
            weight = float(np.clip(weight, 0.0, 1.0))
            weights.loc[{'asset': asset}] = weight
            
        except Exception as e:
            continue
    
    total = float(weights.sum())
    if total > 1.0:
        weights = weights / total
    
    return weights

weights = qnbt.backtest(
    competition_type="stocks_nasdaq100",
    load_data=lambda period: qndata.stocks.load_ndx_data(tail=period),
    lookback_period=365,
    test_period=3*365,
    strategy=strategy,
    analyze=True
)

weights = output.clean(weights, qndata.stocks.load_ndx_data(tail=365*4), "stocks_nasdaq100")
output.check(weights, qndata.stocks.load_ndx_data(tail=365*4), "stocks_nasdaq100")
output.write(weights)

print("\n" + "="*50)
print("ARTA ALGORITHM BACKTEST COMPLETE")
print("="*50)
print("If Sharpe > 0.7, click 'Submit to the contest' button!")
print("="*50)

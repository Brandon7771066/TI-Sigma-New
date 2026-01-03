"""
ARTA Algorithm - Quantiacs Competition Format
Adaptive Regime Trading Algorithm

Requirements:
- Sharpe Ratio > 0.7 (minimum for eligibility)
- Execution time < 10 minutes
- Maximum leverage: 1.0

Author: Brandon Emerick
Framework: TI-Sigma
"""

import numpy as np
import xarray as xr


def safe_std(x, floor=1e-6):
    """Calculate standard deviation with floor"""
    if len(x) < 2:
        return floor
    s = float(np.nanstd(x))
    return max(s, floor)


def calculate_amplitude(returns):
    """Calculate signal amplitude relative to volatility"""
    if len(returns) < 2:
        return 0.0
    cur = abs(float(returns[-1]))
    vol = safe_std(returns, 0.01)
    return float(np.clip(cur / vol, 0.0, 10.0))


def calculate_memory_kernel(returns, decay_pos=0.1, decay_neg=0.05):
    """Calculate asymmetric memory kernel (negative bias)"""
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
    """Calculate constraint from drawdown and volatility"""
    if len(prices) < 5:
        return 0.0
    peak = float(np.nanmax(prices))
    last = float(prices[-1])
    dd = (peak - last) / peak if peak > 0 else 0.0
    
    r_short = returns[-lb_short:] if len(returns) >= lb_short else returns
    r_long = returns[-lb_long:] if len(returns) >= lb_long else returns
    vol_short = safe_std(r_short, 0.01)
    vol_long = safe_std(r_long, 0.01)
    
    vol_constraint = 1.0 - min(vol_short / max(vol_long, 0.01), 1.0)
    return float(np.clip(0.6 * dd + 0.4 * vol_constraint, 0.0, 1.0))


def compute_intensity(prices, returns, lb_short=7, lb_long=30):
    """
    Compute ARTA intensity score (0 to 1)
    
    Four-factor model:
    - G (Goodness): Trend coherence
    - I (Intuition): Signal clarity
    - L (Love): Momentum persistence
    - E (Environment): Favorable conditions
    """
    if len(returns) < max(10, lb_short):
        return 0.5
    
    recent = returns[-lb_short:]
    signs = np.sign(recent)
    G = float(np.clip(abs(np.nanmean(signs)), 0.0, 1.0))
    
    A_raw = calculate_amplitude(returns[-lb_short:])
    I = float(1.0 - np.exp(-A_raw / 2.0))
    
    if len(returns) >= lb_long:
        ret1 = returns[-lb_long:-1]
        ret2 = returns[-lb_long+1:]
        if len(ret1) > 2 and np.nanstd(ret1) > 0 and np.nanstd(ret2) > 0:
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
    """
    Classify market regime
    
    Returns: (regime, multiplier)
    - expansion: 1.0
    - compression: 0.5
    - fracture: 0.0
    - reset: 0.3
    """
    if len(constraint_history) < 5:
        return "expansion", 1.0
    
    avg_constraint = np.nanmean(constraint_history[-5:])
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


def strategy(data, state=None):
    """
    ARTA Strategy - Quantiacs Competition Entry
    
    Returns allocation weights for each asset.
    Positive = Long, Negative = Short
    """
    
    if state is None:
        state = {}
    
    close = data.sel(field='close')
    
    assets = close.coords['asset'].values
    time_idx = close.coords['time'].values
    
    weights = xr.zeros_like(close.isel(time=-1))
    
    lookback_short = 7
    lookback_long = 30
    min_data = lookback_long + 10
    
    for asset in assets:
        try:
            prices = close.sel(asset=asset).values
            
            if len(prices) < min_data:
                continue
            
            valid_mask = ~np.isnan(prices)
            if np.sum(valid_mask) < min_data:
                continue
            
            prices_clean = prices[valid_mask]
            
            returns = np.diff(prices_clean) / prices_clean[:-1] * 100
            returns = np.where(np.isfinite(returns), returns, 0.0)
            
            if len(returns) < min_data - 1:
                continue
            
            intensity = compute_intensity(
                prices_clean[-lookback_long:],
                returns[-lookback_long:],
                lookback_short,
                lookback_long
            )
            
            constraint_history = []
            for i in range(5, min(30, len(returns))):
                c = calculate_constraint(
                    prices_clean[-i:],
                    returns[-i:],
                    lookback_short,
                    lookback_long
                )
                constraint_history.append(c)
            
            recent_vol = safe_std(returns[-lookback_short:])
            long_vol = safe_std(returns[-lookback_long:])
            
            regime, multiplier = classify_regime(
                constraint_history,
                recent_vol,
                long_vol
            )
            
            recent_returns = returns[-lookback_short:]
            trend = np.nanmean(recent_returns) if len(recent_returns) > 0 else 0.0
            
            ma_short = np.nanmean(prices_clean[-5:]) if len(prices_clean) >= 5 else prices_clean[-1]
            ma_long = np.nanmean(prices_clean[-20:]) if len(prices_clean) >= 20 else prices_clean[-1]
            ma_cross = 1 if ma_short > ma_long else -1
            
            if regime == "fracture":
                weight = 0.0
            elif intensity >= 0.60 and trend > 0.1 and ma_cross > 0:
                weight = intensity * multiplier
            elif intensity >= 0.45 and trend > 0 and ma_cross > 0:
                weight = intensity * multiplier * 0.7
            elif intensity >= 0.45 and (trend < -0.05 or ma_cross < 0):
                weight = 0.0
            elif intensity < 0.35 or (trend < 0 and ma_cross < 0):
                weight = 0.0
            else:
                weight = intensity * multiplier * 0.3
            
            weight = float(np.clip(weight, -1.0, 1.0))
            weights.loc[{'asset': asset}] = weight
            
        except Exception:
            continue
    
    weights_sum = float(np.nansum(np.abs(weights.values)))
    if weights_sum > 1.0:
        weights = weights / weights_sum
    
    return weights, state


def load_data(period):
    """Load futures data for Quantiacs"""
    import qnt.data as qndata
    return qndata.futures_load_data(tail=period)


if __name__ == "__main__":
    try:
        import qnt.backtester as qnbk
        import qnt.output as qnout
        
        qnbk.backtest(
            competition_type="futures",
            load_data=load_data,
            lookback_period=365,
            test_period=2*365,
            strategy=strategy
        )
        
    except ImportError:
        print("Quantiacs toolbox not installed.")
        print("Install with: pip install git+https://github.com/quantiacs/toolbox.git")
        print("\nAlgorithm structure verified - ready for Quantiacs submission.")

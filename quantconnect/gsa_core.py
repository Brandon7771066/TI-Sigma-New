# gsa_core.py
import numpy as np

SACRED_MIN, SACRED_MAX = -0.666, 0.333

class MarketRegime:
    EXPANSION = "expansion"
    COMPRESSION = "compression"
    FRACTURE = "fracture"
    RESET = "reset"

def safe_std(x: np.ndarray, floor: float = 1e-6) -> float:
    s = float(np.std(x)) if len(x) > 1 else 0.0
    return max(s, floor)

def calculate_amplitude(returns: np.ndarray) -> float:
    if len(returns) < 2:
        return 0.0
    cur = abs(float(returns[-1]))
    vol = safe_std(returns, 0.01)
    return float(np.clip(cur / vol, 0.0, 10.0))

def calculate_memory_kernel(returns: np.ndarray, decay_pos: float = 0.1, decay_neg: float = 0.05) -> float:
    if len(returns) < 3:
        return 0.5
    r = returns[::-1]
    pos = r[r > 0]
    neg = r[r < 0]
    k_pos = sum(abs(float(v)) * np.exp(-decay_pos * i) for i, v in enumerate(pos))
    k_neg = sum(abs(float(v)) * np.exp(-decay_neg * i) for i, v in enumerate(neg))
    tot = k_pos + k_neg
    return float(np.clip(k_neg / tot, 0.0, 1.0)) if tot > 0 else 0.5

def calculate_constraint(prices: np.ndarray, returns: np.ndarray, lookback_short: int = 7, lookback_long: int = 30) -> float:
    if len(prices) < 5:
        return 0.0
    peak = float(np.max(prices))
    last = float(prices[-1])
    dd = (peak - last) / peak if peak > 0 else 0.0

    r_short = returns[-lookback_short:] if len(returns) >= lookback_short else returns
    r_long = returns[-lookback_long:] if len(returns) >= lookback_long else returns
    vol_short = safe_std(r_short, 0.01)
    vol_long = safe_std(r_long, 0.01)

    vol_constraint = 1.0 - min(vol_short / max(vol_long, 0.01), 1.0)
    return float(np.clip(0.6 * dd + 0.4 * vol_constraint, 0.0, 1.0))

def valence_weight(return_pct: float) -> float:
    if return_pct > 5.0: return 1.5
    if return_pct > SACRED_MAX: return 1.0
    if return_pct > SACRED_MIN: return 1.0
    if return_pct > -5.0: return 2.0
    return 6.0

def compute_xi(prices: np.ndarray, returns_pct: np.ndarray,
               lb_short: int = 7, lb_long: int = 30) -> dict:
    """Original multiplicative Ξ formula (for backwards compatibility)."""
    if len(returns_pct) < max(5, lb_short):
        return dict(A=0.0, kappa=0.5, C=0.0, xi_unsigned=0.0, xi_signed=0.0, pd=0.0)

    A = calculate_amplitude(returns_pct[-lb_short:])
    kappa = calculate_memory_kernel(returns_pct[-lb_long:])
    C = calculate_constraint(prices[-lb_long:], returns_pct[-lb_long:], lb_short, lb_long)

    xi_unsigned = A * kappa * C
    r = float(returns_pct[-1])
    sgn = 1.0 if r >= 0 else -1.0
    xi_signed = sgn * xi_unsigned * valence_weight(r)

    pd = float(np.clip(np.sign(xi_signed) * np.log1p(abs(xi_signed)), -3.0, 2.0))
    return dict(A=A, kappa=kappa, C=C, xi_unsigned=xi_unsigned, xi_signed=xi_signed, pd=pd)


def compute_xi_ti_aligned(prices: np.ndarray, returns_pct: np.ndarray,
                          lb_short: int = 7, lb_long: int = 30) -> dict:
    """
    TI-Aligned Ξ Formula based on Tralseness theory.
    
    Core Principles:
    - 0.85 = Major Truth threshold (causation/manifestation)
    - 0.92 = √0.85 = Sustainable Coherence threshold
    - Each GILE dimension targets 0.92 independently
    - Formula should produce values that can reach these thresholds
    
    Components (rescaled to [0,1]):
    - G (Goodness): Trend alignment - are returns moving coherently?
    - I (Intuition): Signal clarity - how clear is the directional signal?
    - L (Love): Momentum persistence - is the trend self-reinforcing?
    - E (Environment): Favorable conditions - low constraint, expansion regime
    
    Formula: Ξ = (G × I × L × E)^0.25 (geometric mean of 4 dimensions)
    """
    if len(returns_pct) < max(10, lb_short):
        return dict(G=0.0, I=0.0, L=0.0, E=0.0, xi_ti=0.0, 
                    above_085=False, above_092=False, regime_score=0.0)
    
    # G (Goodness): Trend coherence - correlation of returns over time
    # High G = returns consistently positive or negative (not oscillating)
    recent = returns_pct[-lb_short:]
    signs = np.sign(recent)
    sign_consistency = abs(np.mean(signs))  # 1.0 if all same sign, 0.0 if balanced
    G = float(np.clip(sign_consistency, 0.0, 1.0))
    
    # I (Intuition): Signal clarity - how "loud" is the signal vs noise?
    # Use asymptotic scaling so it CAN reach 1.0
    A_raw = calculate_amplitude(returns_pct[-lb_short:])
    I = float(1.0 - np.exp(-A_raw / 2.0))  # Asymptotes to 1.0 as amplitude increases
    
    # L (Love): Momentum persistence - are gains building on gains?
    # Measure autocorrelation of returns
    if len(returns_pct) >= lb_long:
        ret1 = returns_pct[-lb_long:-1]
        ret2 = returns_pct[-lb_long+1:]
        if len(ret1) > 2 and np.std(ret1) > 0 and np.std(ret2) > 0:
            autocorr = np.corrcoef(ret1, ret2)[0, 1]
            L = float(np.clip((autocorr + 1) / 2, 0.0, 1.0))  # Rescale [-1,1] to [0,1]
        else:
            L = 0.5
    else:
        L = 0.5
    
    # E (Environment): Favorable conditions = inverse of constraint
    # Low drawdown + low volatility ratio = good environment
    C_raw = calculate_constraint(prices[-lb_long:], returns_pct[-lb_long:], lb_short, lb_long)
    E = float(1.0 - C_raw)  # Invert: low constraint = high E
    
    # Compute Ξ using weighted average (additive)
    # Weights based on TEST 4 correlations: L > G > E > I
    xi_raw = float(0.30 * G + 0.20 * I + 0.35 * L + 0.15 * E)
    
    # Scale to [0, 1] using logistic transformation
    # This allows reaching 0.85+ while preserving ordering
    # k controls steepness, x0 is the midpoint
    k = 6.0  # Steepness
    x0 = 0.45  # Midpoint (near observed mean)
    xi_ti = float(1.0 / (1.0 + np.exp(-k * (xi_raw - x0))))
    
    # Key TI thresholds
    above_085 = xi_ti >= 0.85  # Major Truth
    above_092 = xi_ti >= 0.92  # Sustainable Coherence
    
    # Regime score: weighted combination for trading signal
    regime_score = float(np.clip(
        0.3 * G + 0.3 * I + 0.2 * L + 0.2 * E,
        0.0, 1.0
    ))
    
    return dict(
        G=G, I=I, L=L, E=E,
        xi_raw=xi_raw,
        xi_ti=xi_ti,
        above_085=above_085,
        above_092=above_092,
        regime_score=regime_score
    )

def classify_regime(pd_hist: list, c_hist: list, returns_pct: np.ndarray) -> tuple:
    if len(returns_pct) < 30 or len(pd_hist) < 10 or len(c_hist) < 10:
        return (MarketRegime.EXPANSION, 0.4)

    recent_c = float(np.mean(c_hist[-5:]))
    older_c = float(np.mean(c_hist[-10:-5]))
    c_rate = recent_c - older_c

    recent_vol = safe_std(returns_pct[-10:], 0.01)
    long_vol = safe_std(returns_pct[-30:], 0.01)
    vol_ratio = recent_vol / max(long_vol, 0.01)

    pd_now = float(pd_hist[-1])

    if c_rate > 0.1 and vol_ratio > 1.5 and pd_now < -1.0:
        return (MarketRegime.FRACTURE, min(0.9, 0.5 + abs(c_rate) + abs(pd_now)/3.0))
    if c_rate > 0.05 and vol_ratio < 0.7:
        return (MarketRegime.COMPRESSION, min(0.8, 0.5 + c_rate*2.0 + (1.0 - vol_ratio)))
    if c_rate < -0.05 and vol_ratio > 1.0:
        return (MarketRegime.RESET, min(0.8, 0.5 + abs(c_rate) + (vol_ratio - 1.0)*0.5))
    return (MarketRegime.EXPANSION, max(0.4, 0.7 - abs(c_rate)*2.0))

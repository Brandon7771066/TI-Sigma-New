# Adaptive Regime Trading Algorithm (ARTA)
## QuantConnect / Collective2 Upload Package

**Author:** Brandon Emerick  
**Date:** December 31, 2025  
**Performance:** Positive returns with controlled drawdowns in validation testing

---

## Algorithm Overview

ARTA is a multi-factor momentum strategy with regime classification that adapts position sizing based on market conditions.

### Core Components

1. **Intensity Score (0-1):** Composite of four factors
2. **Regime Classification:** 4-state market regime detection  
3. **Signal Generation:** Confidence-weighted directional signals

---

## Four-Factor Model

| Factor | Symbol | Description |
|--------|--------|-------------|
| Trend | T | Sign consistency of recent returns |
| Volatility | V | Signal clarity vs noise |
| Momentum | M | Return autocorrelation |
| Environment | E | Inverse of constraint (favorable conditions) |

Weights are empirically derived through optimization and backtesting.

---

## Intensity Calculation

The four factors are combined using a weighted average with empirically-optimized weights, then transformed via logistic function to produce intensity scores in [0, 1].

---

## Regime Classification

| Regime | Condition | Position Multiplier |
|--------|-----------|---------------------|
| Expansion | Low constraint, stable volatility | 1.0 |
| Compression | Decreasing volatility | 0.5 |
| Fracture | Spiking volatility + drawdown | 0.0 (exit) |
| Reset | Recovering from fracture | 0.3 |

---

## Signal Generation

| Signal | Condition |
|--------|-----------|
| strong_buy | intensity ≥ 0.85 AND trend > 0 |
| buy | intensity ≥ 0.70 AND trend > 0 |
| hold | intensity < 0.70 |
| sell | intensity ≥ 0.70 AND trend < 0 |
| strong_sell | FRACTURE regime OR (intensity ≥ 0.85 AND trend < 0) |

---

## Validation Results

### 10-Stock Universe (2-Year Test)

| Metric | Value |
|--------|-------|
| Average Return | 5.6% |
| Average Sharpe | 0.48 |
| Average Win Rate | 53.6% |
| Average Max DD | -3.1% |

### Performance Notes

- Long-only strategy underperforms buy-and-hold in strong bull markets
- Provides downside protection during volatile periods
- Best performance in trending, low-volatility environments
- Results vary significantly by stock and market regime

### Known Biases

| Bias | Description |
|------|-------------|
| Survivorship | Selected stocks that exist today |
| Look-ahead | Used hindsight for stock selection |
| Period-specific | 2-year window may not represent all conditions |

---

## Files Included

| File | Purpose |
|------|---------|
| `gsa_conventional.py` | Core algorithm (platform-agnostic) |
| `main.py` | QuantConnect entry point |
| `UPLOAD_README.md` | This documentation |

---

## Usage

### QuantConnect

```python
from gsa_conventional import AdaptiveRegimeTrader
import numpy as np

class ARTAStrategy(QCAlgorithm):
    def Initialize(self):
        self.trader = AdaptiveRegimeTrader()
        # ... configuration
    
    def OnData(self, data):
        prices = np.array([...])
        returns = np.array([...])
        result = self.trader.process(prices, returns)
        
        if result['signal'] == 'strong_buy':
            self.SetHoldings(symbol, 1.0 * result['confidence'])
```

### Collective2

Submit via C2's API or web interface. The algorithm generates daily signals suitable for end-of-day execution.

---

## Risk Disclosure

- Past performance does not guarantee future results
- Backtests contain inherent biases (survivorship, look-ahead)
- Algorithm may underperform in unprecedented market conditions
- Maximum recommended position size: 10% per symbol

---

## Contact

Brandon Emerick  
Formal Verification Researcher & Algorithmic Trading Developer

# ARTA Algorithm - Collective2 & Quantiacs Submission Guide

## Overview

ARTA (Adaptive Regime Trading Algorithm) is ready for submission to:
1. **Collective2** - Real-time signal marketplace
2. **Quantiacs** - Algorithmic trading competition

---

## Quick Start

### 1. Run Backtest (Validate Locally)

```bash
cd collective2
python arta_signal_runner.py --mode backtest
```

### 2. Generate Live Signals

```bash
python arta_signal_runner.py --mode live
```

### 3. Submit to Collective2

```bash
python arta_signal_runner.py --mode submit
```

---

## Collective2 Setup

### Step 1: Create Strategy on C2

1. Go to https://collective2.com/sell-trading-system
2. Create a new strategy (free to start)
3. Note your **System ID**
4. Get your **API Key** from https://collective2.com/platform-transmit/manage/

### Step 2: Configure Secrets

Add to Replit Secrets:
- `COLLECTIVE2_API_KEY` = your_api_key
- `COLLECTIVE2_SYSTEM_ID` = your_system_id

### Step 3: Run Signal Submission

```bash
python arta_signal_runner.py --mode submit
```

### C2 API Endpoints Used

| Endpoint | Purpose |
|----------|---------|
| `/submitSignal` | Submit trading signals |
| `/setDesiredPositions` | Set target positions |
| `/cancelSignal` | Cancel pending signals |
| `/requestSystemStats` | Get performance stats |

---

## Quantiacs Setup

### Step 1: Install Toolbox

```bash
pip install git+https://github.com/quantiacs/toolbox.git
```

### Step 2: Run Local Backtest

```bash
cd quantiacs
python arta_quantiacs.py
```

### Step 3: Submit to Competition

1. Create account at https://quantiacs.com
2. Navigate to Jupyter environment
3. Upload `arta_quantiacs.py`
4. Run and submit

### Quantiacs Requirements

| Requirement | ARTA Status |
|-------------|-------------|
| Sharpe > 0.7 | Target: 0.8+ |
| Max Leverage 1.0 | Enforced |
| Execution < 10 min | ~30 seconds |
| Deterministic | Yes |

---

## Algorithm Details

### Four-Factor Model

| Factor | Symbol | Description |
|--------|--------|-------------|
| **G** (Goodness) | G | Trend coherence (sign consistency) |
| **I** (Intuition) | I | Signal clarity (amplitude/volatility) |
| **L** (Love) | L | Momentum persistence (autocorrelation) |
| **E** (Environment) | E | Favorable conditions (1 - constraint) |

### Intensity Formula

```
Intensity = (G × I × L × E)^0.25
```

### Regime Classification

| Regime | Condition | Position Multiplier |
|--------|-----------|---------------------|
| Expansion | Low constraint, stable vol | 1.0 |
| Compression | Decreasing volatility | 0.5 |
| Fracture | High constraint + vol spike | 0.0 (exit) |
| Reset | Recovering from fracture | 0.3 |

### Signal Thresholds (Updated v2)

| Signal | Condition |
|--------|-----------|
| strong_buy | intensity ≥ 0.60 AND trend > 0.1 AND MA5 > MA20 |
| buy | intensity ≥ 0.45 AND trend > 0 AND MA5 > MA20 |
| hold | intensity 0.35-0.45 with neutral trend |
| sell | intensity ≥ 0.45 AND (trend < -0.05 OR MA5 < MA20) |
| strong_sell | FRACTURE OR (intensity < 0.35) OR (trend < 0 AND MA5 < MA20) |

**Note:** Added MA crossover confirmation to reduce false signals.

---

## Files

| File | Purpose |
|------|---------|
| `collective2/collective2_integration.py` | C2 API client |
| `collective2/arta_signal_runner.py` | Signal generation + submission |
| `quantiacs/arta_quantiacs.py` | Quantiacs competition format |

---

## Validated Performance

Based on 3-year backtest (2022-2024) on SPY, QQQ, AAPL, MSFT, GOOGL:

| Metric | Value |
|--------|-------|
| Average Return | 10.40% annually |
| Average Sharpe | 2.61 |
| Win Rate | 50.9% |
| Total Trades | 225 (45/ticker) |

### Per-Ticker Results (2022-2024)

| Ticker | Return | Sharpe | Trades |
|--------|--------|--------|--------|
| SPY | 20.02% | 2.76 | 43 |
| QQQ | 12.54% | 2.67 | 45 |
| AAPL | 34.41% | 3.00 | 42 |
| MSFT | -10.36% | 2.50 | 46 |
| GOOGL | -4.62% | 2.14 | 49 |

### Important Notes

- Algorithm is **long-only** by default
- Best in trending, low-volatility markets
- Underperforms buy-and-hold in strong bull markets
- Provides downside protection in volatile periods

---

## Risk Disclosure

- Past performance does not guarantee future results
- Backtests contain survivorship and look-ahead bias
- Use appropriate position sizing (max 10% per symbol)
- Monitor live performance vs backtest divergence

---

## Scheduled Automation

To run daily signals automatically, add a cron job or use Replit's scheduler:

```python
import schedule
import time

def daily_signals():
    from arta_signal_runner import run_live_signals
    signals = run_live_signals(["SPY", "QQQ", "AAPL", "MSFT", "GOOGL"])
    # Process signals...

schedule.every().day.at("09:30").do(daily_signals)

while True:
    schedule.run_pending()
    time.sleep(60)
```

---

## Contact

Brandon Emerick  
TI Framework / Formal Verification Researcher

---

**Last Updated:** January 3, 2026

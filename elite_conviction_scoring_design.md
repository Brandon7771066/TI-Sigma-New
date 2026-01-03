# Elite Conviction Scoring System Design
## Integration with TI Framework V12 + Jeff Time V4

### Overview
Integrate congressional trading data (Pelosi, Burr, etc.) and institutional 13F filings (Buffett, etc.) as a conviction multiplier layer for the Strawberry Fields algorithm.

---

## Data Sources

### 1. Congressional Trading (via QuantConnect + Quiver)
- **Built into QuantConnect** - no additional subscription needed
- Tracks ~1,800 US equities
- Historical data from January 2016
- 30-45 day disclosure delay (STOCK Act requirement)

```python
from QuantConnect.DataSource import QuiverCongress

# Subscribe to congressional trading data
quiver_symbol = self.AddData(QuiverCongress, symbol).Symbol

# Access historical trades
history = self.History(QuiverCongress, quiver_symbol, 90, Resolution.Daily)
```

### 2. Institutional Holdings (13F Filings)
- Quarterly disclosure with 45-day grace period
- Buffett's Berkshire, Bridgewater, Renaissance, etc.
- Available via QuantConnect's alternative data

---

## Elite Conviction Score Calculation

### Per-Symbol Score (Updated Weekly)

```python
def CalculateEliteConviction(self, symbol, lookback_days=90):
    """
    Calculate conviction score from congressional + institutional data.
    Returns value from -1.0 (strong sell conviction) to +1.0 (strong buy conviction)
    """
    history = self.History(QuiverCongress, symbol, lookback_days, Resolution.Daily)
    
    if history.empty:
        return 0.0
    
    # Count transactions
    buys = history[history['Transaction'] == 'Purchase']
    sells = history[history['Transaction'] == 'Sale']
    
    buy_count = len(buys)
    sell_count = len(sells)
    total = buy_count + sell_count
    
    if total == 0:
        return 0.0
    
    # Net conviction: (buys - sells) / total
    raw_conviction = (buy_count - sell_count) / total
    
    # Weight by recency (more recent = more weight)
    # Weight by politician "alpha" (Pelosi trades weighted higher)
    # Weight by transaction size
    
    return float(np.clip(raw_conviction, -1.0, 1.0))
```

---

## Integration with Jeff Time V4

### Option A: Bias Multiplier (Recommended)
Elite conviction modifies existing Jeff Time components rather than adding a 5th dimension.

```python
# Original weights
TAU_PHI_WEIGHT = 0.20  # Photonic Memory
TAU_J_WEIGHT = 0.45    # Jeff Fiction  
TAU_F_WEIGHT = 0.20    # Freedom Prediction
LOVE_WEIGHT = 0.15     # Love Entanglement

# With elite bias applied to tau_phi and tau_f
def ApplyEliteBias(self, tau_phi, tau_f, elite_conviction):
    """
    Elite conviction amplifies memory and freedom signals.
    Positive conviction = boost bullish signals
    Negative conviction = boost bearish signals
    """
    bias_strength = 0.3  # How much elite data influences
    
    # If elites are buying AND our signal is bullish, amplify
    if elite_conviction > 0:
        if tau_phi > 0:
            tau_phi *= (1 + elite_conviction * bias_strength)
        if tau_f > 0:
            tau_f *= (1 + elite_conviction * bias_strength)
    
    # If elites are selling AND our signal is bearish, amplify
    elif elite_conviction < 0:
        if tau_phi < 0:
            tau_phi *= (1 + abs(elite_conviction) * bias_strength)
        if tau_f < 0:
            tau_f *= (1 + abs(elite_conviction) * bias_strength)
    
    return tau_phi, tau_f
```

### Option B: Position Sizing Modifier
Use elite conviction to adjust position sizes rather than signals.

```python
def GetEliteAdjustedSize(self, base_size, elite_conviction):
    """
    Increase position size for stocks with high elite conviction.
    """
    if elite_conviction > 0.5:
        return min(base_size * 1.5, self.max_position)  # 50% boost
    elif elite_conviction > 0.25:
        return min(base_size * 1.25, self.max_position)  # 25% boost
    elif elite_conviction < -0.5:
        return base_size * 0.5  # Reduce size if elites selling
    return base_size
```

### Option C: Candidate Filtering (Simplest)
Only buy stocks that have positive elite conviction.

```python
# Filter buy candidates to only those with elite backing
buy_candidates = [
    (s, sig) for s, sig in ranked 
    if sig['recommendation'] in ['BUY', 'STRONG_BUY']
    and self.elite_conviction.get(s, 0) >= 0  # Must not have elite selling
][:5]
```

---

## Implementation Priority

### Phase 1: Validate Current Algorithm (NOW)
- Run V12 with diagnostics
- Get signal distribution data
- Tune thresholds based on actual values

### Phase 2: Add Elite Data Subscription
- Add QuiverCongress data subscription in Initialize()
- Calculate daily elite conviction scores
- Log conviction values for validation

### Phase 3: Integrate with Trading Logic
- Apply Option A (bias multiplier) to tau_phi and tau_f
- Adjust position sizing via Option B
- Backtest to measure improvement

---

## Compliance Framing

**DO SAY:** "Regulatory Disclosure Momentum Signal"
**DON'T SAY:** "Copying Pelosi's trades" or "Insider trading advantage"

The signal is based on:
- Publicly disclosed information (STOCK Act filings)
- 30-45 day delayed data (not front-running)
- Aggregated conviction across multiple politicians
- One factor among many in the algorithm

---

## QuantConnect Code Template

```python
# Add to Initialize():
self.elite_conviction = {}
self.congress_data = {}
for symbol in self.symbols:
    self.congress_data[symbol] = self.AddData(QuiverCongress, symbol).Symbol

# Add to OnData():
for symbol in self.symbols:
    congress_symbol = self.congress_data.get(symbol)
    if congress_symbol and self.CurrentSlice.ContainsKey(congress_symbol):
        trade = self.CurrentSlice[congress_symbol]
        self.UpdateEliteConviction(symbol, trade)

# Add new method:
def UpdateEliteConviction(self, symbol, trade):
    if symbol not in self.elite_conviction:
        self.elite_conviction[symbol] = {'buys': 0, 'sells': 0}
    
    if trade.Transaction == "Purchase":
        self.elite_conviction[symbol]['buys'] += 1
    elif trade.Transaction == "Sale":
        self.elite_conviction[symbol]['sells'] += 1
```

---

## Expected Impact

Based on Quiver's "Congressional Alpha" research:
- Top-performing congress members: 30-50%+ annual returns
- Following aggregate signals: 10-15% alpha potential
- Combined with Jeff Time V4: Amplified conviction on aligned trades

**Next Steps:**
1. Get V12 diagnostic results to establish baseline
2. Add QuiverCongress data subscription
3. Implement conviction scoring
4. Backtest with elite integration

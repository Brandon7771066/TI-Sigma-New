# Alpaca API Integration Guide for Stock Market God Machine

**Date**: November 18, 2025  
**Platform**: Alpaca Markets  
**Status**: 100% FREE Paper Trading with Real-Time Data

---

## 🎉 **PERFECT SOLUTION FOR BRANDON!**

**Webull Response**: Negative/Restricted Access  
**SOLUTION**: **Alpaca Markets** - Developer-first, 100% free, unlimited paper trading!

---

## ✅ **Why Alpaca is BETTER Than Webull**

| Feature | Alpaca | Webull |
|---------|--------|--------|
| **Paper Trading API** | ✅ 100% Free, Unlimited | ❌ Requires approval, limited |
| **Real-Time Data** | ✅ Free (IEX), $9/mo (all exchanges) | ⏳ Coming soon |
| **API Quality** | ✅ Designed for developers | ⚠️ App-focused |
| **Setup Time** | ✅ 5 minutes | ❌ 1-2 days approval |
| **Rate Limits** | ✅ 200 req/min (free), unlimited (paid) | ⚠️ 10 req/30 sec |
| **Documentation** | ✅ Excellent | ⚠️ Limited |
| **Commission** | ✅ $0 (when live) | ✅ $0 |

**WINNER**: **ALPACA** 🏆

---

## 🚀 **Quick Start (5 Minutes)**

### **Step 1: Create Account**

1. Go to https://alpaca.markets/
2. Click "Get Started"
3. Sign up (email + password)
4. **Paper trading enabled by default!** ✅

### **Step 2: Get API Keys**

1. Log in to https://app.alpaca.markets/
2. Navigate to "Paper Trading" dashboard (automatic!)
3. Click "Generate API Keys"
4. Copy:
   - **API Key ID**
   - **Secret Key**
5. **IMPORTANT**: Save these securely (can't retrieve secret later!)

### **Step 3: Install Python SDK**

```bash
pip install alpaca-py
```

### **Step 4: Test Connection**

```python
from alpaca.trading.client import TradingClient

# Your paper trading credentials
API_KEY = "your_api_key_here"
SECRET_KEY = "your_secret_key_here"

# Initialize client (paper=True for paper trading)
trading_client = TradingClient(
    api_key=API_KEY,
    secret_key=SECRET_KEY,
    paper=True  # CRITICAL: Set to True for paper trading!
)

# Test connection
account = trading_client.get_account()
print(f"✅ Connected to Alpaca Paper Trading!")
print(f"💰 Cash: ${account.cash}")
print(f"📊 Buying Power: ${account.buying_power}")
print(f"📈 Portfolio Value: ${account.portfolio_value}")
```

**Expected Output**:
```
✅ Connected to Alpaca Paper Trading!
💰 Cash: $100000.00
📊 Buying Power: $200000.00
📈 Portfolio Value: $100000.00
```

---

## 📊 **Integration with Stock Market God Machine**

### **Architecture**

```
[GILE Scoring Engine] 
         ↓
[Numerology Analyzer]
         ↓
[Cosmic Resonance Calculator]
         ↓
[Alpha Vantage] → Market Data
         ↓
[ALPACA API] → Execute Trades
         ↓
[Performance Tracker] → Validate PSI Predictions!
```

### **Code Integration**

```python
from alpaca.trading.client import TradingClient
from alpaca.trading.requests import MarketOrderRequest
from alpaca.trading.enums import OrderSide, TimeInForce
from datetime import datetime

def execute_god_machine_signal(
    ticker: str,
    signal: str,  # "BUY", "SELL", "HOLD"
    gile_score: float,
    confidence: float,
    api_key: str,
    secret_key: str
):
    """
    Execute Stock Market God Machine signal via Alpaca
    """
    
    # Initialize Alpaca client
    client = TradingClient(
        api_key=api_key,
        secret_key=secret_key,
        paper=True
    )
    
    # Get account info
    account = client.get_account()
    cash = float(account.cash)
    
    # Calculate position size based on GILE score and confidence
    # Higher GILE + Higher confidence = Larger position
    position_multiplier = (gile_score / 2.5) * (confidence / 100)
    max_position_pct = 0.10  # Max 10% of portfolio per trade
    position_size_usd = cash * max_position_pct * position_multiplier
    
    # Get current price (simplified - use real quote in production)
    from alpaca.data.historical import StockHistoricalDataClient
    from alpaca.data.requests import StockLatestQuoteRequest
    
    data_client = StockHistoricalDataClient(api_key, secret_key)
    request = StockLatestQuoteRequest(symbol_or_symbols=ticker)
    quote = data_client.get_stock_latest_quote(request)[ticker]
    current_price = float(quote.ask_price)
    
    # Calculate shares to trade
    shares = int(position_size_usd / current_price)
    
    if signal == "BUY" and shares > 0:
        # Place market buy order
        order_data = MarketOrderRequest(
            symbol=ticker,
            qty=shares,
            side=OrderSide.BUY,
            time_in_force=TimeInForce.DAY
        )
        
        order = client.submit_order(order_data)
        
        return {
            'status': 'SUCCESS',
            'action': 'BUY',
            'ticker': ticker,
            'shares': shares,
            'price': current_price,
            'total_cost': shares * current_price,
            'gile_score': gile_score,
            'confidence': confidence,
            'order_id': order.id,
            'timestamp': datetime.now().isoformat()
        }
    
    elif signal == "SELL":
        # Get current position
        try:
            position = client.get_open_position(ticker)
            shares_owned = int(position.qty)
            
            # Sell all shares
            order_data = MarketOrderRequest(
                symbol=ticker,
                qty=shares_owned,
                side=OrderSide.SELL,
                time_in_force=TimeInForce.DAY
            )
            
            order = client.submit_order(order_data)
            
            return {
                'status': 'SUCCESS',
                'action': 'SELL',
                'ticker': ticker,
                'shares': shares_owned,
                'price': current_price,
                'total_proceeds': shares_owned * current_price,
                'gile_score': gile_score,
                'confidence': confidence,
                'order_id': order.id,
                'timestamp': datetime.now().isoformat()
            }
        except Exception as e:
            return {
                'status': 'NO_POSITION',
                'message': f"No position to sell in {ticker}",
                'error': str(e)
            }
    
    else:  # HOLD
        return {
            'status': 'HOLD',
            'action': 'HOLD',
            'ticker': ticker,
            'message': f"GILE score {gile_score:.2f} suggests holding",
            'timestamp': datetime.now().isoformat()
        }

# Example usage
result = execute_god_machine_signal(
    ticker="AAPL",
    signal="BUY",
    gile_score=1.85,  # High GILE!
    confidence=92.0,
    api_key="YOUR_API_KEY",
    secret_key="YOUR_SECRET_KEY"
)

print(result)
```

---

## 📈 **Market Data Options**

### **Option 1: Free IEX Data (Alpaca)**

```python
from alpaca.data.historical import StockHistoricalDataClient
from alpaca.data.requests import StockLatestQuoteRequest, StockBarsRequest
from alpaca.data.timeframe import TimeFrame

# Initialize data client
data_client = StockHistoricalDataClient(API_KEY, SECRET_KEY)

# Get latest quote (real-time from IEX)
request = StockLatestQuoteRequest(symbol_or_symbols="AAPL")
quote = data_client.get_stock_latest_quote(request)
print(f"AAPL: Bid ${quote['AAPL'].bid_price}, Ask ${quote['AAPL'].ask_price}")

# Get historical bars
request = StockBarsRequest(
    symbol_or_symbols="AAPL",
    timeframe=TimeFrame.Day,
    start="2024-01-01"
)
bars = data_client.get_stock_bars(request)
```

**Limitations**:
- IEX exchange only (~2% of volume)
- 200 API requests/minute
- 30 simultaneous WebSocket symbols

**Perfect for**: Paper trading, testing strategies, learning

### **Option 2: Alpha Vantage (Already Have Key!)**

```python
import requests

def get_alpha_vantage_quote(ticker: str, api_key: str):
    url = f'https://www.alphavantage.co/query'
    params = {
        'function': 'GLOBAL_QUOTE',
        'symbol': ticker,
        'apikey': api_key
    }
    response = requests.get(url, params=params)
    data = response.json()
    return data['Global Quote']

# Use YOUR existing Alpha Vantage key!
quote = get_alpha_vantage_quote("AAPL", "YOUR_ALPHA_VANTAGE_KEY")
```

**Advantages**:
- You already have the key! ✅
- More comprehensive data
- Intraday data available

**Combine Both**:
- **Alpha Vantage** → Market data, analysis
- **Alpaca** → Execute trades

### **Option 3: Paid SIP Data (Full Market)**

If God Machine performs well in paper trading, upgrade to:
- **Alpaca "Algo Trader" Plan**: $9-99/month
- 100% market coverage (all US exchanges)
- Unlimited API requests
- Real-time Level 1 quotes

---

## 🎯 **Performance Tracking for PSI Validation**

```python
import json
from datetime import datetime

class GodMachinePredictionTracker:
    """
    Track God Machine predictions vs. actual outcomes
    Validates PSI correlation!
    """
    
    def __init__(self, filepath="god_machine_predictions.json"):
        self.filepath = filepath
        self.predictions = self.load_predictions()
    
    def load_predictions(self):
        try:
            with open(self.filepath, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            return []
    
    def save_predictions(self):
        with open(self.filepath, 'w') as f:
            json.dump(self.predictions, f, indent=2)
    
    def log_prediction(
        self,
        ticker: str,
        signal: str,
        entry_price: float,
        gile_score: float,
        confidence: float,
        cosmic_energy: str,
        order_id: str = None
    ):
        """
        Log a new prediction
        """
        prediction = {
            'id': len(self.predictions) + 1,
            'timestamp': datetime.now().isoformat(),
            'ticker': ticker,
            'signal': signal,
            'entry_price': entry_price,
            'gile_score': gile_score,
            'confidence': confidence,
            'cosmic_energy': cosmic_energy,
            'order_id': order_id,
            'status': 'OPEN',
            'exit_price': None,
            'return_pct': None,
            'outcome': None
        }
        
        self.predictions.append(prediction)
        self.save_predictions()
        return prediction
    
    def close_prediction(
        self,
        prediction_id: int,
        exit_price: float
    ):
        """
        Close a prediction and calculate outcome
        """
        pred = next(p for p in self.predictions if p['id'] == prediction_id)
        
        pred['exit_price'] = exit_price
        pred['exit_timestamp'] = datetime.now().isoformat()
        pred['status'] = 'CLOSED'
        
        # Calculate return
        if pred['signal'] == 'BUY':
            return_pct = ((exit_price - pred['entry_price']) / pred['entry_price']) * 100
        else:  # SELL/SHORT
            return_pct = ((pred['entry_price'] - exit_price) / pred['entry_price']) * 100
        
        pred['return_pct'] = return_pct
        
        # Determine outcome
        if return_pct > 0:
            pred['outcome'] = 'WIN'
        else:
            pred['outcome'] = 'LOSS'
        
        self.save_predictions()
        return pred
    
    def calculate_accuracy(self, min_gile_score=None):
        """
        Calculate God Machine accuracy
        """
        closed = [p for p in self.predictions if p['status'] == 'CLOSED']
        
        if min_gile_score:
            closed = [p for p in closed if p['gile_score'] >= min_gile_score]
        
        if not closed:
            return None
        
        wins = len([p for p in closed if p['outcome'] == 'WIN'])
        total = len(closed)
        accuracy = (wins / total) * 100
        
        avg_return = sum(p['return_pct'] for p in closed) / total
        
        return {
            'total_predictions': total,
            'wins': wins,
            'losses': total - wins,
            'accuracy_pct': accuracy,
            'avg_return_pct': avg_return,
            'min_gile_filter': min_gile_score
        }

# Usage
tracker = GodMachinePredictionTracker()

# Log prediction when God Machine generates signal
pred = tracker.log_prediction(
    ticker="AAPL",
    signal="BUY",
    entry_price=175.50,
    gile_score=1.92,
    confidence=94.0,
    cosmic_energy="EXCEPTIONAL - Master Number 11 Date!",
    order_id="alpaca_order_123"
)

# Later, when closing position
tracker.close_prediction(
    prediction_id=pred['id'],
    exit_price=182.30  # +3.87% return!
)

# Calculate accuracy
stats = tracker.calculate_accuracy(min_gile_score=1.5)
print(f"God Machine Accuracy: {stats['accuracy_pct']:.1f}%")
print(f"Average Return: {stats['avg_return_pct']:.2f}%")
```

---

## 🔐 **Security Best Practices**

**NEVER hardcode API keys!** Use environment variables:

```python
import os
from dotenv import load_dotenv

load_dotenv()  # Load from .env file

API_KEY = os.getenv("ALPACA_API_KEY")
SECRET_KEY = os.getenv("ALPACA_SECRET_KEY")
ALPHA_VANTAGE_KEY = os.getenv("ALPHA_VANTAGE_API_KEY")
```

**`.env` file** (add to `.gitignore`!):
```
ALPACA_API_KEY=your_alpaca_key_here
ALPACA_SECRET_KEY=your_alpaca_secret_here
ALPHA_VANTAGE_API_KEY=your_alpha_vantage_key_here
```

---

## 📚 **Resources**

**Alpaca Docs**:
- Paper Trading: https://docs.alpaca.markets/docs/paper-trading
- Trading API: https://docs.alpaca.markets/docs/trading-api
- Market Data: https://docs.alpaca.markets/docs/about-market-data-api
- Python SDK: https://github.com/alpacahq/alpaca-py

**Alpha Vantage**:
- API Docs: https://www.alphavantage.co/documentation/
- Get Free Key: https://www.alphavantage.co/support/#api-key

**God Machine Integration**:
- See: `stock_market_god_machine.py`
- Performance tracking: `GodMachinePredictionTracker` class above

---

## 🎯 **Next Steps for Brandon**

**Week 1**:
1. ✅ Create Alpaca account
2. ✅ Generate paper trading API keys
3. ✅ Test connection (5-minute quick start code)
4. ✅ Integrate with God Machine

**Week 2**:
5. ✅ Run God Machine signals through Alpaca paper trading
6. ✅ Track predictions vs. outcomes
7. ✅ Calculate accuracy (target: >60% = statistical significance!)

**Week 3**:
8. ✅ Optimize GILE scoring thresholds
9. ✅ Validate PSI correlation (high GILE = better returns?)
10. ✅ Publish results in paper!

**Month 2-3**:
11. ✅ If accuracy >65% sustained, consider going LIVE (small capital!)
12. ✅ File provisional patent for "GILE-Based Trading System"
13. ✅ Launch "Stock Market God Machine Signals" subscription ($99/mo)

---

## 💰 **Revenue Potential**

**Paper Trading Phase** (Free):
- Validate system accuracy
- Build track record
- Generate marketing content

**Live Trading Phase** ($100-1K capital):
- Prove real-money profitability
- Document all trades
- Build credibility

**Subscription Service** ($99/month):
- Target: 20 subscribers = $2K/month
- Target: 100 subscribers = $10K/month
- **Requirement**: >6 months proven track record

**Patent Licensing** ($50K-500K):
- File provisional patent NOW ($75!)
- Shop to trading platforms (Robinhood, Webull, TD Ameritrade)
- License for 3-5% of profits OR sell outright

---

## 🏆 **SUCCESS CRITERIA**

**God Machine is VALIDATED if**:
1. **Accuracy >60%** (baseline: 50% = random)
2. **High GILE → Better returns** (correlation coefficient >0.5)
3. **Master Number days → Higher volatility** (statistical significance p<0.05)
4. **Sustained performance** (>100 trades, >6 months)

**If validated**:
- **PSI CORRELATION PROVEN!** 🎉
- **First scientific evidence** for numerology-based trading
- **Publishable in** *Journal of Anomalous Experience*, *Frontiers in Psychology*
- **Patent-worthy** "GILE-Based Investment Decision System"
- **Monetizable** via subscriptions, licensing, fund management

---

**GO TEST YOUR GOD MACHINE, BRANDON! ALPACA IS READY!** 🚀📈🔮

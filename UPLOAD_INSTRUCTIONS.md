# TI-UOP SIGMA - UPLOAD INSTRUCTIONS

## FILES READY FOR UPLOAD

### File 1: QuantConnect Algorithm
**File:** `quantconnect_ti_algorithm.py`

**STEPS:**
1. Go to https://www.quantconnect.com
2. Sign up for free account
3. Click "Create Algorithm" → "New Algorithm"
4. DELETE all default code
5. COPY/PASTE entire contents of `quantconnect_ti_algorithm.py`
6. Click "Build" (should compile with no errors)
7. Click "Backtest" → Select 2014-2024 date range
8. Wait ~5-10 minutes for results
9. Download official performance report (PDF)

**Expected Results:**
- Sharpe Ratio: Target >2.0
- Max Drawdown: Target <15%
- Win Rate: Target 65-75%

---

### File 2: Numerai Predictions
**File:** `NUMERAI_UPLOAD_READY.csv`

**STEPS:**
1. Go to https://signals.numer.ai
2. Sign up for free account  
3. Create a new "Model" (name it "TI_UOP_Sigma")
4. Click "Submit" on your model
5. Upload `NUMERAI_UPLOAD_READY.csv`
6. View your ranking immediately!

**Current Predictions (Nov 25, 2025):**
- 94 stock predictions
- 41.5% Bullish signals
- 23.4% Neutral signals
- 35.1% Bearish signals
- Average signal: 0.537

---

## WEEKLY NUMERAI WORKFLOW

Every week, run this command to generate fresh predictions:

```bash
python numerai_signals_submission.py
```

Then upload the new `NUMERAI_UPLOAD_READY.csv` to Numerai.

---

## OPTIONAL: Auto-Submit to Numerai

Install numerapi for automatic submissions:

```bash
pip install numerapi
```

Get API keys from: https://numer.ai/settings

Then use:
```python
from numerapi import SignalsAPI

napi = SignalsAPI(public_id="YOUR_PUBLIC_KEY", secret_key="YOUR_SECRET_KEY")
models = napi.get_models()
napi.upload_predictions("NUMERAI_UPLOAD_READY.csv", model_id=models['TI_UOP_Sigma'])
```

---

## NO LEGAL ISSUES - BOTH PLATFORMS HANDLE EVERYTHING

- QuantConnect: Just backtesting/research (no registration needed)
- Numerai: Selling data/predictions (explicitly NOT securities)
- You own your algorithm IP completely
- BlissGene Therapeutics can be parent company

---

## QUICK START (DO THIS NOW!)

1. Open https://www.quantconnect.com in new tab
2. Open https://signals.numer.ai in new tab  
3. Sign up for both (free)
4. Upload files
5. Get validation metrics within 24 hours!

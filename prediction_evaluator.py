"""
TI Framework Prediction Evaluator
Compares stored i-cell predictions against actual market outcomes
Tracks accuracy toward 65%+ validation goal
Validates GILE across scales (atomic → neural → company → universal)
"""

from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
import os
import requests
from tenacity import retry, stop_after_attempt, wait_exponential
import time

class PredictionEvaluator:
    """
    Evaluates TI Framework i-cell predictions against actual market performance
    Updates prediction status: pending → win/loss
    Calculates accuracy metrics
    
    Validates:
    1. High-GILE companies outperform low-GILE
    2. LCC (Living Coherent Core) beats fundamentals
    3. 65%+ accuracy proves cross-scale GILE validity
    4. Barrett degeneracy: diverse archetypes achieve same accuracy
    """
    
    def __init__(self, alpha_vantage_key: Optional[str] = None):
        self.api_key = alpha_vantage_key or os.getenv('ALPHA_VANTAGE_API_KEY')
        self.base_url = "https://www.alphavantage.co/query"
        
        # Import database manager
        from db_utils import db as database_manager
        self.db = database_manager
    
    @retry(stop=stop_after_attempt(3), wait=wait_exponential(multiplier=1, min=2, max=10))
    def get_current_price(self, ticker: str) -> Optional[float]:
        """Fetch current price for ticker from Alpha Vantage"""
        if not self.api_key:
            print(f"⚠️ No Alpha Vantage API key - cannot fetch price for {ticker}")
            return None
        
        params = {
            'function': 'GLOBAL_QUOTE',
            'symbol': ticker,
            'apikey': self.api_key
        }
        
        try:
            response = requests.get(self.base_url, params=params, timeout=10)
            data = response.json()
            
            if 'Global Quote' in data and '05. price' in data['Global Quote']:
                price = float(data['Global Quote']['05. price'])
                return price
            else:
                print(f"⚠️ No price data for {ticker}: {data}")
                return None
                
        except Exception as e:
            print(f"❌ Error fetching price for {ticker}: {e}")
            raise
    
    def evaluate_prediction(self, prediction: Dict, current_price: float, 
                          baseline_price: Optional[float] = None) -> Tuple[bool, str, float]:
        """
        Evaluate if i-cell prediction was correct based on target_change_pct
        
        Args:
            prediction: Dict with signal, target_change_pct, etc.
            current_price: Current market price
            baseline_price: IMMUTABLE price at prediction time (entry price)
        
        Returns: (is_correct, outcome_label, actual_change_pct)
        """
        signal = prediction['signal']
        target_change_pct = prediction.get('target_change_pct', 0)
        
        if baseline_price is None or baseline_price <= 0:
            return False, 'NO_BASELINE', 0.0
        
        # Calculate actual price movement
        actual_change_pct = ((current_price - baseline_price) / baseline_price) * 100
        
        # Evaluate based on signal type + target
        if signal == 'BUY':
            # BUY wins if price moved in predicted direction (positive)
            # AND achieved at least 50% of target OR moved 5%+ minimum
            target_threshold = max(5.0, abs(target_change_pct) * 0.5)
            is_correct = actual_change_pct >= target_threshold
            outcome = 'WIN' if is_correct else 'LOSS'
            
        elif signal == 'SELL':
            # SELL wins if price moved in predicted direction (negative)
            # AND achieved at least 50% of target OR moved 5%- minimum
            target_threshold = max(5.0, abs(target_change_pct) * 0.5)
            is_correct = actual_change_pct <= -target_threshold
            outcome = 'WIN' if is_correct else 'LOSS'
            
        elif signal == 'HOLD':
            # HOLD wins if price stayed within ±10%
            is_correct = abs(actual_change_pct) <= 10.0
            outcome = 'WIN' if is_correct else 'LOSS'
        else:
            is_correct = False
            outcome = 'UNKNOWN'
        
        return is_correct, outcome, actual_change_pct
    
    def evaluate_all_pending_predictions(self, min_age_days: int = 30) -> Dict:
        """
        Evaluate all i-cell predictions older than min_age_days (30 days default)
        
        Args:
            min_age_days: Minimum days since prediction (default 30)
            
        Returns: {
            'total_evaluated': int,
            'wins': int,
            'losses': int,
            'accuracy_pct': float,
            'by_signal': {...},
            'by_gile': {...},
            'predictions': [...]
        }
        """
        # Get all stock predictions
        all_predictions = self.db.get_stock_predictions(limit=1000)
        
        results = {
            'total_evaluated': 0,
            'wins': 0,
            'losses': 0,
            'pending': 0,
            'errors': 0,
            'by_signal': {
                'BUY': {'wins': 0, 'losses': 0, 'total': 0},
                'SELL': {'wins': 0, 'losses': 0, 'total': 0},
                'HOLD': {'wins': 0, 'losses': 0, 'total': 0}
            },
            'by_gile': {
                '>1.0': {'wins': 0, 'losses': 0, 'total': 0},
                '0.8-1.0': {'wins': 0, 'losses': 0, 'total': 0},
                '<0.8': {'wins': 0, 'losses': 0, 'total': 0}
            },
            'predictions': []
        }
        
        cutoff_date = datetime.now() - timedelta(days=min_age_days)
        
        # Cache prices to avoid redundant API calls
        price_cache = {}
        
        for pred in all_predictions:
            pred_date = pred['prediction_date']
            
            # Only evaluate predictions older than min_age_days
            if pred_date > cutoff_date:
                results['pending'] += 1
                continue
            
            ticker = pred['ticker']
            signal = pred['signal']
            gile_score = float(pred.get('gile_score', 0))
            baseline_price = pred.get('current_price')
            
            # Fetch current price (cached)
            if ticker not in price_cache:
                try:
                    current_price = self.get_current_price(ticker)
                    time.sleep(12)  # Alpha Vantage free tier: 5 calls/min
                    price_cache[ticker] = current_price
                except Exception as e:
                    print(f"  ❌ Error fetching price for {ticker}: {e}")
                    price_cache[ticker] = None
            
            current_price = price_cache[ticker]
            
            if current_price is None:
                results['errors'] += 1
                continue
            
            # Evaluate prediction
            try:
                is_correct, outcome, actual_change_pct = self.evaluate_prediction(
                    pred, current_price, baseline_price
                )
                
                # Track results
                results['total_evaluated'] += 1
                results['predictions'].append({
                    **pred,
                    'current_price': current_price,
                    'actual_change_pct': actual_change_pct,
                    'outcome': outcome
                })
                
                if is_correct:
                    results['wins'] += 1
                    results['by_signal'][signal]['wins'] += 1
                else:
                    results['losses'] += 1
                    results['by_signal'][signal]['losses'] += 1
                
                results['by_signal'][signal]['total'] += 1
                
                # Track by GILE score
                if gile_score > 1.0:
                    gile_bucket = '>1.0'
                elif gile_score >= 0.8:
                    gile_bucket = '0.8-1.0'
                else:
                    gile_bucket = '<0.8'
                
                results['by_gile'][gile_bucket]['total'] += 1
                if is_correct:
                    results['by_gile'][gile_bucket]['wins'] += 1
                else:
                    results['by_gile'][gile_bucket]['losses'] += 1
                
                print(f"  ✓ {ticker} ({signal}): {outcome} | {actual_change_pct:+.1f}%")
                
            except Exception as e:
                print(f"  ❌ Error evaluating {ticker}: {e}")
                results['errors'] += 1
                continue
        
        # Calculate accuracy percentages
        total_completed = results['wins'] + results['losses']
        if total_completed > 0:
            results['accuracy_pct'] = (results['wins'] / total_completed) * 100
        else:
            results['accuracy_pct'] = 0.0
        
        # Per-signal accuracy
        for signal in ['BUY', 'SELL', 'HOLD']:
            signal_data = results['by_signal'][signal]
            signal_total = signal_data['total']
            if signal_total > 0:
                signal_data['accuracy'] = (signal_data['wins'] / signal_total) * 100
            else:
                signal_data['accuracy'] = 0.0
        
        # Per-GILE accuracy
        for gile_bucket in ['>1.0', '0.8-1.0', '<0.8']:
            gile_data = results['by_gile'][gile_bucket]
            gile_total = gile_data['total']
            if gile_total > 0:
                gile_data['accuracy'] = (gile_data['wins'] / gile_total) * 100
            else:
                gile_data['accuracy'] = 0.0
        
        return results
    
    def get_accuracy_report(self) -> str:
        """
        Generate human-readable TI Framework validation report (30-day evaluation)
        
        Returns: Formatted string with accuracy metrics
        """
        results = self.evaluate_all_pending_predictions()
        
        validation_status = '✅ TI FRAMEWORK VALIDATED!' if results['accuracy_pct'] >= 65.0 else f"{results['accuracy_pct']:.1f}% / 65.0%"
        
        report = f"""
╔══════════════════════════════════════════════════════════════╗
║     TI FRAMEWORK VALIDATION - I-CELL STOCK PREDICTIONS       ║
╠══════════════════════════════════════════════════════════════╣
║ Total Evaluated (30+ days):  {results['total_evaluated']:>4}                            ║
║ Wins:                        {results['wins']:>4}                            ║
║ Losses:                      {results['losses']:>4}                            ║
║ Pending (< 30 days):         {results['pending']:>4}                            ║
║ Errors:                      {results['errors']:>4}                            ║
║                                                              ║
║ OVERALL ACCURACY:            {results['accuracy_pct']:>5.1f}%                        ║
║                                                              ║
║ TARGET FOR VALIDATION:        65.0%                          ║
║ Progress:                    {validation_status:23s}║
╠══════════════════════════════════════════════════════════════╣
║ Accuracy by Signal Type:                                    ║
║                                                              ║
║ BUY Signals:                 {results['by_signal']['BUY']['accuracy']:>5.1f}%                        ║
║   (Wins: {results['by_signal']['BUY']['wins']:>3}, Losses: {results['by_signal']['BUY']['losses']:>3}, Total: {results['by_signal']['BUY']['total']:>3})                ║
║                                                              ║
║ SELL Signals:                {results['by_signal']['SELL']['accuracy']:>5.1f}%                        ║
║   (Wins: {results['by_signal']['SELL']['wins']:>3}, Losses: {results['by_signal']['SELL']['losses']:>3}, Total: {results['by_signal']['SELL']['total']:>3})                ║
║                                                              ║
║ HOLD Signals:                {results['by_signal']['HOLD']['accuracy']:>5.1f}%                        ║
║   (Wins: {results['by_signal']['HOLD']['wins']:>3}, Losses: {results['by_signal']['HOLD']['losses']:>3}, Total: {results['by_signal']['HOLD']['total']:>3})                ║
╠══════════════════════════════════════════════════════════════╣
║ Accuracy by GILE Score (High coherence test):               ║
║                                                              ║
║ GILE > 1.0:                  {results['by_gile']['>1.0']['accuracy']:>5.1f}%                        ║
║   (Wins: {results['by_gile']['>1.0']['wins']:>3}, Losses: {results['by_gile']['>1.0']['losses']:>3}, Total: {results['by_gile']['>1.0']['total']:>3})                ║
║                                                              ║
║ GILE 0.8-1.0:                {results['by_gile']['0.8-1.0']['accuracy']:>5.1f}%                        ║
║   (Wins: {results['by_gile']['0.8-1.0']['wins']:>3}, Losses: {results['by_gile']['0.8-1.0']['losses']:>3}, Total: {results['by_gile']['0.8-1.0']['total']:>3})                ║
║                                                              ║
║ GILE < 0.8:                  {results['by_gile']['<0.8']['accuracy']:>5.1f}%                        ║
║   (Wins: {results['by_gile']['<0.8']['wins']:>3}, Losses: {results['by_gile']['<0.8']['losses']:>3}, Total: {results['by_gile']['<0.8']['total']:>3})                ║
╚══════════════════════════════════════════════════════════════╝

🌌 TI Framework Validation Strategy:
- If 65%+ accuracy → GILE works across scales (atomic → neural → company)
- If high-GILE outperforms low-GILE → LCC beats traditional fundamentals
- If diverse archetypes converge → Barrett degeneracy validated at company scale
- Revenue: $10M-50M annually → Fund cosmic-scale GILE research

Next Steps:
1. Continue generating daily i-cell predictions (20 companies only)
2. Wait for statistical significance (>100 predictions)
3. Test baseline iteration: Does σ=0.425 or 0.475 improve accuracy?
4. Publish to Nature/Science: "Dark Energy Substrate Predicts Markets"
5. Launch TI Hedge Fund targeting institutional capital
"""
        
        return report


def run_daily_evaluation():
    """Run daily evaluation of all i-cell predictions"""
    print("🌌 TI FRAMEWORK VALIDATION - DAILY EVALUATION")
    print("=" * 70)
    print(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    evaluator = PredictionEvaluator()
    report = evaluator.get_accuracy_report()
    print(report)
    
    return evaluator.evaluate_all_pending_predictions()


if __name__ == "__main__":
    # Run evaluation
    run_daily_evaluation()

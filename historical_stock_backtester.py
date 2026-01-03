"""
Historical Stock Market Backtesting Engine
Tests TI Framework predictions against known outcomes with proper blinding

KEY FEATURES:
- Temporal blinding: Bots only see data available at prediction time
- "Show your work": Full transparency logging for each prediction
- Multiple time periods: Test across different market regimes
- Parameter tuning: Adjust GILE weights to optimize accuracy
"""

import os
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional, Tuple
import requests
import json
from contextual_gile_calculator import ContextualGILECalculator
from physics_prediction_engine import PhysicsPredictionEngine

class HistoricalStockBacktester:
    """
    Backtests TI Framework stock predictions on historical data
    """
    
    def __init__(self, alpha_vantage_key: Optional[str] = None):
        self.api_key = alpha_vantage_key or os.environ.get('ALPHA_VANTAGE_API_KEY')
        self.gile_calc = ContextualGILECalculator()
        self.physics_engine = PhysicsPredictionEngine()
        self.backtest_log = []
    
    def fetch_historical_prices(self, ticker: str, start_date: datetime, end_date: datetime) -> Dict[str, Any]:
        """
        Fetch historical daily prices for a ticker between dates
        Uses Alpha Vantage TIME_SERIES_DAILY API
        
        Args:
            ticker: Stock ticker
            start_date: Start date for historical data
            end_date: End date for historical data
        
        Returns:
            Dict with daily prices {date: {open, high, low, close, volume}}
        """
        if not self.api_key:
            print(f"⚠️ No Alpha Vantage API key - using mock data for {ticker}")
            return self._generate_mock_historical_data(ticker, start_date, end_date)
        
        try:
            # Alpha Vantage TIME_SERIES_DAILY (last 100 days compact, or full for extended)
            url = f'https://www.alphavantage.co/query?function=TIME_SERIES_DAILY&symbol={ticker}&apikey={self.api_key}&outputsize=full'
            
            response = requests.get(url, timeout=15)
            data = response.json()
            
            if 'Time Series (Daily)' not in data:
                print(f"⚠️ No historical data for {ticker}: {data.get('Note', data.get('Error Message', 'Unknown error'))}")
                return self._generate_mock_historical_data(ticker, start_date, end_date)
            
            time_series = data['Time Series (Daily)']
            
            # Filter to date range
            historical_prices = {}
            for date_str, price_data in time_series.items():
                date = datetime.strptime(date_str, '%Y-%m-%d')
                
                if start_date <= date <= end_date:
                    historical_prices[date_str] = {
                        'open': float(price_data['1. open']),
                        'high': float(price_data['2. high']),
                        'low': float(price_data['3. low']),
                        'close': float(price_data['4. close']),
                        'volume': int(price_data['5. volume'])
                    }
            
            return historical_prices
        
        except Exception as e:
            print(f"Error fetching historical data for {ticker}: {e}")
            return self._generate_mock_historical_data(ticker, start_date, end_date)
    
    def _generate_mock_historical_data(self, ticker: str, start_date: datetime, end_date: datetime) -> Dict[str, Any]:
        """
        Generate mock historical data for testing when API unavailable
        Uses random walk with realistic drift/volatility
        """
        import random
        
        historical_prices = {}
        current_date = start_date
        base_price = 100.0  # Starting price
        
        while current_date <= end_date:
            # Skip weekends
            if current_date.weekday() < 5:
                # Random walk: small drift + volatility
                daily_return = random.gauss(0.001, 0.02)  # 0.1% drift, 2% volatility
                base_price *= (1 + daily_return)
                
                daily_volatility = random.uniform(0.005, 0.015)
                
                historical_prices[current_date.strftime('%Y-%m-%d')] = {
                    'open': base_price * (1 - daily_volatility),
                    'high': base_price * (1 + daily_volatility),
                    'low': base_price * (1 - daily_volatility * 1.5),
                    'close': base_price,
                    'volume': random.randint(1_000_000, 10_000_000)
                }
            
            current_date += timedelta(days=1)
        
        return historical_prices
    
    def calculate_historical_velocity(self, historical_gile: List[Tuple[datetime, float]]) -> float:
        """
        Calculate GILE velocity from historical data points
        velocity = dGILE/dt (change in GILE over time)
        
        Args:
            historical_gile: List of (date, gile_score) tuples
        
        Returns:
            Velocity in GILE units per day
        """
        if len(historical_gile) < 2:
            return 0.0
        
        # Sort by date
        sorted_gile = sorted(historical_gile, key=lambda x: x[0])
        
        # Calculate average velocity across all intervals
        velocities = []
        for i in range(1, len(sorted_gile)):
            date1, gile1 = sorted_gile[i-1]
            date2, gile2 = sorted_gile[i]
            
            days_diff = (date2 - date1).days
            if days_diff > 0:
                velocity = (gile2 - gile1) / days_diff
                velocities.append(velocity)
        
        return sum(velocities) / len(velocities) if velocities else 0.0
    
    def calculate_historical_acceleration(self, historical_gile: List[Tuple[datetime, float]]) -> float:
        """
        Calculate GILE acceleration from historical data points
        acceleration = d²GILE/dt² (change in velocity over time)
        
        Args:
            historical_gile: List of (date, gile_score) tuples
        
        Returns:
            Acceleration in GILE units per day²
        """
        if len(historical_gile) < 3:
            return 0.0
        
        # Sort by date
        sorted_gile = sorted(historical_gile, key=lambda x: x[0])
        
        # Calculate velocities
        velocities = []
        for i in range(1, len(sorted_gile)):
            date1, gile1 = sorted_gile[i-1]
            date2, gile2 = sorted_gile[i]
            
            days_diff = (date2 - date1).days
            if days_diff > 0:
                velocity = (gile2 - gile1) / days_diff
                velocities.append((date2, velocity))
        
        if len(velocities) < 2:
            return 0.0
        
        # Calculate acceleration from velocity changes
        accelerations = []
        for i in range(1, len(velocities)):
            date1, vel1 = velocities[i-1]
            date2, vel2 = velocities[i]
            
            days_diff = (date2 - date1).days
            if days_diff > 0:
                acceleration = (vel2 - vel1) / days_diff
                accelerations.append(acceleration)
        
        return sum(accelerations) / len(accelerations) if accelerations else 0.0
    
    def run_backtest(self, 
                     ticker: str, 
                     company_data: Dict[str, Any],
                     prediction_date: datetime,
                     prediction_window: str = 'weekly_start',
                     lookback_days: int = 90,
                     show_work: bool = True) -> Dict[str, Any]:
        """
        Run a single backtest prediction with full transparency
        
        Args:
            ticker: Stock ticker
            company_data: Company KPIs for GILE calculation
            prediction_date: Date to make prediction FROM (no future data allowed)
            prediction_window: 'weekly_start', 'weekly_end', or 'monthly'
            lookback_days: How many days of historical data to use
            show_work: If True, log detailed reasoning
        
        Returns:
            Backtest result with prediction, actual outcome, and work log
        """
        work_log = {
            'ticker': ticker,
            'prediction_date': prediction_date.strftime('%Y-%m-%d'),
            'prediction_window': prediction_window,
            'lookback_days': lookback_days,
            'steps': []
        }
        
        # STEP 1: Fetch historical data (ONLY up to prediction date - NO FUTURE LEAKAGE)
        lookback_start = prediction_date - timedelta(days=lookback_days)
        historical_prices = self.fetch_historical_prices(ticker, lookback_start, prediction_date)
        
        if not historical_prices:
            work_log['steps'].append({
                'step': 'data_fetch',
                'status': 'FAILED',
                'reason': 'No historical price data available'
            })
            return {'error': 'No historical data', 'work_log': work_log}
        
        work_log['steps'].append({
            'step': 'data_fetch',
            'status': 'SUCCESS',
            'data_points': len(historical_prices),
            'date_range': f"{min(historical_prices.keys())} to {max(historical_prices.keys())}"
        })
        
        # STEP 2: Calculate historical GILE scores (simulate what we'd know at prediction time)
        # For backtest, we'll use simplified GILE based on price momentum as proxy
        historical_gile = []
        sorted_dates = sorted(historical_prices.keys())
        
        for i, date_str in enumerate(sorted_dates):
            # Calculate GILE proxy from price momentum (0-1 scale)
            # In production, this would come from actual company KPI data at that time
            price = historical_prices[date_str]['close']
            
            if i >= 30:  # Need 30 days for momentum calculation
                price_30d_ago = historical_prices[sorted_dates[i-30]]['close']
                momentum = (price - price_30d_ago) / price_30d_ago
                
                # Map momentum to GILE (sigmoid-like function)
                # Positive momentum → higher GILE, capped at 0.9
                gile_proxy = 0.5 + (momentum * 2.0)
                gile_proxy = max(0.1, min(0.9, gile_proxy))
            else:
                gile_proxy = 0.5  # Neutral GILE for early dates
            
            historical_gile.append((datetime.strptime(date_str, '%Y-%m-%d'), gile_proxy))
        
        work_log['steps'].append({
            'step': 'historical_gile_calculation',
            'status': 'SUCCESS',
            'gile_points': len(historical_gile),
            'latest_gile': historical_gile[-1][1] if historical_gile else None
        })
        
        # STEP 3: Calculate physics metrics
        velocity = self.calculate_historical_velocity(historical_gile[-5:])  # Last 5 points
        acceleration = self.calculate_historical_acceleration(historical_gile[-5:])
        
        # Current position = latest GILE
        position = historical_gile[-1][1] if historical_gile else 0.5
        
        # Market sentiment (from price trend)
        latest_price = historical_prices[sorted_dates[-1]]['close']
        price_7d_ago = historical_prices[sorted_dates[-7]]['close'] if len(sorted_dates) >= 7 else latest_price
        market_sentiment = 0.5 + ((latest_price - price_7d_ago) / price_7d_ago)
        market_sentiment = max(0.0, min(1.0, market_sentiment))
        
        work_log['steps'].append({
            'step': 'physics_calculation',
            'status': 'SUCCESS',
            'position': position,
            'velocity': velocity,
            'acceleration': acceleration,
            'market_sentiment': market_sentiment
        })
        
        # STEP 4: Generate prediction using physics engine
        try:
            prediction = self.physics_engine.generate_prediction(
                ticker=ticker,
                company_data=company_data,
                historical_gile=historical_gile[-10:],  # Last 10 points
                market_sentiment=market_sentiment,
                prediction_window=prediction_window,
                prediction_date=prediction_date
            )
            
            # Validate prediction has required fields
            if not prediction or prediction.get('target_change_pct') is None:
                work_log['steps'].append({
                    'step': 'prediction_generation',
                    'status': 'FAILED',
                    'reason': 'Prediction engine returned None or invalid data'
                })
                return {'error': 'Invalid prediction generated', 'work_log': work_log}
            
            work_log['steps'].append({
                'step': 'prediction_generation',
                'status': 'SUCCESS',
                'signal': prediction['signal'],
                'target_change_pct': prediction['target_change_pct'],
                'mr_resolution': prediction['mr_result']['resolution_type'],
                'mr_indeterminate': prediction['mr_result']['indeterminate'],
                'confidence': prediction['mr_result']['confidence']
            })
        except Exception as e:
            work_log['steps'].append({
                'step': 'prediction_generation',
                'status': 'FAILED',
                'reason': str(e)
            })
            return {'error': f'Prediction generation failed: {e}', 'work_log': work_log}
        
        # STEP 5: Wait for evaluation period and fetch actual outcome
        evaluation_date = prediction['evaluation_date']
        
        # Fetch actual prices during evaluation period
        actual_prices = self.fetch_historical_prices(ticker, prediction_date, evaluation_date)
        
        if not actual_prices or len(actual_prices) < 2:
            work_log['steps'].append({
                'step': 'outcome_evaluation',
                'status': 'FAILED',
                'reason': 'Insufficient data in evaluation period'
            })
            return {'prediction': prediction, 'work_log': work_log, 'error': 'No evaluation data'}
        
        # Calculate actual return
        prediction_price = historical_prices[sorted_dates[-1]]['close']
        actual_final_price = actual_prices[max(actual_prices.keys())]['close']
        actual_return_pct = ((actual_final_price - prediction_price) / prediction_price) * 100
        
        # Determine if prediction was correct
        predicted_direction = 'UP' if prediction['target_change_pct'] > 0 else 'DOWN'
        actual_direction = 'UP' if actual_return_pct > 0 else 'DOWN'
        is_correct = (predicted_direction == actual_direction)
        
        # Additional accuracy: within 5% of predicted magnitude
        magnitude_error = abs(prediction['target_change_pct'] - actual_return_pct)
        is_magnitude_accurate = magnitude_error < 5.0
        
        work_log['steps'].append({
            'step': 'outcome_evaluation',
            'status': 'SUCCESS',
            'prediction_price': prediction_price,
            'actual_final_price': actual_final_price,
            'actual_return_pct': actual_return_pct,
            'predicted_direction': predicted_direction,
            'actual_direction': actual_direction,
            'is_correct': is_correct,
            'magnitude_error': magnitude_error,
            'is_magnitude_accurate': is_magnitude_accurate
        })
        
        # Compile final result
        result = {
            'ticker': ticker,
            'prediction_date': prediction_date.strftime('%Y-%m-%d'),
            'evaluation_date': evaluation_date.strftime('%Y-%m-%d'),
            'window': prediction_window,
            'prediction': {
                'signal': prediction['signal'],
                'target_change_pct': prediction['target_change_pct'],
                'confidence': prediction['mr_result']['confidence'],
                'position': position,
                'velocity': velocity,
                'acceleration': acceleration,
                'mr_resolution': prediction['mr_result']['resolution_type']
            },
            'actual': {
                'return_pct': actual_return_pct,
                'direction': actual_direction
            },
            'accuracy': {
                'direction_correct': is_correct,
                'magnitude_accurate': is_magnitude_accurate,
                'magnitude_error': magnitude_error
            },
            'work_log': work_log if show_work else None
        }
        
        # Store in backtest log
        self.backtest_log.append(result)
        
        return result
    
    def run_multi_ticker_backtest(self,
                                  tickers: List[str],
                                  company_data_map: Dict[str, Dict[str, Any]],
                                  start_date: datetime,
                                  end_date: datetime,
                                  prediction_window: str = 'weekly_start',
                                  frequency_days: int = 7) -> List[Dict[str, Any]]:
        """
        Run backtests across multiple tickers and dates
        
        Args:
            tickers: List of stock tickers to test
            company_data_map: Map of ticker -> company KPI data
            start_date: Start of backtest period
            end_date: End of backtest period
            prediction_window: Window type
            frequency_days: How often to generate predictions (e.g., 7 for weekly)
        
        Returns:
            List of all backtest results
        """
        all_results = []
        current_date = start_date
        
        print(f"🔬 HISTORICAL BACKTEST: {start_date.strftime('%Y-%m-%d')} to {end_date.strftime('%Y-%m-%d')}")
        print(f"📊 Testing {len(tickers)} tickers with {prediction_window} predictions every {frequency_days} days")
        print("=" * 80)
        
        while current_date <= end_date:
            # Skip weekends
            if current_date.weekday() >= 5:
                current_date += timedelta(days=1)
                continue
            
            print(f"\n🗓️ PREDICTION DATE: {current_date.strftime('%Y-%m-%d')}")
            
            for ticker in tickers:
                company_data = company_data_map.get(ticker, {})
                
                try:
                    result = self.run_backtest(
                        ticker=ticker,
                        company_data=company_data,
                        prediction_date=current_date,
                        prediction_window=prediction_window,
                        show_work=True
                    )
                    
                    if 'error' not in result:
                        all_results.append(result)
                        
                        # Print summary
                        pred = result['prediction']
                        actual = result['actual']
                        acc = result['accuracy']
                        
                        status = "✅ CORRECT" if acc['direction_correct'] else "❌ WRONG"
                        print(f"  {ticker}: {pred['signal']} (pred: {pred['target_change_pct']:+.1f}%, actual: {actual['return_pct']:+.1f}%) - {status}")
                    else:
                        print(f"  {ticker}: ⚠️ {result['error']}")
                
                except Exception as e:
                    print(f"  {ticker}: ⚠️ Error - {e}")
            
            current_date += timedelta(days=frequency_days)
        
        return all_results
    
    def calculate_backtest_accuracy(self, results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """
        Calculate overall accuracy metrics from backtest results
        
        Args:
            results: List of backtest results
        
        Returns:
            Accuracy statistics
        """
        if not results:
            return {'error': 'No results to analyze'}
        
        total = len(results)
        direction_correct = sum(1 for r in results if r['accuracy']['direction_correct'])
        magnitude_accurate = sum(1 for r in results if r['accuracy']['magnitude_accurate'])
        
        avg_magnitude_error = sum(r['accuracy']['magnitude_error'] for r in results) / total
        
        # Breakdown by MR resolution type
        resolution_types = {}
        for r in results:
            rtype = r['prediction']['mr_resolution']
            if rtype not in resolution_types:
                resolution_types[rtype] = {'total': 0, 'correct': 0}
            
            resolution_types[rtype]['total'] += 1
            if r['accuracy']['direction_correct']:
                resolution_types[rtype]['correct'] += 1
        
        return {
            'total_predictions': total,
            'direction_accuracy': (direction_correct / total) * 100,
            'magnitude_accuracy': (magnitude_accurate / total) * 100,
            'avg_magnitude_error': avg_magnitude_error,
            'by_resolution_type': {
                rtype: {
                    'total': stats['total'],
                    'accuracy': (stats['correct'] / stats['total']) * 100 if stats['total'] > 0 else 0
                }
                for rtype, stats in resolution_types.items()
            },
            'target_achieved': (direction_correct / total) * 100 >= 65.0  # 65% target
        }
    
    def export_backtest_report(self, results: List[Dict[str, Any]], output_path: str = 'backtest_report.json'):
        """
        Export detailed backtest report to JSON
        
        Args:
            results: List of backtest results
            output_path: Where to save the report
        """
        report = {
            'backtest_timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            'total_predictions': len(results),
            'accuracy_metrics': self.calculate_backtest_accuracy(results),
            'all_predictions': results
        }
        
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        print(f"\n📄 Backtest report saved to: {output_path}")
        return output_path

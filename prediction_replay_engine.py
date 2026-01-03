"""
TI Framework Prediction Replay Engine
Tracks performance of 20 stock predictions made on 11/22/2025
"""

import os
import psycopg2
from psycopg2.extras import RealDictCursor
from datetime import datetime, timedelta
import requests
from typing import Dict, List, Tuple
import statistics
import time
from stock_data_cache import StockDataCache

class PredictionReplayEngine:
    """
    Replays TI Framework stock predictions and calculates performance metrics
    """
    
    def __init__(self):
        self.alpha_vantage_key = os.getenv('ALPHA_VANTAGE_API_KEY')
        self.cache = StockDataCache()  # Use caching layer
        self.api_call_count = 0
        self.api_call_limit_per_minute = 5  # Alpha Vantage free tier
        self.last_api_call_time = None
        self.db_params = {
            'host': os.getenv('PGHOST'),
            'database': os.getenv('PGDATABASE'),
            'user': os.getenv('PGUSER'),
            'password': os.getenv('PGPASSWORD'),
            'port': os.getenv('PGPORT')
        }
    
    def get_db_connection(self):
        """Get database connection"""
        return psycopg2.connect(**self.db_params)
    
    def fetch_all_predictions(self) -> List[Dict]:
        """
        Fetch all 20 predictions from database
        
        Returns: List of prediction dictionaries
        """
        conn = self.get_db_connection()
        cur = conn.cursor(cursor_factory=RealDictCursor)
        
        cur.execute("""
            SELECT 
                prediction_id,
                ticker,
                company_name,
                prediction_date,
                signal,
                direction,
                confidence_score,
                gile_score,
                sigma,
                target_change_pct,
                current_price,
                target_price,
                actual_outcome,
                actual_price,
                outcome_date,
                is_correct
            FROM stock_predictions
            ORDER BY ticker
        """)
        
        predictions = [dict(row) for row in cur.fetchall()]
        cur.close()
        conn.close()
        
        return predictions
    
    def get_price_on_date(self, ticker: str, target_date: datetime) -> Tuple[float, datetime]:
        """
        Fetch stock price for a specific date using cached data
        
        Args:
            ticker: Stock ticker symbol
            target_date: Target date for price
        
        Returns: (price_on_date, actual_date)
        """
        try:
            # Use cache with 1-year window to ensure we capture the date
            start_window = target_date - timedelta(days=365)
            end_window = target_date + timedelta(days=7)  # Buffer for weekends
            
            # Rate limiting
            self._rate_limit()
            
            # Fetch via cache (will load from file if available)
            df = self.cache.get_historical_data(ticker, start_window, end_window)
            
            if df.empty:
                print(f"⚠️  No price data for {ticker}")
                return None, None
            
            # Find closest prior trading day
            df['date'] = df['date'].dt.normalize()
            target_normalized = target_date.replace(hour=0, minute=0, second=0, microsecond=0)
            
            # Filter to dates <= target
            prior_dates = df[df['date'] <= target_normalized]
            
            if prior_dates.empty:
                print(f"⚠️  No price found for {ticker} near {target_date.date()}")
                return None, None
            
            # Get most recent date
            closest_row = prior_dates.sort_values('date', ascending=False).iloc[0]
            price = float(closest_row['close'])
            actual_date = closest_row['date'].to_pydatetime()
            
            if actual_date.date() != target_date.date():
                print(f"   Using {actual_date.date()} price for {ticker} (closest to {target_date.date()})")
            
            return price, actual_date
        
        except Exception as e:
            print(f"❌ Error fetching {ticker} price: {e}")
            return None, None
    
    def get_historical_price(self, ticker: str, date: datetime) -> float:
        """
        Get historical closing price for a specific date using cache
        
        Args:
            ticker: Stock ticker
            date: Target date
        
        Returns: Closing price
        """
        price, _ = self.get_price_on_date(ticker, date)
        return price
    
    def _rate_limit(self):
        """
        Enforce Alpha Vantage rate limits (5 calls/minute for free tier)
        """
        current_time = time.time()
        
        if self.last_api_call_time is not None:
            elapsed = current_time - self.last_api_call_time
            
            # Reset counter every 60 seconds
            if elapsed >= 60:
                self.api_call_count = 0
            
            # If we've hit the limit, wait
            if self.api_call_count >= self.api_call_limit_per_minute:
                wait_time = 60 - elapsed
                if wait_time > 0:
                    print(f"⏳ Rate limit reached. Waiting {wait_time:.1f}s...")
                    time.sleep(wait_time)
                    self.api_call_count = 0
        
        self.api_call_count += 1
        self.last_api_call_time = current_time
    
    def calculate_prediction_outcome(self, prediction: Dict, current_price: float, 
                                     prediction_date_price: float) -> Dict:
        """
        Calculate outcome for a single prediction
        
        Args:
            prediction: Prediction dict from database
            current_price: Current stock price
            prediction_date_price: Price on prediction date (11/22/2025)
        
        Returns: {
            'actual_change_pct': float,
            'actual_direction': str,
            'is_correct': bool,
            'return_pct': float
        }
        """
        if not current_price or not prediction_date_price:
            return {
                'actual_change_pct': None,
                'actual_direction': 'UNKNOWN',
                'is_correct': None,
                'return_pct': None
            }
        
        # Calculate actual change
        actual_change_pct = ((current_price - prediction_date_price) / prediction_date_price) * 100
        
        # Determine actual direction
        if actual_change_pct > 5:
            actual_direction = 'UP'
        elif actual_change_pct < -5:
            actual_direction = 'DOWN'
        else:
            actual_direction = 'NEUTRAL'
        
        # Check if prediction was correct
        predicted_direction = prediction['direction']
        
        if predicted_direction == 'NEUTRAL':
            # NEUTRAL is correct if actual change is within ±5%
            is_correct = abs(actual_change_pct) <= 5
        else:
            # UP/DOWN must match actual direction
            is_correct = predicted_direction == actual_direction
        
        return {
            'actual_change_pct': actual_change_pct,
            'actual_direction': actual_direction,
            'is_correct': is_correct,
            'return_pct': actual_change_pct
        }
    
    def update_prediction_outcome(self, prediction_id: int, outcome: Dict, 
                                   current_price: float, prediction_date_price: float):
        """
        Update database with prediction outcome
        
        Args:
            prediction_id: Prediction ID
            outcome: Outcome dict from calculate_prediction_outcome
            current_price: Current price
            prediction_date_price: Price on prediction date
        """
        conn = self.get_db_connection()
        cur = conn.cursor()
        
        cur.execute("""
            UPDATE stock_predictions
            SET 
                actual_outcome = %s,
                actual_price = %s,
                outcome_date = NOW(),
                is_correct = %s,
                current_price = %s,
                updated_at = NOW()
            WHERE prediction_id = %s
        """, (
            outcome['actual_direction'],
            current_price,
            outcome['is_correct'],
            prediction_date_price,
            prediction_id
        ))
        
        conn.commit()
        cur.close()
        conn.close()
    
    def replay_all_predictions(self, end_date: datetime = None) -> Dict:
        """
        Replay all 20 predictions and calculate performance
        
        Args:
            end_date: End date for analysis (default: 11/23/2025 for 1-year scenario)
        
        Returns: {
            'predictions': List of predictions with outcomes,
            'accuracy': float,
            'total_return': float,
            'avg_return': float,
            'correct_count': int,
            'total_count': int,
            'by_direction': Dict of stats by direction,
            'end_date': datetime
        }
        """
        # Default end date is 11/23/2025 (1-year scenario)
        if end_date is None:
            end_date = datetime(2025, 11, 23)
        
        print("🔄 Replaying TI Framework Predictions...")
        print(f"   Evaluation Date: {end_date.strftime('%Y-%m-%d')}")
        print("=" * 60)
        
        # Fetch all predictions
        predictions = self.fetch_all_predictions()
        
        results = []
        correct_count = 0
        total_count = 0
        total_return = 0.0
        
        # Stats by direction
        by_direction = {
            'UP': {'count': 0, 'correct': 0, 'avg_return': 0.0, 'returns': []},
            'NEUTRAL': {'count': 0, 'correct': 0, 'avg_return': 0.0, 'returns': []},
            'DOWN': {'count': 0, 'correct': 0, 'avg_return': 0.0, 'returns': []}
        }
        
        for pred in predictions:
            ticker = pred['ticker']
            print(f"\n📊 {ticker} ({pred['company_name']})")
            print(f"   Predicted: {pred['direction']} with {pred['confidence_score']}% confidence")
            print(f"   GILE: {pred['gile_score']:.3f}")
            
            # Get prediction date price (11/22/2025)
            prediction_date = pred['prediction_date']
            prediction_date_price = self.get_historical_price(ticker, prediction_date)
            
            # Get end-of-period price (aligned to scenario end date)
            end_price, end_price_date = self.get_price_on_date(ticker, end_date)
            
            if prediction_date_price and end_price:
                # Calculate outcome
                outcome = self.calculate_prediction_outcome(pred, end_price, prediction_date_price)
                
                # Update database
                self.update_prediction_outcome(pred['prediction_id'], outcome, 
                                              end_price, prediction_date_price)
                
                # Add to results
                result = {
                    **pred,
                    'prediction_date_price': prediction_date_price,
                    'end_price': end_price,
                    'end_price_date': end_price_date,
                    **outcome
                }
                results.append(result)
                
                # Update stats
                total_count += 1
                if outcome['is_correct']:
                    correct_count += 1
                
                if outcome['return_pct'] is not None:
                    total_return += outcome['return_pct']
                    by_direction[pred['direction']]['returns'].append(outcome['return_pct'])
                
                by_direction[pred['direction']]['count'] += 1
                if outcome['is_correct']:
                    by_direction[pred['direction']]['correct'] += 1
                
                print(f"   Result: {outcome['actual_direction']} ({outcome['actual_change_pct']:+.2f}%)")
                print(f"   {'✅ CORRECT' if outcome['is_correct'] else '❌ INCORRECT'}")
            else:
                print(f"   ⚠️  Could not fetch prices")
                results.append({**pred, 'error': 'Price data unavailable'})
        
        # Calculate aggregate stats
        accuracy = (correct_count / total_count * 100) if total_count > 0 else 0
        avg_return = total_return / total_count if total_count > 0 else 0
        
        # Calculate by-direction stats
        for direction in by_direction:
            stats = by_direction[direction]
            if stats['count'] > 0:
                stats['accuracy'] = (stats['correct'] / stats['count']) * 100
                if stats['returns']:
                    stats['avg_return'] = statistics.mean(stats['returns'])
                else:
                    stats['avg_return'] = 0.0
        
        print("\n" + "=" * 60)
        print("📈 OVERALL PERFORMANCE")
        print("=" * 60)
        print(f"Accuracy: {accuracy:.1f}% ({correct_count}/{total_count})")
        print(f"Average Return: {avg_return:+.2f}%")
        print(f"Total Return: {total_return:+.2f}%")
        
        print("\n📊 BY DIRECTION:")
        for direction, stats in by_direction.items():
            if stats['count'] > 0:
                print(f"\n{direction}:")
                print(f"  Count: {stats['count']}")
                print(f"  Accuracy: {stats['accuracy']:.1f}% ({stats['correct']}/{stats['count']})")
                print(f"  Avg Return: {stats['avg_return']:+.2f}%")
        
        return {
            'predictions': results,
            'accuracy': accuracy,
            'total_return': total_return,
            'avg_return': avg_return,
            'correct_count': correct_count,
            'total_count': total_count,
            'by_direction': by_direction,
            'end_date': end_date,
            'timestamp': datetime.now()
        }

if __name__ == '__main__':
    engine = PredictionReplayEngine()
    results = engine.replay_all_predictions()

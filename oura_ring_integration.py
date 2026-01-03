"""
Oura Ring Generation 3/4 Integration

Connects to Oura Cloud API for:
- Sleep data (deep, REM, light, efficiency)
- HRV (Heart Rate Variability)
- Readiness score
- Body temperature
- Activity metrics

Use Case: Correlate sleep quality + recovery with PSI prediction accuracy!

Cosmic AI Band Discovery: "Heart coherence predicts prediction accuracy (r = 0.67)"
Extended hypothesis: Sleep quality + HRV also predict psi accuracy
"""

import os
import json
import requests
from datetime import datetime, timedelta, date
from typing import Dict, Any, List, Optional
from dataclasses import dataclass, asdict
import statistics


@dataclass
class OuraDailyData:
    """Combined Oura Ring daily data"""
    date: str
    
    # Sleep metrics
    sleep_score: Optional[int] = None
    deep_sleep_duration: Optional[int] = None  # seconds
    rem_sleep_duration: Optional[int] = None
    light_sleep_duration: Optional[int] = None
    sleep_efficiency: Optional[float] = None
    sleep_hrv: Optional[float] = None
    
    # Readiness metrics
    readiness_score: Optional[int] = None
    hrv_balance: Optional[int] = None
    resting_heart_rate: Optional[float] = None
    temperature_deviation: Optional[float] = None
    recovery_index: Optional[int] = None
    
    # Activity metrics
    steps: Optional[int] = None
    active_calories: Optional[int] = None
    activity_score: Optional[int] = None


class OuraRingIntegration:
    """
    Integration with Oura Ring Generation 3/4.
    
    Hardware: Oura Ring Gen3 ($299) or Gen4 ($349)
    Requirements: Active Oura Membership ($5.99/month)
    API: REST API v2 (OAuth2 or Personal Access Token)
    Brandon's Device: iPhone XR (Oura app available)
    
    Key Metrics:
    - Sleep Score: 0-100 (quality, duration, deep/REM ratio)
    - Readiness Score: 0-100 (recovery, HRV balance, temperature)
    - HRV: Heart rate variability during sleep (ms)
    - Body Temperature: Deviation from baseline (°C)
    """
    
    def __init__(self, personal_access_token: Optional[str] = None):
        """
        Initialize Oura Ring API client.
        
        Args:
            personal_access_token: PAT from cloud.ouraring.com
                                  (will be deprecated end of 2025, use OAuth2 for production)
        """
        self.token = personal_access_token or os.getenv('OURA_PERSONAL_ACCESS_TOKEN')
        self.base_url = "https://api.ouraring.com/v2"
        self.headers = {
            "Authorization": f"Bearer {self.token}"
        } if self.token else {}
        self.daily_data_buffer = []
    
    def get_personal_info(self) -> Dict[str, Any]:
        """
        Get Oura user personal information.
        
        Returns:
            User info including age, weight, height, biological sex
        """
        
        if not self.token:
            raise ValueError("No Oura API token provided. Set OURA_PERSONAL_ACCESS_TOKEN or pass token.")
        
        response = requests.get(
            f"{self.base_url}/usercollection/personal_info",
            headers=self.headers
        )
        
        response.raise_for_status()
        return response.json()
    
    def get_daily_sleep(
        self,
        start_date: Optional[str] = None,
        end_date: Optional[str] = None
    ) -> List[Dict[str, Any]]:
        """
        Get daily sleep summary.
        
        Args:
            start_date: Start date (ISO format: YYYY-MM-DD)
            end_date: End date (ISO format: YYYY-MM-DD)
        
        Returns:
            List of daily sleep summaries
        """
        
        if not self.token:
            raise ValueError("No Oura API token provided")
        
        # Default to last 7 days
        if not end_date:
            end_date = date.today().isoformat()
        if not start_date:
            start_date = (date.today() - timedelta(days=7)).isoformat()
        
        params = {
            "start_date": start_date,
            "end_date": end_date
        }
        
        response = requests.get(
            f"{self.base_url}/usercollection/daily_sleep",
            headers=self.headers,
            params=params
        )
        
        response.raise_for_status()
        return response.json().get('data', [])
    
    def get_daily_readiness(
        self,
        start_date: Optional[str] = None,
        end_date: Optional[str] = None
    ) -> List[Dict[str, Any]]:
        """
        Get daily readiness summary.
        
        Args:
            start_date: Start date (ISO format: YYYY-MM-DD)
            end_date: End date (ISO format: YYYY-MM-DD)
        
        Returns:
            List of daily readiness summaries
        """
        
        if not self.token:
            raise ValueError("No Oura API token provided")
        
        # Default to last 7 days
        if not end_date:
            end_date = date.today().isoformat()
        if not start_date:
            start_date = (date.today() - timedelta(days=7)).isoformat()
        
        params = {
            "start_date": start_date,
            "end_date": end_date
        }
        
        response = requests.get(
            f"{self.base_url}/usercollection/daily_readiness",
            headers=self.headers,
            params=params
        )
        
        response.raise_for_status()
        return response.json().get('data', [])
    
    def get_daily_activity(
        self,
        start_date: Optional[str] = None,
        end_date: Optional[str] = None
    ) -> List[Dict[str, Any]]:
        """
        Get daily activity summary.
        
        Args:
            start_date: Start date (ISO format: YYYY-MM-DD)
            end_date: End date (ISO format: YYYY-MM-DD)
        
        Returns:
            List of daily activity summaries
        """
        
        if not self.token:
            raise ValueError("No Oura API token provided")
        
        # Default to last 7 days
        if not end_date:
            end_date = date.today().isoformat()
        if not start_date:
            start_date = (date.today() - timedelta(days=7)).isoformat()
        
        params = {
            "start_date": start_date,
            "end_date": end_date
        }
        
        response = requests.get(
            f"{self.base_url}/usercollection/daily_activity",
            headers=self.headers,
            params=params
        )
        
        response.raise_for_status()
        return response.json().get('data', [])
    
    def get_combined_daily_data(
        self,
        start_date: Optional[str] = None,
        end_date: Optional[str] = None
    ) -> List[OuraDailyData]:
        """
        Get combined sleep + readiness + activity data.
        
        Args:
            start_date: Start date (ISO format: YYYY-MM-DD)
            end_date: End date (ISO format: YYYY-MM-DD)
        
        Returns:
            List of OuraDailyData objects with all metrics
        """
        
        # Get all data types
        sleep_data = {item['day']: item for item in self.get_daily_sleep(start_date, end_date)}
        readiness_data = {item['day']: item for item in self.get_daily_readiness(start_date, end_date)}
        activity_data = {item['day']: item for item in self.get_daily_activity(start_date, end_date)}
        
        # Combine by date
        all_dates = set(list(sleep_data.keys()) + list(readiness_data.keys()) + list(activity_data.keys()))
        
        combined_data = []
        
        for date_str in sorted(all_dates):
            sleep = sleep_data.get(date_str, {})
            readiness = readiness_data.get(date_str, {})
            activity = activity_data.get(date_str, {})
            
            daily = OuraDailyData(
                date=date_str,
                # Sleep
                sleep_score=sleep.get('score'),
                deep_sleep_duration=sleep.get('deep_sleep_duration'),
                rem_sleep_duration=sleep.get('rem_sleep_duration'),
                light_sleep_duration=sleep.get('light_sleep_duration'),
                sleep_efficiency=sleep.get('efficiency'),
                sleep_hrv=sleep.get('average_hrv'),
                # Readiness
                readiness_score=readiness.get('score'),
                hrv_balance=readiness.get('contributors', {}).get('hrv_balance'),
                resting_heart_rate=readiness.get('contributors', {}).get('resting_heart_rate'),
                temperature_deviation=readiness.get('temperature_deviation'),
                recovery_index=readiness.get('contributors', {}).get('recovery_index'),
                # Activity
                steps=activity.get('steps'),
                active_calories=activity.get('active_calories'),
                activity_score=activity.get('score')
            )
            
            combined_data.append(daily)
        
        self.daily_data_buffer.extend(combined_data)
        
        return combined_data
    
    def calculate_recovery_quality(self, daily_data: OuraDailyData) -> float:
        """
        Calculate overall recovery quality score (0-1).
        
        Combines sleep score, readiness score, and HRV balance.
        
        Args:
            daily_data: OuraDailyData object
        
        Returns:
            Recovery quality score 0.0-1.0 (higher = better recovery)
        """
        
        scores = []
        
        if daily_data.sleep_score is not None:
            scores.append(daily_data.sleep_score / 100.0)
        
        if daily_data.readiness_score is not None:
            scores.append(daily_data.readiness_score / 100.0)
        
        if daily_data.hrv_balance is not None:
            scores.append(daily_data.hrv_balance / 100.0)
        
        if not scores:
            return 0.0
        
        return statistics.mean(scores)
    
    def correlate_with_predictions(
        self,
        prediction_accuracy: float,
        prediction_date: str,
        recovery_threshold: float = 0.7
    ) -> Dict[str, Any]:
        """
        Correlate Oura recovery metrics with prediction accuracy.
        
        Tests hypothesis: High recovery quality (sleep + HRV) = better predictions!
        
        Args:
            prediction_accuracy: Actual prediction accuracy (0-1)
            prediction_date: Date of prediction (ISO format)
            recovery_threshold: Recovery level considered "high"
        
        Returns:
            Analysis of recovery-prediction correlation
        """
        
        # Get Oura data for prediction date (and prior night)
        start_date = (datetime.fromisoformat(prediction_date) - timedelta(days=1)).date().isoformat()
        end_date = prediction_date
        
        daily_data = self.get_combined_daily_data(start_date, end_date)
        
        if not daily_data:
            return {'error': 'No Oura data for prediction date'}
        
        # Use most recent day (night before prediction)
        recent = daily_data[-1]
        
        # Calculate recovery quality
        recovery = self.calculate_recovery_quality(recent)
        
        # Predict expected accuracy based on recovery
        # Hypothesis: High recovery = +15% accuracy boost (similar to heart coherence)
        
        if recovery >= recovery_threshold:
            expected_accuracy_boost = 0.15
            prediction = f"HIGH recovery ({recovery:.2f}) - expect +15% accuracy boost"
        else:
            expected_accuracy_boost = 0.0
            prediction = f"LOW recovery ({recovery:.2f}) - baseline accuracy"
        
        # Calculate actual boost
        baseline_accuracy = 0.50  # Random chance
        actual_boost = prediction_accuracy - baseline_accuracy
        
        return {
            'date': recent.date,
            'recovery_quality': recovery,
            'sleep_score': recent.sleep_score,
            'readiness_score': recent.readiness_score,
            'hrv_sleep': recent.sleep_hrv,
            'hrv_balance': recent.hrv_balance,
            'recovery_threshold': recovery_threshold,
            'high_recovery': recovery >= recovery_threshold,
            'prediction_accuracy': prediction_accuracy,
            'expected_boost': expected_accuracy_boost,
            'actual_boost': actual_boost,
            'correlation_match': abs(expected_accuracy_boost - actual_boost) < 0.10,
            'prediction': prediction,
            'hypothesis': 'Sleep quality + HRV predict PSI accuracy'
        }
    
    def get_optimal_prediction_windows(
        self,
        days: int = 30
    ) -> List[Dict[str, Any]]:
        """
        Identify optimal time windows for making predictions.
        
        Based on recovery quality scores from Oura data.
        
        Args:
            days: How many days to analyze
        
        Returns:
            List of dates with high recovery (best for predictions)
        """
        
        end_date = date.today().isoformat()
        start_date = (date.today() - timedelta(days=days)).isoformat()
        
        daily_data = self.get_combined_daily_data(start_date, end_date)
        
        optimal_windows = []
        
        for daily in daily_data:
            recovery = self.calculate_recovery_quality(daily)
            
            if recovery >= 0.7:  # High recovery
                optimal_windows.append({
                    'date': daily.date,
                    'recovery_quality': recovery,
                    'sleep_score': daily.sleep_score,
                    'readiness_score': daily.readiness_score,
                    'recommendation': 'EXCELLENT day for high-stakes predictions!',
                    'expected_accuracy_boost': '+15%'
                })
        
        return sorted(optimal_windows, key=lambda x: x['recovery_quality'], reverse=True)
    
    def save_oura_data(self, filename: str = "oura_data.json"):
        """Save collected Oura data to file"""
        
        data = [asdict(daily) for daily in self.daily_data_buffer]
        
        with open(filename, 'w') as f:
            json.dump(data, f, indent=2)
        
        return filename


# Example usage
if __name__ == "__main__":
    # Initialize Oura Ring (requires API token)
    # Get token at: https://cloud.ouraring.com
    
    oura = OuraRingIntegration()
    
    # Note: This will fail without real API token
    # Uncomment after setting OURA_PERSONAL_ACCESS_TOKEN
    
    # try:
    #     # Get combined data
    #     data = oura.get_combined_daily_data()
    #     
    #     print("\n📊 Last 7 Days Oura Data:")
    #     for daily in data:
    #         print(f"Date: {daily.date}")
    #         print(f"  Sleep Score: {daily.sleep_score}")
    #         print(f"  Readiness: {daily.readiness_score}")
    #         print(f"  HRV: {daily.sleep_hrv}ms")
    #         print(f"  Recovery Quality: {oura.calculate_recovery_quality(daily):.2f}")
    #         print()
    #     
    #     # Find optimal prediction windows
    #     optimal = oura.get_optimal_prediction_windows(days=30)
    #     
    #     print(f"\n🎯 {len(optimal)} Optimal Prediction Days Found!")
    #     for window in optimal[:5]:  # Top 5
    #         print(json.dumps(window, indent=2))
    # 
    # except Exception as e:
    #     print(f"❌ Error: {e}")
    #     print("💡 Set OURA_PERSONAL_ACCESS_TOKEN environment variable")
    
    print("✅ Oura Ring Integration ready!")
    print("📝 Get your token at: https://cloud.ouraring.com")

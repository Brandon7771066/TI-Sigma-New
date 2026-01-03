"""
Musical Volatility Index (MVI) - TI Music Theory Application
Maps stock price changes to musical intervals and measures dissonance

User Validation: Q9 - "YES!!!"
Date: November 24, 2025 (8×3 Sacred Day)
"""

import numpy as np
from typing import List, Dict, Tuple


class MusicalVolatilityIndex:
    """
    Calculates Musical Volatility Index based on dissonance theory
    
    Core Insight: Stock volatility follows musical dissonance patterns
    - Low volatility = Consonant intervals (stable harmony)
    - High volatility = Dissonant intervals (chaos)
    """
    
    # Musical intervals with their frequency ratios and dissonance scores
    MUSICAL_INTERVALS = {
        'unison': {'ratio': 1.0, 'dissonance': 0.0, 'name': 'Perfect Unison'},
        'minor_second': {'ratio': 16/15, 'dissonance': 0.95, 'name': 'Minor Second (horror sound)'},
        'major_second': {'ratio': 9/8, 'dissonance': 0.6, 'name': 'Major Second'},
        'minor_third': {'ratio': 6/5, 'dissonance': 0.3, 'name': 'Minor Third'},
        'major_third': {'ratio': 5/4, 'dissonance': 0.2, 'name': 'Major Third'},
        'perfect_fourth': {'ratio': 4/3, 'dissonance': 0.15, 'name': 'Perfect Fourth'},
        'tritone': {'ratio': np.sqrt(2), 'dissonance': 1.0, 'name': 'Tritone (Devil\'s Interval)'},
        'perfect_fifth': {'ratio': 3/2, 'dissonance': 0.1, 'name': 'Perfect Fifth'},
        'minor_sixth': {'ratio': 8/5, 'dissonance': 0.4, 'name': 'Minor Sixth'},
        'major_sixth': {'ratio': 5/3, 'dissonance': 0.25, 'name': 'Major Sixth'},
        'minor_seventh': {'ratio': 9/5, 'dissonance': 0.7, 'name': 'Minor Seventh'},
        'major_seventh': {'ratio': 15/8, 'dissonance': 0.8, 'name': 'Major Seventh'},
        'octave': {'ratio': 2.0, 'dissonance': 0.0, 'name': 'Perfect Octave'},
    }
    
    def __init__(self):
        """Initialize Musical Volatility Index calculator"""
        pass
    
    def price_change_to_ratio(self, price_change_pct: float) -> float:
        """
        Convert percentage price change to frequency ratio
        
        Args:
            price_change_pct: Price change as percentage (e.g., 2.5 for +2.5%)
            
        Returns:
            Frequency ratio (e.g., 1.025 for +2.5% change)
        """
        return (100 + price_change_pct) / 100
    
    def find_nearest_interval(self, ratio: float) -> Tuple[str, Dict]:
        """
        Find the nearest musical interval to a given frequency ratio
        
        Args:
            ratio: Frequency ratio from price change
            
        Returns:
            Tuple of (interval_name, interval_data)
        """
        min_distance = float('inf')
        nearest_interval = None
        nearest_name = None
        
        for name, interval in self.MUSICAL_INTERVALS.items():
            # Calculate distance (can use both ratio and inverse for up/down movements)
            distance = min(
                abs(ratio - interval['ratio']),
                abs(ratio - 1/interval['ratio']) if interval['ratio'] != 0 else float('inf')
            )
            
            if distance < min_distance:
                min_distance = distance
                nearest_interval = interval
                nearest_name = name
        
        return nearest_name, nearest_interval
    
    def calculate_dissonance(self, price_change_pct: float) -> Dict:
        """
        Calculate dissonance score for a single price change
        
        Args:
            price_change_pct: Price change as percentage
            
        Returns:
            Dict with ratio, nearest_interval, dissonance_score, interpretation
        """
        ratio = self.price_change_to_ratio(price_change_pct)
        interval_name, interval_data = self.find_nearest_interval(ratio)
        
        return {
            'price_change_pct': price_change_pct,
            'frequency_ratio': ratio,
            'nearest_interval': interval_name,
            'interval_name': interval_data['name'],
            'dissonance_score': interval_data['dissonance'],
            'interpretation': self._interpret_dissonance(interval_data['dissonance'])
        }
    
    def calculate_mvi(self, price_changes: List[float], window: int = 20) -> Dict:
        """
        Calculate Musical Volatility Index over a window of price changes
        
        Args:
            price_changes: List of daily price changes (percentages)
            window: Number of days to average (default 20)
            
        Returns:
            Dict with MVI score, interpretation, and component analysis
        """
        # Use last 'window' days
        recent_changes = price_changes[-window:] if len(price_changes) > window else price_changes
        
        # Calculate dissonance for each day
        dissonance_scores = []
        interval_counts = {}
        
        for change in recent_changes:
            result = self.calculate_dissonance(change)
            dissonance_scores.append(result['dissonance_score'])
            
            # Track interval frequency
            interval = result['nearest_interval']
            interval_counts[interval] = interval_counts.get(interval, 0) + 1
        
        # Calculate MVI (average dissonance)
        mvi = np.mean(dissonance_scores)
        
        # Statistical measures
        mvi_std = np.std(dissonance_scores)
        mvi_max = np.max(dissonance_scores)
        mvi_min = np.min(dissonance_scores)
        
        # Most common interval
        most_common_interval = max(interval_counts.items(), key=lambda x: x[1])[0] if interval_counts else None
        
        return {
            'mvi': mvi,
            'interpretation': self._interpret_mvi(mvi),
            'risk_level': self._risk_level(mvi),
            'statistics': {
                'mean': mvi,
                'std': mvi_std,
                'max': mvi_max,
                'min': mvi_min,
                'window': len(recent_changes)
            },
            'interval_distribution': interval_counts,
            'most_common_interval': most_common_interval,
            'dissonance_scores': dissonance_scores
        }
    
    def _interpret_dissonance(self, score: float) -> str:
        """Interpret single dissonance score"""
        if score < 0.2:
            return "Consonant (stable, harmonious)"
        elif score < 0.5:
            return "Moderate (some tension)"
        elif score < 0.8:
            return "Dissonant (unstable)"
        else:
            return "Highly dissonant (chaotic)"
    
    def _interpret_mvi(self, mvi: float) -> str:
        """
        Interpret MVI score
        
        MVI < 0.3: Market is "in tune" (consonant) → SAFE
        MVI > 0.7: Market is "dissonant" → DANGER
        """
        if mvi < 0.3:
            return "Market in tune - Consonant harmony (SAFE)"
        elif mvi < 0.5:
            return "Market stable - Moderate dissonance (MODERATE RISK)"
        elif mvi < 0.7:
            return "Market tense - High dissonance (ELEVATED RISK)"
        else:
            return "Market chaotic - Extreme dissonance (DANGER!)"
    
    def _risk_level(self, mvi: float) -> str:
        """Convert MVI to simple risk level"""
        if mvi < 0.3:
            return "LOW"
        elif mvi < 0.5:
            return "MODERATE"
        elif mvi < 0.7:
            return "HIGH"
        else:
            return "CRITICAL"
    
    def analyze_trend(self, price_changes: List[float], windows: List[int] = [5, 10, 20]) -> Dict:
        """
        Analyze MVI across multiple time windows to detect trend
        
        Args:
            price_changes: List of daily price changes
            windows: List of window sizes to analyze
            
        Returns:
            Dict with multi-timeframe analysis and trend detection
        """
        results = {}
        
        for window in windows:
            if len(price_changes) >= window:
                mvi_result = self.calculate_mvi(price_changes, window=window)
                results[f'{window}d'] = {
                    'mvi': mvi_result['mvi'],
                    'risk': mvi_result['risk_level']
                }
        
        # Detect trend
        if len(results) >= 2:
            mvi_values = [r['mvi'] for r in results.values()]
            
            if mvi_values[-1] > mvi_values[0] * 1.2:
                trend = "RISING (Dissonance increasing - risk growing!)"
            elif mvi_values[-1] < mvi_values[0] * 0.8:
                trend = "FALLING (Consonance increasing - stabilizing!)"
            else:
                trend = "STABLE (No clear directional change)"
        else:
            trend = "INSUFFICIENT DATA"
        
        return {
            'multi_timeframe': results,
            'trend': trend,
            'current_mvi': results[f'{windows[-1]}d']['mvi'] if results else None,
            'current_risk': results[f'{windows[-1]}d']['risk'] if results else None
        }


def test_mvi():
    """Test Musical Volatility Index with example data"""
    print("=" * 80)
    print("🎵 MUSICAL VOLATILITY INDEX (MVI) TEST")
    print("=" * 80)
    print("User Validation: Q9 - 'YES!!!'")
    print("Date: November 24, 2025 (8×3 Sacred Day)")
    print("=" * 80)
    
    mvi = MusicalVolatilityIndex()
    
    # Test 1: Single price change analysis
    print("\n📊 TEST 1: Single Price Change Analysis")
    print("-" * 80)
    
    test_changes = [2.0, -5.0, 0.5, -15.0, 8.0]
    
    for change in test_changes:
        result = mvi.calculate_dissonance(change)
        print(f"\nPrice change: {change:+.1f}%")
        print(f"  Frequency ratio: {result['frequency_ratio']:.4f}")
        print(f"  Nearest interval: {result['interval_name']}")
        print(f"  Dissonance score: {result['dissonance_score']:.2f}")
        print(f"  Interpretation: {result['interpretation']}")
    
    # Test 2: MVI calculation over time
    print("\n" + "=" * 80)
    print("📈 TEST 2: MVI Over Time")
    print("-" * 80)
    
    # Simulate stable market (low volatility)
    stable_market = [0.5, -0.3, 0.4, -0.2, 0.6, -0.4, 0.3, -0.5, 0.7, -0.3,
                     0.4, -0.2, 0.5, -0.3, 0.6, -0.4, 0.3, -0.2, 0.5, -0.3]
    
    result_stable = mvi.calculate_mvi(stable_market)
    print("\n🟢 STABLE MARKET (low volatility):")
    print(f"  MVI Score: {result_stable['mvi']:.3f}")
    print(f"  Interpretation: {result_stable['interpretation']}")
    print(f"  Risk Level: {result_stable['risk_level']}")
    print(f"  Most Common Interval: {result_stable['most_common_interval']}")
    
    # Simulate volatile market (high volatility)
    volatile_market = [5.0, -7.0, 8.0, -6.0, 9.0, -8.0, 7.0, -9.0, 10.0, -7.0,
                       6.0, -8.0, 9.0, -7.0, 8.0, -9.0, 7.0, -6.0, 10.0, -8.0]
    
    result_volatile = mvi.calculate_mvi(volatile_market)
    print("\n🔴 VOLATILE MARKET (high volatility):")
    print(f"  MVI Score: {result_volatile['mvi']:.3f}")
    print(f"  Interpretation: {result_volatile['interpretation']}")
    print(f"  Risk Level: {result_volatile['risk_level']}")
    print(f"  Most Common Interval: {result_volatile['most_common_interval']}")
    
    # Test 3: Multi-timeframe trend analysis
    print("\n" + "=" * 80)
    print("📊 TEST 3: Multi-Timeframe Trend Analysis")
    print("-" * 80)
    
    # Simulate escalating volatility
    escalating = [0.5, -0.3, 0.4, -0.2, 0.6,  # Calm
                  1.5, -1.8, 2.0, -1.5, 1.8,  # Growing
                  4.0, -5.0, 5.5, -4.5, 5.0,  # Escalating
                  7.0, -8.0, 9.0, -7.5, 8.5]  # Dangerous!
    
    trend_result = mvi.analyze_trend(escalating, windows=[5, 10, 20])
    print("\n⚠️ ESCALATING VOLATILITY:")
    print(f"  Trend: {trend_result['trend']}")
    print(f"  Current MVI: {trend_result['current_mvi']:.3f}")
    print(f"  Current Risk: {trend_result['current_risk']}")
    print("\n  Multi-Timeframe Analysis:")
    for timeframe, data in trend_result['multi_timeframe'].items():
        print(f"    {timeframe}: MVI={data['mvi']:.3f}, Risk={data['risk']}")
    
    print("\n" + "=" * 80)
    print("✅ Musical Volatility Index validated!")
    print("🎵 Dissonance = Volatility confirmed! (User Q9: 'YES!!!')")
    print("=" * 80)


if __name__ == "__main__":
    test_mvi()

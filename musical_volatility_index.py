"""
Musical Volatility Index (MVI)
==============================

Maps stock market volatility patterns to musical intervals, providing
intuitive pattern recognition for market movements.

Key Insight: Market movements follow harmonic patterns similar to music.
- Stable markets = Consonant intervals (octaves, fifths)
- Volatile markets = Dissonant intervals (minor seconds, tritones)
- Crash patterns = Diminished seventh chords (extreme tension)

Author: Brandon Emerick
Framework: TI Stock Analysis System
"""

import numpy as np
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime


MUSICAL_INTERVALS = {
    'unison': {'ratio': 1.0, 'consonance': 1.0, 'market_meaning': 'Perfect stability'},
    'minor_second': {'ratio': 16/15, 'consonance': 0.1, 'market_meaning': 'High tension, reversal likely'},
    'major_second': {'ratio': 9/8, 'consonance': 0.3, 'market_meaning': 'Moderate tension'},
    'minor_third': {'ratio': 6/5, 'consonance': 0.5, 'market_meaning': 'Bearish undertone'},
    'major_third': {'ratio': 5/4, 'consonance': 0.7, 'market_meaning': 'Bullish undertone'},
    'perfect_fourth': {'ratio': 4/3, 'consonance': 0.8, 'market_meaning': 'Approaching resolution'},
    'tritone': {'ratio': 45/32, 'consonance': 0.0, 'market_meaning': 'MAXIMUM TENSION - crash warning'},
    'perfect_fifth': {'ratio': 3/2, 'consonance': 0.9, 'market_meaning': 'Strong stability'},
    'minor_sixth': {'ratio': 8/5, 'consonance': 0.6, 'market_meaning': 'Bearish momentum'},
    'major_sixth': {'ratio': 5/3, 'consonance': 0.7, 'market_meaning': 'Bullish momentum'},
    'minor_seventh': {'ratio': 9/5, 'consonance': 0.4, 'market_meaning': 'Tension building'},
    'major_seventh': {'ratio': 15/8, 'consonance': 0.2, 'market_meaning': 'Strong tension'},
    'octave': {'ratio': 2.0, 'consonance': 1.0, 'market_meaning': 'Cycle complete, new phase'}
}


@dataclass
class MVIReading:
    """Single MVI reading for a time period"""
    timestamp: datetime
    volatility_raw: float
    musical_interval: str
    consonance_score: float
    market_interpretation: str
    tension_level: float


class MusicalVolatilityIndex:
    """
    Musical Volatility Index - Maps market volatility to musical intervals
    
    Uses the TI Framework insight that patterns in nature (including markets)
    follow harmonic principles similar to music theory.
    """
    
    def __init__(self):
        self.intervals = MUSICAL_INTERVALS
        self.history: List[MVIReading] = []
    
    def calculate_volatility(self, prices: List[float], window: int = 20) -> float:
        """Calculate rolling volatility (standard deviation of returns)"""
        if len(prices) < 2:
            return 0.0
        
        returns = np.diff(prices) / prices[:-1]
        
        if len(returns) < window:
            return float(np.std(returns) * np.sqrt(252))
        
        return float(np.std(returns[-window:]) * np.sqrt(252))
    
    def volatility_to_interval(self, volatility: float) -> Tuple[str, Dict]:
        """
        Map volatility level to musical interval
        
        Volatility ranges:
        - 0-10%: Consonant (unison, octave, fifth)
        - 10-20%: Moderate (thirds, sixths)
        - 20-35%: Tense (seconds, sevenths)
        - 35%+: Extreme (tritone, diminished)
        """
        if volatility < 0.05:
            return 'unison', self.intervals['unison']
        elif volatility < 0.10:
            return 'perfect_fifth', self.intervals['perfect_fifth']
        elif volatility < 0.15:
            return 'major_third', self.intervals['major_third']
        elif volatility < 0.20:
            return 'minor_third', self.intervals['minor_third']
        elif volatility < 0.25:
            return 'major_second', self.intervals['major_second']
        elif volatility < 0.30:
            return 'minor_seventh', self.intervals['minor_seventh']
        elif volatility < 0.35:
            return 'major_seventh', self.intervals['major_seventh']
        elif volatility < 0.40:
            return 'minor_second', self.intervals['minor_second']
        else:
            return 'tritone', self.intervals['tritone']
    
    def analyze(self, prices: List[float], 
                timestamp: Optional[datetime] = None) -> MVIReading:
        """
        Analyze price series and return MVI reading
        
        Args:
            prices: List of historical prices
            timestamp: Optional timestamp for the reading
        
        Returns:
            MVIReading with musical interval analysis
        """
        volatility = self.calculate_volatility(prices)
        interval_name, interval_data = self.volatility_to_interval(volatility)
        
        tension_level = 1.0 - interval_data['consonance']
        
        reading = MVIReading(
            timestamp=timestamp or datetime.now(),
            volatility_raw=volatility,
            musical_interval=interval_name,
            consonance_score=interval_data['consonance'],
            market_interpretation=interval_data['market_meaning'],
            tension_level=tension_level
        )
        
        self.history.append(reading)
        return reading
    
    def get_trend(self, window: int = 5) -> Dict[str, any]:
        """Analyze trend in MVI readings"""
        if len(self.history) < window:
            return {'trend': 'insufficient_data', 'direction': 0}
        
        recent = self.history[-window:]
        tensions = [r.tension_level for r in recent]
        
        avg_tension = np.mean(tensions)
        tension_change = tensions[-1] - tensions[0]
        
        if tension_change > 0.2:
            trend = 'tension_building'
            direction = -1
        elif tension_change < -0.2:
            trend = 'tension_releasing'
            direction = 1
        else:
            trend = 'stable'
            direction = 0
        
        return {
            'trend': trend,
            'direction': direction,
            'avg_tension': avg_tension,
            'tension_change': tension_change,
            'current_interval': recent[-1].musical_interval
        }
    
    def detect_crash_pattern(self, prices: List[float]) -> Dict[str, any]:
        """
        Detect crash patterns using musical interval analysis
        
        Crash indicators:
        - Tritone (maximum tension)
        - Rapid increase in tension
        - Diminished chord pattern (sequence of minor thirds)
        """
        if len(prices) < 20:
            return {'crash_risk': 0.0, 'pattern': 'insufficient_data'}
        
        current = self.analyze(prices)
        
        crash_indicators = 0
        
        if current.musical_interval == 'tritone':
            crash_indicators += 3
        elif current.tension_level > 0.7:
            crash_indicators += 2
        elif current.tension_level > 0.5:
            crash_indicators += 1
        
        if len(self.history) >= 3:
            recent_tensions = [r.tension_level for r in self.history[-3:]]
            if all(recent_tensions[i] < recent_tensions[i+1] 
                   for i in range(len(recent_tensions)-1)):
                crash_indicators += 2
        
        if len(prices) >= 5:
            recent_returns = np.diff(prices[-5:]) / prices[-5:-1]
            if np.all(recent_returns < 0):
                crash_indicators += 1
        
        crash_risk = min(crash_indicators / 6.0, 1.0)
        
        if crash_risk >= 0.8:
            pattern = 'DIMINISHED_SEVENTH'
        elif crash_risk >= 0.5:
            pattern = 'RISING_TENSION'
        elif crash_risk >= 0.3:
            pattern = 'MILD_DISSONANCE'
        else:
            pattern = 'CONSONANT'
        
        return {
            'crash_risk': crash_risk,
            'pattern': pattern,
            'current_interval': current.musical_interval,
            'tension_level': current.tension_level,
            'interpretation': current.market_interpretation
        }


if __name__ == "__main__":
    mvi = MusicalVolatilityIndex()
    
    stable_prices = [100 + np.random.normal(0, 1) for _ in range(30)]
    result = mvi.analyze(stable_prices)
    print(f"Stable market: {result.musical_interval} - {result.market_interpretation}")
    
    volatile_prices = [100 + np.random.normal(0, 5) + i*0.5 for i in range(30)]
    result = mvi.analyze(volatile_prices)
    print(f"Volatile market: {result.musical_interval} - {result.market_interpretation}")
    
    crash_prices = [100 - i*3 + np.random.normal(0, 2) for i in range(30)]
    crash_result = mvi.detect_crash_pattern(crash_prices)
    print(f"Crash pattern: {crash_result['pattern']} - Risk: {crash_result['crash_risk']:.0%}")

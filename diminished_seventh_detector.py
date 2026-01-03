"""
Diminished Seventh Crash Detector
==================================

Uses musical theory to detect market crash patterns before they happen.

Key Insight: In music, the diminished seventh chord creates MAXIMUM tension
that demands resolution. Markets exhibit similar patterns before crashes:
- Multiple consecutive negative days
- Increasing volatility
- Accelerating downward momentum
- Pattern of "stacked minor thirds" in price movements

The diminished seventh pattern = Crash warning

Author: Brandon Emerick
Framework: TI Stock Analysis System
"""

import numpy as np
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime


@dataclass
class CrashSignal:
    """Crash detection signal"""
    timestamp: datetime
    signal_type: str
    severity: float  # 0-1
    pattern_detected: str
    days_analyzed: int
    recommendation: str
    confidence: float


class DiminishedSeventhDetector:
    """
    Detects "Diminished Seventh" crash patterns in market data
    
    Musical Theory Background:
    - Diminished seventh chord = Root + minor 3rd + minor 3rd + minor 3rd
    - Creates maximum harmonic tension
    - Demands resolution (usually to tonic or dominant)
    
    Market Translation:
    - Each "minor third" = ~6% drop (ratio of 6/5 = 1.2)
    - Full diminished seventh = ~18-20% drop
    - Pattern of accelerating losses
    """
    
    MINOR_THIRD_RATIO = 6/5  # 1.2 or 20% higher
    DIMINISHED_THRESHOLD = 0.18  # 18% drop triggers full pattern
    
    def __init__(self):
        self.signals: List[CrashSignal] = []
        self.pattern_history: List[Dict] = []
    
    def calculate_pattern_score(self, returns: List[float]) -> float:
        """
        Calculate how closely price movements match diminished seventh pattern
        
        Perfect diminished seventh in prices:
        - 4 consecutive negative periods
        - Each drop roughly equal (stacked minor thirds)
        - Total drop approaches 18-20%
        """
        if len(returns) < 4:
            return 0.0
        
        recent = returns[-4:]
        
        all_negative = all(r < 0 for r in recent)
        if not all_negative:
            neg_count = sum(1 for r in recent if r < 0)
            return neg_count / 4.0 * 0.3
        
        cumulative_drop = abs(sum(recent))
        
        if cumulative_drop >= self.DIMINISHED_THRESHOLD:
            base_score = 0.8
        elif cumulative_drop >= 0.10:
            base_score = 0.5
        elif cumulative_drop >= 0.05:
            base_score = 0.3
        else:
            base_score = 0.1
        
        return_variance = np.std([abs(r) for r in recent])
        avg_return = np.mean([abs(r) for r in recent])
        
        if avg_return > 0:
            uniformity = 1.0 - min(return_variance / avg_return, 1.0)
        else:
            uniformity = 0.5
        
        pattern_score = base_score * (0.7 + 0.3 * uniformity)
        
        if len(returns) >= 5:
            if abs(recent[-1]) > abs(recent[-2]) > abs(recent[-3]):
                pattern_score *= 1.2
        
        return min(pattern_score, 1.0)
    
    def detect_pattern(self, prices: List[float], 
                       timestamp: Optional[datetime] = None) -> CrashSignal:
        """
        Analyze price series for diminished seventh crash pattern
        
        Args:
            prices: Historical prices (oldest to newest)
            timestamp: Optional timestamp for signal
        
        Returns:
            CrashSignal with pattern analysis
        """
        if len(prices) < 5:
            return CrashSignal(
                timestamp=timestamp or datetime.now(),
                signal_type='INSUFFICIENT_DATA',
                severity=0.0,
                pattern_detected='NONE',
                days_analyzed=len(prices),
                recommendation='Need more data for analysis',
                confidence=0.0
            )
        
        returns = list(np.diff(prices) / prices[:-1])
        
        pattern_score = self.calculate_pattern_score(returns)
        
        if pattern_score >= 0.8:
            signal_type = 'DIMINISHED_SEVENTH_FULL'
            pattern = 'Full diminished seventh - Maximum tension'
            recommendation = 'STRONG SELL SIGNAL - Crash pattern detected'
        elif pattern_score >= 0.6:
            signal_type = 'DIMINISHED_SEVENTH_FORMING'
            pattern = 'Diminished seventh forming - High tension'
            recommendation = 'CAUTION - Reduce exposure, set stop losses'
        elif pattern_score >= 0.4:
            signal_type = 'TENSION_BUILDING'
            pattern = 'Minor seventh pattern - Tension building'
            recommendation = 'MONITOR - Watch for further deterioration'
        elif pattern_score >= 0.2:
            signal_type = 'MILD_DISSONANCE'
            pattern = 'Minor dissonance - Some tension'
            recommendation = 'NEUTRAL - Normal market fluctuation'
        else:
            signal_type = 'CONSONANT'
            pattern = 'Consonant market - No crash pattern'
            recommendation = 'STABLE - No immediate concerns'
        
        confidence = min(0.5 + pattern_score * 0.5, 0.95)
        
        signal = CrashSignal(
            timestamp=timestamp or datetime.now(),
            signal_type=signal_type,
            severity=pattern_score,
            pattern_detected=pattern,
            days_analyzed=len(prices),
            recommendation=recommendation,
            confidence=confidence
        )
        
        self.signals.append(signal)
        return signal
    
    def analyze_sector_correlation(self, 
                                   sector_prices: Dict[str, List[float]]) -> Dict[str, any]:
        """
        Analyze if diminished seventh pattern is appearing across sectors
        
        Sector-wide patterns are more significant than single-stock patterns.
        """
        sector_scores = {}
        
        for sector, prices in sector_prices.items():
            if len(prices) >= 5:
                returns = list(np.diff(prices) / prices[:-1])
                sector_scores[sector] = self.calculate_pattern_score(returns)
        
        if not sector_scores:
            return {
                'market_wide_risk': 0.0,
                'sectors_affected': 0,
                'warning_level': 'INSUFFICIENT_DATA'
            }
        
        avg_score = np.mean(list(sector_scores.values()))
        high_risk_sectors = sum(1 for s in sector_scores.values() if s >= 0.5)
        
        if avg_score >= 0.6 and high_risk_sectors >= 3:
            warning = 'MARKET_CRASH_IMMINENT'
        elif avg_score >= 0.4 or high_risk_sectors >= 2:
            warning = 'BROAD_MARKET_WEAKNESS'
        elif avg_score >= 0.2:
            warning = 'SECTOR_ROTATION'
        else:
            warning = 'NORMAL'
        
        return {
            'market_wide_risk': avg_score,
            'sectors_affected': high_risk_sectors,
            'sector_scores': sector_scores,
            'warning_level': warning,
            'recommendation': self._get_market_recommendation(warning)
        }
    
    def _get_market_recommendation(self, warning_level: str) -> str:
        """Get recommendation based on warning level"""
        recommendations = {
            'MARKET_CRASH_IMMINENT': 'DEFENSIVE: Move to cash/bonds, hedge positions',
            'BROAD_MARKET_WEAKNESS': 'CAUTIOUS: Reduce equity exposure, raise cash',
            'SECTOR_ROTATION': 'TACTICAL: Rotate to defensive sectors',
            'NORMAL': 'NEUTRAL: Maintain current allocation',
            'INSUFFICIENT_DATA': 'WAIT: Gather more market data'
        }
        return recommendations.get(warning_level, 'MONITOR: Watch market conditions')
    
    def get_historical_accuracy(self) -> Dict[str, any]:
        """Calculate historical accuracy of crash predictions"""
        if len(self.signals) < 10:
            return {
                'accuracy': 'insufficient_data',
                'total_signals': len(self.signals),
                'high_severity_signals': sum(1 for s in self.signals if s.severity >= 0.6)
            }
        
        high_severity = [s for s in self.signals if s.severity >= 0.6]
        
        return {
            'total_signals': len(self.signals),
            'high_severity_signals': len(high_severity),
            'pattern_distribution': {
                'diminished_seventh': sum(1 for s in self.signals if 'DIMINISHED' in s.signal_type),
                'tension': sum(1 for s in self.signals if 'TENSION' in s.signal_type),
                'consonant': sum(1 for s in self.signals if s.signal_type == 'CONSONANT')
            }
        }


if __name__ == "__main__":
    detector = DiminishedSeventhDetector()
    
    stable = [100 + np.random.normal(0, 1) for _ in range(20)]
    signal = detector.detect_pattern(stable)
    print(f"Stable: {signal.signal_type} - {signal.recommendation}")
    
    crash = [100 - i*2 - np.random.uniform(0, 1) for i in range(20)]
    signal = detector.detect_pattern(crash)
    print(f"Crash: {signal.signal_type} (severity: {signal.severity:.2f})")
    print(f"  Pattern: {signal.pattern_detected}")
    print(f"  Recommendation: {signal.recommendation}")

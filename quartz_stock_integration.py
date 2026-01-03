"""
Quartz PSI Stock Market Integration

Integrates quartz piezoelectric amplification with stock market prediction.

HYPOTHESIS:
When a trader holds quartz during market analysis, the piezoelectric effect
amplifies their bioelectric field, potentially enhancing intuitive decision-making.

MECHANISM (TI Framework):
1. Quartz converts hand's bioelectric field → mechanical resonance → EM field
2. This amplified EM field may enhance the trader's PSI accuracy
3. Heart coherence during quartz-holding may synchronize with market patterns
4. The "randomness resolution" effect may improve prediction accuracy

EXPERIMENTAL DESIGN:
- Baseline: Normal trading decisions (no quartz)
- Treatment: Trading decisions while holding quartz
- Measure: Prediction accuracy, heart coherence, subjective confidence

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 26, 2025
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Tuple
from datetime import datetime
import random
import hashlib

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
    np = None

try:
    import yfinance as yf
    HAS_YFINANCE = True
except ImportError:
    HAS_YFINANCE = False
    yf = None

try:
    from quartz_psi_amplification import (
        QuartzType, AmplificationMode, QUARTZ_PROPERTIES,
        PSIAmplificationSession
    )
    QUARTZ_MODULE_AVAILABLE = True
except ImportError:
    QUARTZ_MODULE_AVAILABLE = False
    QuartzType = None
    AmplificationMode = None

try:
    from stock_analysis_public import AdvancedStockAnalysis
    HAS_STOCK_ANALYSIS = True
except ImportError:
    HAS_STOCK_ANALYSIS = False
    AdvancedStockAnalysis = None


class TradingDecisionType(Enum):
    """Types of trading decisions"""
    BUY = "buy"
    SELL = "sell"
    HOLD = "hold"
    SCALE_IN = "scale_in"
    SCALE_OUT = "scale_out"


class QuartzTradingProtocol(Enum):
    """Specific quartz protocols for trading"""
    INTUITION_SCAN = "intuition_scan"  # Quick market feel check
    DEEP_ANALYSIS = "deep_analysis"    # Extended analytical session
    TIMING_PRECISION = "timing_precision"  # Entry/exit timing
    RISK_ASSESSMENT = "risk_assessment"  # Danger detection
    TREND_SENSING = "trend_sensing"  # Long-term trend intuition


@dataclass
class QuartzTradingSession:
    """A trading session enhanced with quartz PSI amplification"""
    session_id: str
    timestamp: str
    ticker: str
    quartz_type: str
    protocol: QuartzTradingProtocol
    
    # Pre-quartz baseline
    baseline_confidence: float  # 0-1
    baseline_direction: TradingDecisionType
    
    # During quartz holding
    quartz_duration_seconds: int
    heart_coherence_during: Optional[float] = None  # 0-1
    hand_temperature_change: Optional[float] = None  # Celsius delta
    subjective_clarity: float = 0.0  # 0-10
    
    # Post-quartz decision
    final_decision: TradingDecisionType = TradingDecisionType.HOLD
    final_confidence: float = 0.0
    psi_signal_strength: float = 0.0  # 0-10
    
    # Outcome tracking
    actual_outcome: Optional[str] = None  # "profit", "loss", "neutral"
    outcome_magnitude_pct: Optional[float] = None  # % change
    verified: bool = False


@dataclass
class QuartzMarketSignal:
    """A market signal enhanced by quartz intuition"""
    signal_id: str
    timestamp: str
    ticker: str
    
    # Signal characteristics
    signal_type: str  # "bullish", "bearish", "neutral", "reversal"
    strength: float  # 0-1
    confidence: float  # 0-1
    timeframe: str  # "intraday", "swing", "position"
    
    # Quartz enhancement
    quartz_enhanced: bool
    psi_contribution: float  # 0-1 (how much of signal came from PSI vs data)
    coherence_level: float  # Heart coherence during signal reception
    
    # TI Framework mapping
    ti_layer: str  # "VESSEL", "ME", "SOUL"
    gile_dimension: str  # Which GILE dimension most activated


class QuartzStockAnalyzer:
    """
    Integrates quartz PSI amplification with stock market analysis.
    
    The core insight: Markets are influenced by collective consciousness,
    and quartz may help attune to this collective field.
    
    INTEGRATION WITH REAL STOCK DATA:
    - Connects to AdvancedStockAnalysis for live market data
    - Uses yfinance for real-time price fetching
    - Combines quartz-enhanced intuition with technical analysis
    """
    
    def __init__(self):
        self.sessions: List[QuartzTradingSession] = []
        self.signals: List[QuartzMarketSignal] = []
        self.validation_results: Dict[str, Dict] = {}
        self.stock_analyzer = AdvancedStockAnalysis() if HAS_STOCK_ANALYSIS else None
    
    def fetch_live_data(self, ticker: str, days: int = 30) -> Optional[Dict]:
        """
        Fetch real stock data for quartz-enhanced analysis.
        Connects to the platform's existing stock analysis system.
        Falls back to yfinance if AdvancedStockAnalysis is unavailable.
        
        Returns a normalized dict with consistent keys regardless of source.
        """
        # Try AdvancedStockAnalysis first
        if self.stock_analyzer:
            try:
                result = self.stock_analyzer.analyze_stock(ticker)
                if result and result.get('status') == 'success':
                    return {
                        'status': 'success',
                        'ticker': ticker,
                        'current_price': float(result.get('current_price', 0)),
                        'daily_return': float(result.get('daily_return', 0)),
                        'volume': int(result.get('volume', 0)),
                        'avg_return_20d': float(result.get('avg_score', 0)),
                        'volatility': abs(float(result.get('market_score', 0))) * 0.5,
                        'market_score': float(result.get('market_score', 0)),
                        'in_optimal_interval': result.get('in_optimal_interval', False),
                        'source': 'AdvancedStockAnalysis'
                    }
            except Exception as e:
                pass
        
        # Fallback to direct yfinance
        if HAS_YFINANCE and HAS_NUMPY:
            try:
                stock = yf.Ticker(ticker)
                from datetime import timedelta
                end_date = datetime.now()
                start_date = end_date - timedelta(days=days)
                df = stock.history(start=start_date, end=end_date)
                
                if df.empty:
                    return {'status': 'error', 'message': f'No data available for {ticker}'}
                
                df['Daily_Return'] = df['Close'].pct_change() * 100
                latest = df.iloc[-1]
                
                daily_ret = float(latest['Daily_Return']) if not np.isnan(latest['Daily_Return']) else 0
                
                return {
                    'status': 'success',
                    'ticker': ticker,
                    'current_price': float(latest['Close']),
                    'daily_return': daily_ret,
                    'volume': int(latest['Volume']),
                    'avg_return_20d': float(df['Daily_Return'].tail(20).mean()) if len(df) >= 20 else 0,
                    'volatility': float(df['Daily_Return'].std()) if len(df) >= 5 else 0,
                    'market_score': daily_ret * 0.5,  # Simple approximation
                    'in_optimal_interval': -0.666 <= daily_ret <= 0.333,
                    'source': 'yfinance_direct'
                }
            except Exception as e:
                return {'status': 'error', 'message': str(e)}
        
        return {'status': 'error', 'message': 'No stock data source available'}
    
    def create_quartz_enhanced_analysis(
        self,
        ticker: str,
        quartz_type: str = "clear_quartz",
        heart_coherence: float = 0.5,
        quartz_duration: int = 120
    ) -> Dict:
        """
        Perform complete quartz-enhanced stock analysis.
        
        This is the main integration point that:
        1. Fetches real market data
        2. Applies quartz PSI amplification
        3. Generates enhanced trading signals
        4. Tracks for validation
        """
        market_data = self.fetch_live_data(ticker)
        
        if not market_data or market_data.get('status') == 'error':
            return {
                'status': 'error',
                'message': market_data.get('message', 'Unable to fetch market data')
            }
        
        session = self.create_trading_session(
            ticker=ticker,
            quartz_type=quartz_type,
            protocol=self.get_protocol_for_situation('uncertain_direction'),
            baseline_confidence=0.5,
            baseline_direction=TradingDecisionType.HOLD
        )
        
        self.record_quartz_enhancement(
            session=session,
            duration_seconds=quartz_duration,
            heart_coherence=heart_coherence,
            subjective_clarity=5.0 + heart_coherence * 3
        )
        
        daily_return = market_data.get('daily_return', 0)
        volatility = market_data.get('volatility', 1)
        
        if daily_return > 0.5 and session.psi_signal_strength > 6:
            signal_type = "bullish"
            decision = TradingDecisionType.BUY
        elif daily_return < -0.5 and session.psi_signal_strength > 6:
            signal_type = "bearish"
            decision = TradingDecisionType.SELL
        elif abs(daily_return) < 0.2:
            signal_type = "neutral"
            decision = TradingDecisionType.HOLD
        else:
            psi_direction = (session.psi_signal_strength - 5) / 5
            if psi_direction > 0.3:
                signal_type = "bullish"
                decision = TradingDecisionType.BUY
            elif psi_direction < -0.3:
                signal_type = "bearish"
                decision = TradingDecisionType.SELL
            else:
                signal_type = "neutral"
                decision = TradingDecisionType.HOLD
        
        signal_strength = min(session.psi_signal_strength / 10, 0.95)
        
        signal = self.generate_market_signal(
            ticker=ticker,
            signal_type=signal_type,
            strength=signal_strength,
            quartz_enhanced=True,
            heart_coherence=heart_coherence
        )
        
        confidence = 0.5 + signal_strength * 0.4
        self.finalize_decision(session, decision, confidence)
        
        return {
            'status': 'success',
            'ticker': ticker,
            'market_data': {
                'price': market_data.get('current_price'),
                'daily_return': daily_return,
                'volatility': volatility,
                'volume': market_data.get('volume')
            },
            'quartz_enhancement': {
                'quartz_type': quartz_type,
                'duration_seconds': quartz_duration,
                'heart_coherence': heart_coherence,
                'psi_signal_strength': session.psi_signal_strength
            },
            'signal': {
                'type': signal_type,
                'strength': signal_strength,
                'ti_layer': signal.ti_layer,
                'gile_dimension': signal.gile_dimension,
                'psi_contribution': signal.psi_contribution
            },
            'decision': {
                'action': decision.value,
                'confidence': confidence,
                'session_id': session.session_id
            },
            'recommendation': self.get_quartz_recommendation('uncertain_direction')
        }
    
    def generate_session_id(self) -> str:
        """Generate unique session ID"""
        data = f"{datetime.now().isoformat()}{random.random()}"
        return hashlib.sha256(data.encode()).hexdigest()[:12]
    
    def create_trading_session(
        self,
        ticker: str,
        quartz_type: str = "clear_quartz",
        protocol: QuartzTradingProtocol = QuartzTradingProtocol.INTUITION_SCAN,
        baseline_confidence: float = 0.5,
        baseline_direction: TradingDecisionType = TradingDecisionType.HOLD
    ) -> QuartzTradingSession:
        """Create a new quartz-enhanced trading session"""
        
        session = QuartzTradingSession(
            session_id=self.generate_session_id(),
            timestamp=datetime.now().isoformat(),
            ticker=ticker.upper(),
            quartz_type=quartz_type,
            protocol=protocol,
            baseline_confidence=baseline_confidence,
            baseline_direction=baseline_direction,
            quartz_duration_seconds=0
        )
        
        self.sessions.append(session)
        return session
    
    def record_quartz_enhancement(
        self,
        session: QuartzTradingSession,
        duration_seconds: int,
        heart_coherence: Optional[float] = None,
        temperature_change: Optional[float] = None,
        subjective_clarity: float = 5.0
    ) -> QuartzTradingSession:
        """Record the quartz holding phase of the session"""
        
        session.quartz_duration_seconds = duration_seconds
        session.heart_coherence_during = heart_coherence
        session.hand_temperature_change = temperature_change
        session.subjective_clarity = subjective_clarity
        
        # Calculate PSI signal strength
        session.psi_signal_strength = self._calculate_psi_strength(
            duration_seconds, heart_coherence, subjective_clarity
        )
        
        return session
    
    def _calculate_psi_strength(
        self,
        duration: int,
        coherence: Optional[float],
        clarity: float
    ) -> float:
        """
        Calculate PSI signal strength from session parameters.
        
        Factors:
        - Duration: Longer = stronger (diminishing returns after 5 min)
        - Heart coherence: Higher = stronger PSI reception
        - Subjective clarity: Personal sense of intuitive signal
        """
        # Duration factor (0-3, peaks at 5 minutes)
        duration_factor = min(duration / 100, 3.0)
        
        # Coherence factor (0-4, if available)
        coherence_factor = (coherence or 0.5) * 4.0
        
        # Clarity factor (0-3)
        clarity_factor = clarity / 3.33
        
        # Combined strength (0-10)
        psi_strength = (duration_factor + coherence_factor + clarity_factor)
        
        return min(psi_strength, 10.0)
    
    def finalize_decision(
        self,
        session: QuartzTradingSession,
        final_decision: TradingDecisionType,
        final_confidence: float
    ) -> QuartzTradingSession:
        """Record the final trading decision after quartz enhancement"""
        
        session.final_decision = final_decision
        session.final_confidence = final_confidence
        
        return session
    
    def record_outcome(
        self,
        session_id: str,
        outcome: str,  # "profit", "loss", "neutral"
        magnitude_pct: float
    ) -> Optional[QuartzTradingSession]:
        """Record the actual outcome of a trading decision"""
        
        for session in self.sessions:
            if session.session_id == session_id:
                session.actual_outcome = outcome
                session.outcome_magnitude_pct = magnitude_pct
                session.verified = True
                return session
        
        return None
    
    def generate_market_signal(
        self,
        ticker: str,
        signal_type: str,
        strength: float,
        quartz_enhanced: bool = False,
        heart_coherence: float = 0.5,
        timeframe: str = "swing"
    ) -> QuartzMarketSignal:
        """Generate a market signal with optional quartz enhancement"""
        
        # Determine TI layer based on signal characteristics
        if strength > 0.8:
            ti_layer = "SOUL"  # Strong signals from deeper consciousness
        elif strength > 0.5:
            ti_layer = "ME"  # Moderate signals from pattern recognition
        else:
            ti_layer = "VESSEL"  # Weak signals from surface analysis
        
        # Map to GILE dimension
        gile_map = {
            "bullish": "G",  # Goodness (positive growth)
            "bearish": "L",  # Love (protective caution)
            "neutral": "E",  # Environment (waiting for conditions)
            "reversal": "I"  # Intuition (sensing change)
        }
        
        # Calculate PSI contribution
        if quartz_enhanced:
            psi_contribution = min(0.3 + (heart_coherence * 0.5), 0.8)
        else:
            psi_contribution = 0.1
        
        signal = QuartzMarketSignal(
            signal_id=self.generate_session_id(),
            timestamp=datetime.now().isoformat(),
            ticker=ticker.upper(),
            signal_type=signal_type,
            strength=strength,
            confidence=strength * (1 + psi_contribution * 0.5),
            timeframe=timeframe,
            quartz_enhanced=quartz_enhanced,
            psi_contribution=psi_contribution,
            coherence_level=heart_coherence,
            ti_layer=ti_layer,
            gile_dimension=gile_map.get(signal_type, "E")
        )
        
        self.signals.append(signal)
        return signal
    
    def get_protocol_for_situation(self, situation: str) -> QuartzTradingProtocol:
        """Recommend best quartz protocol for trading situation"""
        
        situation_map = {
            "uncertain_direction": QuartzTradingProtocol.INTUITION_SCAN,
            "complex_analysis": QuartzTradingProtocol.DEEP_ANALYSIS,
            "entry_timing": QuartzTradingProtocol.TIMING_PRECISION,
            "exit_timing": QuartzTradingProtocol.TIMING_PRECISION,
            "high_volatility": QuartzTradingProtocol.RISK_ASSESSMENT,
            "trend_confirmation": QuartzTradingProtocol.TREND_SENSING,
            "reversal_detection": QuartzTradingProtocol.INTUITION_SCAN,
            "position_sizing": QuartzTradingProtocol.RISK_ASSESSMENT
        }
        
        return situation_map.get(situation, QuartzTradingProtocol.INTUITION_SCAN)
    
    def get_quartz_recommendation(self, situation: str) -> Dict:
        """Get complete quartz recommendation for trading situation"""
        
        protocol = self.get_protocol_for_situation(situation)
        
        protocol_details = {
            QuartzTradingProtocol.INTUITION_SCAN: {
                "quartz_type": "clear_quartz",
                "duration_seconds": 60,
                "preparation": [
                    "Hold quartz in dominant hand",
                    "Take 3 deep breaths",
                    "Focus on the ticker symbol",
                    "Notice first impression without analysis"
                ],
                "interpretation": "Trust the immediate feeling - don't overthink"
            },
            QuartzTradingProtocol.DEEP_ANALYSIS: {
                "quartz_type": "amethyst",
                "duration_seconds": 300,
                "preparation": [
                    "Place quartz on desk in front of screen",
                    "Enter heart coherence state (6 breaths/min)",
                    "Review all available data",
                    "Let insights emerge naturally"
                ],
                "interpretation": "Combine analytical and intuitive signals"
            },
            QuartzTradingProtocol.TIMING_PRECISION: {
                "quartz_type": "double_terminated",
                "duration_seconds": 120,
                "preparation": [
                    "Hold double-terminated quartz point up",
                    "Visualize the price chart",
                    "Ask: 'When is the optimal moment?'",
                    "Notice body sensations (tingling, warmth)"
                ],
                "interpretation": "Physical sensations indicate timing"
            },
            QuartzTradingProtocol.RISK_ASSESSMENT: {
                "quartz_type": "smoky_quartz",
                "duration_seconds": 180,
                "preparation": [
                    "Ground with smoky quartz at base of spine",
                    "Visualize worst-case scenario",
                    "Notice emotional response",
                    "Ask: 'Is this risk acceptable?'"
                ],
                "interpretation": "Strong negative feelings = reduce position"
            },
            QuartzTradingProtocol.TREND_SENSING: {
                "quartz_type": "citrine",
                "duration_seconds": 240,
                "preparation": [
                    "Hold citrine while viewing weekly chart",
                    "Feel the 'flow' of the trend",
                    "Ask: 'Where is this going?'",
                    "Notice any resistance or ease"
                ],
                "interpretation": "Ease = trend continues, resistance = change coming"
            }
        }
        
        details = protocol_details.get(protocol, protocol_details[QuartzTradingProtocol.INTUITION_SCAN])
        
        return {
            "protocol": protocol.value,
            "situation": situation,
            **details
        }
    
    def calculate_accuracy_stats(self) -> Dict:
        """Calculate accuracy statistics for quartz-enhanced trading"""
        
        verified = [s for s in self.sessions if s.verified]
        
        if not verified:
            return {"message": "No verified sessions yet"}
        
        # Overall accuracy
        correct = sum(1 for s in verified if 
            (s.final_decision in [TradingDecisionType.BUY, TradingDecisionType.SCALE_IN] 
             and s.actual_outcome == "profit") or
            (s.final_decision in [TradingDecisionType.SELL, TradingDecisionType.SCALE_OUT] 
             and s.actual_outcome == "loss") or
            (s.final_decision == TradingDecisionType.HOLD 
             and s.actual_outcome == "neutral")
        )
        
        accuracy = correct / len(verified) if verified else 0
        
        # Group by PSI strength
        high_psi = [s for s in verified if s.psi_signal_strength >= 7.0]
        low_psi = [s for s in verified if s.psi_signal_strength < 5.0]
        
        def calc_group_accuracy(group):
            if not group:
                return 0
            correct = sum(1 for s in group if 
                (s.final_decision in [TradingDecisionType.BUY, TradingDecisionType.SCALE_IN] 
                 and s.actual_outcome == "profit") or
                (s.final_decision in [TradingDecisionType.SELL, TradingDecisionType.SCALE_OUT] 
                 and s.actual_outcome == "loss")
            )
            return correct / len(group)
        
        return {
            "total_sessions": len(verified),
            "overall_accuracy": accuracy,
            "high_psi_accuracy": calc_group_accuracy(high_psi),
            "low_psi_accuracy": calc_group_accuracy(low_psi),
            "high_psi_count": len(high_psi),
            "low_psi_count": len(low_psi),
            "psi_enhancement_factor": (
                calc_group_accuracy(high_psi) / calc_group_accuracy(low_psi)
                if calc_group_accuracy(low_psi) > 0 else 1.0
            )
        }
    
    def get_protocol_guide(self) -> Dict[str, List[str]]:
        """Get complete protocol guide for quartz-enhanced trading"""
        
        return {
            "before_trading": [
                "1. Cleanse quartz under running water for 30 seconds",
                "2. Sit comfortably with good lighting on your screen",
                "3. Take 3 deep breaths to enter coherent state",
                "4. Set clear intention: 'I seek accurate market insight'"
            ],
            "during_analysis": [
                "1. Hold quartz in non-dominant hand while viewing charts",
                "2. Maintain soft focus - don't strain to 'see' answers",
                "3. Notice any body sensations (warmth, tingling, tension)",
                "4. Pay attention to spontaneous thoughts or images",
                "5. Record impressions before analytical thinking kicks in"
            ],
            "making_decisions": [
                "1. State your decision options aloud or mentally",
                "2. Hold each option in mind and notice body response",
                "3. Expansion/warmth = positive, Contraction/cold = caution",
                "4. Trust strong signals, verify weak ones with data",
                "5. Record your confidence level (1-10)"
            ],
            "after_trading": [
                "1. Record outcome when position closes",
                "2. Note correlation between PSI strength and accuracy",
                "3. Identify which quartz types work best for you",
                "4. Track heart coherence correlation with success"
            ],
            "best_practices": [
                "Use clear quartz for general scanning",
                "Use amethyst for complex decisions",
                "Use smoky quartz when risk seems high",
                "Use citrine for trend confirmation",
                "Always combine PSI with technical analysis",
                "Higher heart coherence = more reliable PSI signals"
            ]
        }


QUARTZ_TRADING_PROTOCOLS = {
    'intuition_scan': {
        'name': "Quick Intuition Scan",
        'duration': 60,
        'quartz': 'clear_quartz',
        'purpose': "Rapid market direction sensing",
        'steps': [
            "Hold clear quartz point facing screen",
            "Take 3 slow breaths",
            "Glance at price action",
            "Notice first gut feeling",
            "Record impression immediately"
        ]
    },
    'deep_analysis': {
        'name': "Deep Analytical Session",
        'duration': 300,
        'quartz': 'amethyst',
        'purpose': "Complex multi-factor analysis",
        'steps': [
            "Place amethyst at third eye level near screen",
            "Review fundamental data",
            "Switch to technical charts",
            "Let patterns emerge naturally",
            "Synthesize insights over 5 minutes"
        ]
    },
    'timing_precision': {
        'name': "Entry/Exit Timing",
        'duration': 120,
        'quartz': 'double_terminated',
        'purpose': "Precise timing for entries and exits",
        'steps': [
            "Hold DT quartz horizontally at heart level",
            "Visualize price at different time points",
            "Notice which timing creates warmth",
            "Test multiple scenarios",
            "Record strongest signal timing"
        ]
    },
    'risk_assessment': {
        'name': "Risk and Danger Detection",
        'duration': 180,
        'quartz': 'smoky_quartz',
        'purpose': "Identify hidden risks and dangers",
        'steps': [
            "Place smoky quartz at base of spine",
            "Visualize the trade going wrong",
            "Notice any fear or protective feelings",
            "Scale position size inversely to fear",
            "Trust protective instincts"
        ]
    },
    'trend_sensing': {
        'name': "Long-Term Trend Intuition",
        'duration': 240,
        'quartz': 'citrine',
        'purpose': "Sense long-term trend direction",
        'steps': [
            "Hold citrine at solar plexus",
            "View weekly or monthly charts",
            "Ask 'Where is this going over months?'",
            "Notice feelings of expansion or contraction",
            "Record directional impressions"
        ]
    }
}

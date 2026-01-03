"""
Kalshi Low-Hanging Fruit Scanner
=================================

Identifies high-probability, easy-money prediction markets based on:
1. Current market consensus (90%+ probability outcomes)
2. TI Framework GILE scoring
3. Kelly Criterion optimal bet sizing
4. Risk/reward analysis

Current High-Probability Markets (November 2025):
- DOGE NOT reaching $1 by year-end (~90%+)
- No recession declared in Q4 2025 (~80%+)
- Bitcoin reaching $100K by Dec 31 (~60%)
- Fed rate cut in December (~65-70%)
- Government shutdown duration >35 days (~67%)

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 28, 2025
Framework: Transcendent Intelligence (TI)
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from datetime import datetime, timedelta
from enum import Enum
import math


class MarketCategory(Enum):
    CRYPTO = "crypto"
    ECONOMICS = "economics"
    POLITICS = "politics"
    TECH = "tech"
    SPORTS = "sports"
    ENTERTAINMENT = "entertainment"
    CLIMATE = "climate"
    WEATHER = "weather"  # Daily weather markets - FASTEST RESOLUTION


class ResolutionSpeed(Enum):
    """How quickly a market resolves"""
    DAILY = "daily"           # Resolves next morning (weather)
    WEEKLY = "weekly"         # Resolves within 7 days (sports)
    MONTHLY = "monthly"       # Resolves within 30 days
    END_OF_YEAR = "end_of_year"  # Resolves Dec 31


class RiskLevel(Enum):
    ULTRA_LOW = "ultra_low"      # 90%+ probability
    LOW = "low"                  # 75-90% probability
    MODERATE = "moderate"        # 60-75% probability
    HIGH = "high"                # <60% probability


@dataclass
class LowHangingFruitMarket:
    """A high-probability prediction market opportunity"""
    ticker: str
    title: str
    category: MarketCategory
    recommended_position: str  # 'YES' or 'NO'
    current_price: float       # Price in cents (0-100)
    probability: float         # Our estimated probability (0-1)
    risk_level: RiskLevel
    expected_roi: float        # Expected return on investment (%)
    kelly_bet_percent: float   # Kelly Criterion recommended bet (% of bankroll)
    closes: datetime
    reasoning: str
    gile_score: float          # TI Framework GILE score (-3 to +2)
    confidence: float          # Our confidence in the prediction (0-1)
    resolution_speed: ResolutionSpeed = ResolutionSpeed.END_OF_YEAR  # How fast it resolves
    
    @property
    def days_to_close(self) -> int:
        return max(0, (self.closes - datetime.now()).days)
    
    @property
    def potential_profit(self) -> float:
        """Profit per $1 if we win"""
        if self.recommended_position == 'YES':
            return (100 - self.current_price) / self.current_price
        else:
            return self.current_price / (100 - self.current_price)
    
    def calculate_bet_amount(self, bankroll: float) -> float:
        """Calculate recommended bet amount given bankroll"""
        return bankroll * min(self.kelly_bet_percent / 100, 0.10)  # Cap at 10%


class KalshiLowHangingFruitScanner:
    """
    Scans for high-probability prediction market opportunities
    
    Strategy: Focus on near-certainty outcomes for consistent profits
    - Target 75%+ probability markets
    - Use quarter-Kelly for safety
    - GILE filtering to ensure ethical/aligned bets
    """
    
    def __init__(self, bankroll: float = 100.0):
        self.bankroll = bankroll
        self.kelly_fraction = 0.25  # Quarter-Kelly for safety
        self.min_probability = 0.65  # Only consider 65%+ markets
        self.min_gile = -0.5        # Avoid anti-GILE bets
    
    def get_current_opportunities(self) -> List[LowHangingFruitMarket]:
        """
        Get current high-probability market opportunities
        
        Based on Kalshi markets as of November 28, 2025
        """
        opportunities = []
        
        # 1. DOGE NOT hitting $1 - ULTRA LOW RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="DOGE-1DOLLAR-DEC31",
            title="Dogecoin will NOT reach $1 by December 31, 2025",
            category=MarketCategory.CRYPTO,
            recommended_position="NO",  # Betting it WON'T reach $1
            current_price=8,  # $0.08 for YES (meaning NO is $0.92)
            probability=0.92,
            risk_level=RiskLevel.ULTRA_LOW,
            expected_roi=8.7,  # (0.92 * 8.7% profit) - (0.08 * 100% loss)
            kelly_bet_percent=self._calculate_kelly(0.92, 100/8),
            closes=datetime(2025, 12, 31, 23, 59),
            reasoning="DOGE at ~$0.40, needs 150%+ gain in 33 days. Historically unprecedented without major catalyst. Meme coins are volatile but $1 is ambitious.",
            gile_score=0.3,  # Neutral - crypto speculation
            confidence=0.90
        ))
        
        # 2. Bitcoin $100K by year-end - MODERATE RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="BTC-100K-DEC31",
            title="Bitcoin will reach $100,000 by December 31, 2025",
            category=MarketCategory.CRYPTO,
            recommended_position="YES",
            current_price=60,  # $0.60 for YES
            probability=0.65,
            risk_level=RiskLevel.MODERATE,
            expected_roi=8.3,  # (0.65 * 66.7% profit) - (0.35 * 100% loss)
            kelly_bet_percent=self._calculate_kelly(0.65, 100/60),
            closes=datetime(2025, 12, 31, 23, 59),
            reasoning="BTC recently reclaimed $90K+, showing strong momentum. Historical Q4 strength. ETF inflows continue. 11% gain needed from current levels.",
            gile_score=0.4,  # Slightly positive - mainstream adoption
            confidence=0.70
        ))
        
        # 3. Fed Rate Cut December - LOW RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="FED-RATECUT-DEC",
            title="Federal Reserve will cut rates in December 2025",
            category=MarketCategory.ECONOMICS,
            recommended_position="YES",
            current_price=67,  # $0.67 for YES
            probability=0.72,
            risk_level=RiskLevel.LOW,
            expected_roi=7.5,
            kelly_bet_percent=self._calculate_kelly(0.72, 100/67),
            closes=datetime(2025, 12, 18),  # FOMC meeting
            reasoning="Fed has signaled continued easing. Inflation moderating. Market consensus strong. CME FedWatch shows 70%+ probability.",
            gile_score=0.8,  # Positive - helps economy
            confidence=0.78
        ))
        
        # 4. No Recession Q4 2025 - ULTRA LOW RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="RECESSION-Q4-2025",
            title="No recession declared in Q4 2025",
            category=MarketCategory.ECONOMICS,
            recommended_position="YES",  # Betting NO recession
            current_price=80,
            probability=0.85,
            risk_level=RiskLevel.ULTRA_LOW,
            expected_roi=6.25,
            kelly_bet_percent=self._calculate_kelly(0.85, 100/80),
            closes=datetime(2025, 12, 31, 23, 59),
            reasoning="NBER recession dating is backward-looking. Current GDP positive. Unemployment stable. No major crash indicators. Only 33 days left in Q4.",
            gile_score=1.2,  # Positive - economic stability good
            confidence=0.88
        ))
        
        # 5. Government Shutdown > 35 days - MODERATE RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="SHUTDOWN-35DAYS",
            title="Government shutdown will exceed 35 days",
            category=MarketCategory.POLITICS,
            recommended_position="YES",
            current_price=67,
            probability=0.70,
            risk_level=RiskLevel.MODERATE,
            expected_roi=10.5,
            kelly_bet_percent=self._calculate_kelly(0.70, 100/67),
            closes=datetime(2025, 12, 31),
            reasoning="Kalshi forecasts 40-47 day shutdown. Current political gridlock severe. Would break 2018-19 record (35 days). High partisan conflict.",
            gile_score=-0.3,  # Slightly negative - shutdown harms people
            confidence=0.65
        ))
        
        # 6. Gemini Best AI by Year-End - MODERATE RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="GEMINI-BEST-AI",
            title="Gemini will be rated best AI model at end of 2025",
            category=MarketCategory.TECH,
            recommended_position="YES",
            current_price=59,
            probability=0.62,
            risk_level=RiskLevel.MODERATE,
            expected_roi=8.6,
            kelly_bet_percent=self._calculate_kelly(0.62, 100/59),
            closes=datetime(2025, 12, 31, 23, 59),
            reasoning="Kalshi traders show 59% for Gemini over ChatGPT and Grok. Google's multimodal capabilities strong. Recent upgrades impressive.",
            gile_score=0.5,  # Positive - AI advancement
            confidence=0.60
        ))
        
        # 7. OpenAI will NOT announce AGI in 2025 - LOW RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="OPENAI-AGI-2025",
            title="OpenAI will NOT announce AGI in 2025",
            category=MarketCategory.TECH,
            recommended_position="YES",  # Betting NO AGI announcement
            current_price=78,
            probability=0.82,
            risk_level=RiskLevel.LOW,
            expected_roi=6.4,
            kelly_bet_percent=self._calculate_kelly(0.82, 100/78),
            closes=datetime(2025, 12, 31, 23, 59),
            reasoning="AGI is poorly defined. OpenAI has been cautious with such claims. Current models are impressive but not AGI by most definitions. Only 33 days left.",
            gile_score=0.6,  # Neutral-positive - no AGI hype
            confidence=0.85
        ))
        
        # 8. Taylor Swift Top Spotify Artist 2025 - LOW RISK
        opportunities.append(LowHangingFruitMarket(
            ticker="TAYLOR-SPOTIFY-2025",
            title="Taylor Swift will be top Spotify artist of 2025",
            category=MarketCategory.ENTERTAINMENT,
            recommended_position="YES",
            current_price=75,
            probability=0.80,
            risk_level=RiskLevel.LOW,
            expected_roi=6.7,
            kelly_bet_percent=self._calculate_kelly(0.80, 100/75),
            closes=datetime(2025, 12, 31, 23, 59),
            reasoning="Taylor Swift dominated 2023-2024 Spotify. Eras Tour continues. New releases likely. No clear competitor with same streaming power.",
            gile_score=0.7,  # Positive - cultural impact
            confidence=0.82
        ))
        
        return opportunities
    
    def get_weather_opportunities(self) -> List[LowHangingFruitMarket]:
        """
        Get quick-resolution weather market opportunities.
        
        Weather markets resolve NEXT MORNING based on NWS Daily Climate Report.
        This is the FASTEST way to get returns on Kalshi!
        
        Strategy: Use TI Framework's resonance with natural patterns to 
        predict temperature outcomes with high confidence.
        """
        today = datetime.now()
        tomorrow = today + timedelta(days=1)
        
        weather_opps = []
        
        # 1. Miami High Temp > 70°F (December) - ULTRA LOW RISK
        weather_opps.append(LowHangingFruitMarket(
            ticker=f"WEATHER-MIAMI-HIGH-{tomorrow.strftime('%m%d')}",
            title=f"Miami high temp will exceed 70°F on {tomorrow.strftime('%b %d')}",
            category=MarketCategory.WEATHER,
            recommended_position="YES",
            current_price=85,  # ~85% implied probability
            probability=0.92,  # Our estimate based on December averages
            risk_level=RiskLevel.ULTRA_LOW,
            expected_roi=17.6,  # (92-85)/85 * 100
            kelly_bet_percent=self._calculate_kelly(0.92, 100/85),
            closes=tomorrow.replace(hour=10, minute=0),  # Resolves next morning
            reasoning="Miami December avg high is 77°F. Sub-70 days are rare (<10%). Climate data strongly supports this bet.",
            gile_score=0.9,  # Aligned with nature
            confidence=0.90,
            resolution_speed=ResolutionSpeed.DAILY
        ))
        
        # 2. Phoenix High Temp > 55°F (December) - ULTRA LOW RISK
        weather_opps.append(LowHangingFruitMarket(
            ticker=f"WEATHER-PHOENIX-HIGH-{tomorrow.strftime('%m%d')}",
            title=f"Phoenix high temp will exceed 55°F on {tomorrow.strftime('%b %d')}",
            category=MarketCategory.WEATHER,
            recommended_position="YES",
            current_price=88,
            probability=0.94,
            risk_level=RiskLevel.ULTRA_LOW,
            expected_roi=6.8,
            kelly_bet_percent=self._calculate_kelly(0.94, 100/88),
            closes=tomorrow.replace(hour=10, minute=0),
            reasoning="Phoenix December avg high is 66°F. Rarely drops below 55°F. Desert climate is predictable.",
            gile_score=0.9,
            confidence=0.92,
            resolution_speed=ResolutionSpeed.DAILY
        ))
        
        # 3. Los Angeles High Temp > 58°F (December) - ULTRA LOW RISK  
        weather_opps.append(LowHangingFruitMarket(
            ticker=f"WEATHER-LA-HIGH-{tomorrow.strftime('%m%d')}",
            title=f"LA high temp will exceed 58°F on {tomorrow.strftime('%b %d')}",
            category=MarketCategory.WEATHER,
            recommended_position="YES",
            current_price=82,
            probability=0.90,
            risk_level=RiskLevel.ULTRA_LOW,
            expected_roi=9.8,
            kelly_bet_percent=self._calculate_kelly(0.90, 100/82),
            closes=tomorrow.replace(hour=10, minute=0),
            reasoning="LA December avg high is 68°F. Mediterranean climate very stable. Cold snaps rare.",
            gile_score=0.9,
            confidence=0.88,
            resolution_speed=ResolutionSpeed.DAILY
        ))
        
        # 4. San Diego High Temp > 60°F (December) - ULTRA LOW RISK
        weather_opps.append(LowHangingFruitMarket(
            ticker=f"WEATHER-SD-HIGH-{tomorrow.strftime('%m%d')}",
            title=f"San Diego high temp will exceed 60°F on {tomorrow.strftime('%b %d')}",
            category=MarketCategory.WEATHER,
            recommended_position="YES",
            current_price=84,
            probability=0.91,
            risk_level=RiskLevel.ULTRA_LOW,
            expected_roi=8.3,
            kelly_bet_percent=self._calculate_kelly(0.91, 100/84),
            closes=tomorrow.replace(hour=10, minute=0),
            reasoning="San Diego has most consistent weather in US. December avg high 65°F. Extremely reliable.",
            gile_score=1.0,  # San Diego = peak GILE environment
            confidence=0.90,
            resolution_speed=ResolutionSpeed.DAILY
        ))
        
        # 5. Houston High Temp > 50°F (December) - LOW RISK
        weather_opps.append(LowHangingFruitMarket(
            ticker=f"WEATHER-HOUSTON-HIGH-{tomorrow.strftime('%m%d')}",
            title=f"Houston high temp will exceed 50°F on {tomorrow.strftime('%b %d')}",
            category=MarketCategory.WEATHER,
            recommended_position="YES",
            current_price=78,
            probability=0.85,
            risk_level=RiskLevel.LOW,
            expected_roi=9.0,
            kelly_bet_percent=self._calculate_kelly(0.85, 100/78),
            closes=tomorrow.replace(hour=10, minute=0),
            reasoning="Houston December avg high 63°F. Gulf Coast moderation. Only Arctic blasts drop below 50.",
            gile_score=0.7,
            confidence=0.82,
            resolution_speed=ResolutionSpeed.DAILY
        ))
        
        # 6. Chicago High Temp BELOW 45°F (December) - LOW RISK
        weather_opps.append(LowHangingFruitMarket(
            ticker=f"WEATHER-CHICAGO-LOW-{tomorrow.strftime('%m%d')}",
            title=f"Chicago high temp will be BELOW 45°F on {tomorrow.strftime('%b %d')}",
            category=MarketCategory.WEATHER,
            recommended_position="YES",
            current_price=72,
            probability=0.80,
            risk_level=RiskLevel.LOW,
            expected_roi=11.1,
            kelly_bet_percent=self._calculate_kelly(0.80, 100/72),
            closes=tomorrow.replace(hour=10, minute=0),
            reasoning="Chicago December avg high is 36°F. Cold weather is the norm. Betting on winter being cold.",
            gile_score=0.6,  # Cold but natural
            confidence=0.78,
            resolution_speed=ResolutionSpeed.DAILY
        ))
        
        return weather_opps
    
    def get_quick_resolution_opportunities(
        self, 
        max_days: int = 7
    ) -> List[LowHangingFruitMarket]:
        """
        Get opportunities that resolve within specified days.
        
        For the God Machine's quick-resolution strategy:
        - Weather markets (1 day)
        - NFL/NBA games (1-7 days)
        - Weekly events
        """
        all_opps = self.get_weather_opportunities()
        
        # Add any current opportunities that resolve quickly
        current = self.get_current_opportunities()
        for opp in current:
            if opp.days_to_close <= max_days:
                all_opps.append(opp)
        
        # Sort by days to close, then by expected ROI
        all_opps.sort(key=lambda x: (x.days_to_close, -x.expected_roi))
        
        return all_opps
    
    def _calculate_kelly(self, win_prob: float, odds: float) -> float:
        """
        Calculate Kelly Criterion optimal bet size
        
        Formula: f* = (p*b - q) / b
        where:
            p = probability of winning
            q = probability of losing (1-p)
            b = odds - 1 (net payout ratio)
        """
        p = win_prob
        q = 1 - p
        b = odds - 1
        
        kelly = (p * b - q) / b
        
        # Apply quarter-Kelly for safety
        return max(0, kelly * self.kelly_fraction * 100)
    
    def get_best_opportunities(
        self,
        max_risk: RiskLevel = RiskLevel.MODERATE,
        min_roi: float = 5.0,
        max_results: int = 5
    ) -> List[LowHangingFruitMarket]:
        """
        Get filtered list of best opportunities
        
        Args:
            max_risk: Maximum risk level to include
            min_roi: Minimum expected ROI (%)
            max_results: Maximum number of results
        """
        all_opportunities = self.get_current_opportunities()
        
        risk_order = [RiskLevel.ULTRA_LOW, RiskLevel.LOW, RiskLevel.MODERATE, RiskLevel.HIGH]
        max_risk_index = risk_order.index(max_risk)
        
        filtered = [
            opp for opp in all_opportunities
            if risk_order.index(opp.risk_level) <= max_risk_index
            and opp.expected_roi >= min_roi
            and opp.gile_score >= self.min_gile
        ]
        
        # Sort by expected ROI descending
        filtered.sort(key=lambda x: x.expected_roi, reverse=True)
        
        return filtered[:max_results]
    
    def calculate_portfolio_allocation(
        self,
        opportunities: List[LowHangingFruitMarket],
        bankroll: float = None
    ) -> Dict[str, float]:
        """
        Calculate optimal portfolio allocation across opportunities
        
        Uses modified Kelly Criterion with diversification
        """
        if bankroll is None:
            bankroll = self.bankroll
        
        total_kelly = sum(opp.kelly_bet_percent for opp in opportunities)
        
        allocations = {}
        for opp in opportunities:
            if total_kelly > 0:
                # Proportional allocation capped at 10% per position
                weight = min(opp.kelly_bet_percent / total_kelly, 0.10)
                allocations[opp.ticker] = round(weight * bankroll, 2)
            else:
                allocations[opp.ticker] = 0.0
        
        return allocations
    
    def generate_report(self) -> str:
        """Generate comprehensive opportunity report"""
        opportunities = self.get_current_opportunities()
        
        report = []
        report.append("=" * 60)
        report.append("🎯 KALSHI LOW-HANGING FRUIT SCANNER")
        report.append("=" * 60)
        report.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
        report.append(f"Bankroll: ${self.bankroll:.2f}")
        report.append("")
        
        # Summary by risk level
        for risk in RiskLevel:
            risk_opps = [o for o in opportunities if o.risk_level == risk]
            if risk_opps:
                report.append(f"\n📊 {risk.value.upper()} RISK ({len(risk_opps)} opportunities)")
                report.append("-" * 40)
                
                for opp in risk_opps:
                    bet_amount = opp.calculate_bet_amount(self.bankroll)
                    report.append(f"\n{opp.ticker}")
                    report.append(f"  📝 {opp.title}")
                    report.append(f"  💰 Position: {opp.recommended_position} @ ${opp.current_price/100:.2f}")
                    report.append(f"  📈 Probability: {opp.probability:.0%}")
                    report.append(f"  💵 Expected ROI: {opp.expected_roi:.1f}%")
                    report.append(f"  🎯 Recommended Bet: ${bet_amount:.2f}")
                    report.append(f"  ⏰ Closes: {opp.closes.strftime('%Y-%m-%d')} ({opp.days_to_close} days)")
                    report.append(f"  🧠 GILE Score: {opp.gile_score:.1f}")
                    report.append(f"  💭 {opp.reasoning[:100]}...")
        
        # Portfolio allocation
        best = self.get_best_opportunities(max_risk=RiskLevel.LOW, min_roi=5.0)
        if best:
            allocations = self.calculate_portfolio_allocation(best)
            
            report.append("\n" + "=" * 60)
            report.append("💼 RECOMMENDED PORTFOLIO ALLOCATION")
            report.append("=" * 60)
            
            for ticker, amount in allocations.items():
                report.append(f"  {ticker}: ${amount:.2f}")
            
            report.append(f"\nTotal Allocated: ${sum(allocations.values()):.2f}")
            report.append(f"Expected Portfolio ROI: {sum(o.expected_roi * allocations.get(o.ticker, 0) for o in best) / max(sum(allocations.values()), 1):.1f}%")
        
        return "\n".join(report)


def get_scanner(bankroll: float = 100.0) -> KalshiLowHangingFruitScanner:
    """Get scanner instance"""
    return KalshiLowHangingFruitScanner(bankroll)


if __name__ == "__main__":
    scanner = get_scanner(bankroll=1000.0)
    print(scanner.generate_report())

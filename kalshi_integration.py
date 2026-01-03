"""
Kalshi Prediction Market Integration with TI Framework
======================================================

Integrates Kalshi API with GILE-based market scoring and optimal bet sizing.

Features:
- Real-time market data fetching
- TI-based GILE scoring for each market
- Kelly Criterion + TI risk/reward calculation
- Category filtering (politics, tech, health, renewable energy)
- Conservative 70% confidence threshold

Author: Brandon Emerick
Date: November 22, 2025
Framework: Transcendent Intelligence (TI)
"""

import requests
from typing import List, Dict, Optional, Any
from datetime import datetime, timedelta
import numpy as np
from dataclasses import dataclass, asdict
import json


@dataclass
class KalshiMarket:
    """Represents a single Kalshi prediction market"""
    ticker: str
    title: str
    category: str
    close_time: datetime
    yes_price: float  # 0-100 cents
    no_price: float   # 0-100 cents
    volume_24h: int
    liquidity: int
    
    # TI-specific fields
    gile_score: Optional[float] = None
    ti_confidence: Optional[float] = None  # 0-100%
    recommended_bet: Optional[str] = None  # 'YES', 'NO', or 'SKIP'
    recommended_amount: Optional[float] = None  # USD
    expected_roi: Optional[float] = None  # %


class KalshiTIIntegration:
    """
    Kalshi API integration with TI Framework
    
    **DEMO MODE - NOT PRODUCTION-READY**
    
    This is a proof-of-concept demonstrating TI Framework applied to prediction markets.
    TI win probabilities are derived from GILE heuristics and NOT empirically calibrated.
    
    Production requirements (NOT YET MET):
    - [ ] Empirical calibration: TI_prob grounded in backtested accuracy per category
    - [ ] Confidence clamping: Never exceed 70% unless model shows ≥0.70 hit rate
    - [ ] Signed edge validation: Ensure confidence only increases when recommended direction has positive edge
    - [ ] Drawdown protection: Halve bet size if cumulative loss >15%
    - [ ] 100+ validated predictions before real money deployment
    
    Current Provides:
    1. Market fetching and filtering
    2. GILE-based market scoring (theoretical)
    3. Optimal bet sizing using Kelly Criterion + TI (unvalidated)
    4. Conservative 70% confidence threshold (not empirically enforced)
    """
    
    def __init__(self, api_key: Optional[str] = None, demo_mode: bool = True):
        """
        Initialize Kalshi integration
        
        Args:
            api_key: Kalshi API key (None for demo mode)
            demo_mode: Use simulated data instead of real API
        """
        self.api_key = api_key
        self.demo_mode = demo_mode or not api_key
        self.base_url = "https://api.elections.kalshi.com/trade-api/v2" if not demo_mode else None
        
        # User preferences
        self.target_categories = ['politics', 'tech', 'health', 'energy', 'climate']
        self.confidence_threshold = 70.0  # Conservative 70% minimum
        self.max_bet_fraction = 0.10  # Max 10% of bankroll per bet
        self.kelly_fraction = 0.25  # Quarter-Kelly for safety
    
    def get_active_markets(self, limit: int = 50) -> List[KalshiMarket]:
        """
        Fetch active markets from Kalshi API
        
        Args:
            limit: Maximum markets to return
            
        Returns:
            List of KalshiMarket objects
        """
        if self.demo_mode:
            return self._get_demo_markets()
        
        try:
            headers = {
                'Authorization': f'Bearer {self.api_key}',
                'Content-Type': 'application/json'
            }
            
            params = {
                'limit': limit,
                'status': 'open'
            }
            
            response = requests.get(
                f"{self.base_url}/markets",
                headers=headers,
                params=params,
                timeout=10
            )
            response.raise_for_status()
            
            data = response.json()
            markets = []
            
            for market_data in data.get('markets', []):
                market = self._parse_market(market_data)
                if market and self._is_relevant_category(market.category):
                    markets.append(market)
            
            return markets[:limit]
            
        except Exception as e:
            print(f"❌ Kalshi API error: {e}")
            return self._get_demo_markets()  # Fallback to demo
    
    def _parse_market(self, data: Dict) -> Optional[KalshiMarket]:
        """Parse market data from API response"""
        try:
            return KalshiMarket(
                ticker=data['ticker'],
                title=data['title'],
                category=data.get('category', 'other'),
                close_time=datetime.fromisoformat(data['close_time'].replace('Z', '+00:00')),
                yes_price=data.get('yes_price', 50),
                no_price=data.get('no_price', 50),
                volume_24h=data.get('volume_24h', 0),
                liquidity=data.get('liquidity', 0)
            )
        except Exception as e:
            print(f"⚠️ Failed to parse market: {e}")
            return None
    
    def _is_relevant_category(self, category: str) -> bool:
        """Check if category matches user interests"""
        category_lower = category.lower()
        return any(target in category_lower for target in self.target_categories)
    
    def calculate_gile_score(self, market: KalshiMarket) -> float:
        """
        Calculate GILE score for a prediction market
        
        GILE mapping for markets:
        - Goodness (G): Societal benefit, ethical alignment
        - Intuition (I): Information quality, expert consensus
        - Love (L): Community engagement, genuine interest
        - Environment (E): Market liquidity, time to close
        
        Returns:
            GILE score (-2.5 to +2.5 scale)
        """
        # G: Goodness - Does this market benefit society?
        # User interests (politics, tech, health, energy) should have positive GILE
        goodness = 0.5  # Baseline positive for user interests
        
        # Boost for explicitly positive outcomes
        if any(word in market.title.lower() for word in ['health', 'climate', 'cure', 'clean', 'peace', 'solar', 'renewable', 'approve', 'success']):
            goodness = 2.0
        # Only go negative for truly harmful outcomes
        elif any(word in market.title.lower() for word in ['war', 'crisis', 'disaster', 'fail', 'collapse']):
            goodness = -1.5
        
        # I: Intuition - Information quality (relaxed thresholds for user interests)
        intuition = 0.5  # Baseline positive
        if market.volume_24h > 5000:  # Lowered threshold
            intuition = 2.0
        elif market.volume_24h > 1000:
            intuition = 1.5
        elif market.volume_24h > 100:
            intuition = 0.5
        else:
            intuition = 0.0  # Neutral, not negative
        
        # L: Love - Community engagement
        love = 0.5  # Baseline positive for user interests
        days_to_close = (market.close_time - datetime.now()).days
        if days_to_close <= 7:  # Short-term = high engagement
            love = 2.0
        elif days_to_close <= 30:
            love = 1.5
        elif days_to_close <= 90:
            love = 0.8
        else:
            love = 0.3  # Still slightly positive
        
        # E: Environment - Market liquidity (relaxed thresholds)
        environment = 0.5  # Baseline positive
        if market.liquidity > 20000:  # Lowered threshold
            environment = 2.0
        elif market.liquidity > 5000:
            environment = 1.5
        elif market.liquidity > 1000:
            environment = 0.8
        else:
            environment = 0.3  # Still slightly positive
        
        # Weighted GILE calculation
        gile_raw = (
            0.3 * goodness +     # Increased weight on societal benefit
            0.25 * intuition +
            0.2 * love +
            0.25 * environment
        )
        
        return max(-2.5, min(2.5, gile_raw))
    
    def calculate_ti_confidence(self, market: KalshiMarket, ti_win_prob: float = None) -> float:
        """
        Calculate TI-based confidence for market prediction
        
        Combines GILE coherence with market edge (TI probability vs market odds).
        Only high confidence if BOTH GILE is strong AND we have real edge.
        
        Args:
            market: KalshiMarket object
            ti_win_prob: TI-predicted win probability (0-1), calculated from GILE
            
        Returns:
            Confidence percentage (0-100%)
        """
        # Calculate TI win probability from GILE if not provided
        if ti_win_prob is None:
            # Map GILE score to win probability
            # GILE > 1.0 → 75%+ win prob
            # GILE 0.5-1.0 → 60-75% win prob
            # GILE 0-0.5 → 50-60% win prob
            # GILE < 0 → <50% win prob
            if market.gile_score >= 1.0:
                ti_win_prob = 0.70 + (market.gile_score - 1.0) * 0.10
            elif market.gile_score >= 0.0:
                ti_win_prob = 0.50 + (market.gile_score * 0.20)
            else:
                ti_win_prob = 0.50 + (market.gile_score * 0.15)
            
            ti_win_prob = min(0.95, max(0.05, ti_win_prob))
        
        # Market-implied probability
        market_prob = market.yes_price / 100.0
        
        # Calculate edge: How much better is TI vs market?
        edge = abs(ti_win_prob - market_prob)
        edge_confidence = min(100.0, edge * 400.0)  # 5%+ edge = 100% confidence from edge
        
        # GILE coherence confidence: Higher GILE = more trustworthy
        gile_confidence = 50.0 + (market.gile_score * 15.0)  # Map -2.5 to +2.5 → 12.5% to 87.5%
        
        # Liquidity confidence: Can we actually place the bet?
        liquidity_confidence = min(100.0, (market.liquidity / 500.0) * 10.0)
        
        # Volume confidence: Is there real information flow?
        volume_confidence = min(100.0, (market.volume_24h / 1000.0) * 2.0)
        
        # Combined confidence - MUST have edge AND high GILE
        total_confidence = (
            0.35 * edge_confidence +      # Most important: do we have real edge?
            0.35 * gile_confidence +      # Second: is GILE trustworthy?
            0.15 * liquidity_confidence + # Can we execute?
            0.15 * volume_confidence      # Is there info flow?
        )
        
        return min(100.0, max(0.0, total_confidence))
    
    def calculate_kelly_bet_size(
        self,
        bankroll: float,
        win_prob: float,
        odds: float,
        kelly_fraction: float = 0.25
    ) -> float:
        """
        Calculate optimal bet size using Kelly Criterion
        
        Args:
            bankroll: Total available funds
            win_prob: Probability of winning (0-1)
            odds: Decimal odds (e.g., 2.0 for even money)
            kelly_fraction: Fraction of Kelly to use (0.25 = quarter-Kelly)
            
        Returns:
            Recommended bet amount in USD
        """
        # Kelly formula: f = (p * (b + 1) - 1) / b
        # where f = fraction of bankroll, p = win prob, b = odds - 1
        
        b = odds - 1.0
        kelly_f = (win_prob * (b + 1) - 1) / b
        
        # Apply fractional Kelly for safety
        conservative_f = kelly_f * kelly_fraction
        
        # Cap at max bet fraction
        final_f = min(conservative_f, self.max_bet_fraction)
        
        # Ensure non-negative
        final_f = max(0.0, final_f)
        
        return bankroll * final_f
    
    def score_and_recommend(
        self,
        markets: List[KalshiMarket],
        bankroll: float = 100.0
    ) -> List[KalshiMarket]:
        """
        Score all markets with GILE and provide betting recommendations
        
        Args:
            markets: List of markets to score
            bankroll: Available betting capital
            
        Returns:
            Scored markets with recommendations
        """
        scored_markets = []
        
        for market in markets:
            # Calculate GILE score
            market.gile_score = self.calculate_gile_score(market)
            
            # Calculate TI win probability from GILE
            if market.gile_score >= 1.0:
                ti_win_prob = 0.70 + (market.gile_score - 1.0) * 0.10
            elif market.gile_score >= 0.0:
                ti_win_prob = 0.50 + (market.gile_score * 0.20)
            else:
                ti_win_prob = 0.50 + (market.gile_score * 0.15)
            ti_win_prob = min(0.95, max(0.05, ti_win_prob))
            
            # Calculate TI confidence (requires edge + GILE strength)
            market.ti_confidence = self.calculate_ti_confidence(market, ti_win_prob)
            
            # Market-implied probability
            market_yes_prob = market.yes_price / 100.0
            market_no_prob = market.no_price / 100.0
            
            # Determine bet recommendation - only if we have real edge
            if market.ti_confidence >= self.confidence_threshold:
                # Check if TI probability materially exceeds market probability
                # YES if: TI predicts higher chance than market prices in
                # NO if: TI predicts lower chance than market prices in
                
                yes_edge = ti_win_prob - market_yes_prob  # Positive = underpriced
                no_edge = (1 - ti_win_prob) - market_no_prob  # Positive = overpriced outcome
                
                # Require at least 5% edge to recommend
                min_edge = 0.05
                
                if yes_edge > min_edge and market.gile_score > 0:
                    # TI thinks event more likely than market + good outcome → BET YES
                    market.recommended_bet = 'YES'
                    win_prob = ti_win_prob
                    odds = 100.0 / market.yes_price
                elif no_edge > min_edge or (yes_edge > min_edge and market.gile_score < 0):
                    # TI thinks event less likely OR bad outcome → BET NO
                    market.recommended_bet = 'NO'
                    win_prob = 1 - ti_win_prob  # Probability NO wins
                    odds = 100.0 / market.no_price
                else:
                    # No significant edge
                    market.recommended_bet = 'SKIP'
                    win_prob = 0.5
                    odds = 2.0
                
                # Calculate bet size using proper win probability
                if market.recommended_bet != 'SKIP':
                    market.recommended_amount = self.calculate_kelly_bet_size(
                        bankroll, win_prob, odds, self.kelly_fraction
                    )
                    
                    # Calculate expected ROI: (win_prob * payout) - loss_prob
                    market.expected_roi = ((odds - 1) * win_prob - (1 - win_prob)) * 100
                    
                    # Clamp bet amount to max 10% bankroll
                    market.recommended_amount = min(market.recommended_amount, bankroll * 0.10)
                else:
                    market.recommended_amount = 0.0
                    market.expected_roi = 0.0
            else:
                market.recommended_bet = 'SKIP'
                market.recommended_amount = 0.0
                market.expected_roi = 0.0
            
            scored_markets.append(market)
        
        # Sort by expected ROI (descending)
        scored_markets.sort(key=lambda m: m.expected_roi or 0.0, reverse=True)
        
        return scored_markets
    
    def _get_demo_markets(self) -> List[KalshiMarket]:
        """Generate demo markets for testing"""
        demo_markets = [
            KalshiMarket(
                ticker="PRES-2024",
                title="Will a Democrat win the 2024 Presidential Election?",
                category="politics",
                close_time=datetime.now() + timedelta(days=3),
                yes_price=62,
                no_price=38,
                volume_24h=125000,
                liquidity=250000
            ),
            KalshiMarket(
                ticker="SOLAR-2025",
                title="Will solar energy capacity exceed 500 GW globally by EOY 2025?",
                category="energy",
                close_time=datetime.now() + timedelta(days=14),
                yes_price=71,
                no_price=29,
                volume_24h=45000,
                liquidity=120000
            ),
            KalshiMarket(
                ticker="AI-GPT5",
                title="Will OpenAI release GPT-5 before December 31, 2025?",
                category="tech",
                close_time=datetime.now() + timedelta(days=7),
                yes_price=55,
                no_price=45,
                volume_24h=89000,
                liquidity=180000
            ),
            KalshiMarket(
                ticker="COVID-VACCINE",
                title="Will a new COVID variant vaccine be approved in 2025?",
                category="health",
                close_time=datetime.now() + timedelta(days=21),
                yes_price=43,
                no_price=57,
                volume_24h=32000,
                liquidity=95000
            ),
            KalshiMarket(
                ticker="CLIMATE-ACCORD",
                title="Will 10+ nations sign new climate accord by June 2025?",
                category="climate",
                close_time=datetime.now() + timedelta(days=60),
                yes_price=38,
                no_price=62,
                volume_24h=18000,
                liquidity=65000
            ),
        ]
        
        return demo_markets


def get_kalshi_integration(api_key: Optional[str] = None) -> KalshiTIIntegration:
    """Get singleton Kalshi integration instance"""
    if not hasattr(get_kalshi_integration, '_instance'):
        get_kalshi_integration._instance = KalshiTIIntegration(api_key)
    return get_kalshi_integration._instance

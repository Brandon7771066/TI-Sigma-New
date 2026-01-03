"""
Kalshi TI Framework Connector
Applies GILE Framework to prediction markets for exponential wealth generation

FEATURES:
- Market data fetching from Kalshi
- GILE-based prediction analysis
- Automated trading signals
- Performance tracking
- Risk management
"""

import os
from typing import Dict, List, Any, Optional
from datetime import datetime
import json

class KalshiTIConnector:
    """
    Connects Kalshi prediction markets with TI Framework analysis
    """
    
    def __init__(self, api_key_id: Optional[str] = None, private_key_path: Optional[str] = None):
        """
        Initialize Kalshi connector
        
        Args:
            api_key_id: Kalshi API key ID
            private_key_path: Path to private key PEM file
        """
        self.api_key_id = api_key_id or os.environ.get('KALSHI_API_KEY_ID')
        self.private_key_path = private_key_path or os.environ.get('KALSHI_PRIVATE_KEY_PATH')
        
        self.client = None
        self._authenticated = False
        
        # Track predictions
        self.predictions = []
        self.positions = []
    
    def authenticate(self) -> bool:
        """
        Authenticate with Kalshi API
        
        Returns:
            True if authentication successful
        """
        if not self.api_key_id or not self.private_key_path:
            print("⚠️ No Kalshi credentials configured - using demo mode")
            return False
        
        try:
            from kalshi_python.configuration import Configuration
            from kalshi_python import KalshiClient
            
            # Read private key
            with open(self.private_key_path, 'r') as f:
                private_key = f.read()
            
            # Configure client
            config = Configuration(
                host="https://api.elections.kalshi.com/trade-api/v2"
            )
            config.api_key_id = self.api_key_id
            config.private_key_pem = private_key
            
            # Initialize client
            self.client = KalshiClient(config)
            
            # Test authentication with balance check
            balance = self.client.get_balance()
            print(f"✅ Kalshi authenticated! Balance: ${balance.balance / 100:.2f}")
            
            self._authenticated = True
            return True
        
        except Exception as e:
            print(f"❌ Kalshi authentication failed: {e}")
            return False
    
    def get_markets(self, limit: int = 10, category: Optional[str] = None) -> List[Dict[str, Any]]:
        """
        Fetch available prediction markets
        
        Args:
            limit: Number of markets to fetch
            category: Filter by category (economics, politics, etc.)
        
        Returns:
            List of market dictionaries
        """
        if not self._authenticated or not self.client:
            print("⚠️ Not authenticated - returning demo markets")
            return self._get_demo_markets(limit)
        
        try:
            # Fetch markets from Kalshi
            markets = self.client.get_markets(limit=limit, category=category)
            
            return [self._format_market(m) for m in markets.markets]
        
        except Exception as e:
            print(f"Error fetching markets: {e}")
            return self._get_demo_markets(limit)
    
    def _format_market(self, market: Any) -> Dict[str, Any]:
        """
        Format Kalshi market data
        
        Args:
            market: Kalshi market object
        
        Returns:
            Formatted market dict
        """
        # Kalshi SDK uses yes_bid_price/no_bid_price (not yes_bid/no_bid)
        # Must use 'is not None' check to preserve 0-priced bids
        yes_price = 0.5
        no_price = 0.5
        
        if hasattr(market, 'yes_bid_price') and market.yes_bid_price is not None:
            yes_price = market.yes_bid_price / 100
        elif hasattr(market, 'yes_bid') and market.yes_bid is not None:
            yes_price = market.yes_bid / 100
        
        if hasattr(market, 'no_bid_price') and market.no_bid_price is not None:
            no_price = market.no_bid_price / 100
        elif hasattr(market, 'no_bid') and market.no_bid is not None:
            no_price = market.no_bid / 100
        
        return {
            'id': market.ticker if hasattr(market, 'ticker') else 'UNKNOWN',
            'title': market.title if hasattr(market, 'title') else 'Unknown Market',
            'category': market.category if hasattr(market, 'category') else 'unknown',
            'yes_price': yes_price,
            'no_price': no_price,
            'volume': market.volume if hasattr(market, 'volume') else 0,
            'open_interest': market.open_interest if hasattr(market, 'open_interest') else 0,
            'close_time': market.close_time if hasattr(market, 'close_time') else None,
            'status': market.status if hasattr(market, 'status') else 'active'
        }
    
    def _get_demo_markets(self, limit: int = 10) -> List[Dict[str, Any]]:
        """
        Generate demo prediction markets for testing
        
        Returns:
            List of demo markets
        """
        demo_markets = [
            {
                'id': 'SPY-2025-UP',
                'title': 'Will S&P 500 be up in 2025?',
                'category': 'economics',
                'yes_price': 0.62,
                'no_price': 0.38,
                'volume': 125000,
                'open_interest': 45000,
                'close_time': '2025-12-31T23:59:59Z',
                'status': 'active'
            },
            {
                'id': 'NASDAQ-Q1-2025',
                'title': 'Will NASDAQ reach 20,000 in Q1 2025?',
                'category': 'economics',
                'yes_price': 0.45,
                'no_price': 0.55,
                'volume': 98000,
                'open_interest': 32000,
                'close_time': '2025-03-31T23:59:59Z',
                'status': 'active'
            },
            {
                'id': 'CRYPTO-2025',
                'title': 'Will Bitcoin exceed $150k in 2025?',
                'category': 'crypto',
                'yes_price': 0.38,
                'no_price': 0.62,
                'volume': 210000,
                'open_interest': 78000,
                'close_time': '2025-12-31T23:59:59Z',
                'status': 'active'
            },
            {
                'id': 'AI-2025',
                'title': 'Will GPT-5 be released in 2025?',
                'category': 'technology',
                'yes_price': 0.71,
                'no_price': 0.29,
                'volume': 156000,
                'open_interest': 52000,
                'close_time': '2025-12-31T23:59:59Z',
                'status': 'active'
            },
            {
                'id': 'CLIMATE-2025',
                'title': 'Will 2025 be hottest year on record?',
                'category': 'science',
                'yes_price': 0.58,
                'no_price': 0.42,
                'volume': 87000,
                'open_interest': 28000,
                'close_time': '2025-12-31T23:59:59Z',
                'status': 'active'
            }
        ]
        
        return demo_markets[:limit]
    
    def analyze_market_with_gile(self, market: Dict[str, Any]) -> Dict[str, Any]:
        """
        Analyze prediction market using GILE Framework
        
        Args:
            market: Market data dictionary
        
        Returns:
            Analysis with TI Framework prediction
        """
        # Extract market data
        yes_price = market['yes_price']
        no_price = market['no_price']
        volume = market['volume']
        open_interest = market['open_interest']
        
        # GILE-based analysis
        # Higher GILE → more likely to resolve "YES"
        
        # Calculate implied GILE from market prices
        # Market efficiency: price ≈ probability
        market_probability = yes_price
        
        # Map market probability to GILE score
        # 0.5 (50%) → 0.5 GILE (neutral)
        # 0.0 (0%) → 0.0 GILE (low)
        # 1.0 (100%) → 1.0 GILE (high)
        implied_gile = market_probability
        
        # Calculate market momentum (volume/open_interest ratio)
        momentum = (volume / open_interest) if open_interest > 0 else 0
        
        # High momentum = strong conviction
        # Adjust GILE based on momentum
        if momentum > 3.0:
            # Very high momentum - strengthen signal
            adjusted_gile = implied_gile * 1.1
        elif momentum > 1.5:
            # Moderate momentum
            adjusted_gile = implied_gile * 1.05
        else:
            # Low momentum - weaken signal
            adjusted_gile = implied_gile * 0.95
        
        # Cap at [0, 1]
        adjusted_gile = max(0.0, min(1.0, adjusted_gile))
        
        # Generate TI Framework prediction
        if adjusted_gile > 0.65:
            signal = 'BUY_YES'
            confidence = adjusted_gile
            reasoning = f"High GILE ({adjusted_gile:.2f}) suggests YES outcome likely"
        elif adjusted_gile < 0.35:
            signal = 'BUY_NO'
            confidence = 1.0 - adjusted_gile
            reasoning = f"Low GILE ({adjusted_gile:.2f}) suggests NO outcome likely"
        else:
            signal = 'HOLD'
            confidence = 0.5
            reasoning = f"Neutral GILE ({adjusted_gile:.2f}) - insufficient edge"
        
        # Calculate expected value (EV)
        if signal == 'BUY_YES':
            ev = (adjusted_gile * (1 - yes_price)) - ((1 - adjusted_gile) * yes_price)
        elif signal == 'BUY_NO':
            ev = ((1 - adjusted_gile) * (1 - no_price)) - (adjusted_gile * no_price)
        else:
            ev = 0.0
        
        return {
            'market_id': market['id'],
            'market_title': market['title'],
            'implied_gile': implied_gile,
            'adjusted_gile': adjusted_gile,
            'momentum': momentum,
            'signal': signal,
            'confidence': confidence,
            'expected_value': ev,
            'reasoning': reasoning,
            'current_yes_price': yes_price,
            'current_no_price': no_price,
            'analysis_timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        }
    
    def batch_analyze_markets(self, markets: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        Analyze multiple markets using GILE Framework
        
        Args:
            markets: List of market dictionaries
        
        Returns:
            List of analyses
        """
        return [self.analyze_market_with_gile(m) for m in markets]
    
    def get_top_opportunities(self, markets: List[Dict[str, Any]], min_ev: float = 0.05) -> List[Dict[str, Any]]:
        """
        Find best trading opportunities using GILE analysis
        
        Args:
            markets: List of market dictionaries
            min_ev: Minimum expected value threshold
        
        Returns:
            Sorted list of opportunities (best first)
        """
        analyses = self.batch_analyze_markets(markets)
        
        # Filter for opportunities with positive EV and actionable signals
        opportunities = [
            a for a in analyses 
            if a['signal'] != 'HOLD' and a['expected_value'] > min_ev
        ]
        
        # Sort by expected value (highest first)
        opportunities.sort(key=lambda x: x['expected_value'], reverse=True)
        
        return opportunities
    
    def place_order(self, market_id: str, side: str, quantity: int, price: float) -> Dict[str, Any]:
        """
        Place order on Kalshi (if authenticated)
        
        Args:
            market_id: Market ticker
            side: 'yes' or 'no'
            quantity: Number of contracts
            price: Limit price (0-100 cents)
        
        Returns:
            Order result
        """
        if not self._authenticated or not self.client:
            print("⚠️ Not authenticated - simulating order")
            return {
                'status': 'simulated',
                'market_id': market_id,
                'side': side,
                'quantity': quantity,
                'price': price,
                'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            }
        
        try:
            # Place limit order
            order = self.client.create_order(
                ticker=market_id,
                client_order_id=f"TI-{datetime.now().timestamp()}",
                side=side,
                action='buy',
                count=quantity,
                type='limit',
                yes_price=int(price * 100) if side == 'yes' else None,
                no_price=int(price * 100) if side == 'no' else None
            )
            
            return {
                'status': 'placed',
                'order_id': order.order_id,
                'market_id': market_id,
                'side': side,
                'quantity': quantity,
                'price': price,
                'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            }
        
        except Exception as e:
            return {
                'status': 'error',
                'error': str(e),
                'market_id': market_id
            }
    
    def export_predictions(self, predictions: List[Dict[str, Any]], output_path: str = 'kalshi_predictions.json'):
        """
        Export predictions to JSON file
        
        Args:
            predictions: List of prediction analyses
            output_path: Where to save
        """
        report = {
            'export_timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            'total_predictions': len(predictions),
            'predictions': predictions
        }
        
        with open(output_path, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"📄 Predictions exported to: {output_path}")
        return output_path


if __name__ == '__main__':
    # Test connector
    connector = KalshiTIConnector()
    
    # Get demo markets
    markets = connector.get_markets(limit=5)
    
    print("\n📊 KALSHI TI FRAMEWORK ANALYSIS")
    print("=" * 80)
    
    # Analyze markets
    opportunities = connector.get_top_opportunities(markets)
    
    if opportunities:
        print(f"\n🎯 Found {len(opportunities)} trading opportunities:\n")
        
        for i, opp in enumerate(opportunities, 1):
            print(f"{i}. {opp['market_title']}")
            print(f"   Signal: {opp['signal']}")
            print(f"   GILE: {opp['adjusted_gile']:.2f}")
            print(f"   Expected Value: {opp['expected_value']:+.2%}")
            print(f"   Reasoning: {opp['reasoning']}")
            print()
    else:
        print("\n⚠️ No opportunities found with current criteria")

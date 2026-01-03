"""
Quiver Quantitative Data Pipeline
==================================
Congressional trading data ingestion for TI Framework Elite Conviction Scoring

Data Sources:
- Quiver Quantitative API (congressional trades, lobbyist disclosures)
- 30-45 day disclosure delay per STOCK Act
- Tracks ~1,800 US equities from January 2016

Integration with Jeff Time V4:
- Elite conviction modifies tau_phi (Photonic Memory) and tau_f (Freedom Prediction)
- Position sizing adjustment based on congressional consensus
"""

import os
import json
import requests
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
import numpy as np

class QuiverQuantitativePipeline:
    """
    Congressional trading data pipeline for TI Framework.
    
    Uses Quiver Quantitative API to track politician stock trades
    and calculate Elite Conviction Scores.
    """
    
    # Known high-alpha politicians (based on historical performance)
    ELITE_POLITICIANS = {
        'Nancy Pelosi': {'alpha_weight': 1.5, 'avg_return': 0.65},
        'Dan Crenshaw': {'alpha_weight': 1.3, 'avg_return': 0.45},
        'Josh Gottheimer': {'alpha_weight': 1.2, 'avg_return': 0.38},
        'Brian Mast': {'alpha_weight': 1.2, 'avg_return': 0.35},
        'Marjorie Taylor Greene': {'alpha_weight': 1.1, 'avg_return': 0.32},
    }
    
    # Transaction type mappings
    TRANSACTION_TYPES = {
        'Purchase': 1.0,
        'Sale': -1.0,
        'Sale (Partial)': -0.5,
        'Exchange': 0.0,
    }
    
    def __init__(self, api_key: Optional[str] = None):
        """
        Initialize Quiver pipeline.
        
        Args:
            api_key: Quiver Quantitative API key (optional for demo mode)
        """
        self.api_key = api_key or os.environ.get('QUIVER_API_KEY')
        self.base_url = "https://api.quiverquant.com/beta"
        self.cache = {}
        self.conviction_scores = {}
        
    def _make_request(self, endpoint: str, params: Dict = None) -> Optional[Dict]:
        """Make authenticated request to Quiver API."""
        if not self.api_key:
            print("Warning: No Quiver API key - using demo data")
            return self._get_demo_data(endpoint)
            
        headers = {
            'Authorization': f'Bearer {self.api_key}',
            'Accept': 'application/json'
        }
        
        try:
            response = requests.get(
                f"{self.base_url}/{endpoint}",
                headers=headers,
                params=params,
                timeout=30
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            print(f"Quiver API error: {e}")
            return None
    
    def _get_demo_data(self, endpoint: str) -> Dict:
        """Return demo data when no API key available."""
        demo_trades = [
            {
                'Ticker': 'NVDA',
                'Representative': 'Nancy Pelosi',
                'Transaction': 'Purchase',
                'Amount': '$1,000,001 - $5,000,000',
                'TransactionDate': '2024-11-15',
                'DisclosureDate': '2024-12-15',
            },
            {
                'Ticker': 'AAPL',
                'Representative': 'Nancy Pelosi',
                'Transaction': 'Purchase',
                'Amount': '$500,001 - $1,000,000',
                'TransactionDate': '2024-11-10',
                'DisclosureDate': '2024-12-10',
            },
            {
                'Ticker': 'TSLA',
                'Representative': 'Dan Crenshaw',
                'Transaction': 'Sale',
                'Amount': '$250,001 - $500,000',
                'TransactionDate': '2024-11-08',
                'DisclosureDate': '2024-12-08',
            },
            {
                'Ticker': 'MSFT',
                'Representative': 'Josh Gottheimer',
                'Transaction': 'Purchase',
                'Amount': '$100,001 - $250,000',
                'TransactionDate': '2024-11-05',
                'DisclosureDate': '2024-12-05',
            },
            {
                'Ticker': 'GOOGL',
                'Representative': 'Nancy Pelosi',
                'Transaction': 'Purchase',
                'Amount': '$250,001 - $500,000',
                'TransactionDate': '2024-10-28',
                'DisclosureDate': '2024-11-28',
            },
        ]
        return demo_trades
    
    def get_congressional_trades(
        self, 
        ticker: Optional[str] = None,
        lookback_days: int = 90
    ) -> List[Dict]:
        """
        Fetch congressional trading data.
        
        Args:
            ticker: Optional ticker to filter (e.g., 'AAPL')
            lookback_days: Number of days to look back
            
        Returns:
            List of trade records
        """
        endpoint = "bulk/congresstrading"
        if ticker:
            endpoint = f"historical/congresstrading/{ticker}"
            
        data = self._make_request(endpoint)
        
        if not data:
            return []
            
        # Filter by date
        cutoff_date = datetime.now() - timedelta(days=lookback_days)
        
        filtered_trades = []
        for trade in data:
            try:
                trade_date = datetime.strptime(
                    trade.get('TransactionDate', '2020-01-01'), 
                    '%Y-%m-%d'
                )
                if trade_date >= cutoff_date:
                    filtered_trades.append(trade)
            except:
                continue
                
        return filtered_trades
    
    def parse_amount_range(self, amount_str: str) -> float:
        """
        Parse STOCK Act amount range to midpoint value.
        
        Ranges: $1,001-$15,000, $15,001-$50,000, $50,001-$100,000,
                $100,001-$250,000, $250,001-$500,000, $500,001-$1,000,000,
                $1,000,001-$5,000,000, $5,000,001-$25,000,000, Over $50,000,000
        """
        amount_map = {
            '$1,001 - $15,000': 8000,
            '$15,001 - $50,000': 32500,
            '$50,001 - $100,000': 75000,
            '$100,001 - $250,000': 175000,
            '$250,001 - $500,000': 375000,
            '$500,001 - $1,000,000': 750000,
            '$1,000,001 - $5,000,000': 3000000,
            '$5,000,001 - $25,000,000': 15000000,
            '$25,000,001 - $50,000,000': 37500000,
            'Over $50,000,000': 75000000,
        }
        
        # Clean and match
        clean_amount = amount_str.strip()
        return amount_map.get(clean_amount, 100000)  # Default midpoint
    
    def calculate_elite_conviction(
        self, 
        ticker: str, 
        lookback_days: int = 90
    ) -> Dict:
        """
        Calculate Elite Conviction Score for a ticker.
        
        Returns:
            Dict with conviction score and component details
        """
        trades = self.get_congressional_trades(ticker, lookback_days)
        
        if not trades:
            return {
                'ticker': ticker,
                'conviction': 0.0,
                'buy_count': 0,
                'sell_count': 0,
                'net_value': 0,
                'elite_traders': [],
                'recency_weight': 1.0,
                'confidence': 0.0,
            }
        
        # Aggregate by direction
        buy_signals = []
        sell_signals = []
        elite_traders = set()
        
        for trade in trades:
            rep = trade.get('Representative', 'Unknown')
            transaction = trade.get('Transaction', 'Unknown')
            amount = self.parse_amount_range(trade.get('Amount', '$100,001 - $250,000'))
            
            # Get politician alpha weight
            alpha_weight = 1.0
            if rep in self.ELITE_POLITICIANS:
                alpha_weight = self.ELITE_POLITICIANS[rep]['alpha_weight']
                elite_traders.add(rep)
            
            # Get transaction direction
            direction = self.TRANSACTION_TYPES.get(transaction, 0.0)
            
            # Calculate weighted signal
            weighted_signal = direction * alpha_weight * (amount / 1000000)  # Normalize by $1M
            
            # Calculate recency weight (more recent = more weight)
            try:
                trade_date = datetime.strptime(trade.get('TransactionDate', '2020-01-01'), '%Y-%m-%d')
                days_ago = (datetime.now() - trade_date).days
                recency_weight = max(0.1, 1.0 - (days_ago / lookback_days))
            except:
                recency_weight = 0.5
            
            final_signal = weighted_signal * recency_weight
            
            if final_signal > 0:
                buy_signals.append(final_signal)
            elif final_signal < 0:
                sell_signals.append(final_signal)
        
        # Calculate net conviction (fixed normalization)
        total_buy = sum(buy_signals) if buy_signals else 0
        total_sell = abs(sum(sell_signals)) if sell_signals else 0
        total_magnitude = total_buy + total_sell
        
        if total_magnitude == 0:
            conviction = 0.0
        else:
            # Simple ratio: (buys - sells) / (buys + sells)
            conviction = (total_buy - total_sell) / total_magnitude
            conviction = np.clip(conviction, -1.0, 1.0)
        
        # Confidence based on number of trades
        trade_count = len(buy_signals) + len(sell_signals)
        confidence = min(1.0, trade_count / 10.0)  # Max confidence at 10+ trades
        
        result = {
            'ticker': ticker,
            'conviction': float(conviction),
            'buy_count': len(buy_signals),
            'sell_count': len(sell_signals),
            'net_value': float(net_signal),
            'elite_traders': list(elite_traders),
            'total_trades': trade_count,
            'confidence': float(confidence),
            'lookback_days': lookback_days,
            'last_updated': datetime.now().isoformat(),
        }
        
        # Cache result
        self.conviction_scores[ticker] = result
        
        return result
    
    def get_portfolio_convictions(
        self, 
        tickers: List[str],
        lookback_days: int = 90
    ) -> Dict[str, Dict]:
        """
        Calculate conviction scores for a portfolio of tickers.
        
        Args:
            tickers: List of ticker symbols
            lookback_days: Lookback period
            
        Returns:
            Dict mapping tickers to conviction data
        """
        results = {}
        for ticker in tickers:
            results[ticker] = self.calculate_elite_conviction(ticker, lookback_days)
        return results
    
    def apply_elite_bias(
        self, 
        tau_phi: float, 
        tau_f: float, 
        elite_conviction: float,
        bias_strength: float = 0.3
    ) -> Tuple[float, float]:
        """
        Apply elite conviction bias to Jeff Time V4 components.
        
        Integration with TI Framework:
        - Positive conviction amplifies bullish tau_phi and tau_f
        - Negative conviction amplifies bearish tau_phi and tau_f
        - Cross-signals (elite buy + bearish signal) are NOT modified
        
        Args:
            tau_phi: Photonic Memory component (τ_φ)
            tau_f: Freedom Prediction component (τ_f)
            elite_conviction: Conviction score from -1 to +1
            bias_strength: How much elite data influences (default 0.3)
            
        Returns:
            Tuple of modified (tau_phi, tau_f)
        """
        # If elites are buying AND our signal is bullish, amplify
        if elite_conviction > 0:
            if tau_phi > 0:
                tau_phi *= (1 + elite_conviction * bias_strength)
            if tau_f > 0:
                tau_f *= (1 + elite_conviction * bias_strength)
        
        # If elites are selling AND our signal is bearish, amplify
        elif elite_conviction < 0:
            if tau_phi < 0:
                tau_phi *= (1 + abs(elite_conviction) * bias_strength)
            if tau_f < 0:
                tau_f *= (1 + abs(elite_conviction) * bias_strength)
        
        return tau_phi, tau_f
    
    def get_elite_adjusted_size(
        self, 
        base_size: float, 
        elite_conviction: float,
        max_position: float = 0.15
    ) -> float:
        """
        Adjust position size based on elite conviction.
        
        Args:
            base_size: Base position size (0-1)
            elite_conviction: Conviction score (-1 to +1)
            max_position: Maximum allowed position size
            
        Returns:
            Adjusted position size
        """
        if elite_conviction > 0.5:
            return min(base_size * 1.5, max_position)  # 50% boost
        elif elite_conviction > 0.25:
            return min(base_size * 1.25, max_position)  # 25% boost
        elif elite_conviction < -0.5:
            return base_size * 0.5  # 50% reduction
        elif elite_conviction < -0.25:
            return base_size * 0.75  # 25% reduction
        return base_size
    
    def generate_conviction_report(self, tickers: List[str]) -> str:
        """Generate a formatted conviction report for tickers."""
        convictions = self.get_portfolio_convictions(tickers)
        
        report = []
        report.append("=" * 60)
        report.append("ELITE CONVICTION REPORT - Congressional Trading Analysis")
        report.append(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report.append("=" * 60)
        report.append("")
        
        # Sort by conviction (highest to lowest)
        sorted_tickers = sorted(
            convictions.items(), 
            key=lambda x: x[1]['conviction'], 
            reverse=True
        )
        
        for ticker, data in sorted_tickers:
            conviction = data['conviction']
            
            # Determine signal strength
            if conviction > 0.5:
                signal = "🟢 STRONG BUY"
            elif conviction > 0.2:
                signal = "🟢 BUY"
            elif conviction > -0.2:
                signal = "⚪ NEUTRAL"
            elif conviction > -0.5:
                signal = "🔴 SELL"
            else:
                signal = "🔴 STRONG SELL"
            
            report.append(f"📊 {ticker}: {signal}")
            report.append(f"   Conviction Score: {conviction:+.3f}")
            report.append(f"   Buys: {data['buy_count']} | Sells: {data['sell_count']}")
            report.append(f"   Confidence: {data['confidence']:.1%}")
            
            if data['elite_traders']:
                report.append(f"   Elite Traders: {', '.join(data['elite_traders'])}")
            report.append("")
        
        report.append("=" * 60)
        report.append("ELITE CONVICTION SCORING SYSTEM - TI Framework V4")
        report.append("Based on STOCK Act disclosures (30-45 day delay)")
        report.append("=" * 60)
        
        return "\n".join(report)


def integrate_with_jeff_time_v4(
    tau_phi: float,
    tau_j: float, 
    tau_f: float,
    love: float,
    elite_conviction: float,
    bias_strength: float = 0.3
) -> dict:
    """
    Full integration with Jeff Time V4 algorithm.
    
    Args:
        tau_phi: Photonic Memory component
        tau_j: Jeff Fiction component  
        tau_f: Freedom Prediction component
        love: Love Entanglement component
        elite_conviction: Congressional conviction score (-1 to +1)
        bias_strength: How much elite data influences (default 0.3)
        
    Returns:
        Dict with adjusted components and final signal
    """
    # Apply elite bias to tau_phi and tau_f
    adj_tau_phi = tau_phi
    adj_tau_f = tau_f
    
    if elite_conviction > 0.1:
        # Elites buying - amplify bullish signals
        if tau_phi > 0:
            adj_tau_phi *= (1 + elite_conviction * bias_strength)
        if tau_f > 0:
            adj_tau_f *= (1 + elite_conviction * bias_strength)
    elif elite_conviction < -0.1:
        # Elites selling - amplify bearish signals
        if tau_phi < 0:
            adj_tau_phi *= (1 + abs(elite_conviction) * bias_strength)
        if tau_f < 0:
            adj_tau_f *= (1 + abs(elite_conviction) * bias_strength)
    
    # Jeff Time V4 weights
    TAU_PHI_WEIGHT = 0.20
    TAU_J_WEIGHT = 0.45
    TAU_F_WEIGHT = 0.20
    LOVE_WEIGHT = 0.15
    
    # Calculate unified signal
    unified_signal = (
        TAU_PHI_WEIGHT * adj_tau_phi +
        TAU_J_WEIGHT * tau_j +
        TAU_F_WEIGHT * adj_tau_f +
        LOVE_WEIGHT * love
    )
    
    return {
        'original': {'tau_phi': tau_phi, 'tau_f': tau_f},
        'adjusted': {'tau_phi': adj_tau_phi, 'tau_f': adj_tau_f},
        'elite_conviction': elite_conviction,
        'unified_signal': unified_signal,
        'recommendation': 'BUY' if unified_signal > 0.3 else 'SELL' if unified_signal < -0.3 else 'HOLD'
    }


class QuantConnectEliteIntegration:
    """
    QuantConnect-ready elite conviction integration.
    
    Copy this class into your QuantConnect algorithm for
    congressional trading signal integration.
    """
    
    QUANTCONNECT_TEMPLATE = '''
# Add to Initialize():
from QuantConnect.DataSource import QuiverCongress

self.elite_conviction = {}
self.congress_data = {}
for symbol in self.symbols:
    try:
        self.congress_data[symbol] = self.AddData(QuiverCongress, symbol).Symbol
    except:
        pass

# Add new method:
def CalculateEliteConviction(self, symbol, lookback_days=90):
    """
    Calculate elite conviction from congressional trading data.
    Returns value from -1.0 to +1.0
    """
    congress_symbol = self.congress_data.get(symbol)
    if not congress_symbol:
        return 0.0
    
    try:
        history = self.History(QuiverCongress, congress_symbol, lookback_days, Resolution.Daily)
        if history.empty:
            return 0.0
        
        buys = len(history[history['transaction'] == 'Purchase'])
        sells = len(history[history['transaction'].str.contains('Sale', na=False)])
        total = buys + sells
        
        if total == 0:
            return 0.0
        
        return float(np.clip((buys - sells) / total, -1.0, 1.0))
    except:
        return 0.0

# Add to trading logic:
def ApplyEliteBias(self, tau_phi, tau_f, symbol):
    """Apply elite conviction to Jeff Time components."""
    conviction = self.CalculateEliteConviction(symbol)
    bias_strength = 0.3
    
    if conviction > 0:
        if tau_phi > 0:
            tau_phi *= (1 + conviction * bias_strength)
        if tau_f > 0:
            tau_f *= (1 + conviction * bias_strength)
    elif conviction < 0:
        if tau_phi < 0:
            tau_phi *= (1 + abs(conviction) * bias_strength)
        if tau_f < 0:
            tau_f *= (1 + abs(conviction) * bias_strength)
    
    return tau_phi, tau_f
'''
    
    @staticmethod
    def get_template() -> str:
        """Get QuantConnect integration template."""
        return QuantConnectEliteIntegration.QUANTCONNECT_TEMPLATE


# Demo usage
if __name__ == "__main__":
    # Initialize pipeline (demo mode without API key)
    pipeline = QuiverQuantitativePipeline()
    
    # Test tickers
    test_tickers = ['NVDA', 'AAPL', 'TSLA', 'MSFT', 'GOOGL', 'META', 'AMD', 'AMZN']
    
    # Generate report
    report = pipeline.generate_conviction_report(test_tickers)
    print(report)
    
    # Show QuantConnect template
    print("\n" + "=" * 60)
    print("QUANTCONNECT INTEGRATION TEMPLATE:")
    print("=" * 60)
    print(QuantConnectEliteIntegration.get_template())

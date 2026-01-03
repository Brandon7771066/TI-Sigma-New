"""
Stock Market God Machine - Live Market Data Integration (D3)
=============================================================

**MULTI-SOURCE REAL-WORLD DATA PIPELINE**
Wires together ALL available data sources for maximum signal quality!

Data Source Waterfall:
1. Alpha Vantage (premium technical data) - FREE tier available
2. Yahoo Finance (backup price data) - FREE unlimited
3. Metaculus (crowd wisdom) - FREE public API
4. Kalshi (prediction markets) - Requires $100 account
5. Synthetic (testing/development fallback)

Philosophy: "Guilding doorknobs" - Maximum data quality yields exponential returns!

Author: TI Framework Team  
Date: November 15, 2025
"""

import requests
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
import numpy as np
import json
import os


class MarketDataIntegration:
    """
    Multi-source market data aggregator
    
    Tries multiple real-world APIs in order of quality:
    Alpha Vantage → Yahoo Finance → Synthetic fallback
    
    Also integrates prediction markets (Metaculus, Kalshi)
    """
    
    def __init__(
        self,
        use_live_data: bool = False,
        alpha_vantage_key: Optional[str] = None,
        kalshi_api_key: Optional[str] = None,
        kalshi_api_secret: Optional[str] = None
    ):
        self.use_live_data = use_live_data
        
        # API keys (prefer environment variables)
        self.alpha_vantage_key = alpha_vantage_key or os.getenv('ALPHA_VANTAGE_KEY')
        self.kalshi_api_key = kalshi_api_key or os.getenv('KALSHI_API_KEY')
        self.kalshi_api_secret = kalshi_api_secret or os.getenv('KALSHI_API_SECRET')
        
        # Track which sources are available
        self.sources_available = {
            'alpha_vantage': bool(self.alpha_vantage_key),
            'yahoo_finance': True,  # Always available (no key needed)
            'metaculus': True,  # Always available (public API)
            'kalshi': bool(self.kalshi_api_key and self.kalshi_api_secret),
            'synthetic': True  # Always available (fallback)
        }
        
        print(f"📊 Market Data Sources: {sum(self.sources_available.values())}/5 available")
        for source, available in self.sources_available.items():
            status = "✅" if available else "⚠️ "
            print(f"   {status} {source}")
    
    def get_stock_data(
        self,
        ticker: str,
        days: int = 30,
        interval: str = '1d'
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Fetch stock price and volume data using multi-source waterfall
        
        Priority order:
        1. Alpha Vantage (best technical data)
        2. Yahoo Finance (reliable backup)
        3. Synthetic (testing fallback)
        
        Args:
            ticker: Stock symbol (e.g., "SPY", "AAPL")
            days: Historical days to fetch
            interval: Data interval - '1d' (daily), '1h' (hourly), '15m' (15-min), '5m', '1m'
        
        Returns:
            (prices, volumes) as numpy arrays
        """
        if not self.use_live_data:
            return self._generate_synthetic_data(ticker, days)
        
        # Try Alpha Vantage first (premium data source)
        if self.sources_available['alpha_vantage']:
            print(f"   📈 Trying Alpha Vantage for {ticker} ({interval})...")
            try:
                prices, volumes = self._fetch_alpha_vantage(ticker, days, interval)
                print(f"   ✅ Alpha Vantage success! Got {len(prices)} data points")
                return prices, volumes
            except Exception as e:
                print(f"   ⚠️  Alpha Vantage failed: {e}")
        
        # Fallback to Yahoo Finance (reliable, free)
        print(f"   📈 Trying Yahoo Finance for {ticker} ({interval})...")
        try:
            prices, volumes = self._fetch_yahoo_finance(ticker, days, interval)
            print(f"   ✅ Yahoo Finance success! Got {len(prices)} data points")
            return prices, volumes
        except Exception as e:
            print(f"   ⚠️  Yahoo Finance failed: {e}")
        
        # Final fallback: Synthetic data
        print(f"   📈 Using synthetic data for {ticker}...")
        return self._generate_synthetic_data(ticker, days)
    
    def _fetch_alpha_vantage(
        self,
        ticker: str,
        days: int,
        interval: str = '1d'
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Fetch data from Alpha Vantage API (PREMIUM source)
        
        Get free API key: https://www.alphavantage.co/support/#api-key
        Free tier: 5 requests/min, 500/day
        
        Supported intervals: '1d' (daily), '60m' (hourly), '15m', '5m', '1m'
        """
        url = "https://www.alphavantage.co/query"
        
        # Map interval to Alpha Vantage function
        if interval == '1d':
            params = {
                'function': 'TIME_SERIES_DAILY',
                'symbol': ticker,
                'apikey': self.alpha_vantage_key,
                'outputsize': 'full' if days > 100 else 'compact'
            }
            time_series_key = 'Time Series (Daily)'
        else:
            # Intraday data (1min, 5min, 15min, 30min, 60min)
            av_interval = interval.replace('m', 'min').replace('h', 'min')
            if av_interval == '1h':
                av_interval = '60min'
            
            params = {
                'function': 'TIME_SERIES_INTRADAY',
                'symbol': ticker,
                'interval': av_interval,
                'apikey': self.alpha_vantage_key,
                'outputsize': 'full' if days > 5 else 'compact'
            }
            time_series_key = f'Time Series ({av_interval})'
        
        response = requests.get(url, params=params, timeout=10)
        data = response.json()
        
        # Check for errors
        if 'Error Message' in data:
            raise ValueError(f"Alpha Vantage error: {data['Error Message']}")
        if 'Note' in data:
            raise ValueError(f"Alpha Vantage rate limit: {data['Note']}")
        
        # Parse time series
        time_series = data.get(time_series_key, {})
        if not time_series:
            raise ValueError("No time series data in response")
        
        # Extract prices and volumes (sorted by timestamp)
        timestamps = sorted(time_series.keys(), reverse=True)
        
        # Limit to requested days of data
        if interval != '1d':
            # For intraday, calculate how many data points = days
            points_per_day = {'1m': 390, '5m': 78, '15m': 26, '30m': 13, '1h': 6.5, '60m': 6.5}
            max_points = int(days * points_per_day.get(interval, 390))
            timestamps = timestamps[:max_points]
        else:
            timestamps = timestamps[:days]
        
        prices = [float(time_series[d]['4. close']) for d in timestamps]
        volumes = [float(time_series[d]['5. volume']) for d in timestamps]
        
        return np.array(prices[::-1]), np.array(volumes[::-1])  # Reverse to chronological
    
    def _fetch_yahoo_finance(
        self,
        ticker: str,
        days: int,
        interval: str = '1d'
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Fetch data from Yahoo Finance (BACKUP source, always free)
        
        No API key needed - uses public endpoint
        Supported intervals: '1d', '1h', '30m', '15m', '5m', '1m'
        Note: Intraday data only available for last 7-60 days depending on interval
        """
        # Yahoo Finance API endpoint (public)
        end_date = datetime.now()
        start_date = end_date - timedelta(days=days)
        
        # Convert to Unix timestamps
        start_ts = int(start_date.timestamp())
        end_ts = int(end_date.timestamp())
        
        url = f"https://query1.finance.yahoo.com/v8/finance/chart/{ticker}"
        params = {
            'period1': start_ts,
            'period2': end_ts,
            'interval': interval,  # Now uses parameter! '1d', '1h', '5m', etc.
            'includePrePost': 'false'
        }
        
        headers = {
            'User-Agent': 'Mozilla/5.0'
        }
        
        response = requests.get(url, params=params, headers=headers, timeout=10)
        data = response.json()
        
        # Parse response
        result = data['chart']['result'][0]
        prices = np.array(result['indicators']['quote'][0]['close'])
        volumes = np.array(result['indicators']['quote'][0]['volume'])
        
        # Remove NaN values
        valid_idx = ~np.isnan(prices)
        prices = prices[valid_idx]
        volumes = volumes[valid_idx]
        
        return prices, volumes
    
    def _generate_synthetic_data(
        self,
        ticker: str,
        days: int,
        base_price: float = 450.0
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Generate realistic synthetic market data for testing
        
        Simulates:
        - Trends (drift)
        - Volatility (random walk)
        - Volume patterns
        """
        # Seed based on ticker for reproducibility
        seed = sum(ord(c) for c in ticker)
        np.random.seed(seed)
        
        # Price evolution (geometric Brownian motion)
        drift = 0.0005  # Slight upward bias (stocks go up long-term)
        volatility = 0.02  # Daily volatility ~2%
        
        returns = np.random.normal(drift, volatility, days)
        prices = base_price * np.exp(np.cumsum(returns))
        
        # Volume (log-normal distribution)
        mean_volume = 50_000_000  # 50M shares/day
        volumes = np.random.lognormal(
            np.log(mean_volume),
            0.3,  # Volatility of volume
            days
        )
        
        return prices, volumes
    
    def get_prediction_market_sentiment(
        self,
        topic: str = "stock_market"
    ) -> Dict:
        """
        Get crowd wisdom from prediction markets (MULTI-SOURCE!)
        
        Priority order:
        1. Kalshi (real money markets - most accurate!)
        2. Metaculus (expert forecasters - high quality)
        3. Synthetic (fallback)
        
        Returns:
            Sentiment dict with source and confidence
        """
        # Try Kalshi first (real money = best signal!)
        if self.sources_available['kalshi']:
            print(f"   🎲 Trying Kalshi for {topic}...")
            try:
                kalshi_sentiment = self._fetch_kalshi_sentiment(topic)
                if kalshi_sentiment is not None:
                    print(f"   ✅ Kalshi success! Sentiment: {kalshi_sentiment:.2f}")
                    return {
                        'sentiment': float(kalshi_sentiment),
                        'source': 'Kalshi',
                        'confidence': 0.9  # Real money = highest confidence!
                    }
            except Exception as e:
                print(f"   ⚠️  Kalshi failed: {e}")
        
        # Try Metaculus (free, public data)
        print(f"   🎲 Trying Metaculus for {topic}...")
        try:
            metaculus_sentiment = self._fetch_metaculus_sentiment(topic)
            if metaculus_sentiment is not None:
                print(f"   ✅ Metaculus success! Sentiment: {metaculus_sentiment:.2f}")
                return {
                    'sentiment': float(metaculus_sentiment),
                    'source': 'Metaculus',
                    'confidence': 0.8
                }
        except Exception as e:
            print(f"   ⚠️  Metaculus failed: {e}")
        
        # Fallback: Synthetic sentiment
        print(f"   🎲 Using synthetic sentiment for {topic}...")
        seed = sum(ord(c) for c in topic)
        np.random.seed(seed)
        sentiment = np.random.beta(5, 5)  # Centered around 0.5
        
        return {
            'sentiment': float(sentiment),
            'source': 'Synthetic',
            'confidence': 0.5
        }
    
    def _fetch_kalshi_sentiment(self, topic: str) -> Optional[float]:
        """
        Fetch prediction from Kalshi (REAL MONEY markets - BEST signal!)
        
        Requires $100 minimum account: https://kalshi.com/
        API docs: https://docs.kalshi.com/
        
        Real money markets provide the strongest prediction signals!
        Confidence: 0.9 (highest of all sources)
        
        Note: Kalshi API has NO text search - we map topics to series_ticker
        """
        # Map common topics to Kalshi series tickers (updated Nov 2025)
        TOPIC_TO_SERIES = {
            'stock market': 'INX',  # S&P 500
            'stock_market': 'INX',  # Handle underscore version
            'sp500': 'INX',
            's&p 500': 'INX',
            's&p': 'INX',
            'economy': 'RECESSION',  # Recession predictions
            'recession': 'RECESSION',
            'unemployment': 'UNEMP',
            'inflation': 'CPI',
            'interest rate': 'FED',
            'interest_rate': 'FED',  # Handle underscore
            'fed': 'FED',
            'federal reserve': 'FED',
            'federal_reserve': 'FED',  # Handle underscore
            'bitcoin': 'KXBTC',
            'crypto': 'KXBTC',
            'election': 'PRES',  # Presidential/political
            'president': 'PRES',
        }
        
        # Step 1: Authenticate (email/password login)
        auth_url = "https://trading-api.kalshi.com/trade-api/v2/login"
        auth_headers = {
            "accept": "application/json",
            "content-type": "application/json"
        }
        auth_payload = {
            'email': self.kalshi_api_key,  # Your Kalshi email
            'password': self.kalshi_api_secret  # Your Kalshi password
        }
        
        # Get bearer token (expires in 30 min)
        auth_response = requests.post(
            auth_url,
            headers=auth_headers,
            json=auth_payload,
            timeout=10
        )
        auth_data = auth_response.json()
        
        if 'token' not in auth_data:
            raise ValueError(f"Kalshi auth failed: {auth_data}")
        
        token = auth_data['token']
        
        # Step 2: Normalize and find series_ticker for topic
        # Normalize: lowercase, replace underscores/dashes with spaces
        topic_normalized = topic.lower().replace('_', ' ').replace('-', ' ').strip()
        series_ticker = None
        
        # Check exact topic match
        if topic_normalized in TOPIC_TO_SERIES:
            series_ticker = TOPIC_TO_SERIES[topic_normalized]
        elif topic.lower() in TOPIC_TO_SERIES:  # Try original (for "stock_market")
            series_ticker = TOPIC_TO_SERIES[topic.lower()]
        else:
            # Check if any key phrase appears in normalized topic
            for key, series in TOPIC_TO_SERIES.items():
                if key in topic_normalized:
                    series_ticker = series
                    break
        
        # Build markets URL with series filter if available
        if series_ticker:
            search_url = f"https://trading-api.kalshi.com/trade-api/v2/markets?series_ticker={series_ticker}&status=open&limit=100"
        else:
            # Fallback: get all open markets (up to 1000)
            search_url = f"https://trading-api.kalshi.com/trade-api/v2/markets?limit=1000&status=open"
        
        headers = {
            "accept": "application/json",
            "Authorization": f"Bearer {token}"
        }
        
        markets_response = requests.get(search_url, headers=headers, timeout=10)
        markets_data = markets_response.json()
        
        if 'markets' not in markets_data or len(markets_data['markets']) == 0:
            return None
        
        # If we filtered by series_ticker, just use the first market
        # (already filtered to relevant series!)
        if series_ticker:
            best_market = markets_data['markets'][0]
        else:
            # No series filter - need keyword matching
            # Use NORMALIZED topic for keyword extraction!
            topic_keywords = [word for word in topic_normalized.split() if len(word) > 3]
            
            if not topic_keywords:
                # Fallback if no meaningful keywords
                topic_keywords = topic_normalized.split()
            
            best_market = None
            best_score = 0
            
            for market in markets_data['markets']:
                market_title = market.get('title', '').lower()
                market_ticker = market.get('ticker_name', '').lower()
                
                # Score based on keyword matches in title + ticker
                score = sum(1 for keyword in topic_keywords if keyword in market_title)
                score += sum(0.5 for keyword in topic_keywords if keyword in market_ticker)
                
                if score > best_score:
                    best_score = score
                    best_market = market
            
            # Only use market if we have at least one keyword match
            if not best_market or best_score == 0:
                # No relevant market found
                return None
        
        # Step 3: Extract probability from market prices
        # In prediction markets: price = probability (0-1 scale, often in cents)
        yes_ask = best_market.get('yes_ask')  # Ask price for YES outcome
        yes_bid = best_market.get('yes_bid')  # Bid price for YES outcome
        
        if yes_ask is not None and yes_bid is not None:
            # Use mid-price (average of bid/ask) for best estimate
            # Prices are in cents (0-100), convert to probability (0-1)
            mid_price = (yes_ask + yes_bid) / 2 / 100.0
            return mid_price
        elif yes_ask is not None:
            return yes_ask / 100.0
        elif yes_bid is not None:
            return yes_bid / 100.0
        
        return None
    
    def _fetch_metaculus_sentiment(self, topic: str) -> Optional[float]:
        """
        Fetch prediction from Metaculus (FREE, no API key!)
        
        Metaculus API structure (November 2025):
        - Predictions in: question['aggregations']['recency_weighted']['forecast_values']
        - For binary questions: [NO_probability, YES_probability]
        - Returns YES probability as sentiment (0-1 scale)
        """
        # Search for relevant open questions with actual predictions
        search_url = f"https://www.metaculus.com/api2/questions/?search={topic.replace(' ', '+')}&status=open&order_by=-activity&limit=5"
        
        try:
            response = requests.get(search_url, timeout=10)
            data = response.json()
            
            if not data.get('results'):
                return None
            
            # Try to find a question with actual aggregation data
            for result in data['results']:
                question_obj = result.get('question', {})
                
                # Check if it's a binary question
                if question_obj.get('type') != 'binary':
                    continue
                
                # Get aggregations
                aggregations = question_obj.get('aggregations', {})
                recency_weighted = aggregations.get('recency_weighted', {})
                latest = recency_weighted.get('latest')
                
                # If latest aggregation exists, use it
                if latest and 'forecast_values' in latest:
                    forecast_values = latest['forecast_values']
                    if len(forecast_values) >= 2:
                        # Return YES probability (second value)
                        return float(forecast_values[1])
                
                # Fallback: check forecast_values directly
                forecast_values = recency_weighted.get('forecast_values')
                if forecast_values and len(forecast_values) >= 2:
                    return float(forecast_values[1])
            
            return None
        except Exception as e:
            print(f"Metaculus error: {e}")
            return None
    
    def get_technical_indicators(
        self,
        prices: np.ndarray
    ) -> Dict[str, float]:
        """
        Calculate technical indicators
        
        Returns common indicators:
        - RSI (Relative Strength Index)
        - MACD (Moving Average Convergence Divergence)
        - Bollinger Bands
        """
        indicators = {}
        
        # RSI (14-period)
        if len(prices) >= 14:
            deltas = np.diff(prices)
            gains = np.where(deltas > 0, deltas, 0)
            losses = np.where(deltas < 0, -deltas, 0)
            
            avg_gain = np.mean(gains[-14:])
            avg_loss = np.mean(losses[-14:])
            
            if avg_loss > 0:
                rs = avg_gain / avg_loss
                rsi = 100 - (100 / (1 + rs))
            else:
                rsi = 100  # No losses = overbought
            
            indicators['RSI'] = float(rsi)
        
        # Moving averages
        if len(prices) >= 20:
            indicators['SMA_20'] = float(np.mean(prices[-20:]))
        
        if len(prices) >= 50:
            indicators['SMA_50'] = float(np.mean(prices[-50:]))
        
        # Bollinger Bands (20-period, 2 std dev)
        if len(prices) >= 20:
            sma = np.mean(prices[-20:])
            std = np.std(prices[-20:])
            indicators['BB_upper'] = float(sma + 2 * std)
            indicators['BB_lower'] = float(sma - 2 * std)
            indicators['BB_width'] = float(4 * std / sma)  # Normalized
        
        return indicators


# ============================================================================
# PRACTICAL MARKET SIGNALS (D4)
# ============================================================================

class PracticalMarketSignals:
    """
    Conventional technical analysis signals
    
    Complements TI algorithms with proven strategies:
    - Trend detection (moving averages)
    - Volatility analysis (Bollinger Bands)
    - Momentum (RSI, MACD)
    """
    
    @staticmethod
    def detect_trend(prices: np.ndarray) -> Dict:
        """
        Detect market trend using moving averages
        
        Returns trend classification and strength
        """
        if len(prices) < 50:
            return {
                'signal': 'HOLD',
                'confidence': 0.5,
                'explanation': 'Insufficient data for trend detection'
            }
        
        # Calculate moving averages
        sma_20 = np.mean(prices[-20:])
        sma_50 = np.mean(prices[-50:])
        current_price = prices[-1]
        
        # Trend logic
        if current_price > sma_20 > sma_50:
            # Strong uptrend
            strength = min(1.0, (current_price - sma_50) / sma_50 * 10)
            return {
                'signal': 'BUY',
                'confidence': float(strength),
                'explanation': f'Strong uptrend: Price ${current_price:.2f} > SMA20 ${sma_20:.2f} > SMA50 ${sma_50:.2f}'
            }
        elif current_price < sma_20 < sma_50:
            # Strong downtrend
            strength = min(1.0, (sma_50 - current_price) / sma_50 * 10)
            return {
                'signal': 'SELL',
                'confidence': float(strength),
                'explanation': f'Strong downtrend: Price ${current_price:.2f} < SMA20 ${sma_20:.2f} < SMA50 ${sma_50:.2f}'
            }
        else:
            # Mixed/sideways
            return {
                'signal': 'HOLD',
                'confidence': 0.6,
                'explanation': 'Mixed signals: Sideways market detected'
            }
    
    @staticmethod
    def analyze_volatility(prices: np.ndarray) -> Dict:
        """
        Analyze market volatility using Bollinger Bands
        
        Returns volatility assessment and trading signal
        """
        if len(prices) < 20:
            return {
                'signal': 'HOLD',
                'confidence': 0.5,
                'explanation': 'Insufficient data for volatility analysis'
            }
        
        # Bollinger Bands (20-period, 2 std dev)
        sma = np.mean(prices[-20:])
        std = np.std(prices[-20:])
        upper = sma + 2 * std
        lower = sma - 2 * std
        current = prices[-1]
        
        # Band width (normalized volatility)
        band_width = (upper - lower) / sma
        
        if current >= upper:
            # Price at upper band → Overbought
            return {
                'signal': 'SELL',
                'confidence': 0.7,
                'explanation': f'Overbought: Price ${current:.2f} at upper Bollinger Band ${upper:.2f}'
            }
        elif current <= lower:
            # Price at lower band → Oversold
            return {
                'signal': 'BUY',
                'confidence': 0.7,
                'explanation': f'Oversold: Price ${current:.2f} at lower Bollinger Band ${lower:.2f}'
            }
        elif band_width > 0.1:
            # High volatility → Caution
            return {
                'signal': 'HEDGE',
                'confidence': 0.8,
                'explanation': f'High volatility detected (band width {band_width:.2%})'
            }
        else:
            # Low volatility → Consolidation
            return {
                'signal': 'HOLD',
                'confidence': 0.6,
                'explanation': 'Low volatility: Market consolidating'
            }
    
    @staticmethod
    def check_momentum(prices: np.ndarray) -> Dict:
        """
        Check momentum using RSI
        
        Returns momentum signal
        """
        if len(prices) < 15:
            return {
                'signal': 'HOLD',
                'confidence': 0.5,
                'explanation': 'Insufficient data for RSI'
            }
        
        # Calculate RSI
        deltas = np.diff(prices[-15:])
        gains = np.where(deltas > 0, deltas, 0)
        losses = np.where(deltas < 0, -deltas, 0)
        
        avg_gain = np.mean(gains)
        avg_loss = np.mean(losses)
        
        if avg_loss > 0:
            rs = avg_gain / avg_loss
            rsi = 100 - (100 / (1 + rs))
        else:
            rsi = 100
        
        # RSI interpretation
        if rsi > 70:
            return {
                'signal': 'SELL',
                'confidence': min(1.0, (rsi - 70) / 30),
                'explanation': f'Overbought: RSI {rsi:.1f} > 70'
            }
        elif rsi < 30:
            return {
                'signal': 'BUY',
                'confidence': min(1.0, (30 - rsi) / 30),
                'explanation': f'Oversold: RSI {rsi:.1f} < 30'
            }
        else:
            return {
                'signal': 'HOLD',
                'confidence': 0.5,
                'explanation': f'Neutral momentum: RSI {rsi:.1f}'
            }


# ============================================================================
# GILE SCORING SYSTEM (D5)
# ============================================================================

class GILEMarketScoring:
    """
    GILE Framework for Market Condition Assessment
    
    Scores market based on 4 dimensions of truth:
    - G (Goodness): Market fairness, low manipulation
    - I (Intuition): Pattern clarity, predictability
    - L (Love): Positive sentiment, constructive growth
    - E (Environment): External factors, macro conditions
    """
    
    @staticmethod
    def score_goodness(
        prices: np.ndarray,
        volumes: np.ndarray
    ) -> float:
        """
        Goodness = Market fairness & integrity
        
        High goodness:
        - Smooth price action (low manipulation)
        - Normal volume patterns
        - No flash crashes or pumps
        
        Returns score 0-1
        """
        # Check for abnormal price jumps (manipulation indicator)
        returns = np.diff(prices) / prices[:-1]
        abnormal_moves = np.sum(np.abs(returns) > 0.05)  # >5% moves
        manipulation_score = 1 - min(1.0, abnormal_moves / len(returns))
        
        # Check volume consistency
        volume_cv = np.std(volumes) / (np.mean(volumes) + 1e-10)  # Coefficient of variation
        volume_score = 1 - min(1.0, volume_cv)
        
        goodness = (manipulation_score + volume_score) / 2
        return float(goodness)
    
    @staticmethod
    def score_intuition(
        prices: np.ndarray
    ) -> float:
        """
        Intuition = Pattern clarity & predictability
        
        High intuition:
        - Clear trends
        - Recognizable patterns
        - Low noise
        
        Returns score 0-1
        """
        # Trend strength (R² of linear regression)
        x = np.arange(len(prices))
        coeffs = np.polyfit(x, prices, 1)
        trend_line = coeffs[0] * x + coeffs[1]
        
        ss_res = np.sum((prices - trend_line) ** 2)
        ss_tot = np.sum((prices - np.mean(prices)) ** 2)
        
        r_squared = 1 - (ss_res / (ss_tot + 1e-10))
        
        # Clip to 0-1
        intuition = float(np.clip(r_squared, 0, 1))
        return intuition
    
    @staticmethod
    def score_love(
        prices: np.ndarray
    ) -> float:
        """
        Love = Positive sentiment & constructive growth
        
        High love:
        - Upward trend (wealth creation)
        - Sustainable growth rate
        - Helping investors succeed
        
        Returns score 0-1
        """
        # Overall return
        total_return = (prices[-1] - prices[0]) / prices[0]
        
        # Positive growth gets high love score
        # 10% gain = 0.75, 20% gain = 1.0
        love = float(np.clip(0.5 + total_return * 2.5, 0, 1))
        
        return love
    
    @staticmethod
    def score_environment(
        sentiment: float = 0.5
    ) -> float:
        """
        Environment = External macro conditions
        
        High environment score:
        - Favorable economic conditions
        - Positive crowd wisdom
        - Supportive regulatory climate
        
        Args:
            sentiment: Prediction market sentiment (0-1)
        
        Returns score 0-1
        """
        # For now, use sentiment as proxy
        # In production, would incorporate macro indicators
        return float(sentiment)
    
    @staticmethod
    def calculate_gile_score(
        prices: np.ndarray,
        volumes: np.ndarray,
        sentiment: float = 0.5
    ) -> Dict:
        """
        Calculate comprehensive GILE score for market
        
        Returns all 4 dimensions + composite score
        """
        G = GILEMarketScoring.score_goodness(prices, volumes)
        I = GILEMarketScoring.score_intuition(prices)
        L = GILEMarketScoring.score_love(prices)
        E = GILEMarketScoring.score_environment(sentiment)
        
        # Composite GILE score (weighted average)
        # Weight: G=0.3, I=0.25, L=0.25, E=0.2
        composite = 0.3 * G + 0.25 * I + 0.25 * L + 0.2 * E
        
        # Interpretation
        if composite > 0.8:
            quality = "EXCELLENT"
            action = "High confidence trading environment"
        elif composite > 0.6:
            quality = "GOOD"
            action = "Favorable conditions for trading"
        elif composite > 0.4:
            quality = "FAIR"
            action = "Proceed with caution"
        else:
            quality = "POOR"
            action = "Avoid trading or use defensive strategies"
        
        return {
            'G_goodness': float(G),
            'I_intuition': float(I),
            'L_love': float(L),
            'E_environment': float(E),
            'composite_score': float(composite),
            'market_quality': quality,
            'recommendation': action
        }


# ============================================================================
# EXAMPLE USAGE
# ============================================================================

def example_usage():
    """Demonstrate D3-D5 integration"""
    print("=" * 70)
    print("GOD MACHINE - MARKET DATA INTEGRATION & PRACTICAL SIGNALS")
    print("=" * 70)
    
    # D3: Get market data
    data_api = MarketDataIntegration(use_live_data=False)
    prices, volumes = data_api.get_stock_data("SPY", days=50)
    
    print(f"\n✅ D3 - Market Data Retrieved:")
    print(f"   Ticker: SPY")
    print(f"   Days: 50")
    print(f"   Current Price: ${prices[-1]:.2f}")
    print(f"   Price Range: ${prices.min():.2f} - ${prices.max():.2f}")
    
    # D4: Practical signals
    signals = PracticalMarketSignals()
    trend_signal = signals.detect_trend(prices)
    volatility_signal = signals.analyze_volatility(prices)
    momentum_signal = signals.check_momentum(prices)
    
    print(f"\n✅ D4 - Practical Signals:")
    print(f"   Trend: {trend_signal['signal']} ({trend_signal['confidence']:.0%})")
    print(f"          {trend_signal['explanation']}")
    print(f"   Volatility: {volatility_signal['signal']} ({volatility_signal['confidence']:.0%})")
    print(f"               {volatility_signal['explanation']}")
    print(f"   Momentum: {momentum_signal['signal']} ({momentum_signal['confidence']:.0%})")
    print(f"             {momentum_signal['explanation']}")
    
    # D5: GILE scoring
    gile = GILEMarketScoring()
    gile_score = gile.calculate_gile_score(prices, volumes)
    
    print(f"\n✅ D5 - GILE Market Quality Score:")
    print(f"   G (Goodness):    {gile_score['G_goodness']:.3f}")
    print(f"   I (Intuition):   {gile_score['I_intuition']:.3f}")
    print(f"   L (Love):        {gile_score['L_love']:.3f}")
    print(f"   E (Environment): {gile_score['E_environment']:.3f}")
    print(f"   Composite:       {gile_score['composite_score']:.3f} - {gile_score['market_quality']}")
    print(f"   Recommendation:  {gile_score['recommendation']}")
    
    print("\n" + "=" * 70)


if __name__ == "__main__":
    example_usage()

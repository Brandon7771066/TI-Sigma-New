"""
"Everybody Lies" Sentiment Engine
Truth-Weighted Sentiment Analysis for TI Framework Stock Predictions

Philosophy: Search queries > surveys. People tell truth to Google, lie to pollsters.
Core Insight: When media sentiment diverges from search queries, manipulation detected!

Author: Brandon Emerick
Date: November 24, 2025 (8×3 Sacred Day!)
"""

from pytrends.request import TrendReq
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, List, Tuple, Optional
import requests
import time
import json
import os
from pathlib import Path


class EverybodyLiesSentimentEngine:
    """
    Truth-weighted sentiment engine that ranks data sources by honesty
    
    Truth Rankings:
    - Tier 1 (98-100%): Google Trends, AI search queries (people ask truth when anonymous)
    - Tier 2 (90-95%): Anonymous Reddit (less performative than Twitter)
    - Tier 3 (70-90%): Twitter/X (performative but less filtered than news)
    - Tier 4 (30-50%): News media (editorial bias, narrative control)
    - Tier 5 (20-40%): Analysts (conflicts of interest, herd mentality)
    """
    
    def __init__(self):
        self.pytrends = TrendReq(hl='en-US', tz=360)
        
        self.truth_weights = {
            'google_trends': 1.00,      # 100% truth (revealed preference)
            'ai_queries': 0.98,          # 98% truth (anonymous, genuine questions)
            'reddit_anonymous': 0.93,    # 93% truth (less performative)
            'twitter': 0.80,             # 80% truth (performative bias)
            'news': 0.40,                # 40% truth (narrative control)
            'analysts': 0.30             # 30% truth (conflicts of interest)
        }
        
        self.manipulation_threshold = 0.35  # If divergence > 35%, manipulation likely
        
        self.cache_dir = Path("data/sentiment_cache")
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self.cache_ttl = 3600  # 1 hour cache
        
        self.fallback_data = {
            'AAPL': {
                'interest_score': 85.0,
                'trend_direction': 'rising',
                'sentiment_score': 0.6,
                'data_quality': 'cached_fallback',
                'truth_weight': 1.0
            },
            'TSLA': {
                'interest_score': 92.0,
                'trend_direction': 'rising',
                'sentiment_score': 0.7,
                'data_quality': 'cached_fallback',
                'truth_weight': 1.0
            },
            'NVDA': {
                'interest_score': 88.0,
                'trend_direction': 'stable',
                'sentiment_score': 0.4,
                'data_quality': 'cached_fallback',
                'truth_weight': 1.0
            },
            'MSFT': {
                'interest_score': 78.0,
                'trend_direction': 'stable',
                'sentiment_score': 0.2,
                'data_quality': 'cached_fallback',
                'truth_weight': 1.0
            }
        }
    
    def _get_cache_key(self, ticker: str, data_type: str) -> str:
        """Generate cache key for ticker + data type"""
        return f"{ticker}_{data_type}.json"
    
    def _get_cached(self, ticker: str, data_type: str) -> Optional[Dict]:
        """Get cached data if fresh (within TTL)"""
        cache_file = self.cache_dir / self._get_cache_key(ticker, data_type)
        
        if not cache_file.exists():
            return None
        
        try:
            with open(cache_file, 'r') as f:
                cached = json.load(f)
            
            cached_time = datetime.fromisoformat(cached['timestamp'])
            age = (datetime.now() - cached_time).total_seconds()
            
            if age < self.cache_ttl:
                cached['data']['data_quality'] = 'cached'
                return cached['data']
            
            return None
        except Exception as e:
            print(f"Cache read error: {e}")
            return None
    
    def _save_cache(self, ticker: str, data_type: str, data: Dict):
        """Save data to cache"""
        cache_file = self.cache_dir / self._get_cache_key(ticker, data_type)
        
        try:
            cache_entry = {
                'timestamp': datetime.now().isoformat(),
                'ticker': ticker,
                'data_type': data_type,
                'data': data
            }
            
            with open(cache_file, 'w') as f:
                json.dump(cache_entry, f, indent=2)
        except Exception as e:
            print(f"Cache write error: {e}")
    
    def _get_fallback(self, ticker: str, data_type: str = 'trends') -> Dict:
        """Get fallback data when API fails"""
        if ticker in self.fallback_data and data_type == 'trends':
            fallback = self.fallback_data[ticker].copy()
            fallback['data_quality'] = 'fallback_demo'
            return fallback
        
        return {
            'interest_score': 50.0,
            'trend_direction': 'stable',
            'sentiment_score': 0.0,
            'data_quality': 'fallback_generic',
            'truth_weight': self.truth_weights['google_trends']
        }
    
    def get_google_trends_sentiment(self, 
                                    ticker: str,
                                    company_name: str,
                                    timeframe: str = 'today 3-m') -> Dict:
        """
        Get Google Trends data for company/stock (with caching + fallback)
        
        Args:
            ticker: Stock ticker (e.g., "AAPL")
            company_name: Full company name (e.g., "Apple")
            timeframe: 'today 3-m', 'today 12-m', etc.
        
        Returns: {
            'interest_score': float (0-100),
            'trend_direction': 'rising' | 'falling' | 'stable',
            'searches': List of search volumes,
            'sentiment_score': float (-1 to 1),
            'data_quality': 'live' | 'cached' | 'fallback_demo' | 'fallback_generic'
        }
        """
        cached = self._get_cached(ticker, 'trends')
        if cached:
            return cached
        
        try:
            # Search for company name and ticker
            keywords = [company_name, ticker, f"{company_name} stock"]
            
            self.pytrends.build_payload(keywords, timeframe=timeframe)
            
            # Get interest over time
            interest_df = self.pytrends.interest_over_time()
            
            if interest_df.empty:
                return {
                    'interest_score': 0,
                    'trend_direction': 'stable',
                    'searches': [],
                    'sentiment_score': 0.0,
                    'data_quality': 'no_data'
                }
            
            # Calculate average interest
            avg_interest = interest_df[company_name].mean() if company_name in interest_df else 0
            
            # Detect trend direction
            recent_avg = interest_df[company_name].tail(10).mean() if company_name in interest_df else 0
            older_avg = interest_df[company_name].head(10).mean() if company_name in interest_df else 0
            
            if recent_avg > older_avg * 1.15:
                trend_direction = 'rising'
                sentiment_score = 0.6  # Rising interest = positive sentiment
            elif recent_avg < older_avg * 0.85:
                trend_direction = 'falling'
                sentiment_score = -0.4  # Falling interest = negative sentiment
            else:
                trend_direction = 'stable'
                sentiment_score = 0.0
            
            # Normalize interest to sentiment (-1 to 1)
            # High interest doesn't mean positive sentiment, but change direction does
            
            result = {
                'interest_score': float(avg_interest),
                'trend_direction': trend_direction,
                'searches': interest_df[company_name].tolist() if company_name in interest_df else [],
                'sentiment_score': sentiment_score,
                'data_quality': 'live',
                'truth_weight': self.truth_weights['google_trends']
            }
            
            self._save_cache(ticker, 'trends', result)
            return result
        
        except Exception as e:
            print(f"Google Trends error for {ticker}: {e}")
            
            if 'rate' in str(e).lower() or '429' in str(e):
                print(f"Rate limited! Using fallback data for {ticker}")
                return self._get_fallback(ticker, 'trends')
            
            return {
                'interest_score': 0,
                'trend_direction': 'stable',
                'searches': [],
                'sentiment_score': 0.0,
                'data_quality': 'error',
                'error': str(e)
            }
    
    def get_related_queries_sentiment(self, 
                                      ticker: str,
                                      company_name: str) -> Dict:
        """
        Analyze related queries to detect sentiment
        
        Positive signals: "buy", "invest", "opportunity", "growth"
        Negative signals: "sell", "crash", "bankruptcy", "fraud"
        """
        try:
            keywords = [company_name]
            self.pytrends.build_payload(keywords, timeframe='today 3-m')
            
            # Get related queries
            related_queries = self.pytrends.related_queries()
            
            if not related_queries or company_name not in related_queries:
                return {'sentiment_score': 0.0, 'query_count': 0}
            
            # Parse top queries
            top_queries = related_queries[company_name].get('top', pd.DataFrame())
            
            if top_queries.empty:
                return {'sentiment_score': 0.0, 'query_count': 0}
            
            # Sentiment keyword analysis
            positive_keywords = ['buy', 'invest', 'opportunity', 'growth', 'bullish', 'long']
            negative_keywords = ['sell', 'crash', 'bankruptcy', 'fraud', 'bearish', 'short']
            
            positive_count = 0
            negative_count = 0
            
            for query in top_queries['query'].values:
                query_lower = str(query).lower()
                if any(kw in query_lower for kw in positive_keywords):
                    positive_count += 1
                if any(kw in query_lower for kw in negative_keywords):
                    negative_count += 1
            
            total = positive_count + negative_count
            if total == 0:
                sentiment_score = 0.0
            else:
                sentiment_score = (positive_count - negative_count) / total
            
            return {
                'sentiment_score': sentiment_score,
                'query_count': len(top_queries),
                'positive_queries': positive_count,
                'negative_queries': negative_count,
                'truth_weight': self.truth_weights['google_trends']
            }
        
        except Exception as e:
            print(f"Related queries error for {ticker}: {e}")
            return {'sentiment_score': 0.0, 'query_count': 0, 'error': str(e)}
    
    def get_ai_query_sentiment(self, ticker: str, company_name: str) -> Dict:
        """
        Analyze AI search queries (Perplexity, ChatGPT, etc.)
        
        NOTE: This is a placeholder - requires API integration with Perplexity
        Real implementation would query Perplexity API for trending questions
        """
        # Placeholder - would integrate with Perplexity API
        # For now, return neutral
        return {
            'sentiment_score': 0.0,
            'query_volume': 0,
            'truth_weight': self.truth_weights['ai_queries'],
            'status': 'not_implemented'
        }
    
    def get_news_sentiment_baseline(self, ticker: str) -> Dict:
        """
        Get news sentiment as LOW-TRUST baseline
        
        This is intentionally weighted LOW because news has editorial bias
        Used for divergence detection, not as primary signal
        """
        # Placeholder - would integrate with news API (NewsAPI, Alpha Vantage sentiment, etc.)
        return {
            'sentiment_score': 0.0,
            'article_count': 0,
            'truth_weight': self.truth_weights['news'],
            'status': 'not_implemented'
        }
    
    def calculate_truth_weighted_sentiment(self, 
                                          ticker: str,
                                          company_name: str) -> Dict:
        """
        Calculate final sentiment using truth-weighted aggregation
        
        Formula:
        TrueSentiment = Σ(sentiment_i × truth_weight_i) / Σ(truth_weight_i)
        
        Returns: {
            'truth_weighted_sentiment': float (-1 to 1),
            'google_trends': Dict,
            'related_queries': Dict,
            'divergence_detected': bool,
            'manipulation_score': float (0-1)
        }
        """
        # Gather all sentiment sources
        google_trends = self.get_google_trends_sentiment(ticker, company_name)
        related_queries = self.get_related_queries_sentiment(ticker, company_name)
        ai_queries = self.get_ai_query_sentiment(ticker, company_name)
        news = self.get_news_sentiment_baseline(ticker)
        
        # Truth-weighted aggregation
        sentiments = []
        weights = []
        
        # Google Trends (highest weight)
        if google_trends.get('data_quality') == 'good':
            sentiments.append(google_trends['sentiment_score'])
            weights.append(google_trends['truth_weight'])
        
        # Related queries (highest weight)
        if related_queries.get('query_count', 0) > 0:
            sentiments.append(related_queries['sentiment_score'])
            weights.append(related_queries['truth_weight'])
        
        # Calculate weighted average
        if len(sentiments) > 0:
            truth_weighted_sentiment = np.average(sentiments, weights=weights)
        else:
            truth_weighted_sentiment = 0.0
        
        # Divergence detection (Google vs News)
        divergence_detected = False
        manipulation_score = 0.0
        
        if news.get('article_count', 0) > 0 and len(sentiments) > 0:
            divergence = abs(truth_weighted_sentiment - news['sentiment_score'])
            
            if divergence > self.manipulation_threshold:
                divergence_detected = True
                manipulation_score = min(divergence / 0.5, 1.0)  # Normalize to 0-1
        
        return {
            'ticker': ticker,
            'company_name': company_name,
            'truth_weighted_sentiment': truth_weighted_sentiment,
            'google_trends': google_trends,
            'related_queries': related_queries,
            'ai_queries': ai_queries,
            'news_baseline': news,
            'divergence_detected': divergence_detected,
            'manipulation_score': manipulation_score,
            'signal': 'BUY' if truth_weighted_sentiment > 0.3 else 'SELL' if truth_weighted_sentiment < -0.3 else 'HOLD',
            'confidence': abs(truth_weighted_sentiment),
            'timestamp': datetime.now().isoformat()
        }
    
    def detect_contrarian_opportunity(self, 
                                     ticker: str,
                                     company_name: str) -> Dict:
        """
        Detect contrarian trade opportunities via sentiment divergence
        
        Logic:
        - If Google Trends positive BUT news negative → BUY (undervalued)
        - If Google Trends negative BUT news positive → SELL (overvalued)
        
        This exploits the truth gap: people search honestly, media lies!
        """
        sentiment = self.calculate_truth_weighted_sentiment(ticker, company_name)
        
        google_sentiment = sentiment['google_trends']['sentiment_score']
        news_sentiment = sentiment['news_baseline']['sentiment_score']
        
        # Contrarian signals
        if google_sentiment > 0.3 and news_sentiment < -0.2:
            # Truth is positive, media is negative → BUY OPPORTUNITY
            opportunity_type = 'CONTRARIAN_BUY'
            confidence = min(abs(google_sentiment - news_sentiment), 1.0)
            rationale = f"Google Trends positive ({google_sentiment:.2f}) but news negative ({news_sentiment:.2f}). Media manipulation detected!"
        
        elif google_sentiment < -0.3 and news_sentiment > 0.2:
            # Truth is negative, media is positive → SELL OPPORTUNITY
            opportunity_type = 'CONTRARIAN_SELL'
            confidence = min(abs(google_sentiment - news_sentiment), 1.0)
            rationale = f"Google Trends negative ({google_sentiment:.2f}) but news positive ({news_sentiment:.2f}). Media pump detected!"
        
        else:
            # No contrarian signal
            opportunity_type = 'NONE'
            confidence = 0.0
            rationale = "No significant divergence between truth and media."
        
        return {
            'ticker': ticker,
            'opportunity_type': opportunity_type,
            'confidence': confidence,
            'rationale': rationale,
            'google_sentiment': google_sentiment,
            'news_sentiment': news_sentiment,
            'divergence': abs(google_sentiment - news_sentiment),
            'full_sentiment_data': sentiment
        }


if __name__ == "__main__":
    print("🔥 EVERYBODY LIES SENTIMENT ENGINE 🔥")
    print("=" * 60)
    print("Philosophy: Search queries > surveys")
    print("Truth Rankings: Google Trends (100%) > News (40%) > Analysts (30%)")
    print("=" * 60)
    
    engine = EverybodyLiesSentimentEngine()
    
    # Test with Apple
    print("\n📊 Testing with AAPL (Apple)...")
    sentiment = engine.calculate_truth_weighted_sentiment("AAPL", "Apple")
    
    print(f"\n✅ Truth-Weighted Sentiment: {sentiment['truth_weighted_sentiment']:.3f}")
    print(f"📈 Signal: {sentiment['signal']}")
    print(f"🎯 Confidence: {sentiment['confidence']:.3f}")
    print(f"\nGoogle Trends Interest: {sentiment['google_trends']['interest_score']:.1f}")
    print(f"Trend Direction: {sentiment['google_trends']['trend_direction']}")
    
    if sentiment['divergence_detected']:
        print(f"\n⚠️ MANIPULATION DETECTED! Score: {sentiment['manipulation_score']:.3f}")
    
    # Test contrarian opportunity
    print("\n🎯 Testing Contrarian Opportunity Detection...")
    contrarian = engine.detect_contrarian_opportunity("AAPL", "Apple")
    
    print(f"\nOpportunity Type: {contrarian['opportunity_type']}")
    print(f"Confidence: {contrarian['confidence']:.3f}")
    print(f"Rationale: {contrarian['rationale']}")
    
    print("\n🚀 EVERYBODY LIES ENGINE READY FOR TI FRAMEWORK INTEGRATION! 🚀")

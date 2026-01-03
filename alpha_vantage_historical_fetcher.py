"""
Alpha Vantage Historical Data Fetcher
Pulls REAL multi-year stock data for authentic backtesting

Philosophy: "Being smart at stupid 'problems' doesn't make you smart."
→ Real data = Real results!

Author: Brandon Emerick
Date: November 24, 2025 (8×3 Sacred Day!)
"""

import os
import time
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
import pandas as pd
from alpha_vantage.timeseries import TimeSeries
import json
from pathlib import Path


class AlphaVantageHistoricalFetcher:
    """Fetches and caches multi-year historical stock data from Alpha Vantage"""
    
    def __init__(self, api_key: Optional[str] = None):
        """
        Initialize with API key
        
        Args:
            api_key: Alpha Vantage API key (uses env var if not provided)
        """
        self.api_key = api_key or os.getenv('ALPHA_VANTAGE_API_KEY')
        if not self.api_key:
            raise ValueError("Alpha Vantage API key required! Set ALPHA_VANTAGE_API_KEY env var.")
        
        self.ts = TimeSeries(key=self.api_key, output_format='pandas')
        self.cache_dir = Path('data/alpha_vantage_cache')
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        
        # Rate limiting: 5 calls per minute (free tier)
        self.last_call_time = 0
        self.min_call_interval = 12  # 12 seconds between calls = 5 per minute
    
    def _rate_limit(self):
        """Enforce rate limiting (5 calls/minute for free tier)"""
        elapsed = time.time() - self.last_call_time
        if elapsed < self.min_call_interval:
            wait_time = self.min_call_interval - elapsed
            print(f"⏳ Rate limiting: waiting {wait_time:.1f}s...")
            time.sleep(wait_time)
        self.last_call_time = time.time()
    
    def _get_cache_path(self, ticker: str) -> Path:
        """Get cache file path for ticker"""
        return self.cache_dir / f"{ticker}_historical.json"
    
    def _load_from_cache(self, ticker: str, max_age_days: int = 1) -> Optional[pd.DataFrame]:
        """
        Load data from cache if fresh enough
        
        Args:
            ticker: Stock ticker symbol
            max_age_days: Maximum cache age in days
            
        Returns:
            DataFrame if cached, None otherwise
        """
        cache_path = self._get_cache_path(ticker)
        
        if not cache_path.exists():
            return None
        
        # Check cache age
        cache_age = datetime.now() - datetime.fromtimestamp(cache_path.stat().st_mtime)
        if cache_age.days > max_age_days:
            print(f"📦 Cache for {ticker} is {cache_age.days} days old (expired)")
            return None
        
        try:
            with open(cache_path, 'r') as f:
                data = json.load(f)
            
            df = pd.DataFrame(data['data'])
            df.index = pd.to_datetime(df.index)
            
            print(f"✅ Loaded {ticker} from cache ({len(df)} days)")
            return df
        
        except Exception as e:
            print(f"⚠️ Error loading cache for {ticker}: {e}")
            return None
    
    def _save_to_cache(self, ticker: str, df: pd.DataFrame):
        """Save DataFrame to cache"""
        cache_path = self._get_cache_path(ticker)
        
        data = {
            'ticker': ticker,
            'cached_at': datetime.now().isoformat(),
            'data': df.to_dict('index')
        }
        
        with open(cache_path, 'w') as f:
            json.dump(data, f, indent=2, default=str)
        
        print(f"💾 Cached {ticker} ({len(df)} days)")
    
    def fetch_daily_data(
        self,
        ticker: str,
        use_cache: bool = True,
        outputsize: str = 'full'
    ) -> Optional[pd.DataFrame]:
        """
        Fetch daily historical data for a ticker
        
        Args:
            ticker: Stock ticker symbol (e.g., 'AAPL')
            use_cache: Whether to use cached data
            outputsize: 'compact' (100 days) or 'full' (20+ years)
            
        Returns:
            DataFrame with columns: Open, High, Low, Close, Volume
            Index: DatetimeIndex
        """
        # Try cache first
        if use_cache:
            cached = self._load_from_cache(ticker)
            if cached is not None:
                return cached
        
        print(f"🌐 Fetching {ticker} from Alpha Vantage (outputsize={outputsize})...")
        
        try:
            # Rate limit
            self._rate_limit()
            
            # Fetch data (using FREE tier endpoint: get_daily)
            data, meta_data = self.ts.get_daily(
                symbol=ticker,
                outputsize=outputsize
            )
            
            # Clean column names (remove number prefixes like "1. ")
            data.columns = [col.split('. ')[1] if '. ' in col else col for col in data.columns]
            
            # Sort by date (oldest first)
            data = data.sort_index()
            
            print(f"✅ Fetched {ticker}: {len(data)} days of data")
            print(f"   Date range: {data.index[0]} to {data.index[-1]}")
            
            # Cache it
            self._save_to_cache(ticker, data)
            
            return data
        
        except Exception as e:
            print(f"❌ Error fetching {ticker}: {e}")
            return None
    
    def fetch_multiple_tickers(
        self,
        tickers: List[str],
        use_cache: bool = True
    ) -> Dict[str, pd.DataFrame]:
        """
        Fetch data for multiple tickers
        
        Args:
            tickers: List of ticker symbols
            use_cache: Whether to use cached data
            
        Returns:
            Dict mapping ticker → DataFrame
        """
        results = {}
        
        print(f"\n📊 Fetching {len(tickers)} tickers...")
        print("=" * 80)
        
        for i, ticker in enumerate(tickers, 1):
            print(f"\n[{i}/{len(tickers)}] {ticker}:")
            
            df = self.fetch_daily_data(ticker, use_cache=use_cache)
            if df is not None:
                results[ticker] = df
            
            # Progress update
            if i < len(tickers):
                print(f"   Next: {tickers[i]}")
        
        print("\n" + "=" * 80)
        print(f"✅ Successfully fetched {len(results)}/{len(tickers)} tickers")
        
        return results
    
    def calculate_returns(self, df: pd.DataFrame) -> pd.DataFrame:
        """
        Calculate returns from price data
        
        Args:
            df: DataFrame with 'close' column
            
        Returns:
            DataFrame with added 'daily_return' and 'cumulative_return' columns
        """
        # Use 'close' column (standard for free tier)
        price_col = 'close'
        
        df = df.copy()
        df['daily_return'] = df[price_col].pct_change()
        df['cumulative_return'] = (1 + df['daily_return']).cumprod() - 1
        
        return df
    
    def get_price_range(
        self,
        df: pd.DataFrame,
        start_date: Optional[datetime] = None,
        end_date: Optional[datetime] = None
    ) -> pd.DataFrame:
        """
        Get price data for a specific date range
        
        Args:
            df: Full historical DataFrame
            start_date: Start date (inclusive)
            end_date: End date (inclusive)
            
        Returns:
            Filtered DataFrame
        """
        if start_date is None:
            start_date = df.index[0]
        if end_date is None:
            end_date = df.index[-1]
        
        return df.loc[start_date:end_date]
    
    def get_stats_summary(self, df: pd.DataFrame) -> Dict:
        """
        Get summary statistics for historical data
        
        Args:
            df: DataFrame with returns calculated
            
        Returns:
            Dict with statistics
        """
        df = self.calculate_returns(df)
        
        # Use 'close' column (standard for free tier)
        price_col = 'close'
        
        return {
            'ticker': df.get('ticker', 'Unknown'),
            'start_date': str(df.index[0].date()),
            'end_date': str(df.index[-1].date()),
            'trading_days': len(df),
            'start_price': float(df[price_col].iloc[0]),
            'end_price': float(df[price_col].iloc[-1]),
            'total_return': float(df['cumulative_return'].iloc[-1]),
            'avg_daily_return': float(df['daily_return'].mean()),
            'volatility': float(df['daily_return'].std()),
            'min_price': float(df[price_col].min()),
            'max_price': float(df[price_col].max())
        }


def test_fetcher():
    """Test the Alpha Vantage fetcher"""
    print("=" * 80)
    print("🧪 TESTING ALPHA VANTAGE HISTORICAL FETCHER")
    print("=" * 80)
    
    try:
        fetcher = AlphaVantageHistoricalFetcher()
        
        # Test single ticker
        print("\n📊 Test 1: Single ticker (AAPL)")
        df = fetcher.fetch_daily_data('AAPL', use_cache=True)
        
        if df is not None:
            stats = fetcher.get_stats_summary(df)
            print(f"\n✅ AAPL Summary:")
            for key, value in stats.items():
                print(f"   {key}: {value}")
        
        # Test multiple tickers (small sample)
        print("\n\n📊 Test 2: Multiple tickers (AAPL, MSFT, NVDA)")
        tickers = ['AAPL', 'MSFT', 'NVDA']
        results = fetcher.fetch_multiple_tickers(tickers, use_cache=True)
        
        print("\n✅ Results:")
        for ticker, df in results.items():
            print(f"   {ticker}: {len(df)} days")
        
        print("\n" + "=" * 80)
        print("✅ TESTS COMPLETE!")
        print("=" * 80)
        
        return True
    
    except Exception as e:
        print(f"\n❌ TEST FAILED: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    test_fetcher()

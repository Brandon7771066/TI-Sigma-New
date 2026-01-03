"""
Yahoo Finance Historical Data Fetcher
Pulls REAL multi-year stock data (20+ years, FREE!)

Philosophy: "Being smart at stupid 'problems' doesn't make you smart."
→ Real data = Real results, NO premium fees!

Author: Brandon Emerick
Date: November 24, 2025 (8×3 Sacred Day!)
"""

import yfinance as yf
import pandas as pd
import json
from pathlib import Path
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple
import time


class YahooFinanceHistoricalFetcher:
    """Fetches and caches multi-year historical stock data from Yahoo Finance (FREE!)"""
    
    def __init__(self):
        """Initialize fetcher"""
        self.cache_dir = Path('data/yahoo_finance_cache')
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        
        # Rate limiting: Be nice to Yahoo servers
        self.last_call_time = 0
        self.min_call_interval = 0.5  # 500ms between calls
    
    def _rate_limit(self):
        """Enforce rate limiting to be nice to Yahoo servers"""
        elapsed = time.time() - self.last_call_time
        if elapsed < self.min_call_interval:
            wait_time = self.min_call_interval - elapsed
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
            DataFrame if cached and fresh, None otherwise
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
            
            # Convert back to DataFrame
            df = pd.DataFrame(data['data'])
            df.index = pd.to_datetime(df.index)
            df = df.sort_index()
            
            print(f"✅ Loaded {ticker} from cache ({len(df)} days, {data['period']})")
            return df
        
        except Exception as e:
            print(f"⚠️ Error loading cache for {ticker}: {e}")
            return None
    
    def _save_to_cache(self, ticker: str, df: pd.DataFrame, period: str):
        """Save DataFrame to cache"""
        cache_path = self._get_cache_path(ticker)
        
        # Convert index to string for JSON serialization
        df_to_save = df.copy()
        df_to_save.index = df_to_save.index.astype(str)
        
        data = {
            'ticker': ticker,
            'period': period,
            'cached_at': datetime.now().isoformat(),
            'data': df_to_save.to_dict('index')
        }
        
        with open(cache_path, 'w') as f:
            json.dump(data, f, indent=2)
        
        print(f"💾 Cached {ticker} ({len(df)} days, {period})")
    
    def fetch_historical_data(
        self,
        ticker: str,
        period: str = '5y',
        interval: str = '1d',
        use_cache: bool = True
    ) -> Optional[pd.DataFrame]:
        """
        Fetch historical data from Yahoo Finance
        
        Args:
            ticker: Stock ticker symbol (e.g., 'AAPL')
            period: Time period - '1d', '5d', '1mo', '3mo', '6mo', '1y', '2y', '5y', '10y', 'ytd', 'max'
            interval: Data interval - '1d' (daily), '1wk' (weekly), '1mo' (monthly)
            use_cache: Whether to use cached data
            
        Returns:
            DataFrame with columns: Open, High, Low, Close, Volume, Dividends, Stock Splits
            Index: DatetimeIndex
        """
        # Try cache first
        if use_cache:
            cached = self._load_from_cache(ticker)
            if cached is not None:
                return cached
        
        print(f"🌐 Fetching {ticker} from Yahoo Finance (period={period})...")
        
        try:
            # Rate limit
            self._rate_limit()
            
            # Fetch data using yfinance
            stock = yf.Ticker(ticker)
            data = stock.history(period=period, interval=interval)
            
            if data.empty:
                print(f"❌ No data returned for {ticker}")
                return None
            
            # Clean column names (lowercase)
            data.columns = [col.lower().replace(' ', '_') for col in data.columns]
            
            # Sort by date (oldest first)
            data = data.sort_index()
            
            print(f"✅ Fetched {ticker}: {len(data)} days of data")
            print(f"   Date range: {str(data.index[0])[:10]} to {str(data.index[-1])[:10]}")
            print(f"   Latest close: ${data['close'].iloc[-1]:.2f}")
            
            # Cache it
            self._save_to_cache(ticker, data, period)
            
            return data
        
        except Exception as e:
            print(f"❌ Error fetching {ticker}: {e}")
            return None
    
    def fetch_multiple_tickers(
        self,
        tickers: List[str],
        period: str = '5y',
        use_cache: bool = True
    ) -> Dict[str, pd.DataFrame]:
        """
        Fetch data for multiple tickers
        
        Args:
            tickers: List of ticker symbols
            period: Time period for historical data
            use_cache: Whether to use cached data
            
        Returns:
            Dict mapping ticker → DataFrame
        """
        results = {}
        
        print(f"\n📊 Fetching {len(tickers)} tickers (period: {period})...")
        print("=" * 80)
        
        for i, ticker in enumerate(tickers, 1):
            print(f"\n[{i}/{len(tickers)}] {ticker}:")
            
            df = self.fetch_historical_data(ticker, period=period, use_cache=use_cache)
            if df is not None:
                results[ticker] = df
            
            # Progress update
            if i < len(tickers):
                remaining = len(tickers) - i
                print(f"   Remaining: {remaining} ticker{'s' if remaining > 1 else ''}")
        
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
        df = df.copy()
        df['daily_return'] = df['close'].pct_change()
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
            start_date = pd.Timestamp(df.index[0]).to_pydatetime()
        if end_date is None:
            end_date = pd.Timestamp(df.index[-1]).to_pydatetime()
        
        return df.loc[start_date:end_date]
    
    def get_stats_summary(self, ticker: str, df: pd.DataFrame) -> Dict:
        """
        Get summary statistics for historical data
        
        Args:
            ticker: Stock ticker symbol
            df: DataFrame with price data
            
        Returns:
            Dict with statistics
        """
        df = self.calculate_returns(df)
        
        # Calculate annualized metrics
        trading_days_per_year = 252
        years = len(df) / trading_days_per_year
        
        total_return = df['cumulative_return'].iloc[-1]
        annualized_return = (1 + total_return) ** (1 / years) - 1
        annualized_volatility = df['daily_return'].std() * (trading_days_per_year ** 0.5)
        
        # Sharpe ratio (assuming 4% risk-free rate)
        risk_free_rate = 0.04
        sharpe = (annualized_return - risk_free_rate) / annualized_volatility if annualized_volatility > 0 else 0
        
        # Max drawdown
        cumulative = (1 + df['daily_return']).cumprod()
        running_max = cumulative.cummax()
        drawdown = (cumulative - running_max) / running_max
        max_drawdown = drawdown.min()
        
        return {
            'ticker': ticker,
            'start_date': str(df.index[0])[:10],
            'end_date': str(df.index[-1])[:10],
            'trading_days': len(df),
            'years': round(years, 2),
            'start_price': float(df['close'].iloc[0]),
            'end_price': float(df['close'].iloc[-1]),
            'total_return_pct': round(total_return * 100, 2),
            'annualized_return_pct': round(annualized_return * 100, 2),
            'annualized_volatility_pct': round(annualized_volatility * 100, 2),
            'sharpe_ratio': round(sharpe, 2),
            'max_drawdown_pct': round(max_drawdown * 100, 2),
            'avg_daily_return_pct': round(df['daily_return'].mean() * 100, 4),
            'min_price': float(df['close'].min()),
            'max_price': float(df['close'].max())
        }


def test_fetcher():
    """Test the Yahoo Finance fetcher"""
    print("=" * 80)
    print("🧪 TESTING YAHOO FINANCE HISTORICAL FETCHER")
    print("=" * 80)
    print("✨ FREE multi-year data with NO API key required!")
    
    try:
        fetcher = YahooFinanceHistoricalFetcher()
        
        # Test single ticker
        print("\n📊 Test 1: Single ticker (AAPL, 5 years)")
        df = fetcher.fetch_historical_data('AAPL', period='5y', use_cache=True)
        
        if df is not None:
            stats = fetcher.get_stats_summary('AAPL', df)
            print(f"\n✅ AAPL Summary ({stats['years']} years):")
            print(f"   Total Return: {stats['total_return_pct']:.2f}%")
            print(f"   Annualized Return: {stats['annualized_return_pct']:.2f}%")
            print(f"   Annualized Volatility: {stats['annualized_volatility_pct']:.2f}%")
            print(f"   Sharpe Ratio: {stats['sharpe_ratio']:.2f}")
            print(f"   Max Drawdown: {stats['max_drawdown_pct']:.2f}%")
        
        # Test multiple tickers
        print("\n\n📊 Test 2: Multiple tickers (AAPL, TSLA, NVDA) - 3 years")
        tickers = ['AAPL', 'TSLA', 'NVDA']
        results = fetcher.fetch_multiple_tickers(tickers, period='3y', use_cache=True)
        
        print("\n✅ Multi-Ticker Results:")
        for ticker, df in results.items():
            stats = fetcher.get_stats_summary(ticker, df)
            print(f"\n   {ticker}:")
            print(f"      Return: {stats['total_return_pct']:.1f}% ({stats['years']} years)")
            print(f"      Sharpe: {stats['sharpe_ratio']:.2f}")
        
        print("\n" + "=" * 80)
        print("✅ TESTS COMPLETE! Yahoo Finance working perfectly!")
        print("💰 FREE multi-year data - NO premium fees!")
        print("=" * 80)
        
        return True
    
    except Exception as e:
        print(f"\n❌ TEST FAILED: {e}")
        import traceback
        traceback.print_exc()
        return False


if __name__ == "__main__":
    test_fetcher()

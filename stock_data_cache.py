"""
Stock Data Ingestion & Caching Layer
Handles Alpha Vantage API calls with persistent caching
"""

import os
import json
import requests
from datetime import datetime, timedelta
from typing import Dict, List, Optional
from pathlib import Path
import pandas as pd

class StockDataCache:
    """
    Manages stock data retrieval with caching to avoid redundant API calls
    """
    
    def __init__(self, cache_dir: str = "data/stock_history"):
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self.api_key = os.environ.get('ALPHA_VANTAGE_API_KEY')
        
    def get_historical_data(
        self, 
        ticker: str, 
        start_date: datetime, 
        end_date: datetime,
        force_refresh: bool = False
    ) -> pd.DataFrame:
        """
        Get historical stock data with caching
        
        Args:
            ticker: Stock symbol
            start_date: Start date for data
            end_date: End date for data
            force_refresh: Force API call even if cached
        
        Returns:
            DataFrame with columns: date, open, high, low, close, volume
        """
        cache_file = self.cache_dir / f"{ticker}_daily.json"
        
        # Try to load from cache first
        if cache_file.exists() and not force_refresh:
            cached_data = self._load_cache(cache_file)
            if cached_data:
                df = pd.DataFrame(cached_data)
                df['date'] = pd.to_datetime(df['date'])
                
                # Filter to requested date range
                mask = (df['date'] >= start_date) & (df['date'] <= end_date)
                filtered = df.loc[mask].copy()
                
                if not filtered.empty:
                    print(f"✅ Loaded {ticker} from cache ({len(filtered)} days)")
                    return filtered.sort_values('date').reset_index(drop=True)
        
        # Fetch from API
        print(f"📡 Fetching {ticker} from Alpha Vantage API...")
        api_data = self._fetch_from_api(ticker)
        
        if api_data:
            # Save to cache
            self._save_cache(cache_file, api_data)
            
            # Convert to DataFrame and filter
            df = pd.DataFrame(api_data)
            df['date'] = pd.to_datetime(df['date'])
            mask = (df['date'] >= start_date) & (df['date'] <= end_date)
            return df.loc[mask].sort_values('date').reset_index(drop=True)
        else:
            # Return mock data if API fails
            print(f"⚠️ API failed for {ticker}, using mock data")
            return self._generate_mock_data(ticker, start_date, end_date)
    
    def get_sp500_benchmark(
        self, 
        start_date: datetime, 
        end_date: datetime
    ) -> pd.DataFrame:
        """
        Get S&P 500 index data as benchmark
        Uses SPY ETF as proxy
        """
        return self.get_historical_data('SPY', start_date, end_date)
    
    def calculate_returns(
        self, 
        df: pd.DataFrame, 
        initial_investment: float = 100.0
    ) -> pd.DataFrame:
        """
        Calculate cumulative returns from price data
        
        Args:
            df: DataFrame with 'close' prices
            initial_investment: Starting capital
        
        Returns:
            DataFrame with added 'portfolio_value' column
        """
        df = df.copy()
        df['daily_return'] = df['close'].pct_change()
        df['cumulative_return'] = (1 + df['daily_return']).cumprod()
        df['portfolio_value'] = initial_investment * df['cumulative_return']
        return df
    
    def _fetch_from_api(self, ticker: str) -> List[Dict]:
        """Fetch data from Alpha Vantage API"""
        if not self.api_key:
            return None
        
        try:
            # Free tier: outputsize=compact returns last 100 days (no "full" allowed)
            url = f'https://www.alphavantage.co/query?function=TIME_SERIES_DAILY&symbol={ticker}&apikey={self.api_key}'
            response = requests.get(url, timeout=15)
            data = response.json()
            
            if 'Time Series (Daily)' not in data:
                error_msg = data.get('Note', data.get('Information', data.get('Error Message', 'Unknown')))
                print(f"⚠️ API error for {ticker}: {error_msg}")
                return None
            
            # Convert to list of dicts
            time_series = data['Time Series (Daily)']
            records = []
            
            for date_str, price_data in time_series.items():
                records.append({
                    'date': date_str,
                    'open': float(price_data['1. open']),
                    'high': float(price_data['2. high']),
                    'low': float(price_data['3. low']),
                    'close': float(price_data['4. close']),
                    'volume': int(price_data['5. volume'])
                })
            
            return records
        
        except Exception as e:
            print(f"❌ API fetch error for {ticker}: {e}")
            return None
    
    def _load_cache(self, cache_file: Path) -> Optional[List[Dict]]:
        """Load data from cache file"""
        try:
            with open(cache_file, 'r') as f:
                return json.load(f)
        except Exception as e:
            print(f"⚠️ Cache load error: {e}")
            return None
    
    def _save_cache(self, cache_file: Path, data: List[Dict]):
        """Save data to cache file"""
        try:
            with open(cache_file, 'w') as f:
                json.dump(data, f, indent=2)
            print(f"💾 Cached data to {cache_file}")
        except Exception as e:
            print(f"⚠️ Cache save error: {e}")
    
    def _generate_mock_data(
        self, 
        ticker: str, 
        start_date: datetime, 
        end_date: datetime
    ) -> pd.DataFrame:
        """Generate realistic mock data using random walk"""
        import random
        
        dates = pd.date_range(start=start_date, end=end_date, freq='D')
        # Filter to business days only
        dates = dates[dates.weekday < 5]
        
        base_price = 100.0
        data = []
        
        for date in dates:
            # Random walk with realistic drift and volatility
            daily_return = random.gauss(0.0005, 0.015)  # 0.05% drift, 1.5% vol
            base_price *= (1 + daily_return)
            
            daily_vol = random.uniform(0.005, 0.015)
            
            data.append({
                'date': date,
                'open': base_price * (1 - daily_vol),
                'high': base_price * (1 + daily_vol),
                'low': base_price * (1 - daily_vol * 1.2),
                'close': base_price,
                'volume': random.randint(1_000_000, 10_000_000)
            })
        
        return pd.DataFrame(data)

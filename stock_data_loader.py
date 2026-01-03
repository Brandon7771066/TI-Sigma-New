"""
Stock Data Loader with Deterministic Fixtures
Gracefully falls back to demo data when API keys are unavailable

Author: Brandon Emerick
Date: November 24, 2025 (8×3 Sacred Day!)
"""

import json
import os
from pathlib import Path
from typing import Dict, Optional
from datetime import datetime


class StockDataLoader:
    """Load stock data from API or deterministic fixtures"""
    
    def __init__(self):
        self.fixtures_path = Path("data/stock_fixtures/demo_stocks.json")
        self.fixtures = self._load_fixtures()
        self.has_api_key = self._check_api_key()
    
    def _load_fixtures(self) -> Dict:
        """Load deterministic demo data"""
        if not self.fixtures_path.exists():
            return {}
        
        try:
            with open(self.fixtures_path, 'r') as f:
                return json.load(f)
        except Exception as e:
            print(f"Warning: Could not load fixtures: {e}")
            return {}
    
    def _check_api_key(self) -> bool:
        """Check if Alpha Vantage API key exists"""
        key = os.getenv('ALPHA_VANTAGE_API_KEY', '')
        return key != '' and key != 'your_api_key_here'
    
    def get_gile_metadata(self, ticker: str) -> Optional[Dict]:
        """
        Get GILE metadata ONLY (company name, sector, GILE score, prediction)
        Does NOT fetch price data - use Yahoo Finance for that!
        
        Args:
            ticker: Stock ticker symbol (e.g., 'AAPL')
            
        Returns:
            Dict with GILE metadata or None if not in fixtures
        """
        return self._get_from_fixtures(ticker)
    
    def get_stock_data(self, ticker: str, source: str = 'auto') -> Optional[Dict]:
        """
        Get stock data from API or fixtures
        
        DEPRECATED: Use get_gile_metadata() for GILE scores + Yahoo Finance for prices!
        
        Args:
            ticker: Stock ticker (e.g., "AAPL")
            source: 'api' | 'fixtures' | 'auto' (default: auto)
        
        Returns:
            Stock data dict or None if not found
        """
        if source == 'fixtures' or (source == 'auto' and not self.has_api_key):
            return self._get_from_fixtures(ticker)
        
        if source == 'api' or (source == 'auto' and self.has_api_key):
            try:
                return self._get_from_api(ticker)
            except Exception as e:
                print(f"API error for {ticker}: {e}")
                print(f"Falling back to fixtures...")
                return self._get_from_fixtures(ticker)
        
        return None
    
    def _get_from_fixtures(self, ticker: str) -> Optional[Dict]:
        """Get stock data from fixtures"""
        if ticker in self.fixtures:
            data = self.fixtures[ticker].copy()
            data['data_source'] = 'fixture'
            data['is_demo'] = True
            return data
        
        return None
    
    def _get_from_api(self, ticker: str) -> Optional[Dict]:
        """
        Get stock data from Alpha Vantage API
        
        NOTE: This is a placeholder. Real implementation would use:
        - Alpha Vantage for price/fundamentals
        - Glassdoor API for employee satisfaction
        - News API for sentiment
        """
        api_key = os.getenv('ALPHA_VANTAGE_API_KEY')
        
        if not api_key:
            raise ValueError("ALPHA_VANTAGE_API_KEY not found")
        
        raise NotImplementedError("Live API integration coming soon!")
    
    def get_available_tickers(self) -> list:
        """Get list of available demo tickers"""
        return list(self.fixtures.keys())
    
    def print_status(self):
        """Print data source status"""
        print("\n🔍 STOCK DATA LOADER STATUS 🔍")
        print("=" * 60)
        print(f"API Key Available: {'✅ YES' if self.has_api_key else '❌ NO (using fixtures)'}")
        print(f"Fixtures Loaded: {len(self.fixtures)} tickers")
        print(f"Available Tickers: {', '.join(self.get_available_tickers())}")
        print("=" * 60)


if __name__ == "__main__":
    loader = StockDataLoader()
    loader.print_status()
    
    print("\n📊 Testing Stock Data Loader...")
    
    for ticker in ['AAPL', 'TSLA', 'NVDA']:
        print(f"\n{ticker}:")
        data = loader.get_stock_data(ticker)
        
        if data:
            print(f"  Company: {data.get('company_name')}")
            print(f"  Price: ${data.get('price'):.2f}")
            print(f"  GILE Score: {data.get('gile_score'):.3f}")
            print(f"  Prediction: {data.get('prediction')}")
            print(f"  Confidence: {data.get('confidence'):.1%}")
            print(f"  Data Source: {data.get('data_source', 'unknown')}")
        else:
            print(f"  ❌ No data available")
    
    print("\n✅ STOCK DATA LOADER READY!")

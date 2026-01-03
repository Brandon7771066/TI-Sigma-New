"""
Alpha Vantage API Integration for God Machine
Fetches real-time financial data to power GILE/UOP/GTFE/LCC calculations
"""

import os
import requests
from datetime import datetime, timedelta
import time
from typing import Dict, Optional, List
from tenacity import retry, stop_after_attempt, wait_exponential

class AlphaVantageClient:
    """
    Alpha Vantage API client for fetching real-time stock data
    """
    
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key or os.getenv('ALPHA_VANTAGE_API_KEY')
        self.base_url = "https://www.alphavantage.co/query"
        self.cache = {}
        self.cache_duration = 300
        
    @retry(stop=stop_after_attempt(3), wait=wait_exponential(multiplier=1, min=2, max=10))
    def _make_request(self, params: Dict) -> Dict:
        """Make API request with retry logic"""
        params['apikey'] = self.api_key
        response = requests.get(self.base_url, params=params, timeout=30)
        response.raise_for_status()
        data = response.json()
        
        if 'Error Message' in data:
            raise ValueError(f"API Error: {data['Error Message']}")
        if 'Note' in data:
            raise ValueError(f"API Rate Limit: {data['Note']}")
            
        return data
    
    def get_quote(self, symbol: str) -> Optional[Dict]:
        """
        Get real-time quote data for a symbol
        
        Returns: {
            'price': float,
            'change': float,
            'change_percent': float,
            'volume': int,
            'latest_trading_day': str,
            'previous_close': float,
            'open': float,
            'high': float,
            'low': float
        }
        """
        cache_key = f"quote_{symbol}"
        if cache_key in self.cache:
            cached_time, cached_data = self.cache[cache_key]
            if time.time() - cached_time < self.cache_duration:
                return cached_data
        
        try:
            params = {
                'function': 'GLOBAL_QUOTE',
                'symbol': symbol
            }
            data = self._make_request(params)
            
            if 'Global Quote' not in data or not data['Global Quote']:
                return None
            
            quote = data['Global Quote']
            result = {
                'price': float(quote.get('05. price', 0)),
                'change': float(quote.get('09. change', 0)),
                'change_percent': float(quote.get('10. change percent', '0%').rstrip('%')),
                'volume': int(quote.get('06. volume', 0)),
                'latest_trading_day': quote.get('07. latest trading day', ''),
                'previous_close': float(quote.get('08. previous close', 0)),
                'open': float(quote.get('02. open', 0)),
                'high': float(quote.get('03. high', 0)),
                'low': float(quote.get('04. low', 0))
            }
            
            self.cache[cache_key] = (time.time(), result)
            return result
            
        except Exception as e:
            print(f"Error fetching quote for {symbol}: {e}")
            return None
    
    def get_company_overview(self, symbol: str) -> Optional[Dict]:
        """
        Get fundamental company data
        
        Returns extensive fundamental data including:
        - MarketCapitalization
        - PERatio, PEGRatio
        - BookValue, DividendYield
        - ProfitMargin, OperatingMarginTTM
        - ReturnOnAssetsTTM, ReturnOnEquityTTM
        - RevenueTTM, GrossProfitTTM
        - QuarterlyRevenueGrowthYOY, QuarterlyEarningsGrowthYOY
        - Beta (volatility)
        - 52WeekHigh, 52WeekLow
        """
        cache_key = f"overview_{symbol}"
        if cache_key in self.cache:
            cached_time, cached_data = self.cache[cache_key]
            if time.time() - cached_time < self.cache_duration:
                return cached_data
        
        try:
            params = {
                'function': 'OVERVIEW',
                'symbol': symbol
            }
            data = self._make_request(params)
            
            if not data or 'Symbol' not in data:
                return None
            
            self.cache[cache_key] = (time.time(), data)
            return data
            
        except Exception as e:
            print(f"Error fetching overview for {symbol}: {e}")
            return None
    
    def get_rsi(self, symbol: str, interval: str = 'daily', time_period: int = 14) -> Optional[float]:
        """
        Get Relative Strength Index (momentum indicator)
        Values: 0-100 (>70 = overbought, <30 = oversold)
        """
        try:
            params = {
                'function': 'RSI',
                'symbol': symbol,
                'interval': interval,
                'time_period': time_period,
                'series_type': 'close'
            }
            data = self._make_request(params)
            
            if 'Technical Analysis: RSI' not in data:
                return None
            
            rsi_data = data['Technical Analysis: RSI']
            latest_date = sorted(rsi_data.keys(), reverse=True)[0]
            rsi_value = float(rsi_data[latest_date]['RSI'])
            
            return rsi_value
            
        except Exception as e:
            print(f"Error fetching RSI for {symbol}: {e}")
            return None
    
    def get_sma(self, symbol: str, interval: str = 'daily', time_period: int = 50) -> Optional[float]:
        """
        Get Simple Moving Average
        """
        try:
            params = {
                'function': 'SMA',
                'symbol': symbol,
                'interval': interval,
                'time_period': time_period,
                'series_type': 'close'
            }
            data = self._make_request(params)
            
            if 'Technical Analysis: SMA' not in data:
                return None
            
            sma_data = data['Technical Analysis: SMA']
            latest_date = sorted(sma_data.keys(), reverse=True)[0]
            sma_value = float(sma_data[latest_date]['SMA'])
            
            return sma_value
            
        except Exception as e:
            print(f"Error fetching SMA for {symbol}: {e}")
            return None


class TIFinancialAnalyzer:
    """
    Converts Alpha Vantage financial data into TI Framework metrics
    Maps real market data to GILE/UOP/GTFE/LCC scores
    """
    
    def __init__(self, alpha_vantage_key: Optional[str] = None):
        self.av_client = AlphaVantageClient(alpha_vantage_key)
    
    def calculate_gile_from_financials(self, symbol: str) -> Dict:
        """
        Calculate GILE components from real financial data
        
        GILE Mapping:
        - G (Goodness): Profitability, ethical practices, ESG alignment
        - I (Intuition): Market position, innovation, adaptability
        - L (Love): Customer satisfaction, employee welfare, brand loyalty
        - E (Environment): Sustainability, environmental impact, systemic health
        
        Returns: {
            'gile_score': float (0.0 to 1.0),
            'G': float,
            'I': float,
            'L': float,
            'E': float,
            'confidence': float (0.0 to 1.0)
        }
        """
        quote = self.av_client.get_quote(symbol)
        overview = self.av_client.get_company_overview(symbol)
        
        if not quote or not overview:
            return {
                'gile_score': 0.5,
                'G': 0.5,
                'I': 0.5,
                'L': 0.5,
                'E': 0.5,
                'confidence': 0.0,
                'data_source': 'heuristic_fallback'
            }
        
        def safe_float(value, default=0.0):
            """Convert to float with fallback"""
            try:
                if value == 'None' or value is None or value == '':
                    return default
                return float(value)
            except (ValueError, TypeError):
                return default
        
        profit_margin = safe_float(overview.get('ProfitMargin'), 0.0)
        roe = safe_float(overview.get('ReturnOnEquityTTM'), 0.0)
        revenue_growth = safe_float(overview.get('QuarterlyRevenueGrowthYOY'), 0.0)
        pe_ratio = safe_float(overview.get('PERatio'), 15.0)
        beta = safe_float(overview.get('Beta'), 1.0)
        
        G = min(1.0, max(0.0, (profit_margin + 0.1) / 0.3 * 0.5 + (roe + 0.1) / 0.4 * 0.5))
        
        I = min(1.0, max(0.0, (revenue_growth + 0.1) / 0.3 * 0.6 + (1.0 / (1.0 + abs(beta - 1.0))) * 0.4))
        
        price_momentum = quote['change_percent'] / 10.0
        L = min(1.0, max(0.0, 0.5 + price_momentum / 10.0))
        
        sector = overview.get('Sector', '')
        if any(s in sector.lower() for s in ['technology', 'healthcare', 'renewable']):
            E = 0.7
        elif any(s in sector.lower() for s in ['energy', 'utilities']):
            E = 0.5
        else:
            E = 0.6
        
        gile_score = (G + I + L + E) / 4.0
        
        data_completeness = sum([
            1 if profit_margin != 0 else 0,
            1 if roe != 0 else 0,
            1 if revenue_growth != 0 else 0,
            1 if pe_ratio != 15 else 0,
            1 if beta != 1 else 0
        ]) / 5.0
        
        return {
            'gile_score': gile_score,
            'G': G,
            'I': I,
            'L': L,
            'E': E,
            'confidence': data_completeness,
            'data_source': 'alpha_vantage',
            'financials': {
                'profit_margin': profit_margin,
                'roe': roe,
                'revenue_growth': revenue_growth,
                'pe_ratio': pe_ratio,
                'beta': beta
            }
        }
    
    def calculate_uop(self, symbol: str) -> float:
        """
        Universal Optimization Potential (UOP)
        Measures upside potential relative to current position
        """
        quote = self.av_client.get_quote(symbol)
        overview = self.av_client.get_company_overview(symbol)
        
        if not quote or not overview:
            return 0.5
        
        def safe_float(value, default=0.0):
            try:
                if value == 'None' or value is None or value == '':
                    return default
                return float(value)
            except (ValueError, TypeError):
                return default
        
        week_52_high = safe_float(overview.get('52WeekHigh'), quote['price'])
        week_52_low = safe_float(overview.get('52WeekLow'), quote['price'])
        current_price = quote['price']
        
        if week_52_high <= week_52_low:
            return 0.5
        
        position_in_range = (current_price - week_52_low) / (week_52_high - week_52_low)
        
        uop = 1.0 - position_in_range
        
        return max(0.0, min(1.0, uop))
    
    def calculate_gtfe(self, symbol: str) -> float:
        """
        Grand Tralse Flow Energy (GTFE)
        Market momentum and energy flow indicator
        """
        rsi = self.av_client.get_rsi(symbol)
        quote = self.av_client.get_quote(symbol)
        
        if not rsi or not quote:
            return 0.5
        
        rsi_energy = rsi / 100.0
        
        momentum_energy = (quote['change_percent'] + 10) / 20.0
        momentum_energy = max(0.0, min(1.0, momentum_energy))
        
        gtfe = (rsi_energy * 0.6 + momentum_energy * 0.4)
        
        return gtfe
    
    def calculate_lcc(self, symbol: str) -> float:
        """
        Living Consciousness Coherence (LCC)
        Collective coherence score for the company i-web
        """
        gile_data = self.calculate_gile_from_financials(symbol)
        overview = self.av_client.get_company_overview(symbol)
        
        if not overview:
            return 0.5
        
        def safe_float(value, default=0.0):
            try:
                if value == 'None' or value is None or value == '':
                    return default
                return float(value)
            except (ValueError, TypeError):
                return default
        
        market_cap = safe_float(overview.get('MarketCapitalization'), 0)
        
        size_coherence = min(1.0, market_cap / 1e12)
        
        gile_coherence = gile_data['gile_score']
        
        lcc = (size_coherence * 0.3 + gile_coherence * 0.7)
        
        return lcc


if __name__ == "__main__":
    analyzer = TIFinancialAnalyzer()
    
    test_symbols = ['AAPL', 'TSLA', 'MSFT']
    for symbol in test_symbols:
        print(f"\n=== {symbol} ===")
        gile = analyzer.calculate_gile_from_financials(symbol)
        print(f"GILE: {gile['gile_score']:.3f} (G:{gile['G']:.2f}, I:{gile['I']:.2f}, L:{gile['L']:.2f}, E:{gile['E']:.2f})")
        print(f"UOP: {analyzer.calculate_uop(symbol):.3f}")
        print(f"GTFE: {analyzer.calculate_gtfe(symbol):.3f}")
        print(f"LCC: {analyzer.calculate_lcc(symbol):.3f}")

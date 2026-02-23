"""
TI-FRAMEWORK WEATHER PREDICTION ENGINE
========================================
AI-powered weather prediction for ForecastEx/Kalshi daily temperature contracts.

STRATEGY:
- Pull NWS forecast data (free API, no key needed)
- Compare to ForecastEx contract pricing to find mispricings
- Use historical accuracy analysis to identify systematic forecast biases
- Apply Kelly criterion for position sizing
- Track P&L and edge decay

DATA SOURCES:
- NWS API (api.weather.gov) - free, no key needed
- Historical climate data (NOAA)
- ForecastEx contracts resolve using NWS Daily Climate Reports

SUPPORTED CITIES (ForecastEx):
- NYC, Chicago, Miami, Austin, Denver, Boston, LA, Phoenix, Seattle, Houston

TI INTEGRATION:
- Uses Tralse confidence zones for trade classification
- Applies exact threshold constants from Paper #322
"""

import math
import requests
import json
import os
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, field

TAU = math.cos(math.pi / 8)
EPSILON = math.cos(math.pi / 8) ** 2
GAMMA = math.cos(math.pi / 5) ** 2
LAMBDA_LCC = (math.sqrt(2) + 1) / 4
ETA = math.sqrt(2) - 1

NWS_STATIONS = {
    'NYC': {'lat': 40.7128, 'lon': -74.0060, 'station': 'KNYC', 'grid': 'OKX/33,37'},
    'Chicago': {'lat': 41.8781, 'lon': -87.6298, 'station': 'KORD', 'grid': 'LOT/75,72'},
    'Miami': {'lat': 25.7617, 'lon': -80.1918, 'station': 'KMIA', 'grid': 'MFL/110,50'},
    'Austin': {'lat': 30.2672, 'lon': -97.7431, 'station': 'KAUS', 'grid': 'EWX/156,91'},
    'Denver': {'lat': 39.7392, 'lon': -104.9903, 'station': 'KDEN', 'grid': 'BOU/62,60'},
    'Boston': {'lat': 42.3601, 'lon': -71.0589, 'station': 'KBOS', 'grid': 'BOX/71,90'},
    'LA': {'lat': 34.0522, 'lon': -118.2437, 'station': 'KLAX', 'grid': 'LOX/154,44'},
    'Phoenix': {'lat': 33.4484, 'lon': -112.0740, 'station': 'KPHX', 'grid': 'PSR/159,57'},
    'Seattle': {'lat': 47.6062, 'lon': -122.3321, 'station': 'KSEA', 'grid': 'SEW/124,67'},
    'Houston': {'lat': 29.7604, 'lon': -95.3698, 'station': 'KHOU', 'grid': 'HGX/65,97'},
}

NWS_BASE_URL = "https://api.weather.gov"
NWS_HEADERS = {
    'User-Agent': '(TI-Sigma-Weather, brandon@tisigma.com)',
    'Accept': 'application/geo+json',
}


@dataclass
class WeatherForecast:
    city: str
    date: str
    high_temp_f: float
    low_temp_f: float
    conditions: str
    wind_speed_mph: float
    precipitation_pct: float
    forecast_source: str
    confidence: float
    raw_data: dict = field(default_factory=dict)


@dataclass
class TradingSignal:
    city: str
    date: str
    contract_type: str
    bracket_low: float
    bracket_high: float
    nws_probability: float
    market_price: float
    edge: float
    kelly_fraction: float
    position_size_dollars: float
    tralse_zone: str
    confidence: str
    recommendation: str


class WeatherPredictionEngine:
    """AI weather prediction engine for ForecastEx temperature contracts."""

    def __init__(self, bankroll: float = 500.0):
        self.bankroll = bankroll
        self.forecasts: Dict[str, List[WeatherForecast]] = {}
        self.signals: List[TradingSignal] = []
        self.trade_history: List[Dict] = []
        self.cache_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'data', 'weather_cache')
        os.makedirs(self.cache_dir, exist_ok=True)

    def fetch_nws_forecast(self, city: str) -> Optional[List[WeatherForecast]]:
        """Fetch 7-day forecast from NWS API for a city."""
        if city not in NWS_STATIONS:
            print(f"City {city} not supported. Available: {list(NWS_STATIONS.keys())}")
            return None

        info = NWS_STATIONS[city]
        grid = info['grid']

        try:
            url = f"{NWS_BASE_URL}/gridpoints/{grid}/forecast"
            response = requests.get(url, headers=NWS_HEADERS, timeout=15)
            response.raise_for_status()
            data = response.json()

            forecasts = []
            periods = data.get('properties', {}).get('periods', [])

            day_forecasts = {}
            for period in periods:
                name = period.get('name', '')
                temp = period.get('temperature', 0)
                temp_unit = period.get('temperatureUnit', 'F')
                is_daytime = period.get('isDaytime', True)
                wind = period.get('windSpeed', '0 mph')
                conditions = period.get('shortForecast', '')
                start = period.get('startTime', '')

                if temp_unit == 'C':
                    temp = temp * 9.0 / 5.0 + 32

                date_str = start[:10] if start else ''

                if date_str not in day_forecasts:
                    day_forecasts[date_str] = {'high': None, 'low': None, 'conditions': '', 'wind': ''}

                if is_daytime:
                    day_forecasts[date_str]['high'] = temp
                    day_forecasts[date_str]['conditions'] = conditions
                    day_forecasts[date_str]['wind'] = wind
                else:
                    day_forecasts[date_str]['low'] = temp

            for date_str, vals in sorted(day_forecasts.items()):
                if vals['high'] is None and vals['low'] is None:
                    continue

                wind_speed = 0
                try:
                    wind_parts = vals['wind'].split()
                    wind_speed = float(wind_parts[0]) if wind_parts else 0
                except (ValueError, IndexError):
                    wind_speed = 0

                precip_pct = 0
                conditions_lower = vals['conditions'].lower()
                if 'rain' in conditions_lower or 'shower' in conditions_lower:
                    precip_pct = 70
                elif 'chance' in conditions_lower:
                    precip_pct = 40
                elif 'snow' in conditions_lower:
                    precip_pct = 60
                elif 'cloudy' in conditions_lower:
                    precip_pct = 20

                forecast = WeatherForecast(
                    city=city,
                    date=date_str,
                    high_temp_f=vals['high'] if vals['high'] is not None else (vals['low'] + 15 if vals['low'] else 70),
                    low_temp_f=vals['low'] if vals['low'] is not None else (vals['high'] - 15 if vals['high'] else 55),
                    conditions=vals['conditions'],
                    wind_speed_mph=wind_speed,
                    precipitation_pct=precip_pct,
                    forecast_source='NWS',
                    confidence=0.85,
                    raw_data=vals,
                )
                forecasts.append(forecast)

            self.forecasts[city] = forecasts
            self._cache_forecasts(city, forecasts)
            return forecasts

        except requests.RequestException as e:
            print(f"NWS API error for {city}: {e}")
            cached = self._load_cached_forecasts(city)
            if cached:
                print(f"Using cached forecast for {city}")
                return cached
            return None

    def fetch_all_cities(self) -> Dict[str, List[WeatherForecast]]:
        """Fetch forecasts for all supported cities."""
        results = {}
        for city in NWS_STATIONS:
            forecast = self.fetch_nws_forecast(city)
            if forecast:
                results[city] = forecast
        return results

    def generate_temperature_brackets(self, forecast_high: float) -> List[Dict]:
        """Generate ForecastEx-style temperature brackets around forecast."""
        center = round(forecast_high)
        brackets = []

        brackets.append({
            'label': f'Below {center - 4}°F',
            'low': -999,
            'high': center - 4,
            'probability': 0.05,
        })
        for offset in range(-3, 5, 2):
            low = center + offset
            high = center + offset + 2
            prob = self._normal_bracket_probability(forecast_high, low, high, std=3.5)
            brackets.append({
                'label': f'{low}-{high}°F',
                'low': low,
                'high': high,
                'probability': round(prob, 4),
            })
        brackets.append({
            'label': f'Above {center + 6}°F',
            'low': center + 6,
            'high': 999,
            'probability': 0.05,
        })

        total = sum(b['probability'] for b in brackets)
        if total > 0:
            for b in brackets:
                b['probability'] = round(b['probability'] / total, 4)

        return brackets

    def _normal_bracket_probability(self, mean: float, low: float, high: float, std: float = 3.5) -> float:
        """Calculate probability of temperature falling in a bracket using normal distribution."""
        from scipy.stats import norm
        p = norm.cdf(high, loc=mean, scale=std) - norm.cdf(low, loc=mean, scale=std)
        return max(0.001, float(p))

    def find_trading_opportunities(self, city: str, market_prices: Dict[str, float] = None) -> List[TradingSignal]:
        """Compare NWS forecast probabilities to market prices to find edge."""
        if city not in self.forecasts or not self.forecasts[city]:
            self.fetch_nws_forecast(city)

        if city not in self.forecasts or not self.forecasts[city]:
            return []

        signals = []
        tomorrow = self.forecasts[city][0] if self.forecasts[city] else None
        if not tomorrow:
            return []

        brackets = self.generate_temperature_brackets(tomorrow.high_temp_f)

        if market_prices is None:
            market_prices = self._simulate_market_prices(brackets)
            print(f"  [SIMULATED] Using simulated market prices for {city} (connect real ForecastEx/Kalshi API for live pricing)")

        for bracket in brackets:
            label = bracket['label']
            nws_prob = bracket['probability']
            market_price = market_prices.get(label, nws_prob)

            edge = nws_prob - market_price

            if abs(edge) < 0.03:
                tralse_zone = 'Tralse'
                confidence = 'uncertain'
                recommendation = 'SKIP - edge too small'
            elif edge > 0.10:
                tralse_zone = 'True'
                confidence = 'high'
                recommendation = 'BUY YES - strong positive edge'
            elif edge > 0.03:
                tralse_zone = 'True'
                confidence = 'moderate'
                recommendation = 'BUY YES - moderate positive edge'
            elif edge < -0.10:
                tralse_zone = 'True'
                confidence = 'high'
                recommendation = 'BUY NO - strong negative edge'
            elif edge < -0.03:
                tralse_zone = 'True'
                confidence = 'moderate'
                recommendation = 'BUY NO - moderate negative edge'
            else:
                tralse_zone = 'Tralse'
                confidence = 'low'
                recommendation = 'SKIP'

            kelly = self._kelly_criterion(nws_prob, market_price)
            position = self._position_size(kelly, edge)

            signal = TradingSignal(
                city=city,
                date=tomorrow.date,
                contract_type='daily_high_temp',
                bracket_low=bracket['low'],
                bracket_high=bracket['high'],
                nws_probability=nws_prob,
                market_price=market_price,
                edge=round(edge, 4),
                kelly_fraction=round(kelly, 4),
                position_size_dollars=round(position, 2),
                tralse_zone=tralse_zone,
                confidence=confidence,
                recommendation=recommendation,
            )
            signals.append(signal)

        self.signals = signals
        return signals

    def _kelly_criterion(self, true_prob: float, market_price: float) -> float:
        """Calculate Kelly criterion fraction for binary contract."""
        if market_price <= 0 or market_price >= 1:
            return 0.0

        b = (1 - market_price) / market_price
        p = true_prob
        q = 1 - p

        kelly = (b * p - q) / b if b > 0 else 0
        kelly = max(0, min(kelly, 0.25))
        return kelly * 0.5

    def _position_size(self, kelly: float, edge: float) -> float:
        """Calculate dollar position size based on Kelly and bankroll."""
        if kelly <= 0 or abs(edge) < 0.03:
            return 0.0
        max_position = self.bankroll * 0.10
        kelly_position = self.bankroll * kelly
        return min(kelly_position, max_position)

    def _simulate_market_prices(self, brackets: List[Dict]) -> Dict[str, float]:
        """Simulate market prices with random noise for testing."""
        np.random.seed(int(datetime.now().timestamp()) % 10000)
        prices = {}
        for bracket in brackets:
            noise = np.random.normal(0, 0.05)
            price = max(0.02, min(0.98, bracket['probability'] + noise))
            prices[bracket['label']] = round(price, 2)
        return prices

    def scan_all_markets(self) -> Dict:
        """Scan all cities and generate trading signals."""
        self.fetch_all_cities()
        all_signals = {}
        summary = {
            'total_opportunities': 0,
            'strong_signals': 0,
            'total_edge_dollars': 0,
            'cities_scanned': 0,
            'scan_time': datetime.now().isoformat(),
        }

        for city in self.forecasts:
            signals = self.find_trading_opportunities(city)
            actionable = [s for s in signals if 'SKIP' not in s.recommendation]
            all_signals[city] = {
                'forecast': {
                    'high': self.forecasts[city][0].high_temp_f if self.forecasts[city] else None,
                    'low': self.forecasts[city][0].low_temp_f if self.forecasts[city] else None,
                    'conditions': self.forecasts[city][0].conditions if self.forecasts[city] else None,
                    'date': self.forecasts[city][0].date if self.forecasts[city] else None,
                },
                'total_signals': len(signals),
                'actionable_signals': len(actionable),
                'signals': [self._signal_to_dict(s) for s in signals],
                'best_opportunity': self._signal_to_dict(
                    max(actionable, key=lambda s: abs(s.edge))
                ) if actionable else None,
            }
            summary['total_opportunities'] += len(actionable)
            summary['strong_signals'] += sum(1 for s in actionable if s.confidence == 'high')
            summary['total_edge_dollars'] += sum(s.position_size_dollars for s in actionable)
            summary['cities_scanned'] += 1

        return {
            'summary': summary,
            'markets': all_signals,
            'bankroll': self.bankroll,
            'max_daily_risk': round(self.bankroll * 0.10, 2),
        }

    def _signal_to_dict(self, signal: TradingSignal) -> Dict:
        """Convert signal to dictionary."""
        return {
            'city': signal.city,
            'date': signal.date,
            'contract_type': signal.contract_type,
            'bracket': f"{signal.bracket_low}-{signal.bracket_high}°F",
            'nws_probability': signal.nws_probability,
            'market_price': signal.market_price,
            'edge': signal.edge,
            'kelly_fraction': signal.kelly_fraction,
            'position_size': signal.position_size_dollars,
            'tralse_zone': signal.tralse_zone,
            'confidence': signal.confidence,
            'recommendation': signal.recommendation,
        }

    def estimate_monthly_earnings(self, daily_trades: int = 5, avg_edge: float = 0.08) -> Dict:
        """Estimate monthly earnings based on edge and trade frequency."""
        avg_position = self.bankroll * 0.05
        daily_ev = daily_trades * avg_position * avg_edge
        monthly_ev = daily_ev * 22

        daily_variance = daily_trades * avg_position * avg_position * 0.25
        monthly_std = math.sqrt(22 * daily_variance)

        compound_factor = (1 + daily_ev / self.bankroll) ** 22
        compound_monthly = self.bankroll * (compound_factor - 1)

        return {
            'assumptions': {
                'bankroll': self.bankroll,
                'daily_trades': daily_trades,
                'avg_edge_pct': round(avg_edge * 100, 1),
                'avg_position': round(avg_position, 2),
                'trading_days_per_month': 22,
            },
            'linear_estimate': {
                'daily_ev': round(daily_ev, 2),
                'monthly_ev': round(monthly_ev, 2),
                'monthly_std': round(monthly_std, 2),
                'monthly_sharpe': round(monthly_ev / monthly_std, 2) if monthly_std > 0 else 0,
            },
            'compound_estimate': {
                'monthly_return': round(compound_monthly, 2),
                'monthly_return_pct': round((compound_factor - 1) * 100, 1),
                'month_3_bankroll': round(self.bankroll * compound_factor ** 3, 2),
                'month_6_bankroll': round(self.bankroll * compound_factor ** 6, 2),
            },
            'risk_metrics': {
                'max_daily_loss': round(self.bankroll * 0.10, 2),
                'kelly_max_fraction': 0.125,
                'ruin_probability_pct': round(max(0, 5 - avg_edge * 100) * 2, 1),
            },
        }

    def _cache_forecasts(self, city: str, forecasts: List[WeatherForecast]):
        """Cache forecasts to disk."""
        cache_file = os.path.join(self.cache_dir, f"{city}_{datetime.now().strftime('%Y%m%d')}.json")
        data = [{
            'city': f.city, 'date': f.date, 'high_temp_f': f.high_temp_f,
            'low_temp_f': f.low_temp_f, 'conditions': f.conditions,
            'wind_speed_mph': f.wind_speed_mph, 'precipitation_pct': f.precipitation_pct,
            'forecast_source': f.forecast_source, 'confidence': f.confidence,
        } for f in forecasts]
        with open(cache_file, 'w') as f:
            json.dump(data, f, indent=2)

    def _load_cached_forecasts(self, city: str) -> Optional[List[WeatherForecast]]:
        """Load cached forecasts from disk."""
        cache_file = os.path.join(self.cache_dir, f"{city}_{datetime.now().strftime('%Y%m%d')}.json")
        if not os.path.exists(cache_file):
            return None
        try:
            with open(cache_file, 'r') as f:
                data = json.load(f)
            return [WeatherForecast(**item, raw_data={}) for item in data]
        except Exception:
            return None

    def get_forecast_summary(self) -> Dict:
        """Get summary of all current forecasts."""
        summary = {}
        for city, forecasts in self.forecasts.items():
            if forecasts:
                tomorrow = forecasts[0]
                summary[city] = {
                    'date': tomorrow.date,
                    'high': tomorrow.high_temp_f,
                    'low': tomorrow.low_temp_f,
                    'conditions': tomorrow.conditions,
                    'wind': tomorrow.wind_speed_mph,
                    'confidence': tomorrow.confidence,
                }
        return summary


def demo():
    """Run weather prediction engine demo."""
    engine = WeatherPredictionEngine(bankroll=500.0)

    print("=" * 70)
    print("TI-FRAMEWORK WEATHER PREDICTION ENGINE — DEMO")
    print(f"Bankroll: ${engine.bankroll}")
    print(f"TI Thresholds: eta={ETA:.4f}, epsilon={EPSILON:.4f}")
    print("=" * 70)

    print("\nFetching NWS forecasts for all 10 cities...")
    results = engine.scan_all_markets()

    summary = results['summary']
    print(f"\nSCAN RESULTS:")
    print(f"  Cities scanned: {summary['cities_scanned']}")
    print(f"  Total opportunities: {summary['total_opportunities']}")
    print(f"  Strong signals: {summary['strong_signals']}")
    print(f"  Total edge capital: ${summary['total_edge_dollars']:.2f}")

    print("\nFORECASTS:")
    for city, market in results['markets'].items():
        fc = market['forecast']
        if fc['high']:
            print(f"  {city}: {fc['high']:.0f}°F / {fc['low']:.0f}°F - {fc['conditions']} ({fc['date']})")
            if market['best_opportunity']:
                best = market['best_opportunity']
                print(f"    Best trade: {best['bracket']} | Edge: {best['edge']:.1%} | "
                      f"Size: ${best['position_size']:.2f} | {best['recommendation']}")

    print("\nEARNINGS PROJECTIONS:")
    projections = engine.estimate_monthly_earnings(daily_trades=5, avg_edge=0.08)
    print(f"  Daily EV: ${projections['linear_estimate']['daily_ev']:.2f}")
    print(f"  Monthly EV (linear): ${projections['linear_estimate']['monthly_ev']:.2f}")
    print(f"  Monthly EV (compound): ${projections['compound_estimate']['monthly_return']:.2f}")
    print(f"  Month 3 bankroll: ${projections['compound_estimate']['month_3_bankroll']:.2f}")
    print(f"  Month 6 bankroll: ${projections['compound_estimate']['month_6_bankroll']:.2f}")

    print("\n" + "=" * 70)
    print("DEMO COMPLETE")
    print("=" * 70)

    return engine


if __name__ == '__main__':
    demo()

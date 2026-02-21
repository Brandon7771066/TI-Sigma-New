"""
Kalshi Live Market Scanner
===========================
Connects to Kalshi API with RSA-PSS authentication to scan real markets.
Identifies high-confidence prediction opportunities using TI Framework analysis.
"""

import os
import time
import base64
import hashlib
import requests
from datetime import datetime, timezone
from typing import List, Dict, Optional, Any
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding, utils


class KalshiLiveScanner:
    PROD_BASE = "https://api.elections.kalshi.com/trade-api/v2"
    DEMO_BASE = "https://demo-api.kalshi.com/trade-api/v2"

    def __init__(self, use_demo: bool = False):
        self.api_key_id = os.environ.get('KALSHI_API_KEY_ID', '')
        raw_key = os.environ.get('KALSHI_PRIVATE_KEY', '')
        self.private_key_pem = raw_key.replace('\\n', '\n') if raw_key else ''
        self.base_url = self.DEMO_BASE if use_demo else self.PROD_BASE
        self._private_key = None
        self._connected = False

    def _load_private_key(self):
        if self._private_key is None and self.private_key_pem:
            self._private_key = serialization.load_pem_private_key(
                self.private_key_pem.encode(), password=None
            )
        return self._private_key

    def _make_request(self, method: str, endpoint: str, params: dict = None, json_body: dict = None) -> Optional[dict]:
        path = f"/trade-api/v2{endpoint}"
        timestamp_ms = int(datetime.now(timezone.utc).timestamp() * 1000)

        msg = f"{timestamp_ms}{method.upper()}{path}".encode()
        digest = hashlib.sha256(msg).digest()

        key = self._load_private_key()
        if not key:
            return None

        signature = key.sign(
            digest,
            padding.PSS(
                mgf=padding.MGF1(hashes.SHA256()),
                salt_length=padding.PSS.MAX_LENGTH
            ),
            utils.Prehashed(hashes.SHA256())
        )

        headers = {
            'KALSHI-ACCESS-KEY': self.api_key_id,
            'KALSHI-ACCESS-SIGNATURE': base64.b64encode(signature).decode(),
            'KALSHI-ACCESS-TIMESTAMP': str(timestamp_ms),
            'Content-Type': 'application/json',
            'Accept': 'application/json'
        }

        url = f"{self.base_url}{endpoint}"

        try:
            if method.upper() == 'GET':
                resp = requests.get(url, headers=headers, params=params, timeout=15)
            elif method.upper() == 'POST':
                resp = requests.post(url, headers=headers, json=json_body, timeout=15)
            else:
                return None

            if resp.status_code == 200 or resp.status_code == 201:
                return resp.json()
            else:
                print(f"Kalshi API error {resp.status_code}: {resp.text[:200]}")
                return None
        except Exception as e:
            print(f"Kalshi request error: {e}")
            return None

    def connect(self) -> bool:
        if not self.api_key_id or not self.private_key_pem:
            print("Missing Kalshi credentials")
            return False

        try:
            self._load_private_key()
            result = self._make_request('GET', '/portfolio/balance')
            if result is not None:
                self._connected = True
                balance_cents = result.get('balance', 0)
                print(f"Kalshi connected! Balance: ${balance_cents / 100:.2f}")
                return True
            else:
                print("Kalshi connection failed - check API credentials")
                return False
        except Exception as e:
            print(f"Kalshi connection error: {e}")
            return False

    def get_balance(self) -> float:
        result = self._make_request('GET', '/portfolio/balance')
        if result:
            return result.get('balance', 0) / 100.0
        return 0.0

    def get_positions(self) -> List[Dict]:
        result = self._make_request('GET', '/portfolio/positions')
        if result:
            return result.get('market_positions', [])
        return []

    def scan_all_markets(self, limit: int = 200, category: str = None) -> List[Dict]:
        all_markets = []
        cursor = None

        while len(all_markets) < limit:
            params = {'limit': min(100, limit - len(all_markets)), 'status': 'open'}
            if cursor:
                params['cursor'] = cursor

            result = self._make_request('GET', '/markets', params=params)
            if not result:
                break

            markets = result.get('markets', [])
            if not markets:
                break

            for m in markets:
                if category and m.get('category', '').lower() != category.lower():
                    continue
                analyzed = self._analyze_market(m)
                if analyzed:
                    all_markets.append(analyzed)

            cursor = result.get('cursor')
            if not cursor:
                break

            time.sleep(0.2)

        all_markets.sort(key=lambda x: x.get('profit_potential', 0), reverse=True)
        return all_markets

    def scan_events(self, limit: int = 50) -> List[Dict]:
        params = {'limit': limit, 'status': 'open'}
        result = self._make_request('GET', '/events', params=params)
        if result:
            return result.get('events', [])
        return []

    def scan_weather_markets(self, cities: list = None) -> List[Dict]:
        if cities is None:
            cities = ['NY', 'CHI', 'MIA', 'LA', 'DEN', 'ATL', 'PHX', 'HOU', 'SF', 'SEA']

        all_weather = []
        for city in cities:
            series = f"KXHIGH{city}"
            params = {'limit': 50, 'status': 'open', 'series_ticker': series}
            result = self._make_request('GET', '/markets', params=params)
            if result:
                for m in result.get('markets', []):
                    analyzed = self._analyze_market(m)
                    if analyzed:
                        analyzed['subcategory'] = f'Weather - {city}'
                        all_weather.append(analyzed)
            time.sleep(0.1)

        all_weather.sort(key=lambda x: x.get('profit_potential', 0), reverse=True)
        return all_weather

    def scan_profitable_opportunities(self, min_profit_pct: float = 3.0, min_volume: int = 100) -> List[Dict]:
        all_opps = []
        cursor = None
        pages = 0

        while pages < 10:
            params = {'limit': 100, 'status': 'open'}
            if cursor:
                params['cursor'] = cursor

            result = self._make_request('GET', '/markets', params=params)
            if not result:
                break

            markets = result.get('markets', [])
            if not markets:
                break

            for m in markets:
                analyzed = self._analyze_market(m)
                if analyzed and analyzed.get('profit_potential', 0) >= min_profit_pct and analyzed.get('volume', 0) >= min_volume:
                    all_opps.append(analyzed)

            cursor = result.get('cursor')
            if not cursor:
                break

            pages += 1
            time.sleep(0.2)

        all_opps.sort(key=lambda x: (x.get('our_probability', 0), x.get('profit_potential', 0)), reverse=True)
        return all_opps

    def _analyze_market(self, market_data: dict) -> Optional[Dict]:
        ticker = market_data.get('ticker', '')
        title = market_data.get('title', '')
        subtitle = market_data.get('subtitle', '')
        yes_bid = market_data.get('yes_bid', 0) or 0
        yes_ask = market_data.get('yes_ask', 100) or 100
        no_bid = market_data.get('no_bid', 0) or 0
        no_ask = market_data.get('no_ask', 100) or 100
        last_price = market_data.get('last_price', 0) or 0
        volume = market_data.get('volume', 0) or 0
        open_interest = market_data.get('open_interest', 0) or 0
        close_time = market_data.get('close_time', '')
        category = market_data.get('category', '')
        result = market_data.get('result', '')
        series_ticker = market_data.get('series_ticker', '')

        best_yes_price = yes_ask if yes_ask > 0 else last_price
        best_no_price = no_ask if no_ask > 0 else (100 - last_price if last_price > 0 else 50)

        if best_yes_price <= 1 or best_yes_price >= 99:
            return None

        market_implied_prob = best_yes_price / 100.0

        if market_implied_prob >= 0.90:
            consensus_strength = market_implied_prob
            recommended_position = 'YES'
            reasoning = f"Very strong market consensus ({market_implied_prob:.0%} YES). Not our edge - this is what the market believes."
        elif market_implied_prob <= 0.10:
            consensus_strength = 1 - market_implied_prob
            recommended_position = 'NO'
            reasoning = f"Very strong market consensus against (only {market_implied_prob:.0%} YES). Reflects market belief, not independent analysis."
        elif market_implied_prob >= 0.75:
            consensus_strength = market_implied_prob
            recommended_position = 'YES'
            reasoning = f"Strong market consensus ({market_implied_prob:.0%} YES). Profit margin is narrow at this price."
        elif market_implied_prob <= 0.25:
            consensus_strength = 1 - market_implied_prob
            recommended_position = 'NO'
            reasoning = f"Strong market consensus against ({market_implied_prob:.0%} YES)."
        elif market_implied_prob >= 0.60:
            consensus_strength = market_implied_prob
            recommended_position = 'YES'
            reasoning = f"Moderate YES lean ({market_implied_prob:.0%}). Higher risk - consider carefully."
        elif market_implied_prob <= 0.40:
            consensus_strength = 1 - market_implied_prob
            recommended_position = 'NO'
            reasoning = f"Moderate NO lean ({market_implied_prob:.0%} YES). Higher risk - consider carefully."
        else:
            consensus_strength = max(market_implied_prob, 1 - market_implied_prob)
            recommended_position = 'YES' if market_implied_prob >= 0.5 else 'NO'
            reasoning = f"Near 50/50 ({market_implied_prob:.0%}). No clear consensus - avoid without independent analysis."

        our_probability = consensus_strength

        if recommended_position == 'YES':
            entry_price = best_yes_price
        else:
            entry_price = best_no_price

        profit_potential = ((100 - entry_price) / entry_price * 100) if entry_price > 0 else 0

        days_to_close = 0
        if close_time:
            try:
                close_dt = datetime.fromisoformat(close_time.replace('Z', '+00:00'))
                days_to_close = max(0, (close_dt - datetime.now(timezone.utc)).days)
            except:
                pass

        display_title = title
        if subtitle:
            display_title = f"{title} - {subtitle}"

        return {
            'ticker': ticker,
            'title': display_title,
            'category': category,
            'series_ticker': series_ticker,
            'yes_bid': yes_bid,
            'yes_ask': yes_ask,
            'no_bid': no_bid,
            'no_ask': no_ask,
            'yes_price': best_yes_price,
            'no_price': best_no_price,
            'last_price': last_price,
            'volume': volume,
            'open_interest': open_interest,
            'close_time': close_time,
            'days_to_close': days_to_close,
            'market_implied_prob': market_implied_prob,
            'our_probability': our_probability,
            'recommended_position': recommended_position,
            'entry_price': entry_price,
            'profit_potential': profit_potential,
            'reasoning': reasoning
        }

    def place_order(self, ticker: str, side: str, quantity: int, price_cents: int) -> Optional[Dict]:
        if not self._connected:
            print("Not connected to Kalshi")
            return None

        order_body = {
            'ticker': ticker,
            'client_order_id': f"TI-{int(datetime.now().timestamp())}",
            'side': side,
            'action': 'buy',
            'count': quantity,
            'type': 'limit',
        }

        if side == 'yes':
            order_body['yes_price'] = price_cents
        else:
            order_body['no_price'] = price_cents

        result = self._make_request('POST', '/portfolio/orders', json_body=order_body)
        return result

    def get_orderbook(self, ticker: str) -> Optional[Dict]:
        result = self._make_request('GET', f'/markets/{ticker}/orderbook')
        return result


if __name__ == '__main__':
    scanner = KalshiLiveScanner()
    if scanner.connect():
        print(f"\nBalance: ${scanner.get_balance():.2f}")
        markets = scanner.scan_all_markets(limit=20)
        print(f"\nFound {len(markets)} markets")
        high_conf = [m for m in markets if m['our_probability'] >= 0.85]
        print(f"High confidence (85%+): {len(high_conf)}")
        for m in high_conf[:5]:
            print(f"  [{m['our_probability']:.0%}] {m['title'][:60]} | {m['recommended_position']} @ ${m['entry_price']/100:.2f}")
    else:
        print("Could not connect to Kalshi")
